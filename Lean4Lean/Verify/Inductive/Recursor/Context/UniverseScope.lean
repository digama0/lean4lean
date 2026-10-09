import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorAlignment

/-! Universe-scope infrastructure for recursor contexts.

`whnf` in a recursor context preserves the universe-parameter support of its
input (`VContext.LevelsBelow`), relative to any universe scope of the local
context.  This file collects the lemmas transporting that invariant to the
inductive checker's reader contexts: closing bound telescopes, building
universe scopes from declared types, and the universe support of the header
parameters.  The motive pass of the recursor construction uses them to show
that the index telescope of each family mentions only the declaration's
universe parameters. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem _root_.Except.WF.and {ε α : Type} {x : Except ε α} {Q R : α → Prop}
    (h1 : x.WF Q) (h2 : x.WF R) : x.WF fun a => Q a ∧ R a :=
  fun a h => ⟨h1 a h, h2 a h⟩

@[simp] theorem Expr.levelParamsIn_instantiate1_fvar (e : Expr) (fv : FVarId) (k : Nat) :
    (e.instantiate1' (.fvar fv) k).levelParamsIn params = e.levelParamsIn params := by
  induction e generalizing k <;> simp [Expr.instantiate1', Expr.levelParamsIn, *]
  case bvar i =>
    split
    · rfl
    · split <;> rfl

theorem Expr.levelParamsIn_consumeTypeAnnotationsVerified {e : Expr}
    (H : e.levelParamsIn params = true) : (e.consumeTypeAnnotationsVerified annOk).levelParamsIn params = true := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  all_goals simp_all [Expr.levelParamsIn]

namespace VerifyInductive

/-! ### Type-checker runs in a recursor context -/

theorem _root_.Lean4Lean.IsFVarUpSet.and {P Q : FVarId → Prop} (Δ : VLCtx)
    (hP : IsFVarUpSet P Δ) (hQ : IsFVarUpSet Q Δ) :
    IsFVarUpSet (fun fv => P fv ∧ Q fv) Δ := by
  induction Δ with
  | nil => trivial
  | cons d Δ ih =>
    obtain ⟨ofv, d⟩ := d
    cases ofv with
    | none => exact ih hP hQ
    | some p =>
      obtain ⟨fv, deps⟩ := p
      exact ⟨ih hP.1 hQ.1, fun ⟨hp, hq⟩ fv' h => ⟨hP.2 hp fv' h, hQ.2 hq fv' h⟩⟩

/-- Universe support established in the checker context of a recursor frame
holds in its main context, for inputs translated in the checker context. -/
theorem RecursorContextWF.levelsBelow_of_check (Hc : RecursorContextWF c recLparams)
    (hn : TrExprS Hc.venv recLparams Hc.chk.vlctx e e₀)
    (h : Hc.checkTC.LevelsBelow e e₁) : Hc.typeChecker.LevelsBelow e e₁ := by
  intro Us P hs he hP
  refine h Us (fun fv => P fv ∧ fv ∈ Hc.chk.vlctx.fvars) ⟨?_, ?_⟩ he ?_
  · exact IsFVarUpSet.and _ (Hc.check.embed.isFVarUpSet hs.1)
      (IsFVarUpSet.fvars Hc.check.wf.tr.wf.fvwf)
  · intro fv d ⟨hPfv, _⟩ hfind
    change Hc.chk.lctx.find? fv = some d at hfind
    rw [Hc.check.lctx_eq] at hfind
    obtain ⟨d', hfind', hd⟩ := Hc.check.sub fv d hfind
    have hmain : Hc.typeChecker.lctx'.find? fv = some d' := by
      change Hc.mlctx.lctx.find? fv = some d'
      rw [Hc.lctx_eq]; exact hfind'
    have h' := hs.2 fv d' hPfv hmain
    have htype : d'.type = d.type := by
      have e1 : ∀ x : LocalDecl, (x.setIndex 0).type = x.type := by
        intro x; cases x <;> rfl
      rw [← e1 d', hd, e1 d]
    have hvalue : ∀ v, d.value? true = some v → d'.value? true = some v := by
      have e1 : ∀ x : LocalDecl, (x.setIndex 0).value? true = x.value? true := by
        intro x; cases x with
        | cdecl => rfl
        | ldecl _ _ _ _ _ nd => cases nd <;> rfl
      intro v hv
      rw [← e1 d', hd, e1 d]; exact hv
    exact ⟨htype ▸ h'.1, fun v hv => h'.2 v (hvalue v hv)⟩
  · have hc := (fvarsIn_iff.mp hn.fvarsIn).1
    refine fvarsIn_iff.mpr ⟨fun fv hfv => ⟨(fvarsIn_iff.mp hP).1 fv hfv, hc fv hfv⟩,
      (fvarsIn_iff.mp hP).2⟩

/-- `whnf` in a recursor context preserves the universe support of its
input; the run is verified in the checker context, on the checker
translation `hn` of the input. -/
theorem whnfInRecursorContext.levelsWF
    (Hc : RecursorContextWF c recLparams)
    (hn : TrExprS Hc.venv recLparams Hc.chk.vlctx e e₀) :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      Hc.typeChecker.LevelsBelow e e₁ :=
  (liftTypeChecker.recursorWF Hc
    ((TypeChecker.Inner.whnf.WF_levels hn).run)).mono fun _ h =>
      Hc.levelsBelow_of_check hn h

/-! ### Closed telescopes -/

theorem LocalContext.levelParamsIn_mkForall_foldN
    {lctx : LocalContext} {fvars : List FVarId} {Us : List Name}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind) ∧
        type.levelParamsIn Us = true)
    {body : Expr} (hbody : body.levelParamsIn Us = true) :
    (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
      (result.abstractN [fv])) body).levelParamsIn Us = true := by
  induction fvars with
  | nil => exact hbody
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind, htype⟩ := hdecl fv (by simp)
    have ih' := ih (fun other hother => hdecl other (by simp [hother]))
    simp only [List.foldr_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.levelParamsIn, Bool.and_eq_true,
      Expr.levelParamsIn_abstractN]
    exact ⟨htype, ih'⟩

/-- A telescope closed over bound ordinary declarations whose types mention
only `Us` mentions only `Us` when its body does. -/
theorem FVarArrayIn.mkForall_levelParamsIn
    (H : FVarArrayIn c xs) (Hc : BindingContextWF c)
    (hnodup : H.fvars.Nodup) {Us : List Name}
    (htypes : ∀ fv ∈ H.fvars, ∀ decl, c.lctx.find? fv = some decl →
      decl.type.levelParamsIn Us = true)
    {body : Expr} (hbody : body.levelParamsIn Us = true) :
    (c.lctx.mkForall xs body).levelParamsIn Us = true := by
  have hdecl : ∀ fv ∈ H.fvars, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) ∧
        type.levelParamsIn Us = true := by
    intro fv hfv
    obtain ⟨index, name, type, bi, kind, h⟩ := Hc.findCDecl fv (H.members fv hfv)
    exact ⟨index, name, type, bi, kind, h, htypes fv hfv _ h⟩
  have hfind : ∀ fv ∈ H.fvars, ∃ decl, c.lctx.find? fv = some decl := by
    intro fv hfv
    obtain ⟨index, name, type, bi, kind, h, _⟩ := hdecl fv hfv
    exact ⟨_, h⟩
  rw [H.expressions, LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  exact LocalContext.levelParamsIn_mkForall_foldN hdecl hbody

/-- Conversely, a telescope over ordinary declarations mentioning only `Us`
has its declared binder types in `Us`. -/
theorem LocalContext.levelParamsIn_mkForall_foldN_types
    {lctx : LocalContext} {fvars : List FVarId} {Us : List Name}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    {body : Expr}
    (h : (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
      (result.abstractN [fv])) body).levelParamsIn Us = true) :
    ∀ fv ∈ fvars, ∀ decl, lctx.find? fv = some decl →
      decl.type.levelParamsIn Us = true := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl fv (by simp)
    simp only [List.foldr_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.levelParamsIn, Bool.and_eq_true,
      Expr.levelParamsIn_abstractN] at h
    intro other hother decl hdecl'
    simp only [List.mem_cons] at hother
    rcases hother with rfl | hother
    · rw [hfind] at hdecl'
      cases hdecl'
      simpa [LocalDecl.type] using h.1
    · exact ih (fun o ho => hdecl o (by simp [ho])) h.2 other hother decl hdecl'

/-- A telescope closed over bound ordinary declarations mentions only `Us`
only if their declared types do. -/
theorem FVarArrayIn.mkForall_levelParamsIn_types
    (H : FVarArrayIn c xs) (Hc : BindingContextWF c)
    (hnodup : H.fvars.Nodup) {Us : List Name} {body : Expr}
    (h : (c.lctx.mkForall xs body).levelParamsIn Us = true) :
    ∀ fv ∈ H.fvars, ∀ decl, c.lctx.find? fv = some decl →
      decl.type.levelParamsIn Us = true := by
  have hdecl : ∀ fv ∈ H.fvars, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) :=
    fun fv hfv => Hc.findCDecl fv (H.members fv hfv)
  have hfind : ∀ fv ∈ H.fvars, ∃ decl, c.lctx.find? fv = some decl := by
    intro fv hfv
    obtain ⟨index, name, type, bi, kind, h⟩ := hdecl fv hfv
    exact ⟨_, h⟩
  rw [H.expressions, LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup] at h
  exact LocalContext.levelParamsIn_mkForall_foldN_types hdecl h

/-! ### Universe scopes of recursor contexts -/

/-- In a recursor context every declaration is an ordinary local, so a
universe scope only constrains the declared types. -/
theorem RecursorContextWF.universeScope_of_types
    (R : RecursorContextWF c recLparams) {Us : List Name} {P : FVarId → Prop}
    (hup : IsFVarUpSet P R.mlctx.vlctx)
    (htypes : ∀ fv, P fv → ∀ decl, c.lctx.find? fv = some decl →
      decl.type.levelParamsIn Us = true) :
    R.typeChecker.UniverseScope Us P := by
  refine ⟨hup, fun fv decl hP hfind => ?_⟩
  change R.mlctx.lctx.find? fv = some decl at hfind
  rw [R.lctx_eq] at hfind
  refine ⟨htypes fv hP decl hfind, ?_⟩
  intro v hv
  have Hc := R.toBindingContextWF
  rw [Hc.wf.find?_eq_find?_toList] at hfind
  obtain ⟨index, fv', name, type, bi, kind, rfl⟩ :=
    Hc.onlyLams decl (List.mem_of_find?_eq_some hfind)
  simp [LocalDecl.value?] at hv

/-- A universe scope of the root of an exact recent suffix, denoting only
root variables, remains a universe scope after the suffix: the fresh binders
are outside it and the root declarations are unchanged. -/
theorem RecursorFVarSuffix.universeScope
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorFVarSuffix Rroot R xs)
    {Us : List Name} {P : FVarId → Prop}
    (hscope : ∀ fv, P fv → fv ∈ Rroot.mlctx.vlctx.fvars)
    (hU : Rroot.typeChecker.UniverseScope Us P) :
    R.typeChecker.UniverseScope Us P := by
  refine ⟨H.upsetRoot hscope hU.1, fun fv decl hP hfind => hU.2 fv decl hP ?_⟩
  have hmem : fv ∈ root.lctx.fvars := by
    rw [← Rroot.lctx_eq, Rroot.mlctx_wf.tr.fvars_eq]
    exact hscope fv hP
  change R.mlctx.lctx.find? fv = some decl at hfind
  change Rroot.mlctx.lctx.find? fv = some decl
  rw [R.lctx_eq, H.contextLE.declarations fv hmem] at hfind
  rw [Rroot.lctx_eq]
  exact hfind

/-- Every declaration of a header context mentions only the declaration's
universe parameters. -/
theorem ContextWF.find?_levelParamsIn (Hc : ContextWF c)
    {fv : FVarId} {decl : LocalDecl} (hfind : c.lctx.find? fv = some decl) :
    decl.type.levelParamsIn c.lparams = true := by
  have htr := Hc.mlctx_wf.tr
  rw [Hc.lctx_eq] at htr
  have hm : decl ∈ c.lctx.toList := by
    rw [htr.1.find?_eq_find?_toList] at hfind
    exact List.mem_of_find?_eq_some hfind
  obtain ⟨_, _, _, _, _, _, hty⟩ := htr.find?_of_mem Hc.checking.tr.wf hm
  exact hty.levelParamsIn

/-- The declared types of the parameter variables mention only the
declaration's universe parameters. -/
def ParameterUniverseSupport (c : AddInductive.Context) (params : Array Expr) : Prop :=
  ∀ fv ∈ ExprArrayFVarIds params, ∀ decl, c.lctx.find? fv = some decl →
    decl.type.levelParamsIn c.lparams = true

theorem ParameterUniverseSupport.mono
    (H : ParameterUniverseSupport c params) (Hparams : FVarArrayIn c params)
    (hle : BindingContextLE c c') : ParameterUniverseSupport c' params := by
  intro fv hfv decl hfind
  have hmem : fv ∈ c.lctx.fvars := by
    apply Hparams.members
    rw [← Hparams.exprArrayFVarIds]
    exact hfv
  rw [hle.declarations fv hmem] at hfind
  rw [hle.lparams_eq]
  exact H fv hfv decl hfind

/-- The parameters of a header context, transported to any later binding
context of a root with the same local context and universe parameters. -/
theorem ParameterUniverseSupport.of_contextWF {c root c' : AddInductive.Context}
    (Hc : ContextWF c) (Hparams : FVarArrayIn c params)
    (hlctx : root.lctx = c.lctx) (hlparams : root.lparams = c.lparams)
    (hle : BindingContextLE root c') : ParameterUniverseSupport c' params := by
  intro fv hfv decl hfind
  have hmem : fv ∈ root.lctx.fvars := by
    rw [hlctx]
    apply Hparams.members
    rw [← Hparams.exprArrayFVarIds]
    exact hfv
  rw [hle.declarations fv hmem, hlctx] at hfind
  rw [hle.lparams_eq, hlparams]
  exact Hc.find?_levelParamsIn hfind

end VerifyInductive
end Lean4Lean
