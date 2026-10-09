import Lean4Lean.Verify.Inductive.Recursor.Context.TelescopeUniqueness
import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorPremises
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldTypeScope
import Lean4Lean.Verify.Inductive.Recursor.Signature.RecursorTypeInversion
import Lean4Lean.Verify.Inductive.Recursor.Signature.FieldDomainsDefEq

/-! Induction-hypothesis binder groups of the checked recursor type, read off the typed
recursive calls of each field.

`RecursorConstruction.recursorTelescope_hypothesisDomains` identifies the `j`-th hypothesis of a
minor premise of the checked recursor type as a telescope `A` whose domains translate the
argument domains of the recorded induction hypothesis type in the full generator context
(parameters, motives, earlier minors, all fields and the earlier hypotheses). The typed call
templates of the field (`TypedCallTemplatesAt`) record that the generated recursive call is
scoped by the field's own prefix: its argument telescope mentions only the parameters and the
fields before the recursive field. Since the induction hypothesis type and the typed call have
the same `replayTrace`, the hypothesis's argument domains and closed exposed indices inherit
that scope.

Abstracting variables that do not occur is a de Bruijn lift, so the generator sources are lifts
of sources closed only over the field prefix and the parameters. The small translations come
from the checking contexts of the minor pass: the call-local arguments were opened in a
checking context whose base is the field's checking context cut just before the recursive
field, so the binder domains and indices translate there, and closing that checking context
gives translations in `parameters ++ fields.take pos`. Forward weakening
(`TrExprS.liftStep`) and syntactic uniqueness then identify every domain of
`A`, and every index of the motive application, as
`InductiveSignature.Instance.underFields` of these small translations.  This is
`RecursorConstruction.recursorTelescope_hypothesisUnlift`. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- `abstract1` is injective: loose bound variables below the cutoff are
fixed, those at or above it are shifted by one, and only the abstracted variable becomes the
cutoff itself. -/
theorem Expr.abstract1_injective {v : FVarId} :
    ∀ {e e' : Expr} {k : Nat}, e.abstract1 v k = e'.abstract1 v k → e = e' := by
  intro e
  induction e with
  | bvar i =>
    intro e' k h
    cases e' with
    | bvar i' =>
      simp only [Expr.abstract1, Expr.bvar.injEq] at h
      congr 1; split at h <;> split at h <;> omega
    | fvar w =>
      simp only [Expr.abstract1] at h
      by_cases hw : v = w
      · subst hw; simp at h; split at h <;> omega
      · simp [hw] at h
    | _ => simp [Expr.abstract1] at h
  | fvar u =>
    intro e' k h
    cases e' with
    | bvar i' =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u
      · subst hu; simp at h; split at h <;> omega
      · simp [hu] at h
    | fvar w =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u <;> by_cases hw : v = w <;> simp_all
    | _ =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u <;> simp [hu] at h
  | app f a ihf iha =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [ihf h.1, iha h.2]
  | lam n t b bi iht ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2]
  | forallE n t b bi iht ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2]
  | letE n t val b nd iht ihv ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihv h.2.2.1, ihb h.2.2.2.1, h.2.2.2.2]
  | mdata m b ih =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, ih h.2]
  | proj s i b ih =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, h.2.1, ih h.2.2]
  | _ =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try split at h) <;> simp_all

theorem Expr.abstractList_injective :
    ∀ {xs : List FVarId} {e e' : Expr} {k : Nat},
      e.abstractList xs k = e'.abstractList xs k → e = e'
  | [], _, _, _, h => by simpa using h
  | _ :: _, _, _, _, h => Expr.abstract1_injective (Expr.abstractList_injective h)

theorem insertBinders_append (Fs B : List VExpr) (m : Nat) :
    InductiveSignature.insertBinders (Fs ++ B) m =
      InductiveSignature.insertBinders Fs m ++
        (B.zipIdx Fs.length).map fun (e, k) => e.liftN m k := by
  simp [InductiveSignature.insertBinders, List.zipIdx_append]

theorem liftContextPrefix_reverse_reverse (l : List VExpr) (n : Nat) :
    (liftContextPrefix n l.reverse).reverse = InductiveSignature.insertBinders l n := by
  rw [insertBinders_eq_prefix]; rfl

theorem zipIdx_twoLift_eq (B0 : List VExpr) (pos m g : Nat) :
    B0.zipIdx.map (fun (e, k) => (e.liftN m (pos + k)).liftN g k) =
      InductiveSignature.insertBinders ((B0.zipIdx pos).map fun (e, k) => e.liftN m k) g := by
  apply List.ext_getElem
  · simp [InductiveSignature.insertBinders]
  · intro i h₁ h₂
    simp [InductiveSignature.insertBinders, List.getElem_zipIdx]

/-- Forward two-group insertion: a translation in the small context
`PP ++ Fs ++ B0` yields, after inserting `M` directly above `Fs` and `G`
directly above the (lifted) inner telescope `B0`, the doubly lifted
translation of the doubly lifted source. -/
theorem TrExprS.liftStep {env : VEnv} {Us : List Name} (henv : env.Ordered)
    {PP M Fs G B0 : List VExpr} {source : Expr} {t : VExpr}
    (Ht : TrExprS env Us (abstractForallContext (PP ++ Fs ++ B0) []) source t) :
    TrExprS env Us (abstractForallContext (PP ++ M ++
      InductiveSignature.insertBinders Fs M.length ++ G ++
      InductiveSignature.insertBinders
        ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) G.length) [])
      ((source.liftLooseBVars' (Fs.length + B0.length) M.length).liftLooseBVars'
        B0.length G.length)
      ((t.liftN M.length (Fs.length + B0.length)).liftN G.length B0.length) := by
  have hlen : ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k).length =
      B0.length := by
    simp
  have H₁ := TrExprS.insertBeforeInner henv (outer := PP) (inner := Fs ++ B0)
    (by simpa [List.append_assoc] using Ht) M
  dsimp only at H₁
  rw [liftContextPrefix_reverse_reverse, insertBinders_append, List.length_append] at H₁
  have H₂ := TrExprS.insertBeforeInner henv
    (outer := PP ++ M ++ InductiveSignature.insertBinders Fs M.length)
    (inner := (B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k)
    (by simpa [List.append_assoc] using H₁) G
  dsimp only at H₂
  rw [liftContextPrefix_reverse_reverse, hlen] at H₂
  simpa [List.append_assoc] using H₂

/-- A telescope sitting below the two inserted groups is, binder by binder,
the double lift of the small telescope `B0`, whenever every binder of `B0`
translates the corresponding small source. -/
theorem TrExprS.liftTelescope_eq {env : VEnv} {Us : List Name} (henv : env.Ordered)
    {PP M Fs G : List VExpr} (A B0 : List VExpr) (src : Nat → Expr)
    (hlen : B0.length = A.length)
    (Hsmall : ∀ i (hi : i < B0.length),
      TrExprS env Us (abstractForallContext (PP ++ Fs ++ B0.take i) []) (src i) B0[i])
    (H : ∀ i (hi : i < A.length), TrExprS env Us (abstractForallContext
      (PP ++ M ++ InductiveSignature.insertBinders Fs M.length ++ G ++ A.take i) [])
      (((src i).liftLooseBVars' (Fs.length + i) M.length).liftLooseBVars' i G.length) A[i]) :
    A = B0.zipIdx.map (fun (e, k) => (e.liftN M.length (Fs.length + k)).liftN G.length k) := by
  suffices h : ∀ i, i ≤ A.length → A.take i = (B0.take i).zipIdx.map (fun (e, k) =>
      (e.liftN M.length (Fs.length + k)).liftN G.length k) by
    have := h A.length (Nat.le_refl _)
    rwa [List.take_length, ← hlen, List.take_length] at this
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hiA : i < A.length := by omega
    have hiB : i < B0.length := by omega
    have htake := ih (by omega)
    have Hi := H i hiA
    rw [htake, zipIdx_twoLift_eq] at Hi
    have hBi : (B0.take i).length = i := by simp; omega
    have Hs := TrExprS.liftStep henv (PP := PP) (M := M) (G := G) (by
      simpa using Hsmall i hiB)
    rw [hBi] at Hs
    have heq := Hi.uniqueS Hs
    rw [List.take_succ_eq_append_getElem hiA, htake, heq,
      List.take_succ_eq_append_getElem hiB, List.zipIdx_append, List.map_append, hBi]
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, Nat.zero_add]

/-- Pointwise form of `TrExprS.liftStep` for a list of translations in the
context extended by the whole telescope. -/
theorem TrExprS.liftForall₂_eq {env : VEnv} {Us : List Name} (henv : env.Ordered)
    {PP M Fs G B0 : List VExpr} {srcs : List Expr} {indices I : List VExpr}
    (Hs : List.Forall₂ (TrExprS env Us (abstractForallContext (PP ++ Fs ++ B0) [])) srcs indices)
    (H : List.Forall₂ (TrExprS env Us (abstractForallContext (PP ++ M ++
      InductiveSignature.insertBinders Fs M.length ++ G ++
      InductiveSignature.insertBinders
        ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) G.length) []))
      (srcs.map fun s => (s.liftLooseBVars' (Fs.length + B0.length) M.length).liftLooseBVars'
        B0.length G.length) I) :
    I = indices.map (fun e =>
      (e.liftN M.length (Fs.length + B0.length)).liftN G.length B0.length) := by
  induction Hs generalizing I with
  | nil => cases H; rfl
  | cons hs _ ih =>
    cases H with
    | cons hb tb => rw [List.map_cons, hb.uniqueS (TrExprS.liftStep henv hs), ih tb]

theorem TrExprS.getAppArgsList_translations {env : VEnv} {Us : List Name}
    {Δ : VLCtx} {e : Expr} {t : VExpr} (H : TrExprS env Us Δ e t) :
    ∃ args', List.Forall₂ (TrExprS env Us Δ) e.getAppArgsList args' := by
  rw [← Expr.mkAppList_getAppArgsList e] at H
  obtain ⟨_, args', _, hargs, _⟩ := checkPositivityStep.TrExprS.mkAppList_inv H
  exact ⟨args', hargs⟩

theorem _root_.List.Forall₂.drop_both {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ n : Nat,
      List.Forall₂ R (l.drop n) (l'.drop n)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => .cons h t
  | _, _, .cons _ t, n + 1 => t.drop_both n

/-- Closing a term that mentions only parameters and a field prefix over the
generator's hypothesis prefix, all fields and the outer binders is closing it
over the field prefix and the parameters, followed by two lifts: by the outer
non-parameter binders above the field prefix, and by the remaining fields and
hypotheses below it. -/
theorem Expr.closeShapeSource (X : Expr) (hyps F1 F2 P M : List FVarId) (d : Nat)
    (hscope : X.FVarsIn fun fv => fv ∈ F1 ∨ fv ∈ P)
    (hhyps : ∀ fv ∈ hyps, fv ∉ F1 ∧ fv ∉ P)
    (hF2 : ∀ fv ∈ F2, fv ∉ F1 ∧ fv ∉ P)
    (hfb : (F1 ++ F2).Nodup) (hPM : (P ++ M).Nodup) :
    ((X.abstractList hyps d).abstractList (F1 ++ F2) (hyps.length + d)).abstractList (P ++ M)
        (F1.length + F2.length + hyps.length + d) =
      (((X.abstractList F1 d).abstractList P (F1.length + d)).liftLooseBVars'
        (F1.length + d) M.length).liftLooseBVars' d (F2.length + hyps.length) := by
  have h1 : X.abstractList hyps d = X.liftLooseBVars' d hyps.length := by
    apply Lean4Lean.FVarsIn.abstractList_eq_liftLooseBVars
    apply hscope.mono
    intro fv hfv hmem
    rcases hfv with h | h
    · exact (hhyps fv hmem).1 h
    · exact (hhyps fv hmem).2 h
  have h2 := Expr.liftLooseBVars'_abstractList_add X (F1 ++ F2) d d hyps.length
    (Nat.le_refl _) hfb
  have hY := Lean4Lean.FVarsIn.abstractList_not (xs := F1) (k := d) hscope
  have h3 : X.abstractList (F1 ++ F2) d =
      (X.abstractList F1 d).liftLooseBVars' d F2.length := by
    rw [Expr.abstractList_append]
    apply Lean4Lean.FVarsIn.abstractList_eq_liftLooseBVars
    apply hY.mono
    intro fv hfv hmem
    rcases hfv with ⟨h | h, hn⟩
    · exact hn h
    · exact (hF2 fv hmem).2 h
  have h4 := Expr.liftLooseBVars'_abstractList_add (X.abstractList F1 d) (P ++ M) d
    (F1.length + d) (F2.length + hyps.length) (by omega) hPM
  have hZ := Lean4Lean.FVarsIn.abstractList_not (xs := P) (k := F1.length + d) hY
  have h5 : (X.abstractList F1 d).abstractList (P ++ M) (F1.length + d) =
      ((X.abstractList F1 d).abstractList P (F1.length + d)).liftLooseBVars'
        (F1.length + d) M.length := by
    rw [Expr.abstractList_append]
    apply Lean4Lean.FVarsIn.abstractList_eq_liftLooseBVars
    apply hZ.mono
    intro fv hfv _
    rcases hfv with ⟨⟨h | h, hn⟩, hp⟩
    · exact hn h
    · exact hp h
  rw [h1, Nat.add_comm hyps.length d, h2, h3, Lean.Expr.liftLooseBVars'_liftLooseBVars',
    show F1.length + F2.length + hyps.length + d = F1.length + d + (F2.length + hyps.length) by
      omega, h4, h5]

theorem Expr.forallDomainList_forallDomainsOnly :
    ∀ (n : Nat) (e : Expr), Expr.forallDomainList n (Expr.forallDomainsOnly n e) =
      Expr.forallDomainList n e
  | 0, _ => rfl
  | n + 1, e => by
    cases e <;> simp [Expr.forallDomainsOnly, Expr.forallDomainList,
      Expr.forallDomainList_forallDomainsOnly n]

theorem Expr.forallDomainList_fvarsIn {P : FVarId → Prop} :
    ∀ (n : Nat) {e : Expr}, FVarsIn P e → ∀ d ∈ Expr.forallDomainList n e, FVarsIn P d
  | 0, _, _ => by simp [Expr.forallDomainList]
  | n + 1, e, h => by
    cases e with
    | forallE name dom body bi =>
      intro d hd
      simp only [Expr.forallDomainList, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact Expr.forallDomainList_fvarsIn n h.2 d hd
    | _ => simp [Expr.forallDomainList]

theorem InductiveSignature.insertBinders_take (l : List VExpr) (n k : Nat) :
    (InductiveSignature.insertBinders l n).take k =
      InductiveSignature.insertBinders (l.take k) n := by
  apply List.ext_getElem
  · simp [InductiveSignature.insertBinders]
  · intro i _ _
    simp [InductiveSignature.insertBinders]

/-- Each recursive field of a minor is one of its opened field variables. -/
theorem MinorPremiseType.recursiveField_pos (S : MinorPremiseType)
    {env : VEnv} {decl : VInductDecl} {uvars : Nat}
    {sel : List (RecursiveFieldDomainAt env decl uvars)}
    (Hsel : RecursiveFieldSelectionsAt env decl uvars S.fields S.recursiveFields sel)
    (j : Nat) (hj : j < S.recursiveFields.size) :
    ∃ pos, ∃ hpos : pos < S.fields_bound.fvars.length,
      S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) := by
  have hF := Hsel.arguments_at_positions
  have hlen := Lean4Lean.List.Forall₂.length_eq hF
  have hjSel : j < sel.length := by rw [hlen]; simpa using hj
  obtain ⟨hp, hget⟩ := List.forall₂_getElem hF j hjSel (by simpa using hj)
  have hsize := S.fields_bound.length_fvars
  refine ⟨sel[j].fieldIndex, by omega, ?_⟩
  rw [getElem!_pos S.recursiveFields j hj]
  have h1 : S.recursiveFields[j] = S.fields[sel[j].fieldIndex] := by simpa using hget
  rw [h1]
  have h2 : ∀ (xs : Array Expr) (h : sel[j].fieldIndex < xs.size),
      xs = (S.fields_bound.fvars.map Expr.fvar).toArray →
      xs[sel[j].fieldIndex] = .fvar (S.fields_bound.fvars[sel[j].fieldIndex]'(by omega)) := by
    intro xs h hxs; subst hxs; simp
  exact h2 _ hp S.fields_bound.expressions

/-- The call-local argument telescope of a typed recursive call mentions only variables
satisfying any predicate `P` equivalent to the call's root scope. -/
theorem TypedRecursiveCall.localTelescope_fvarsIn
    {R : RecursorContextWF root recLparams}
    (Sc : TypedRecursiveCall indTypes stats motives minors lvls R decl
      callDepth field value)
    {P : FVarId → Prop} (hP : ∀ fv, Sc.rootScope fv ↔ P fv) :
    (Sc.generated.current.lctx.mkForall Sc.generated.localArgs (.sort .zero)).FVarsIn P := by
  let Rc := Sc.current_context
  have hargs : Sc.generated.localArgs.toList = Sc.recent.fvars.map Expr.fvar := by
    have key : ∀ (xs : Array Expr) (fvs : List FVarId), xs = (fvs.map Expr.fvar).toArray →
        xs.toList = fvs.map Expr.fvar := by
      intro xs fvs h; subst h; simp
    exact key _ _ Sc.recent.expressions
  have hrev : Rc.mlctx.fvarRevList Sc.generated.localArgs.size Sc.recent.size_le =
      Sc.recent.fvars.reverse := by
    have h1 := Sc.recent.reverse_eq
    rw [hargs, ← List.map_reverse] at h1
    have hinj : ∀ (l₁ l₂ : List FVarId), l₁.map Expr.fvar = l₂.map Expr.fvar → l₁ = l₂ := by
      intro l₁ l₂ h
      induction l₁ generalizing l₂ with
      | nil => cases l₂ <;> simp_all
      | cons a l ih =>
        cases l₂ with
        | nil => simp at h
        | cons b l' => simp only [List.map_cons, List.cons.injEq, Expr.fvar.injEq] at h; rw [h.1, ih _ h.2]
    exact (hinj _ _ h1).symm
  have hmk : Sc.generated.current.lctx.mkForall Sc.generated.localArgs (.sort .zero) =
      Rc.mlctx.mkForall Sc.generated.localArgs.size Sc.recent.size_le (.sort .zero) := by
    rw [← Rc.lctx_eq]
    exact Rc.mlctx_wf.mkForall_eq _ _ Sc.recent.reverse_eq (by simp [Closed])
  rw [hmk]
  apply MLCtxOnlyLams.mkForall_fvarsIn_upset Rc.onlyLams Rc.mlctx_wf
  · have hpred : (fun fv => fv ∈ Rc.mlctx.fvarRevList Sc.generated.localArgs.size
          Sc.recent.size_le ∨ P fv) =
        (fun fv => fv ∈ Sc.recent.fvars ∨ Sc.rootScope fv) := by
      funext fv
      rw [hrev, hP]
      simp
    rw [hpred]
    exact Sc.current_scope_up
  · simp [FVarsIn, Level.hasMVar']

/-- The argument domains of an induction hypothesis type are the domains of its argument
telescope over `Sort 0`. -/
theorem InductionHypothesisType.argDomains_eq_mkForall
    (O : InductionHypothesisType stats recInfos root field type) :
    O.argDomains =
      Expr.forallDomainList O.args.size (O.current.lctx.mkForall O.args (.sort .zero)) := by
  have key : ∀ t body, t = O.current.lctx.mkForall O.args body →
      Expr.forallDomainList O.args.size t =
        Expr.forallDomainList O.args.size (O.current.lctx.mkForall O.args (.sort .zero)) := by
    intro t body ht
    rw [ht, ← Expr.forallDomainList_forallDomainsOnly O.args.size (O.current.lctx.mkForall _ body),
      O.arguments_bound.toFVarArrayIn.forallDomainsOnly O.current_wf O.arguments_bound.nodup]
  exact key _ _ O.type_eq

/-- An induction hypothesis type with the same `replayTrace` as a typed recursive call inherits
the call's scope: for any predicate `P` equivalent to the call's root scope, every argument
domain of the hypothesis mentions only variables satisfying `P`, and every exposed index,
closed over the hypothesis's own arguments, mentions only such variables; on these indices
`abstractN` agrees with `abstractList`. -/
theorem InductionHypothesisType.scope_of_replayTrace
    (O : InductionHypothesisType stats' recInfos root' field' type)
    {R : RecursorContextWF root recLparams}
    (Sc : TypedRecursiveCall indTypes stats motives minors lvls R decl
      callDepth field value)
    {fieldBinders : List FVarId}
    (hreplay : O.replayTrace fieldBinders = Sc.generated.replayTrace fieldBinders)
    {P : FVarId → Prop} (hP : ∀ fv, Sc.rootScope fv ↔ P fv) :
    (∀ i, i < O.args.size → (O.argDomains[i]!).FVarsIn P) ∧
    ∀ e ∈ (O.exposedType.getAppArgs[stats'.params.size:] : Array Expr).toList,
      e.abstractN O.arguments_bound.fvars = e.abstractList O.arguments_bound.fvars ∧
      (e.abstractN O.arguments_bound.fvars).FVarsIn P := by
  have hScT := Sc.localTelescope_fvarsIn hP
  have hOT : O.current.lctx.mkForall O.args (.sort .zero) =
      Sc.generated.current.lctx.mkForall Sc.generated.localArgs (.sort .zero) := by
    have h := congrArg InductionHypothesisShape.localTelescope hreplay
    simp only [InductionHypothesisType.replayTrace,
      RecursiveCall.replayTrace] at h
    exact Expr.abstractList_injective h
  have hna : O.args.size = Sc.generated.localArgs.size :=
    congrArg InductionHypothesisShape.localArity hreplay
  have hnaO : O.arguments_bound.fvars.length = O.args.size := O.arguments_bound.length_fvars
  have hargsSc : Sc.generated.arguments_bound.fvars = Sc.recent.fvars :=
    Sc.generated.arguments_bound.toFVarArrayIn.exprArrayFVarIds.symm.trans
      Sc.recent.toFVarArrayIn.exprArrayFVarIds
  have hnaSc : Sc.generated.arguments_bound.fvars.length = Sc.generated.localArgs.size :=
    Sc.generated.arguments_bound.length_fvars
  have hdom := O.argDomains_eq_mkForall
  refine ⟨fun i hi => ?_, fun e he => ?_⟩
  · have hi' : i < O.argDomains.length := by rw [O.argDomains_length]; exact hi
    have hall : ∀ d ∈ O.argDomains, d.FVarsIn P := by
      rw [hdom]
      exact Expr.forallDomainList_fvarsIn _ (hOT ▸ hScT)
    rw [getElem!_pos O.argDomains i hi']
    exact hall _ (List.getElem_mem hi')
  have hexposedClosed : Closed Sc.generated.exposedType 0 := by
    have h := Sc.exposed_translation.closed
    rwa [Sc.current_context.mlctx.noBV] at h
  have hind := congrArg (fun t => t.indices.toList) hreplay
  simp only [InductionHypothesisType.replayTrace,
    RecursiveCall.replayTrace, Array.toList_map] at hind
  have hmem := List.mem_map_of_mem
    (f := fun index => (index.abstractList O.arguments_bound.fvars).abstractList
      fieldBinders O.args.size) he
  rw [hind] at hmem
  obtain ⟨e', he', heq⟩ := List.mem_map.1 hmem
  rw [← hna] at heq
  have heq' := Expr.abstractList_injective heq
  rw [Expr.getAppArgs_slice_toList] at he'
  have he'args := List.mem_of_mem_drop he'
  have hscope' := Lean4Lean.FVarsIn.getAppArgsList Sc.exposed_scope he'args
  have hclosed' := Closed.getAppArgsList hexposedClosed he'args
  have hclosedAbs : Closed (e.abstractList O.arguments_bound.fvars 0)
      (0 + O.arguments_bound.fvars.length) := by
    rw [← heq', hnaO, hna, ← hnaSc]
    simpa using Closed.abstractList_at (depth := 0) (outer := 0)
      (fvars := Sc.generated.arguments_bound.fvars) (by simpa using hclosed')
  have hclosedE : Closed e 0 := Expr.closed_of_abstractList hclosedAbs
  have hN : e.abstractN O.arguments_bound.fvars = e.abstractList O.arguments_bound.fvars :=
    Expr.abstractN_eq_abstractList_of_closed O.arguments_bound.nodup hclosedE
  refine ⟨hN, ?_⟩
  rw [hN, ← heq']
  have h := Lean4Lean.FVarsIn.abstractList_not (xs := Sc.generated.arguments_bound.fvars)
    (k := 0) hscope'
  apply h.mono
  intro fv hfv
  rcases hfv with ⟨h1 | h1, h2⟩
  · exact absurd (hargsSc ▸ h1) h2
  · exact (hP fv).1 h1

/-- The small translations behind the `j`-th induction hypothesis of a minor
premise. Let `Sc` be the typed recursive call recorded for the recursive field at position
`pos`, opened above the context `Rorigin` of the typed field traversal `F`, and let `O` be an
induction hypothesis type with the same `replayTrace`. Then there are a binder telescope `B0`
and an index list `indices`, translated in `parameters ++ sourceFields.take pos` (extended by
`B0`), whose sources are the argument domains of `O` and its exposed indices closed over the
fields before `pos` and the parameters. -/
theorem RecursorConstruction.recursorTelescope_hypothesisSmall
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (F : TypedRuleFieldTraversal H.recursorWF stats
      (H.origins.minorShapes mowner hmowner localIndex hlocal))
    (hparams : F.parameterSuffix.parameterDecls = H.parameterSuffix.parameterDecls)
    {Rorigin : RecursorContextWF originRoot (AddInductive.getRecLevelParams H.elimLevel c.lparams)}
    {prior : Array Expr} (Hprior : RecursorFVarSuffix F.terminalWF Rorigin prior)
    (hchkO : Rorigin.chk = F.terminalWF.chk) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let sourceFields := (H.declFieldDomains mowner hmowner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
    ∀ (j : Nat)
      (Sc : TypedRecursiveCall indTypes' stats motives minors lvls Rorigin decl'
        callDepth (S.recursiveFields[j]!) value)
      (pos : Nat) (hpos : pos < S.fields_bound.fvars.length),
      S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) →
      ∀ (O : InductionHypothesisType stats' recInfos' root field type),
      stats'.params.size = stats.params.size →
      O.replayTrace S.fields_bound.fvars = Sc.generated.replayTrace S.fields_bound.fvars →
      ∃ B0 indices : List VExpr, B0.length = O.args.size ∧
        (∀ (i : Nat) (hi : i < B0.length),
          TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ B0.take i) [])
            ((O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
              H.params.fvars (pos + i))
            (B0[i]'hi)) ∧
        List.Forall₂
          (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ B0) []))
          ((O.exposedType.getAppArgs[stats'.params.size:] : Array Expr).toList.map fun e =>
            ((e.abstractN O.arguments_bound.fvars).abstractList
              (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
                (pos + O.args.size))
          indices := by
  intro S sourceFields j Sc pos hpos hfield O hPS hreplay
  have hnf : S.fields_bound.fvars.length = S.fields.size := S.fields_bound.length_fvars
  have hfR : F.fieldsRecent.fvars = S.fields_bound.fvars :=
    F.fieldsRecent.toFVarArrayIn.exprArrayFVarIds.symm.trans S.fields_bound.exprArrayFVarIds
  have hPids : ExprArrayFVarIds stats.params = H.params.fvars := H.params.exprArrayFVarIds
  have hvRc : Sc.current_context.venv = R.context.venv := by
    rw [Sc.recent.venv_eq, Hprior.venv_eq, ← F.terminalExtension.venv_eq, H.recursorEnv]
  have hOT : O.current.lctx.mkForall O.args (.sort .zero) =
      Sc.generated.current.lctx.mkForall Sc.generated.localArgs (.sort .zero) := by
    have h := congrArg InductionHypothesisShape.localTelescope hreplay
    simp only [InductionHypothesisType.replayTrace,
      RecursiveCall.replayTrace] at h
    exact Expr.abstractList_injective h
  have hna : O.args.size = Sc.generated.localArgs.size :=
    congrArg InductionHypothesisShape.localArity hreplay
  have hargsSc : Sc.generated.arguments_bound.fvars = Sc.recent.fvars :=
    Sc.generated.arguments_bound.toFVarArrayIn.exprArrayFVarIds.symm.trans
      Sc.recent.toFVarArrayIn.exprArrayFVarIds
  have hnaSc : Sc.generated.arguments_bound.fvars.length = Sc.generated.localArgs.size :=
    Sc.generated.arguments_bound.length_fvars
  have hdom := O.argDomains_eq_mkForall
  have hIdxN := (O.scope_of_replayTrace Sc hreplay (P := Sc.rootScope) fun _ => Iff.rfl).2
  have hsfLen : sourceFields.length = S.fields.size := by
    simp only [sourceFields, List.length_map]
    exact H.sourceFields_length mowner hmowner localIndex hlocal
  let Fs := sourceFields.take pos
  -- The checking contexts of the minor pass. `M` is the field checking context of the
  -- constructor, `C` the checking context in which the call-local arguments of this
  -- hypothesis were opened, and `C.dropN localArgs.size = Rorigin.chk.dropN jC`
  -- is the prefix of `M` ending just before the recursive field.
  obtain ⟨M, hMwf, hchkM, hnM, hagM, hdropM, -⟩ := F.fieldCheck
  obtain ⟨hnC, hagreeC, jC, hjC, -, hdropC, ⟨kC, htakeC, hkC⟩, -, -, -, ⟨t₁, Ht₁, -⟩, -, -⟩ :=
    Sc.chkAgree
  have hnfpos : 0 < S.fields.size := by omega
  have hRM : Rorigin.chk = M := hchkO.trans (hchkM hnfpos)
  have hMonly : MLCtxOnlyLams M := by rw [← hchkM hnfpos]; exact F.terminalWF.check.onlyLams
  have hPfv : F.parameterSuffix.parameterDecls.fvars = H.params.fvars.reverse := by
    rw [F.parameterSuffix.parameterDecls_fvars, hPids]
  have hMfv : M.fvarList = H.params.fvars ++ S.fields_bound.fvars := by
    have h1 := M.fvars_eq_append (n := S.fields.size) (hn := hnM)
    rw [← hagM.fvarRevList_eq F.fieldsRecent.size_le hnM, F.fieldsRecent.fvarRevList_eq, hfR,
      hdropM, hPfv] at h1
    rw [TypeChecker.MLCtx.fvarList_eq, h1]
    simp
  have hMnodup : M.fvarList.Nodup := by
    rw [TypeChecker.MLCtx.fvarList_eq]; exact List.nodup_reverse.2 hMwf.fvars_nodup
  have hkM : M.fvarList[H.params.fvars.length + pos]? = some (S.fields_bound.fvars[pos]'hpos) := by
    rw [hMfv, List.getElem?_append_right (by omega)]
    simp [hpos]
  have hkEq : H.params.fvars.length + pos = kC := by
    have hk' := hkC
    rw [hRM, hfield] at hk'
    exact (List.getElem?_inj (by rw [hMfv, List.length_append]; omega) hMnodup).1
      (hkM.trans hk'.symm)
  have hBfv : (Rorigin.chk.dropN jC hjC).fvarList =
      H.params.fvars ++ S.fields_bound.fvars.take pos := by
    rw [htakeC, hRM, ← hkEq, hMfv, List.take_append]
    simp [List.take_of_length_le]
  have hBonly : MLCtxOnlyLams (Rorigin.chk.dropN jC hjC) := Rorigin.check.onlyLams.dropN jC hjC
  have hBwf : (Rorigin.chk.dropN jC hjC).WF Rorigin.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) := Rorigin.check.wf.dropN jC hjC
  have hBnodup : (Rorigin.chk.dropN jC hjC).vlctx.fvars.Nodup := hBwf.fvars_nodup
  have hBrev : (Rorigin.chk.dropN jC hjC).vlctx.fvars.reverse =
      H.params.fvars ++ S.fields_bound.fvars.take pos := by
    rw [← TypeChecker.MLCtx.fvarList_eq, hBfv]
  have hPFnodup : (H.params.fvars ++ S.fields_bound.fvars.take pos).Nodup := by
    rw [← hBrev]; exact List.nodup_reverse.2 hBnodup
  -- The checking context's field domains are the minor's field domains.
  have hMdoms : MLCtxForallDomains M S.fields.size hnM = sourceFields := by
    have HMsort := (hMwf.mkForall_trS F.terminalWF.checking.tr.wf (e := .sort .zero)
      (e' := .sort .zero) (.sort (by simp [VLevel.ofLevel])) ⟨_, VEnv.HasType.sort (by trivial)⟩
      S.fields.size hnM).1
    rw [hdropM, TypeChecker.MLCtx.mkForall'_eq_wrapForalls] at HMsort
    have Hdecls := checkInductiveTypes.loopType.MLCtxOnlyLams.declarations (hMonly.dropN S.fields.size hnM)
    rw [hdropM] at Hdecls
    have hPnodup : F.parameterSuffix.parameterDecls.fvars.Nodup := by
      rw [← hdropM]; exact (hMwf.dropN S.fields.size hnM).fvars_nodup
    have Habs := TrExprS.abstractFVarLambdaSuffix (domains := []) Hdecls hPnodup
      (by simpa [abstractForallContext] using HMsort)
    have hsrcEq : H.localContext.lctx.mkForall S.fields (.sort .zero) =
        M.mkForall S.fields.size hnM (.sort .zero) := by
      rw [F.fieldsRecent.toFVarArrayAfter.toFVarArrayIn.mkForall_mono
        F.terminalExtension.contextLE, ← F.terminalWF.lctx_eq,
        F.terminalWF.mlctx_wf.mkForall_eq _ _ F.fieldsRecent.reverse_eq (by simp [Closed])]
      exact hagM.mkForall_eq _ _ _
    obtain ⟨-, -, Hrep⟩ := H.sourceFields_replay mowner hmowner localIndex hlocal
    rw [hsrcEq, ← hparams] at Hrep
    rw [hPfv, List.reverse_reverse] at Habs
    have hv : F.terminalWF.venv = H.recursorWF.venv := F.terminalExtension.venv_eq.symm
    have hvle' : F.terminalWF.venv ≤ H.recursorWF.venv := hv ▸ VEnv.LE.rfl
    replace Habs := Habs.mono hvle'
    have heq := Hrep.uniqueS (by simpa using Habs)
    have hlen : (MLCtxForallDomains M S.fields.size hnM).length = sourceFields.length := by
      rw [hMonly.forallDomains_length, hsfLen]
    exact (VExpr.wrapForalls_inj_of_length hlen heq.symm).1
  -- The small checking context is the parameters followed by the fields before `pos`.
  have hBctx : (Rorigin.chk.dropN jC hjC).vlctx.toCtx.reverse = H.parameterSuffix.parameterDecls.toCtx.reverse ++ Fs := by
    have h1 := Rorigin.check.onlyLams.toCtx_dropN jC hjC
    have h2 : Rorigin.chk.vlctx.toCtx = M.vlctx.toCtx := by rw [hRM]
    have h3 := hMonly.toCtx_eq_forallDomains_reverse_append_dropN S.fields.size hnM
    rw [hdropM, hMdoms] at h3
    rw [h2, h3] at h1
    have hBlen : (Rorigin.chk.dropN jC hjC).vlctx.toCtx.length = H.params.fvars.length + pos := by
      rw [hBonly.toCtx_length, ← TypeChecker.MLCtx.fvarList_length, hBfv]
      simp; omega
    have hMlen : M.vlctx.toCtx.length = H.params.fvars.length + S.fields.size := by
      rw [hMonly.toCtx_length, ← TypeChecker.MLCtx.fvarList_length, hMfv]
      simp [hnf]
    rw [h3] at hMlen
    have hjC' : jC = S.fields.size - pos := by
      have := congrArg List.length h1
      rw [hBlen, List.length_drop, hMlen] at this
      have hjle : jC ≤ M.length := by rw [← hRM]; exact hjC
      have hMl : M.length = H.params.fvars.length + S.fields.size := by
        rw [← TypeChecker.MLCtx.fvarList_length, hMfv]; simp [hnf]
      omega
    rw [h1, hjC', List.drop_append_of_le_length (by simp only [List.length_reverse, hsfLen]; omega), List.drop_reverse]
    simp only [List.reverse_append, List.reverse_reverse, hsfLen,
      ← hparams, Fs]
    congr 2
    omega
  -- The argument telescope in the checker context `C`.
  have hCwf := Sc.current_context.check.wf
  have hConly := Sc.current_context.check.onlyLams
  have HX := (hCwf.mkForall_trS Sc.current_context.checking.tr.wf (e := .sort .zero)
    (e' := .sort .zero) (.sort (by simp [VLevel.ofLevel])) ⟨_, VEnv.HasType.sort (by trivial)⟩
    Sc.generated.localArgs.size hnC).1
  have hvle : Sc.current_context.venv ≤ R.context.venv := hvRc ▸ VEnv.LE.rfl
  rw [hdropC, TypeChecker.MLCtx.mkForall'_eq_wrapForalls] at HX
  replace HX := HX.mono hvle
  generalize hB0def : MLCtxForallDomains Sc.current_context.chk Sc.generated.localArgs.size hnC =
    B0 at HX
  have hB0len' : B0.length = Sc.generated.localArgs.size := by
    rw [← hB0def]; exact hConly.forallDomains_length _ _
  obtain ⟨rC, HCtel⟩ := hagreeC.forallTelescope hnC (W := .sort .zero) (k := 0) (.nil _)
  simp only [Nat.add_zero] at HCtel
  have HD := TrExprS.forallTelescope_domains HCtel HX hB0len'
  have hXeq : O.current.lctx.mkForall O.args (.sort .zero) =
      Sc.current_context.chk.mkForall Sc.generated.localArgs.size hnC (.sort .zero) := by
    rw [hOT, ← Sc.current_context.lctx_eq,
      Sc.current_context.mlctx_wf.mkForall_eq _ _ Sc.recent.reverse_eq (by simp [Closed])]
    exact hagreeC.mkForall_eq _ _ _
  have hB0na : B0.length = O.args.size := hB0len'.trans hna.symm
  have Hsmall : ∀ i (hi : i < B0.length),
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++ Fs ++ B0.take i) [])
        ((O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
          H.params.fvars (pos + i)) B0[i] := by
    intro i hi
    have Hi := HD i hi
    have Habs := TrExprS.abstractFVarLambdaSuffix (checkInductiveTypes.loopType.MLCtxOnlyLams.declarations hBonly) hBnodup Hi
    rw [hBrev, hBctx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi),
      ← Expr.abstractList_after_inner hPFnodup, hXeq.symm, ← hna, ← hdom] at Habs
    have hF1len : (S.fields_bound.fvars.take pos).length = pos := by simp; omega
    rw [hF1len, Nat.add_comm i pos] at Habs
    exact Habs
  -- The exposed indices in the checker context `C`, closed over all of `C`.
  have Ht₁' := Ht₁.mono hvle
  obtain ⟨args', Hargs⟩ : ∃ args', List.Forall₂
      (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        Sc.current_context.chk.vlctx) Sc.generated.exposedType.getAppArgsList args' :=
    TrExprS.getAppArgsList_translations Ht₁'
  have hCfv : Sc.current_context.chk.vlctx.fvars.reverse =
      H.params.fvars ++ S.fields_bound.fvars.take pos ++ Sc.generated.arguments_bound.fvars := by
    rw [Sc.current_context.chk.fvars_eq_append (n := Sc.generated.localArgs.size) (hn := hnC),
      ← hagreeC.fvarRevList_eq Sc.recent.size_le hnC, Sc.recent.fvarRevList_eq, hdropC,
      List.reverse_append, hBrev, List.reverse_reverse, hargsSc]
  have hCctx : Sc.current_context.chk.vlctx.toCtx.reverse = H.parameterSuffix.parameterDecls.toCtx.reverse ++ Fs ++ B0 := by
    rw [hConly.toCtx_eq_forallDomains_reverse_append_dropN _ hnC, hdropC, hB0def,
      List.reverse_append, hBctx, List.reverse_reverse]
  have hCnodup : (Sc.current_context.chk.vlctx.fvars.reverse).Nodup :=
    List.nodup_reverse.2 hCwf.fvars_nodup
  have HIsmall₀ : List.Forall₂
      (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++ Fs ++ B0) []))
      ((Sc.generated.exposedType.getAppArgsList.drop stats.params.size).map fun e =>
        e.abstractList (H.params.fvars ++ S.fields_bound.fvars.take pos ++
          Sc.generated.arguments_bound.fvars) 0)
      (args'.drop stats.params.size) := by
    rw [List.forall₂_map_left_iff]
    refine List.Forall₂.imp ?_ (Hargs.drop_both stats.params.size)
    intro e ie He
    have Habs := TrExprS.abstractFVarLambdaSuffix (domains := []) (checkInductiveTypes.loopType.MLCtxOnlyLams.declarations hConly)
      (List.nodup_reverse.1 hCnodup) (by simpa [abstractForallContext] using He)
    rw [hCfv, hCctx] at Habs
    simpa using Habs
  -- The exposed indices of `O` closed over its own arguments are those of the call.
  have hIdxEq : ((O.exposedType.getAppArgs[stats'.params.size:] : Array Expr).toList.map
      fun e => ((e.abstractN O.arguments_bound.fvars).abstractList
        (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
          (pos + O.args.size)) =
      (Sc.generated.exposedType.getAppArgsList.drop stats.params.size).map fun e =>
        e.abstractList (H.params.fvars ++ S.fields_bound.fvars.take pos ++
          Sc.generated.arguments_bound.fvars) 0 := by
    have hind := congrArg (fun t => t.indices.toList) hreplay
    simp only [InductionHypothesisType.replayTrace,
      RecursiveCall.replayTrace, Array.toList_map] at hind
    rw [hPS, ← hna] at hind
    have hcore : (O.exposedType.getAppArgs[stats.params.size:] : Array Expr).toList.map
          (fun e => e.abstractList O.arguments_bound.fvars) =
        (Sc.generated.exposedType.getAppArgs[stats.params.size:] : Array Expr).toList.map
          (fun e => e.abstractList Sc.generated.arguments_bound.fvars) := by
      apply (List.map_inj_right
        (f := fun s : Expr => s.abstractList S.fields_bound.fvars O.args.size)
        (fun a b h => Expr.abstractList_injective h)).mp
      simpa only [List.map_map, Function.comp_def] using hind
    rw [hPS]
    rw [List.map_congr_left (fun e he => by rw [(hIdxN e (by rw [hPS]; exact he)).1])]
    have h2 := congrArg (List.map fun s =>
      (s.abstractList (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
        (pos + O.args.size)) hcore
    simp only [List.map_map, Function.comp_def] at h2
    rw [h2, Expr.getAppArgs_slice_toList]
    apply List.map_congr_left
    intro e _
    have hF1len : (S.fields_bound.fvars.take pos).length = pos := by simp; omega
    have hPFA : (H.params.fvars ++ (S.fields_bound.fvars.take pos ++
        Sc.generated.arguments_bound.fvars)).Nodup := by
      rw [← List.append_assoc, ← hCfv]; exact hCnodup
    have hFA : (S.fields_bound.fvars.take pos ++ Sc.generated.arguments_bound.fvars).Nodup :=
      hPFA.sublist (List.sublist_append_right _ _)
    have h1 : (e.abstractList Sc.generated.arguments_bound.fvars 0).abstractList
        (S.fields_bound.fvars.take pos) O.args.size =
        e.abstractList (S.fields_bound.fvars.take pos ++ Sc.generated.arguments_bound.fvars) 0 := by
      rw [show O.args.size = 0 + Sc.generated.arguments_bound.fvars.length by omega]
      exact Expr.abstractList_after_inner hFA
    have h2 : (e.abstractList (S.fields_bound.fvars.take pos ++
        Sc.generated.arguments_bound.fvars) 0).abstractList H.params.fvars (pos + O.args.size) =
        e.abstractList (H.params.fvars ++ (S.fields_bound.fvars.take pos ++
          Sc.generated.arguments_bound.fvars)) 0 := by
      rw [show pos + O.args.size = 0 + (S.fields_bound.fvars.take pos ++
        Sc.generated.arguments_bound.fvars).length by simp [hF1len]; omega]
      exact Expr.abstractList_after_inner hPFA
    rw [h1, h2, List.append_assoc]
  refine ⟨B0, args'.drop stats.params.size, hB0na, Hsmall, ?_⟩
  rw [hIdxEq]
  exact HIsmall₀

/-- Lifting the small translations of `recursorTelescope_hypothesisSmall` to
the generator context.  If the argument domains and exposed indices of the
induction hypothesis type `O` of the `j`-th hypothesis mention only the parameters and the fields
before the recursive field at position `pos`, and `B0` and `indices` translate
them in `parameters ++ sourceFields.take pos` (extended by `B0`), then the
`j`-th hypothesis of the minor premise is the `underFields` embedding of `B0`
and `indices`, applied to the owner's motive variable and the recursive field
variable. -/
theorem RecursorConstruction.recursorTelescope_hypothesisLift
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D₀ : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D₀.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let sourceFields := (H.declFieldDomains mowner hmowner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
    let nmot := (H.recInfos.map (·.motive)).size
    let fields := InductiveSignature.insertBinders sourceFields (nmot + minorIdx)
    ∀ (hyps : List VExpr) (res : VExpr) (hhyps : hyps.length = S.hypotheses.size),
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D₀.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
      ∀ (j : Nat) (hj : j < S.hypotheses.size)
        (origins : MinorInductionHypothesisTypes S.sourceFullContext S.recursiveFields
          S.hypotheses),
      origins.stats = stats →
      origins.recInfos.map (·.motive) = H.recInfos.map (·.motive) →
      ∀ {root : AddInductive.Context} {sourceType : Expr}
        (O : InductionHypothesisType origins.stats origins.recInfos root
          (S.recursiveFields[j]!) sourceType)
        (D : FVarDeclAt S.sourceFullContext S.hypotheses j),
      D.type = (sourceType.consumeTypeAnnotationsVerified
        S.sourceFullContext.env.isTypeAnnotationWrapper) →
      O.ownerIdx < H.recInfos.size →
      ∀ (pos : Nat) (hpos : pos < S.fields_bound.fvars.length),
      S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) →
      (∀ i, i < O.args.size → (O.argDomains[i]!).FVarsIn
        (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars)) →
      (∀ e ∈ (O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList,
        (e.abstractN O.arguments_bound.fvars).FVarsIn
          (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars)) →
      ∀ (B0 indices : List VExpr), B0.length = O.args.size →
      (∀ (i : Nat) (hi : i < B0.length),
          TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ B0.take i) [])
            ((O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
              H.params.fvars (pos + i))
            (B0[i]'hi)) →
      List.Forall₂
          (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ B0) []))
          ((O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList.map fun e =>
            ((e.abstractN O.arguments_bound.fvars).abstractList
              (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
                (pos + O.args.size))
          indices →
      hyps[j]'(by rw [hhyps]; exact hj) =
        VExpr.wrapForalls
          (B0.zipIdx.map fun (e, i) =>
            InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx) i)
          (.app
            (VExpr.mkApps (.bvar (S.fields.size + j + O.args.size + minorIdx +
                (nmot - 1 - O.ownerIdx)))
              (indices.map fun e =>
                InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx)
                  O.args.size))
            (VExpr.mkApps (.bvar (j + O.args.size + (S.fields.size - 1 - pos)))
              (InductiveSignature.vars O.args.size 0))) := by
  intro S sourceFields nmot fields hyps res hhyps hminorEq j hj origins₁ hstats hmotives root
    sourceType O D hDtype howner' pos hpos hfield hArgScope hIdxScope B0 indices hB0na Hsmall
    HIsmall
  obtain ⟨A, I, hA, hEq, HI, HA⟩ := H.recursorTelescope_hypothesisDomains howner T minorIdx D₀
    mowner hmowner localIndex hlocal hD hyps res hhyps hminorEq j origins₁ hmotives O D hDtype
    howner' pos hpos hfield
  have hnf : S.fields_bound.fvars.length = S.fields.size := S.fields_bound.length_fvars
  have hPids : ExprArrayFVarIds stats.params = H.params.fvars := H.params.exprArrayFVarIds
  -- Distinctness of the closed variable groups.
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hPM : (H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx)).Nodup := by
    rw [← List.append_assoc]
    apply List.Nodup.sublist _ houter
    exact List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _)
  have hfb : (S.fields_bound.fvars.take pos ++ S.fields_bound.fvars.drop pos).Nodup := by
    rw [List.take_append_drop]; exact S.fields_nodup
  have hfieldsOuter : ∀ fv ∈ S.fields_bound.fvars, fv ∉ H.params.fvars := by
    intro fv hfv hP
    apply H.templates.fields_outer_fresh mowner hmowner localIndex hlocal fv hfv
    rw [hPids]
    exact List.mem_append_left _ (List.mem_append_left _ hP)
  have hhypsD : ∀ fv ∈ S.hypotheses_bound.fvars.take j,
      fv ∉ S.fields_bound.fvars.take pos ∧ fv ∉ H.params.fvars := by
    intro fv hfv
    have hfv' := List.mem_of_mem_take hfv
    refine ⟨fun h => S.hypotheses_fields_fresh fv hfv' (List.mem_of_mem_take h), fun hP => ?_⟩
    have h := origins₁.hypotheses_outer_fresh fv (List.mem_append_left _ (by rw [hstats, hPids]; exact hP))
    rw [S.hypotheses_bound.exprArrayFVarIds] at h
    exact h hfv'
  have hF2D : ∀ fv ∈ S.fields_bound.fvars.drop pos,
      fv ∉ S.fields_bound.fvars.take pos ∧ fv ∉ H.params.fvars := by
    intro fv hfv
    refine ⟨fun h => ?_, hfieldsOuter fv (List.mem_of_mem_drop hfv)⟩
    exact (List.nodup_append.1 hfb).2.2 fv h fv hfv rfl
  -- Lengths.
  have hminorT : minorIdx < T.minors.length := by rw [T.minors_length]; exact D₀.inBounds
  have hjH : j ≤ S.hypotheses_bound.fvars.length := by
    rw [S.hypotheses_bound.length_fvars]; omega
  have hhypsLen : (S.hypotheses_bound.fvars.take j).length = j := by
    rw [List.length_take]; omega
  have hMLen : (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx).length =
      nmot + minorIdx := by
    rw [List.length_append, H.bindings.motives.length_fvars, List.length_take,
      H.bindings.flatMinors.length_fvars]
    have := D₀.inBounds
    simp only [nmot]
    omega
  have hsfLen : sourceFields.length = S.fields.size := by
    simp only [sourceFields, List.length_map]
    exact H.sourceFields_length mowner hmowner localIndex hlocal
  -- Source coincidences: the generator's closed sources are lifts of the small ones.
  have hsrc : ∀ (X : Expr) (d : Nat), X.FVarsIn
        (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars) →
      ((X.abstractList (S.hypotheses_bound.fvars.take j) d).abstractList S.fields_bound.fvars
          (j + d)).abstractList (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx) (S.fields.size + j + d) =
        (((X.abstractList (S.fields_bound.fvars.take pos) d).abstractList H.params.fvars
          (pos + d)).liftLooseBVars' (pos + d) (nmot + minorIdx)).liftLooseBVars' d
            (S.fields.size - pos + j) := by
    intro X d hX
    have h := Expr.closeShapeSource X (S.hypotheses_bound.fvars.take j)
      (S.fields_bound.fvars.take pos) (S.fields_bound.fvars.drop pos) H.params.fvars
      (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx) d hX hhypsD hF2D
      hfb hPM
    rw [List.take_append_drop, ← List.append_assoc, hhypsLen, hMLen, List.length_take,
      List.length_drop, hnf, Nat.min_eq_left (by omega)] at h
    rw [show S.fields.size + j + d = pos + (S.fields.size - pos) + j + d by omega, h]
  -- Environments of the minor-pass contexts.
  have henv : R.context.venv.WF := by rw [← H.recursorEnv]; exact H.recursorWF.checking.tr.wf
  have hparamsT := H.recursorTelescope_params T
  rw [← hparamsT] at Hsmall HIsmall
  let Mv := T.motives ++ T.minors.take minorIdx
  let Fs := sourceFields.take pos
  let G := fields.drop pos ++ hyps.take j
  have hMv : Mv.length = nmot + minorIdx := by
    simp only [Mv, List.length_append, T.motives_length, List.length_take, T.minors_length]
    have := D₀.inBounds
    simp only [nmot]
    omega
  have hFs : Fs.length = pos := by simp only [Fs, List.length_take, hsfLen]; omega
  have hG : G.length = S.fields.size - pos + j := by
    simp only [G, fields, InductiveSignature.insertBinders, List.length_append, List.length_drop,
      List.length_map, List.length_zipIdx, hsfLen, List.length_take]
    omega
  have hctxEq : ∀ X : List VExpr,
      T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++ X =
        T.params ++ Mv ++ InductiveSignature.insertBinders Fs Mv.length ++ G ++ X := by
    intro X
    have hf : fields = InductiveSignature.insertBinders Fs Mv.length ++ fields.drop pos := by
      rw [hMv, ← InductiveSignature.insertBinders_take]
      exact (List.take_append_drop _ _).symm
    conv => lhs; rw [hf]
    simp only [G, Mv, List.append_assoc]
  -- Compare with the generator context.
  have hAeq : A = B0.zipIdx.map (fun (e, k) => (e.liftN Mv.length (Fs.length + k)).liftN G.length k) :=
    TrExprS.liftTelescope_eq henv.ordered A B0
      (fun i => (O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
        H.params.fvars (pos + i))
      (hB0na.trans hA.symm) Hsmall
      (fun i hi => by
        have h := HA i hi
        rw [hsrc _ i (hArgScope i (hA ▸ hi))] at h
        rw [← hctxEq, hFs, hMv, hG]
        exact h)
  have hAfull : A = InductiveSignature.insertBinders
      ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN Mv.length k) G.length := by
    rw [hAeq, zipIdx_twoLift_eq]
  have HI' := HI
  rw [hctxEq] at HI'
  conv at HI' => rw [hAfull]
  have hIsrc : ((O.exposedType.getAppArgs[origins₁.stats.params.size:] : Array Expr).toList.map
      fun e => (((e.abstractN O.arguments_bound.fvars).abstractList
        (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
          (j + O.args.size)).abstractList (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx) (S.fields.size + j + O.args.size)) =
      ((O.exposedType.getAppArgs[origins₁.stats.params.size:] : Array Expr).toList.map
        fun e => ((e.abstractN O.arguments_bound.fvars).abstractList
          (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
            (pos + O.args.size)).map
        (fun s => (s.liftLooseBVars' (Fs.length + B0.length) Mv.length).liftLooseBVars'
          B0.length G.length) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp]
    rw [hsrc _ _ (hIdxScope e he), hFs, hMv, hG, hB0na]
  rw [hIsrc] at HI'
  have hIeq := TrExprS.liftForall₂_eq henv.ordered (M := Mv) (G := G) HIsmall HI'
  -- Assemble.
  have hunder : ∀ (e : VExpr) (k : Nat),
      (e.liftN Mv.length (pos + k)).liftN G.length k =
        InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx) k := by
    intro e k
    simp only [InductiveSignature.Instance.underFields]
    rw [hMv, hG, VExpr.liftN'_comm _ _ _ _ _ (Nat.le_add_left k pos)]
    congr 1
    omega
  have hFs' : (sourceFields.take pos).length = pos := hFs
  rw [hEq, hIeq, hAeq]
  simp only [hFs', hFs, hunder, hB0na]
  rfl

/-- The `j`-th induction hypothesis of a minor premise of the checked recursor
type, unlifted to the small context of its recursive field.

For the induction hypothesis type `O` recorded in the rule templates and the recursive field at
position `pos`, the hypothesis is the generator's `underFields` embedding of a
binder telescope `binders` and of an index list `indices`, applied to the
owner's motive variable and the recursive field variable.  Each `binders[i]`
translates, in `parameters ++ sourceFields.take pos ++ binders.take i`, the
`i`-th literal argument domain `O.argDomains[i]!` closed over the fields before
`pos` (at depth `i`) and the parameters (at depth `pos + i`); the indices are
the closed exposed indices of `O`, closed the same way at depth `O.args.size`.
The generator-context sources of `recursorTelescope_hypothesisDomains` are
exactly the lifts of these sources (`Expr.closeShapeSource`). -/
theorem RecursorConstruction.recursorTelescope_hypothesisUnlift
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D₀ : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D₀.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let sourceFields := (H.declFieldDomains mowner hmowner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
    let nmot := (H.recInfos.map (·.motive)).size
    let fields := InductiveSignature.insertBinders sourceFields (nmot + minorIdx)
    ∀ (hyps : List VExpr) (res : VExpr) (hhyps : hyps.length = S.hypotheses.size),
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D₀.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
      ∀ (j : Nat) (hj : j < S.hypotheses.size),
      ∃ (origins : MinorInductionHypothesisTypes S.sourceFullContext S.recursiveFields
          S.hypotheses)
        (root : AddInductive.Context) (sourceType : Expr)
        (O : InductionHypothesisType origins.stats origins.recInfos root
          (S.recursiveFields[j]!) sourceType)
        (pos : Nat) (hpos : pos < S.fields_bound.fvars.length) (binders indices : List VExpr),
        S.hypothesis_type_origins = some origins ∧ origins.stats = stats ∧
        origins.recInfos.map (·.motive) = H.recInfos.map (·.motive) ∧
        S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) ∧
        binders.length = O.args.size ∧ O.ownerIdx < H.recInfos.size ∧
        hyps[j]'(by rw [hhyps]; exact hj) =
          VExpr.wrapForalls
            (binders.zipIdx.map fun (e, i) =>
              InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx) i)
            (.app
              (VExpr.mkApps (.bvar (S.fields.size + j + O.args.size + minorIdx +
                  (nmot - 1 - O.ownerIdx)))
                (indices.map fun e =>
                  InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx)
                    O.args.size))
              (VExpr.mkApps (.bvar (j + O.args.size + (S.fields.size - 1 - pos)))
                (InductiveSignature.vars O.args.size 0))) ∧
        (∀ (i : Nat) (hi : i < binders.length),
          TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ binders.take i) [])
            ((O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
              H.params.fvars (pos + i))
            (binders[i]'hi)) ∧
        List.Forall₂
          (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ binders) []))
          ((O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList.map fun e =>
            ((e.abstractN O.arguments_bound.fvars).abstractList
              (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
                (pos + O.args.size))
          indices ∧
        (H.recInfos[mowner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).args = O.args ∧
        (H.recInfos[mowner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).lctx =
          O.current.lctx ∧
        (H.recInfos[mowner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).targetIndices =
          O.exposedType.getAppArgs[origins.stats.params.size:] ∧
        (H.recInfos[mowner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).targetTypeIdx =
          O.ownerIdx ∧
        (H.recInfos[mowner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).major =
          S.recursiveFields[j]! ∧
        (H.recInfos[mowner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).template =
          O.current.lctx.mkLambda O.args
            ((mkAppN (.bvar O.args.size) O.exposedType.getAppArgs[origins.stats.params.size:]).app
              (mkAppN S.recursiveFields[j]! O.args)) ∧
        O.argDomains =
          Expr.forallDomainList O.args.size (O.current.lctx.mkForall O.args (.sort .zero)) ∧
        ExprArrayFVarIds O.args = O.arguments_bound.fvars := by
  intro S sourceFields nmot fields hyps res hhyps hminorEq j hj
  -- The recorded templates for this minor.
  obtain ⟨-, -, -, -, -, origins₁, -, horig₁, -, -, Hcalls⟩ :=
    H.templates.entry mowner hmowner localIndex hlocal
  obtain ⟨⟨origins, horig, hstats, hmotives, F, hparams, depth', -, _, Hsel, -, -, -, -, -, -, -,
    -, -, ⟨HcallAt⟩⟩⟩ := H.templateTyping.entry mowner hmowner localIndex hlocal
  have : origins₁ = origins := Option.some.inj (horig₁.symm.trans horig)
  subst this
  obtain ⟨originRoot, sourceType, O, D, -, hDtype, hcall⟩ := Hcalls.entry j hj
  obtain ⟨_, Rorigin, prior, Hprior, -, hchkO, ⟨Csem⟩⟩ := HcallAt.entry j hj
  obtain ⟨Sc, hscope, -, hSreplay⟩ := Csem.semantic indTypes (H.recInfos.flatMap (·.minors)) []
  have hjR : j < S.recursiveFields.size := S.hypotheses_size ▸ hj
  obtain ⟨pos, hpos, hfield⟩ := S.recursiveField_pos Hsel j hjR
  have howner' : O.ownerIdx < H.recInfos.size := by
    have h := Csem.owner_lt
    rw [hcall] at h
    simpa using h
  have hoLt : O.ownerIdx < origins₁.recInfos.size := by
    have h := congrArg Array.size hmotives
    simp only [Array.size_map] at h
    omega
  -- The induction hypothesis type and the typed call have the same `replayTrace`.
  have hreplay : O.replayTrace S.fields_bound.fvars =
      Sc.generated.replayTrace S.fields_bound.fvars := by
    rw [O.replayTrace_eq_template _ hcall hoLt, hmotives, hSreplay]
  -- The typed call is scoped by the parameters and the fields before `pos`.
  have hfR : F.fieldsRecent.fvars = S.fields_bound.fvars :=
    F.fieldsRecent.toFVarArrayIn.exprArrayFVarIds.symm.trans S.fields_bound.exprArrayFVarIds
  have hPids : ExprArrayFVarIds stats.params = H.params.fvars := H.params.exprArrayFVarIds
  have hrootScope : ∀ fv, Sc.rootScope fv ↔
      fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars := by
    intro fv
    rw [hscope, hfield]
    simp only [RecursorFieldPrefixScope, recursorFVarId, hfR,
      List.Nodup.idxOf_getElem S.fields_nodup pos hpos, hPids]
  obtain ⟨hArgScope, hIdxScope⟩ := O.scope_of_replayTrace Sc hreplay hrootScope
  obtain ⟨B0, indices, hB0na, Hsmall, HIsmall⟩ := H.recursorTelescope_hypothesisSmall mowner
    hmowner localIndex hlocal F hparams Hprior hchkO j Sc pos hpos hfield O (by rw [hstats])
    hreplay
  have hEq := H.recursorTelescope_hypothesisLift howner T minorIdx D₀ mowner hmowner localIndex
    hlocal hD hyps res hhyps hminorEq j hj origins₁ hstats hmotives O D hDtype howner' pos hpos
    hfield hArgScope (fun e he => (hIdxScope e he).2) B0 indices hB0na Hsmall HIsmall
  exact ⟨origins₁, originRoot, sourceType, O, pos, hpos, B0, indices, horig, hstats, hmotives,
    hfield, hB0na, howner', hEq, Hsmall, HIsmall, by rw [hcall], by rw [hcall], by rw [hcall],
    by rw [hcall], by rw [hcall], by rw [hcall], O.argDomains_eq_mkForall,
    O.arguments_bound.toFVarArrayIn.exprArrayFVarIds⟩

end Lean4Lean.VerifyInductive
