import Lean4Lean.Verify.Inductive.Recursor.Context.FVarArrays

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! Scope of the declared type of a constructor field opened by the minor pass.

A recursive field's induction hypothesis must be generated from binder
domains scoped over the parameters and the *earlier* fields only.  The
executable infers the field's type by local-context lookup, so its syntactic
scope is read off the stored metacontext declaration rather than through the
abstract `FVarsBelow` contract, which cannot exclude the field itself. -/

/-- `getType` of a free variable returns its declared local type. -/
theorem getTypeFVarRun.WF (c : AddInductive.Context) (fv : FVarId)
    (hmem : ∃ decl, c.lctx.find? fv = some decl) :
    (AddInductive.getType (.fvar fv) c).WF
      fun ty => ∃ decl, c.lctx.find? fv = some decl ∧ ty = decl.type := by
  rcases hmem with ⟨decl, hfind⟩
  intro ty hty
  change Except.ok (c.lctx.get! fv).type = Except.ok ty at hty
  simp only [LocalContext.get!, hfind, Except.ok.injEq] at hty
  exact ⟨decl, hfind, hty.symm⟩

theorem IsFVarUpSet.deps_of_mem {P : FVarId → Prop} {fv : FVarId} {deps : List FVarId}
    {d : VLocalDecl} :
    ∀ {Δ : VLCtx}, IsFVarUpSet P Δ → (some (fv, deps), d) ∈ Δ → P fv → ∀ x ∈ deps, P x
  | [], _, h, _ => by cases h
  | (none, _) :: Δ, hup, hmem, hfv => by
      rcases List.mem_cons.mp hmem with h | h
      · cases h
      · exact deps_of_mem (Δ := Δ) hup h hfv
  | (some (fv', deps'), d') :: Δ, hup, hmem, hfv => by
      rcases List.mem_cons.mp hmem with h | h
      · cases h
        exact hup.2 hfv
      · exact deps_of_mem hup.1 h hfv

/-- The declared type of the `k`-th newest free variable of an all-lambda
metacontext is the stored binder domain: its dependencies are recorded on the
variable's own entry and lie among the older variables. -/
theorem TypeChecker.MLCtx.recentTypeScope {env : VEnv} {Us : List Name} :
    ∀ (c : TypeChecker.MLCtx), c.WF env Us → MLCtxOnlyLams c →
    ∀ (n : Nat) (hn : n ≤ c.length) (k : Nat) (hk : k < n) (decl : LocalDecl),
      c.lctx.find? ((c.fvarRevList n hn)[k]'(by simpa using hk)) = some decl →
      (∃ ty', (some ((c.fvarRevList n hn)[k]'(by simpa using hk), decl.type.fvarsList),
        .vlam ty') ∈ c.vlctx) ∧
      decl.type.FVarsIn (fun x => x ∈ (c.fvarRevList n hn).drop (k + 1) ∨
        x ∈ (c.dropN n hn).vlctx.fvars)
  | _, _, _, 0, _, _, hk, _, _ => by omega
  | .nil, _, _, n+1, hn, _, _, _, _ => by simp at hn
  | .vlet .., _, honly, n+1, _, _, _, _, _ => honly.vlet_false.elim
  | .vlam id name ty ty' bi c, hwf, honly, n+1, hn, k, hk, decl, hfind => by
    obtain ⟨hwfc, hfresh, htr, _⟩ := hwf
    have hn' : n ≤ c.length := Nat.le_of_succ_le_succ hn
    cases k with
    | zero =>
      simp only [TypeChecker.MLCtx.fvarRevList, List.getElem_cons_zero,
        TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
        hwfc.tr.1.map_wf.find?_insert, BEq.rfl, ↓reduceIte, Option.some.injEq] at hfind
      subst hfind
      refine ⟨⟨ty', by simp [LocalDecl.type]⟩, ?_⟩
      simp only [TypeChecker.MLCtx.fvarRevList, TypeChecker.MLCtx.dropN,
        List.drop_succ_cons, List.drop_zero, LocalDecl.type]
      refine htr.fvarsIn.mono ?_
      intro x hx
      rw [TypeChecker.MLCtx.fvars_eq_append (n := n) (hn := hn')] at hx
      simpa using hx
    | succ k =>
      have hk' : k < n := by omega
      have hk1 : k + 1 <
          ((TypeChecker.MLCtx.vlam id name ty ty' bi c).fvarRevList (n + 1) hn).length := by
        simpa using hk
      have hk2 : k < (c.fvarRevList n hn').length := by simpa using hk'
      have hmem : (c.fvarRevList n hn')[k]'hk2 ∈ c.vlctx.fvars :=
        c.fvarRevList_prefix.subset (List.getElem_mem _)
      have hne : id ≠ (c.fvarRevList n hn')[k]'hk2 := fun h =>
        hwfc.tr.find?_eq_none.1 hfresh (h ▸ hmem)
      have hget : ((TypeChecker.MLCtx.vlam id name ty ty' bi c).fvarRevList (n + 1) hn)[k + 1]'hk1 =
          (c.fvarRevList n hn')[k]'hk2 := by
        simp [TypeChecker.MLCtx.fvarRevList]
      rw [hget] at hfind ⊢
      simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
        hwfc.tr.1.map_wf.find?_insert] at hfind
      rw [if_neg (by intro heq; exact hne (beq_iff_eq.mp heq))] at hfind
      obtain ⟨⟨ty'', hmem'⟩, hscope⟩ :=
        recentTypeScope c hwfc honly.tail_vlam n hn' k hk' decl hfind
      refine ⟨⟨ty'', ?_⟩, ?_⟩
      · simp only [TypeChecker.MLCtx.vlctx]
        exact List.mem_cons_of_mem _ hmem'
      · simpa only [TypeChecker.MLCtx.fvarRevList, TypeChecker.MLCtx.dropN,
          List.drop_succ_cons] using hscope

/-- The declared type of an opened field is scoped over the root scope `P`
and the earlier fields: its dependencies are older binders, and an older
binder in the root is in `P` by the field up-set since fields are fresh. -/
theorem RecursorFVarSuffix.fieldTypeScope
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorFVarSuffix Rroot R xs)
    {P : FVarId → Prop}
    (hup : IsFVarUpSet (fun fv => fv ∈ H.fvars ∨ P fv) R.mlctx.vlctx)
    (pos : Nat) (hpos : pos < H.fvars.length) (decl : LocalDecl)
    (hfind : c.lctx.find? H.fvars[pos] = some decl) :
    decl.type.FVarsIn (fun x => x ∈ H.fvars.take pos ∨ P x) := by
  have hlen : H.fvars.length = xs.size := by
    have := congrArg Array.size H.expressions
    simpa using this.symm
  have hk : xs.size - 1 - pos < xs.size := by omega
  have hrev : (R.mlctx.fvarRevList xs.size H.size_le)[xs.size - 1 - pos]'(by simpa using hk) =
      H.fvars[pos] := by
    have h := H.fvarRevList_eq
    simp only [h, List.getElem_reverse]
    congr 1
    omega
  have hfind' : R.mlctx.lctx.find?
      ((R.mlctx.fvarRevList xs.size H.size_le)[xs.size - 1 - pos]'(by simpa using hk)) =
        some decl := by
    rw [hrev, R.lctx_eq]
    exact hfind
  obtain ⟨⟨ty', hmem⟩, hscope⟩ := TypeChecker.MLCtx.recentTypeScope R.mlctx R.mlctx_wf
    R.onlyLams xs.size H.size_le (xs.size - 1 - pos) hk decl hfind'
  rw [hrev] at hmem
  have hdeps : ∀ x ∈ decl.type.fvarsList, x ∈ H.fvars ∨ P x :=
    IsFVarUpSet.deps_of_mem hup hmem (Or.inl (List.getElem_mem hpos))
  rw [H.drop_eq, H.fvarRevList_eq, List.drop_reverse] at hscope
  have hrootFVars : Rroot.mlctx.vlctx.fvars = root.lctx.fvars := by
    rw [← Rroot.lctx_eq, Rroot.mlctx_wf.tr.fvars_eq]
  change FVarsIn _ _ at hscope
  change FVarsIn _ _
  rw [fvarsIn_iff] at hscope ⊢
  refine ⟨?_, hscope.2⟩
  intro x hx
  rcases hscope.1 x hx with htake | hroot
  · left
    have htake' : x ∈ H.fvars.take pos := by
      have : H.fvars.length - (xs.size - 1 - pos + 1) = pos := by omega
      rw [this] at htake
      exact List.mem_reverse.mp htake
    exact htake'
  · rcases hdeps x hx with hfield | hP
    · exact absurd (hrootFVars ▸ hroot) (H.fresh x hfield)
    · exact Or.inr hP

end VerifyInductive
end Lean4Lean
