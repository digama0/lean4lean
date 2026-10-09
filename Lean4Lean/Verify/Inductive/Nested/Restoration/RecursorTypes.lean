import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement

/-! Restored recursor types of a validated nested run, with the parameter
telescope of the lowered recursor type discharged from the restoration step and
the generated recursor type it translates to (section 3.3 of
the design notes). -/

namespace Lean4Lean
namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- A restoration telescope of an expression translating to a forall
telescope whose body is neither a binder is a forall telescope: a `lam`
binder would translate to a `lam`. -/
theorem RestoreTelescope.forallTelescope_of_tr {env : VEnv} {Us : List Name}
    {X : VExpr} (hXlam : ∀ a b, X ≠ .lam a b) (hXforall : ∀ a b, X ≠ .forallE a b) :
    ∀ {e : Expr} {n : Nat} {Δ : VLCtx} {D : List VExpr},
      RestoreTelescope e n → TrExprS env Us Δ e (VExpr.wrapForalls D X) →
      ∃ suffix, Expr.ForallTelescope e n suffix := by
  intro e n Δ D H
  induction H generalizing Δ D with
  | done => intro _; exact ⟨_, .nil _⟩
  | @forallE body n name dom bi _ ih =>
    intro Ht
    generalize hv : VExpr.wrapForalls D X = v at Ht
    cases Ht with
    | forallE _ _ _ hbody =>
      cases D with
      | nil =>
        simp only [VExpr.wrapForalls, List.foldr_nil] at hv
        exact absurd hv (hXforall _ _)
      | cons d D =>
        simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.forallE.injEq] at hv
        rcases hv with ⟨rfl, hv⟩
        rw [← hv] at hbody
        rcases ih hbody with ⟨suffix, hs⟩
        exact ⟨suffix, .cons hs⟩
  | lam _ _ =>
    intro Ht
    generalize hv : VExpr.wrapForalls D X = v at Ht
    cases Ht with
    | lam _ _ _ =>
      cases D with
      | nil =>
        simp only [VExpr.wrapForalls, List.foldr_nil] at hv
        exact absurd hv (hXlam _ _)
      | cons d D =>
        simp [VExpr.wrapForalls] at hv

theorem VExpr.mkApps_append_singleton (f a : VExpr) (l : List VExpr) :
    VExpr.mkApps f (l ++ [a]) = .app (VExpr.mkApps f l) a := by
  simp [VExpr.mkApps, List.foldl_append]

open _root_.Lean4Lean.InductiveSignature in
/-- The parameter telescope of a lowered recursor type whose translation is
a generated recursor type. -/
theorem RestoreTelescope.forallTelescope_of_recursorType
    {s : InductiveSignature} {g : Instance s} {owner : Fin s.families.size}
    {env : VEnv} {Us : List Name} {e : Expr} {n : Nat}
    (H : RestoreTelescope e n) (Ht : TrExprS env Us [] e (g.recursorType owner)) :
    ∃ suffix, Expr.ForallTelescope e n suffix := by
  simp only [Instance.recursorType] at Ht
  refine H.forallTelescope_of_tr ?_ ?_ Ht <;>
  · intro a b h
    simp only [VExpr.mkApps_append_singleton] at h
    cases h


/-- The lowered recursor type of a restoration step at a generated owner's
recursor name translates to the owner's generated recursor type. -/
theorem NestedRun.loweredRecursorTypeTranslation
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    TrExprS E.lowered.recursors.outVEnv Hstep.oldInfo.levelParams []
      Hstep.oldInfo.type
      (E.lowered.recursors.canonicalGeneration.recursorType owner) := by
  rcases E.lowered.recursors.trMetadata owner with
    ⟨rec, hrec, _, M⟩
  have hlen : owner.val < E.lowered.recursors.entries.length := by
    rw [show E.lowered.recursors.entries =
      E.lowered.recursors.entries from rfl,
      E.lowered.recursors.entries_length_eq]
    exact owner.isLt
  have hmem := List.getElem_mem (l := E.lowered.recursors.entries)
    (n := owner.val) hlen
  have hfind := E.lowered.recursors.findRecursorOfMem
    (info := (E.lowered.recursors.entries[owner.val]'hlen).1) hmem
  have hrec' : (E.lowered.recursors.entries[owner.val]'hlen).1 = .recInfo rec := hrec
  rw [hrec'] at hfind
  change E.loweredEnv.find? rec.name = some (.recInfo rec) at hfind
  have h2 : some (ConstantInfo.recInfo rec) = some (.recInfo Hstep.oldInfo) := by
    rw [← hfind, M.name]
    exact Hstep.lookup
  have heq : rec = Hstep.oldInfo := by
    injection h2 with h
    injection h
  rw [heq] at M
  exact M.type

/-- The parameter telescope of the lowered recursor type of a restoration
step at a generated owner's recursor name. -/
theorem NestedRun.loweredRecursorParameterTelescope
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    ∃ suffix, Expr.ForallTelescope Hstep.oldInfo.type result.nparams suffix :=
  Hstep.typeTelescope.forallTelescope_of_recursorType
    (E.loweredRecursorTypeTranslation owner Hstep)

/-- The executable recursor name of a generated entry, as recorded by
`AuxiliaryRecursorGeneratedAlignment.oldRecName_eq`, is the generated
recursor name of the generated owner at the same position. -/
theorem NestedRun.recursorOwnerOfEntry
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {ownerIdx : Nat} (hentry : ownerIdx < E.lowered.recursors.entries.length) :
    ∃ owner : Fin E.lowered.recursors.generationSignature.families.size,
      owner.val = ownerIdx ∧
      Lean.mkRecName E.lowered.indTypes[ownerIdx]!.name =
        E.lowered.recursors.canonicalGeneration.recursorName owner := by
  have hi : ownerIdx < E.lowered.recursors.generationSignature.families.size := by
    rw [← E.lowered.recursors.entries_length_eq]
    exact hentry
  refine ⟨⟨ownerIdx, hi⟩, rfl, ?_⟩
  rcases E.lowered.recursors.trMetadata ⟨ownerIdx, hi⟩ with
    ⟨rec, hrec, _, M⟩
  let G := E.lowered.recursors.generated.entry ownerIdx hentry
  have h : ConstantInfo.recInfo rec = .recInfo G.info := hrec.symm.trans G.source_eq
  injection h with h
  rw [← G.name, ← h, M.name]

end VerifyInductive
end Lean4Lean
