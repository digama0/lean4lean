import Lean4Lean.Theory.Inductive

/-!
Executable decision procedures for the syntactic predicates of `VInductDecl.WF`.

The shape, positivity and result-type predicates of `Lean4Lean.Theory.Inductive` are stated
as propositions and used as such in the theory; only the tests run them, on the translation
of the kernel's own recursor, constructor and ι-rule data. The `Decidable` instances that
make them executable therefore live here rather than beside the definitions.
-/

namespace Lean4Lean

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

namespace VExpr

instance {e f : VExpr} {pre : List VExpr} : Decidable (∃ rest, e = f.mkApps (pre ++ rest)) :=
  decidable_of_iff _ eq_mkApps_append_iff.symm

instance {e f : VExpr} {pre : List VExpr} {n : Nat} :
    Decidable (∃ rest, rest.length = n ∧ e = f.mkApps (pre ++ rest)) :=
  decidable_of_iff _ eq_mkApps_append_length_iff.symm

instance {α : Type _} {o : Option α} {P : α → Prop} [DecidablePred P] :
    Decidable (∃ a, o = some a ∧ P a) :=
  match o with
  | none => isFalse (by rintro ⟨_, h, _⟩; cases h)
  | some a => decidable_of_iff (P a) ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, hp⟩ => Option.some.inj h ▸ hp⟩

instance {cs : List Name} {e : VExpr} : Decidable (e.MentionsConst cs) :=
  decidable_of_iff _ mentionsConst_iff

instance {ty : VExpr} {T : Name} {np nf nind : Nat} : Decidable (ty.CtorResult T np nf nind) :=
  decidable_of_iff _ CtorResult_iff.symm

instance {A : VExpr} {T : Name} {np nm nmin nind : Nat} :
    Decidable (A.MajorApp T np nm nmin nind) := decidable_of_iff _ MajorApp_iff.symm

instance {fs : List Name} {np d : Nat} {e : VExpr} : Decidable (e.ValidIndApp fs np d) :=
  decidable_of_iff _ ValidIndApp_iff.symm

instance {fs : List Name} {np d : Nat} {ty : VExpr} : Decidable (ty.FieldPositive fs np d) := by
  unfold FieldPositive; infer_instance

instance {fs : List Name} {np : Nat} {ty : VExpr} : Decidable (ty.CtorPositive fs np) := by
  unfold CtorPositive; infer_instance

instance {ty : VExpr} {np i : Nat} : Decidable (ty.FieldInIndices np i) := by
  unfold FieldInIndices; infer_instance

instance {A : VExpr} : Decidable A.MotiveShape := by unfold MotiveShape; infer_instance
instance {A : VExpr} {i nm : Nat} : Decidable (A.MinorHeaded i nm) := by
  unfold MinorHeaded; infer_instance
instance {A : VExpr} {c : Name} : Decidable (A.MinorFor c) := by
  unfold MinorFor; infer_instance
instance {ty : VExpr} {np nm nmin nind : Nat} : Decidable (ty.RecShape np nm nmin nind) := by
  unfold RecShape; infer_instance
instance {ty : VExpr} {arity : Nat} : Decidable (ty.CtorShape arity) := by
  unfold CtorShape; infer_instance
instance {rhs : VExpr} {np nm nmin nf nrec j : Nat} :
    Decidable (rhs.RuleShape np nm nmin nf nrec j) := by
  unfold RuleShape; infer_instance

end VExpr

instance {decl : VInductDecl} : Decidable decl.LargeElimShape := by
  unfold VInductDecl.LargeElimShape; infer_instance
