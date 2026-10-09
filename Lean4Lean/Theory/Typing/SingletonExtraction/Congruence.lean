import Lean4Lean.Theory.Typing.SingletonExtraction.Basic
import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Inductive.RestorationNaturality

/-! # Syntactic congruence of singleton extraction

The cast telescope, the extraction functions and the reconstruction `PropElim.occ` are
built from their inputs by syntax constructors, lifting and instantiation only. Hence they
respect every relation on expressions that is a congruence for these operations
(`SynRel`). Universe instantiation (`R x y := y = x.instL ls`) and equality up to
equivalent universe levels (`EqUpToLevels`) are the two instances used by the singleton
and quotient prefix unfoldings. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr

/-- A relation on expressions that is a congruence for the syntax used by singleton
extraction, together with its relation on universe levels. -/
structure SynRel (R : VExpr → VExpr → Prop) (RL : VLevel → VLevel → Prop) : Prop where
  bvar : ∀ i, R (.bvar i) (.bvar i)
  sort : RL u v → R (.sort u) (.sort v)
  const : ∀ {c ls ls'}, List.Forall₂ RL ls ls' → R (.const c ls) (.const c ls')
  app : R f f' → R a a' → R (.app f a) (.app f' a')
  lam : R A A' → R b b' → R (.lam A b) (.lam A' b')
  forallE : R A A' → R b b' → R (.forallE A b) (.forallE A' b')
  liftN : ∀ {e e'} (n k : Nat), R e e' → R (e.liftN n k) (e'.liftN n k)
  instOuter : ∀ {X X' args args'}, R X X' → List.Forall₂ R args args' →
    R (X.instOuter args) (X'.instOuter args')
  zero : RL .zero .zero
  succ : RL u v → RL (.succ u) (.succ v)

namespace SynRel
variable {R : VExpr → VExpr → Prop} {RL : VLevel → VLevel → Prop} (H : SynRel R RL)
include H

theorem dflt : R (default : VExpr) (default : VExpr) := H.sort H.zero

theorem lift (h : R e e') : R e.lift e'.lift := H.liftN 1 0 h

theorem mkApps (hf : R f f') : List.Forall₂ R args args' →
    R (VExpr.mkApps f args) (VExpr.mkApps f' args') := by
  intro ha
  induction ha generalizing f f' with
  | nil => exact hf
  | cons h _ ih => exact ih (H.app hf h)

theorem wrapLams (hb : R b b') : List.Forall₂ R ds ds' →
    R (VExpr.wrapLams ds b) (VExpr.wrapLams ds' b') := by
  intro hd
  induction hd with
  | nil => exact hb
  | cons h _ ih => exact H.lam h ih

theorem wrapForalls (hb : R b b') : List.Forall₂ R ds ds' →
    R (VExpr.wrapForalls ds b) (VExpr.wrapForalls ds' b') := by
  intro hd
  induction hd with
  | nil => exact hb
  | cons h _ ih => exact H.forallE h ih

theorem getD (h : List.Forall₂ R l l') (i : Nat) :
    R (l.getD i default) (l'.getD i default) := by
  induction h generalizing i with
  | nil => exact H.dflt
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih i

theorem refl_bvarRange (n t : Nat) : List.Forall₂ R (bvarRange n t) (bvarRange n t) := by
  simp only [bvarRange]
  induction (List.range n) with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (H.bvar _) ih

theorem map_liftN (h : List.Forall₂ R l l') (n k : Nat) :
    List.Forall₂ R (l.map (·.liftN n k)) (l'.map (·.liftN n k)) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (H.liftN n k h) ih

theorem map_lift (h : List.Forall₂ R l l') :
    List.Forall₂ R (l.map (·.lift)) (l'.map (·.lift)) := H.map_liftN h 1 0

omit H in
theorem take (h : List.Forall₂ R l l') (k : Nat) : List.Forall₂ R (l.take k) (l'.take k) := by
  induction h generalizing k with
  | nil => simp
  | cons h _ ih => cases k with
    | zero => simp
    | succ k => exact .cons h (ih k)

omit H in
theorem append (h : List.Forall₂ R l l') (h' : List.Forall₂ R m m') :
    List.Forall₂ R (l ++ m) (l' ++ m') := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h ih

theorem eqApp (hw : RL w w') (hα : R α α') (ha : R a a') (hb : R b b') :
    R (VExpr.eqApp w α a b) (VExpr.eqApp w' α' a' b') :=
  H.app (H.app (H.app (H.const (.cons hw .nil)) hα) ha) hb

theorem eqReflApp (hw : RL w w') (hα : R α α') (ha : R a a') :
    R (VExpr.eqReflApp w α a) (VExpr.eqReflApp w' α' a') :=
  H.app (H.app (H.const (.cons hw .nil)) hα) ha

theorem typeCast (hu : RL u u') (hX : R X X') (hY : R Y Y') (he : R e e') (hx : R x x') :
    R (VExpr.typeCast u X Y e x) (VExpr.typeCast u' X' Y' e' x') := by
  unfold VExpr.typeCast VExpr.eqRecApp VExpr.castMotive
  exact H.app (H.app (H.app (H.app (H.app (H.app
    (H.const (.cons hu (.cons (H.succ hu) .nil))) (H.sort hu)) hX)
    (H.lam (H.sort hu) (H.lam (H.eqApp (H.succ hu) (H.sort hu) (H.lift hX) (H.bvar 0))
      (H.bvar 1)))) hx) hY) he

end SynRel


theorem forall₂_levels {U : Nat} :
    ∀ {ls ls' : List VLevel}, List.Forall₂ (fun u v => u.WF U ∧ v.WF U ∧ u ≈ v) ls ls' →
      (∀ l ∈ ls, l.WF U) ∧ (∀ l ∈ ls', l.WF U) ∧ List.Forall₂ (· ≈ ·) ls ls'
  | _, _, .nil => ⟨by simp, by simp, .nil⟩
  | _, _, .cons h t => by
    obtain ⟨h1, h2, h3⟩ := forall₂_levels t
    exact ⟨List.forall_mem_cons.2 ⟨h.1, h1⟩, List.forall_mem_cons.2 ⟨h.2.1, h2⟩, .cons h.2.2 h3⟩

/-- Equality up to equivalent well-formed universe levels as a syntactic congruence. -/
theorem SynRel.levels (U : Nat) :
    SynRel (VEnv.EqUpToLevels U) (fun u v => u.WF U ∧ v.WF U ∧ u ≈ v) where
  bvar _ := .bvar
  sort h := .sort h.1 h.2.1 h.2.2
  const h := let ⟨h1, h2, h3⟩ := forall₂_levels h; .const h1 h2 h3
  app h1 h2 := .app h1 h2
  lam h1 h2 := .lam h1 h2
  forallE h1 h2 := .forallE h1 h2
  liftN n k h := h.weakN
  instOuter h ha := by
    rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst]
    apply h.subst_args
    intro i
    have hlen := Lean4Lean.List.Forall₂.length_eq ha
    simp only [VExpr.Subst.ofList, ← hlen]
    split
    · exact List.forall₂_getElem ha _ (by omega) (by omega)
    · exact .bvar
  zero := ⟨by simp [VLevel.WF], by simp [VLevel.WF], rfl⟩
  succ h := ⟨h.1, h.2.1, VLevel.succ_congr h.2.2⟩

namespace SingletonLayout

/-- Related cast specifications: related telescopes and sorts, the same slots. -/
structure Rel (R : VExpr → VExpr → Prop) (RL : VLevel → VLevel → Prop)
    (S S' : SingletonLayout) : Prop where
  fields : List.Forall₂ R S.fields S'.fields
  indices : List.Forall₂ R S.indices S'.indices
  slot : S.slot = S'.slot
  sorts : ∀ i, RL (S.sorts.getD i .zero) (S'.sorts.getD i .zero)

variable {R : VExpr → VExpr → Prop} {RL : VLevel → VLevel → Prop}

theorem Rel.fields_length (h : Rel R RL S S') : S.fields.length = S'.fields.length :=
  Lean4Lean.List.Forall₂.length_eq h.fields

theorem Rel.indices_length (h : Rel R RL S S') : S.indices.length = S'.indices.length :=
  Lean4Lean.List.Forall₂.length_eq h.indices

theorem step_rel (H : SynRel R RL) (hS : Rel R RL S S') (hpa : List.Forall₂ R pa pa')
    (hia : List.Forall₂ R ia ia') (hσ : List.Forall₂ R σ σ') (i : Nat) :
    R (S.step pa ia i σ).1 (S'.step pa' ia' i σ').1 ∧
      R (S.step pa ia i σ).2 (S'.step pa' ia' i σ').2 := by
  have hY := H.instOuter (H.getD hS.fields i) (SynRel.append (H.map_liftN hpa i 0) hσ)
  simp only [step, ← hS.slot]
  split
  · rename_i k _
    have hX := H.instOuter (H.getD hS.indices k)
      (SynRel.append (H.map_liftN hpa i 0) (H.map_liftN (SynRel.take hia k) i 0))
    have hu := hS.sorts i
    refine ⟨H.eqApp (H.succ hu) (H.sort hu) hX hY, ?_⟩
    exact H.typeCast hu (H.lift hX) (H.lift hY) (H.bvar 0) (H.liftN _ 0 (H.getD hia k))
  · exact ⟨hY, H.bvar 0⟩

theorem tel_rel (H : SynRel R RL) (hS : Rel R RL S S') (hpa : List.Forall₂ R pa pa')
    (hia : List.Forall₂ R ia ia') :
    ∀ i, List.Forall₂ R (S.tel pa ia i).1 (S'.tel pa' ia' i).1 ∧
      List.Forall₂ R (S.tel pa ia i).2 (S'.tel pa' ia' i).2
  | 0 => ⟨.nil, .nil⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := tel_rel H hS hpa hia i
    have hs := step_rel H hS hpa hia h2 i
    simp only [tel]
    exact ⟨SynRel.append h1 (.cons hs.1 .nil), SynRel.append (H.map_lift h2) (.cons hs.2 .nil)⟩

theorem target_rel (H : SynRel R RL) (hS : Rel R RL S S') (hpa : List.Forall₂ R pa pa')
    (hia : List.Forall₂ R ia ia') (j : Nat) :
    R (S.target pa ia j) (S'.target pa' ia' j) :=
  H.instOuter (H.getD hS.fields j)
    (SynRel.append (H.map_liftN hpa j 0) (tel_rel H hS hpa hia j).2)

end SingletonLayout

namespace PropElim

/-- Related eliminations: related heads and constructor indices, and minor premises built
from related motives and branches are related. -/
structure Rel (R : VExpr → VExpr → Prop) (E E' : PropElim) : Prop where
  family : R E.family E'.family
  ctor : R E.ctor E'.ctor
  ctorIndices : List.Forall₂ R E.ctorIndices E'.ctorIndices
  elimHead : R E.elimHead E'.elimHead
  minorOf : ∀ {M M' b b'}, R M M' → R b b' → R (E.minorOf M b) (E'.minorOf M' b')

variable {R : VExpr → VExpr → Prop} {RL : VLevel → VLevel → Prop}

theorem value_rel (H : SynRel R RL) (hS : SingletonLayout.Rel R RL S S')
    (hP : List.Forall₂ R params params') (hE : Rel R E E') (j : Nat) :
    R (value S params E j) (value S' params' E' j) := by
  have hPl := Lean4Lean.List.Forall₂.length_eq hP
  have hIl := hS.indices_length
  have hFl := hS.fields_length
  have hmaj : R (majorTy S params E) (majorTy S' params' E') := by
    simp only [majorTy, hPl, hIl]
    exact H.mkApps hE.family (SynRel.append (H.refl_bvarRange _ _) (H.refl_bvarRange _ _))
  have hgpa : genericPa S params = genericPa S' params' := by simp [genericPa, hPl, hIl]
  have hgia : genericIa S = genericIa S' := by simp [genericIa, hIl]
  have hmot : R (motive S params E j) (motive S' params' E' j) := by
    simp only [motive]
    rw [hgpa, hgia]
    have hpa := H.refl_bvarRange (params'.length) (params'.length + S'.indices.length + 1)
    have hia := H.refl_bvarRange S'.indices.length (S'.indices.length + 1)
    exact H.wrapLams (H.wrapForalls (SingletonLayout.target_rel H hS hpa hia j)
      (SingletonLayout.tel_rel H hS hpa hia j).1) (SynRel.append hS.indices (.cons hmaj .nil))
  have hbr : R (branch S params E j) (branch S' params' E' j) := by
    simp only [branch, branchPa, hPl, hFl]
    exact H.wrapLams (H.bvar _)
      (SingletonLayout.tel_rel H hS (H.refl_bvarRange _ _) hE.ctorIndices j).1
  simp only [value, genericPa, hPl, hIl]
  apply H.wrapLams _ (SynRel.append (SynRel.append hP hS.indices) (.cons hmaj .nil))
  apply H.mkApps hE.elimHead
  refine SynRel.append (SynRel.append (H.refl_bvarRange _ _) ?_) (H.refl_bvarRange _ _)
  exact .cons (H.liftN _ 0 hmot) (.cons (H.liftN _ 0 (hE.minorOf hmot hbr)) .nil)

theorem occ_rel (H : SynRel R RL) (hS : SingletonLayout.Rel R RL S S')
    (hP : List.Forall₂ R params params') (hE : Rel R E E')
    (hps : List.Forall₂ R ps ps') (hidx : List.Forall₂ R idx idx') (hm : R m m') :
    ∀ i, List.Forall₂ R (occ S params E ps idx m i).1 (occ S' params' E' ps' idx' m' i).1 ∧
      List.Forall₂ R (occ S params E ps idx m i).2 (occ S' params' E' ps' idx' m' i).2
  | 0 => ⟨.nil, .nil⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := occ_rel H hS hP hE hps hidx hm i
    simp only [occ, ← hS.slot]
    split
    · rename_i k _
      have hu := hS.sorts i
      refine ⟨SynRel.append h1 (.cons (H.eqReflApp (H.succ hu) (H.sort hu)
          (H.instOuter (H.getD hS.indices k) (SynRel.append hps (SynRel.take hidx k)))) .nil),
        SynRel.append h2 (.cons (H.getD hidx k) .nil)⟩
    · have hv := H.mkApps (value_rel H hS hP hE i)
        (SynRel.append (SynRel.append (SynRel.append hps hidx) (.cons hm .nil)) h1)
      exact ⟨SynRel.append h1 (.cons hv .nil), SynRel.append h2 (.cons hv .nil)⟩

end PropElim
end Lean4Lean
