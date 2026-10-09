import Lean4Lean.Theory.Typing.SingletonExtraction.Recursor
import Lean4Lean.Theory.Typing.SingletonExtraction.RecursorLevels
import Lean4Lean.Theory.Typing.SingletonExtraction.Scope

/-! # Scoping of the singleton extraction

The cast specification and the elimination into `Prop` of a registered recursor are
scoped (`PropElim.Closed`), read off the closed generated recursor type. No typing beyond the
registration and no canonical `Eq` are used. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr VEnv

theorem VExpr.ClosedN.wrapForalls_inv_singleton : ∀ {doms : List VExpr} {body : VExpr} {n : Nat},
    (VExpr.wrapForalls doms body).ClosedN n →
      (∀ i (h : i < doms.length), (doms[i]).ClosedN (n + i)) ∧ body.ClosedN (n + doms.length)
  | [], _, _, h => ⟨by simp, h⟩
  | d :: ds, body, n, h => by
    obtain ⟨hd, hb⟩ := h
    obtain ⟨h1, h2⟩ := VExpr.ClosedN.wrapForalls_inv_singleton (doms := ds) (n := n + 1) hb
    refine ⟨fun i hi => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2⟩
    cases i with
    | zero => simpa using hd
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using h1 i (by simpa using hi)

theorem VExpr.ClosedN.instL_iff {e : VExpr} {ls : List VLevel} {n : Nat} :
    (e.instL ls).ClosedN n ↔ e.ClosedN n := ⟨ClosedN.instL_rev, ClosedN.instL⟩

namespace InductiveSignature.RecursorData
variable {env : VEnv} {data : RecursorData}

theorem propElim_closed (henv : env.WF) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    {ls : List VLevel} {S : SingletonLayout} {E : PropElim}
    (hS : data.singletonLayout env ls = some S) (hE : data.propElim ls = some E) :
    PropElim.Closed S (data.propParams ls) E := by
  have F := singletonSignature H hlarge hzero
  unfold propElim at hE
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hE
  obtain ⟨k, hk, i, hi, rfl⟩ := hE
  unfold singletonLayout singletonLayoutGeneric at hS
  simp only [hi, Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.map_some,
    Option.some.injEq] at hS
  subst hS
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := F.constructors; have := i.isLt; omega
  have hfam := F.families
  have hk' : data.target = .param k := by
    unfold targetParam at hk; split at hk <;> simp_all
  obtain ⟨k', hk'', hkU, _⟩ := F.free
  have hkk : k = k' := by rw [hk'] at hk''; injection hk''
  subst hkk
  generalize hc : data.schema.signature.constructors[i] = c
  have hown : c.owner = data.owner := by
    have := c.owner.isLt; have := data.owner.isLt; ext; omega
  have hown0 : c.owner.val = 0 := by have := c.owner.isLt; omega
  have hmem : c ∈ data.schema.signature.constructors.toList := hc ▸ Array.getElem_mem_toList ..
  have harity := F.arity c hmem
  simp only [hown] at harity
  -- the closed generated recursor type, at the instance eliminating into `Prop`
  let gp := data.recursorInstance.specialize 0 (ls.set k .zero)
  have htarget : gp.targetLevel = .zero := by
    show (data.target).inst (ls.set k .zero) = .zero
    rw [hk']
    simp only [VLevel.inst, List.getD_eq_getElem?_getD]
    by_cases hkl : k < ls.length
    · rw [List.getElem?_set_self (by simpa using hkl)]; rfl
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  have hclosed : (gp.recursorType data.owner).ClosedN 0 := by
    have hgen : data.recursorType = some (data.recursorInstance.recursorType data.owner) := by
      simp [recursorType, F.restoration]
    have := (H.recursorType_closed henv hgen).instL (ls := ls.set k .zero)
    rwa [Instance.recursorType_specialize _ 0] at this
  have hrec := gp.recursorType_shape hfam hcs data.owner i
  rw [hc, gp.motive_shape data.owner htarget, gp.minor_shape hfam c hown0, gp.major_lift,
    gp.constructorApp_shape] at hrec
  rw [hrec] at hclosed
  obtain ⟨hdoms, _⟩ := VExpr.ClosedN.wrapForalls_inv_singleton hclosed
  have hPlen : gp.params.length = data.recursorInstance.params.length := by
    simp [Instance.params, Instance.specialize, recursorInstance]
  -- parameters
  have hP : ∀ j (h : j < gp.params.length), (gp.params[j]).ClosedN j := by
    intro j hj
    have := hdoms j (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simp; omega), List.getElem_append_left hj] at this
    simpa using this
  -- the motive and the minor premise
  have hMot := hdoms gp.params.length (by simp)
  rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
    List.getElem_append_left (by simp), List.getElem_append_right (by simp)] at hMot
  simp only [Nat.zero_add, Nat.sub_self, List.getElem_singleton] at hMot
  obtain ⟨hIM, _⟩ := VExpr.ClosedN.wrapForalls_inv_singleton hMot
  have hMin := hdoms (gp.params.length + 1) (by simp)
  rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
    List.getElem_append_right (by simp)] at hMin
  simp only [Nat.zero_add, List.length_append, List.length_singleton, Nat.sub_self,
    List.getElem_singleton] at hMin
  obtain ⟨hD, hbody⟩ := VExpr.ClosedN.wrapForalls_inv_singleton hMin
  -- closedness of the specialized telescopes
  have hI : ∀ k (h : k < (gp.indicesAt data.owner).length),
      ((gp.indicesAt data.owner)[k]).ClosedN (gp.params.length + k) := by
    intro k hk
    have := hIM k (by simp; omega)
    rwa [List.getElem_append_left hk] at this
  have hF : ∀ j (h : j < (gp.fieldsAt c).length),
      ((gp.fieldsAt c)[j]).ClosedN (gp.params.length + j) := by
    intro j hj
    have := hD j (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), VEnv.getElem_insertBinders (by simp; omega)] at this
    exact VExpr.ClosedN.of_liftN (k := gp.params.length + j)
      (by simpa [Nat.add_right_comm, Nat.add_assoc] using this) (by omega)
  have hCI : ∀ e ∈ gp.ctorIndicesAt c, e.ClosedN (gp.params.length + (gp.fieldsAt c).length) := by
    intro e he
    have := (VExpr.ClosedN.mkApps_inv hbody).2 _
      (List.mem_append_left _ (List.mem_map_of_mem he))
    simp only [List.length_append, InductiveSignature.Instance.length_insertBinders] at this
    have h1 := VExpr.ClosedN.of_liftN
      (k := gp.params.length + (gp.fieldsAt c).length + (gp.hypotheses c).length)
      (j := (gp.fieldsAt c).length + (gp.hypotheses c).length) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this) (by omega)
    exact VExpr.ClosedN.of_liftN (j := 0) (n := (gp.hypotheses c).length)
      (k := gp.params.length + (gp.fieldsAt c).length) h1 (Nat.zero_le _)
  -- transfer between the occurrence universes and the `Prop` instance
  have hsF : gp.fieldsAt c = (data.recursorInstance.fieldsAt c).map (·.instL (ls.set k .zero)) :=
    Instance.sFields_specialize _ _ _ _
  have hsI : gp.indicesAt data.owner =
      (data.recursorInstance.indicesAt data.owner).map (·.instL (ls.set k .zero)) :=
    Instance.sIndices_specialize _ _ _ _
  have hsP : gp.params = data.recursorInstance.params.map (·.instL (ls.set k .zero)) :=
    Instance.specialize_params _ _ _
  have hlF : (gp.fieldsAt c).length = (data.recursorInstance.fieldsAt c).length := by simp [hsF]
  have hlI : (gp.indicesAt data.owner).length = (data.recursorInstance.indicesAt data.owner).length := by
    simp [hsI]
  have hlCI : (gp.ctorIndicesAt c).length = (gp.indicesAt data.owner).length := by
    simp [Instance.ctorIndicesAt, Instance.indicesAt, harity]
  have hlP : (data.propParams ls).length = gp.params.length := by simp [propParams, hsP]
  refine {
    scope := ⟨fun j hj => ?_, fun j hj => ?_, fun j k' h => ?_⟩
    params_closed := fun j hj => ?_
    family := trivial
    elimHead := trivial
    ctorIndices := fun e he => ?_
    ctorIndices_length := ?_
    minorOf := fun M b hM hb => ?_ }
  · simp only [SingletonLayout.instL, Instance.singletonCast, List.getElem_map, ClosedN.instL_iff] at hj ⊢
    have := hF j (by rw [hlF]; simpa using hj)
    simp only [hsF, List.getElem_map, ClosedN.instL_iff] at this
    simpa [hlP] using this
  · simp only [SingletonLayout.instL, Instance.singletonCast, List.getElem_map, ClosedN.instL_iff] at hj ⊢
    have := hI j (by rw [hlI]; simpa using hj)
    simp only [hsI, List.getElem_map, ClosedN.instL_iff] at this
    simpa [hlP] using this
  · simp only [SingletonLayout.instL, Instance.singletonCast] at h ⊢
    by_cases hjl : j < (data.recursorInstance.fieldsAt c).length
    · rw [getD_of_lt (by simpa using hjl)] at h
      simp only [List.getElem_map, List.getElem_range] at h
      obtain ⟨hk1, _⟩ := fieldSlot_spec h
      simp only [List.length_map]
      have : (data.recursorInstance.ctorIndicesAt c).length =
          (data.recursorInstance.indicesAt data.owner).length := by
        simp [Instance.ctorIndicesAt, Instance.indicesAt, harity]
      omega
    · simp [List.getD_eq_getElem?_getD, List.getElem?_range, hjl] at h
  · simp only [propParams, List.getElem_map, ClosedN.instL_iff]
    have := hP j (by rw [← hlP]; exact hj)
    simp only [hsP, List.getElem_map, ClosedN.instL_iff] at this
    exact this
  · change e ∈ gp.ctorIndicesAt c at he
    have := hCI e he
    simpa [hlP, SingletonLayout.instL, Instance.singletonCast, hlF] using this
  · show (gp.ctorIndicesAt c).length = _
    simpa [SingletonLayout.instL, Instance.singletonCast] using hlCI.trans hlI
  · simp only [Instance.singletonElim]
    change (VExpr.wrapLams (VExpr.instDomains (insertBinders (gp.fieldsAt c) 1 ++ gp.hypotheses c) M 0)
      (b.liftN (gp.hypotheses c).length)).ClosedN _
    have hbF : ((data.recursorInstance.singletonCast data.owner c (genericSorts env data c)).instL
        ls).fields.length = (gp.fieldsAt c).length := by
      simp [SingletonLayout.instL, Instance.singletonCast, hlF]
    rw [hbF, hlP] at hb
    rw [hlP] at hM ⊢
    apply ClosedN.wrapLams_closed
    · intro j hj
      simp only [VExpr.instDomains_length] at hj
      rw [VExpr.instDomains_getElem _ _ _ _ hj]
      have := hD j hj
      have h2 := VExpr.ClosedN.instN (k := gp.params.length) (j := j) (e2 := M)
        (by rw [show gp.params.length + j + 1 = gp.params.length + 1 + j by omega]; exact this) hM
      simpa using h2
    · simp only [VExpr.instDomains_length, List.length_append,
        InductiveSignature.Instance.length_insertBinders]
      have := hb.liftN (n := (gp.hypotheses c).length) (j := 0)
      simpa [Nat.add_assoc] using this

end InductiveSignature.RecursorData
end Lean4Lean
