import Lean4Lean.Theory.Inductive.CaseRuleConstructors

/-! Exact universe spines of restored heads (`Restoration.headLevels`). -/

namespace Lean4Lean.InductiveSignature

/-- The universe substitution belonging to a restored head, independently
of its term-parameter specialization. -/
def Restoration.headLevels (r : Restoration) (name : Name) (levels : List VLevel) : List VLevel :=
  match r.heads.find? (fun h => h.auxiliary == name) with
  | some h => h.levels.map (·.inst levels)
  | none => levels

theorem Restoration.const_spine_exact {r : Restoration} {output : VExpr}
    (h : Restoration.expr.go r (.const name levels) args = some output) :
    ∃ args', output = VExpr.mkApps
      (.const (r.headName name) (r.headLevels name levels)) args' := by
  unfold Restoration.expr.go at h
  unfold headName headLevels
  split at h
  · rename_i spec hspec
    rw [hspec]
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · cases h
      exact ⟨_, rfl⟩
  · rename_i hspec
    rw [hspec]
    cases h
    exact ⟨_, rfl⟩

theorem Restoration.const_mkApps_exact {r : Restoration} {output : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) args) = some output) :
    ∃ args', output = VExpr.mkApps
      (.const (r.headName name) (r.headLevels name levels)) args' := by
  change Restoration.expr.go r (VExpr.mkApps (.const name levels) args) [] = _ at h
  rw [restoration_mkApps] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨args', _, h⟩ := h
  exact r.const_spine_exact h

theorem Restoration.headLevels_of_mem {r : Restoration} (hr : r.Scoped)
    (hmem : spec ∈ r.heads) :
    r.headLevels spec.auxiliary levels = spec.levels.map (·.inst levels) := by
  unfold headLevels
  cases hf : r.heads.find? (fun h => h.auxiliary == spec.auxiliary) with
  | none =>
    have hfalse := List.find?_eq_none.mp hf spec hmem
    simp at hfalse
  | some found =>
    have hfound := List.mem_of_find?_eq_some hf
    have hname : found.auxiliary = spec.auxiliary := by simpa using List.find?_some hf
    have heq := List.eq_of_mem_of_nodup_map hr.1 hfound hmem hname
    cases heq
    rfl

theorem CaseCompilationData.headLevels_source
    {s : InductiveSignature} (H : CaseCompilationData env source expanded s auxiliaries block)
    (hname : name ∈ familyNames source.types) :
    (compilationRestoration source auxiliaries).headLevels name levels = levels := by
  unfold Restoration.headLevels
  cases hf : (compilationRestoration source auxiliaries).heads.find?
      (fun h => h.auxiliary == name) with
  | some found =>
    have hm := List.mem_of_find?_eq_some hf
    have hn : found.auxiliary = name := by simpa using List.find?_some hf
    exact (H.source_head_disjoint hname (List.mem_map.mpr ⟨found, hm, hn⟩)).elim
  | none => rfl

end Lean4Lean.InductiveSignature
