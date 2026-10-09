import Lean4Lean.Theory.Typing.SingletonExtraction.Basic

/-! # Scoping of singleton extraction

The cast telescope, the motives, branches and extraction functions are closed whenever the
cast specification is scoped and the eliminator's heads are closed. Purely syntactic; no
typing and no canonical `Eq` are needed. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr

theorem VExpr.ClosedN.instOuter_closed {X : VExpr} {args : List VExpr} {m : Nat}
    (hX : X.ClosedN args.length) (ha : ∀ a ∈ args, a.ClosedN m) : (X.instOuter args).ClosedN m := by
  rw [VExpr.instOuter_eq_subst]
  apply VExpr.ClosedN.subst_closed hX
  intro i hi
  rw [VExpr.Subst.ofList_lt _ hi]
  exact ha _ (List.getElem_mem _)

theorem bvarRange_closed {n t m : Nat} (h : t ≤ m) (hn : n ≤ t) :
    ∀ a ∈ bvarRange n t, a.ClosedN m := by
  intro a ha
  simp only [bvarRange, List.mem_map, List.mem_range] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  show _ < _
  omega

theorem closed_getD {l : List VExpr} (h : ∀ a ∈ l, a.ClosedN m) (i : Nat) :
    (l.getD i default).ClosedN m := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[i]? with
  | none => exact trivial
  | some a => exact h a (List.mem_of_getElem? hl)

theorem closed_map_liftN {l : List VExpr} (h : ∀ a ∈ l, a.ClosedN m) (r : Nat) :
    ∀ a ∈ l.map (·.liftN r), a.ClosedN (m + r) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  exact (h b hb).liftN

theorem VExpr.ClosedN.eqApp_closed (hα : α.ClosedN m) (ha : a.ClosedN m) (hb : b.ClosedN m) :
    (VExpr.eqApp w α a b).ClosedN m := ⟨⟨⟨trivial, hα⟩, ha⟩, hb⟩

theorem VExpr.ClosedN.typeCast_closed (hX : X.ClosedN m) (hY : Y.ClosedN m) (he : e.ClosedN m)
    (hx : x.ClosedN m) : (VExpr.typeCast u X Y e x).ClosedN m := by
  unfold VExpr.typeCast VExpr.eqRecApp VExpr.castMotive
  refine ⟨⟨⟨⟨⟨⟨trivial, trivial⟩, hX⟩, ⟨trivial, ?_, ?_⟩⟩, hx⟩, hY⟩, he⟩
  · exact VExpr.ClosedN.eqApp_closed trivial hX.liftN (by show 0 < m + 1; omega)
  · show 1 < m + 1 + 1; omega

namespace SingletonLayout
variable (S : SingletonLayout)

theorem tel_closed (hS : S.Scoped pa.length) (hial : ia.length = S.indices.length)
    (hpa : ∀ a ∈ pa, a.ClosedN n) (hia : ∀ a ∈ ia, a.ClosedN n) :
    ∀ i, (∀ l (h : l < (S.tel pa ia i).1.length), ((S.tel pa ia i).1[l]).ClosedN (n + l)) ∧
      ∀ a ∈ (S.tel pa ia i).2, a.ClosedN (n + i)
  | 0 => ⟨by simp [tel], by simp [tel]⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := tel_closed hS hial hpa hia i
    have hl := S.tel_length pa ia i
    generalize hT : S.tel pa ia i = T at h1 h2 hl
    obtain ⟨doms, σ⟩ := T
    simp only at h1 h2 hl
    have hargs : ∀ a ∈ pa.map (·.liftN i) ++ σ, a.ClosedN (n + i) := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact closed_map_liftN hpa i a ha
      · exact h2 a ha
    have hY : ((S.fields.getD i default).instOuter (pa.map (·.liftN i) ++ σ)).ClosedN (n + i) :=
      VExpr.ClosedN.instOuter_closed (by simpa [hl.2] using hS.fields_getD i) hargs
    have hstep : (S.step pa ia i σ).1.ClosedN (n + i) ∧ (S.step pa ia i σ).2.ClosedN (n + i + 1) := by
      simp only [step]
      split
      · rename_i k hk
        have hkl := hS.slot_lt i k hk
        have hX : ((S.indices.getD k default).instOuter
            (pa.map (·.liftN i) ++ (ia.take k).map (·.liftN i))).ClosedN (n + i) := by
          apply VExpr.ClosedN.instOuter_closed
          · simpa [Nat.min_eq_left (show k ≤ ia.length by omega)] using hS.indices_getD k
          · intro a ha
            rcases List.mem_append.1 ha with ha | ha
            · exact closed_map_liftN hpa i a ha
            · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
              exact (hia b (List.mem_of_mem_take hb)).liftN
        refine ⟨VExpr.ClosedN.eqApp_closed trivial hX hY, ?_⟩
        exact VExpr.ClosedN.typeCast_closed (hX.liftN.mono (by omega)) (hY.liftN.mono (by omega))
          (by show 0 < n + i + 1; omega)
          (by have := (closed_getD hia k).liftN (n := i + 1) (j := 0); simpa [Nat.add_assoc] using this)
      · exact ⟨hY, by show 0 < n + i + 1; omega⟩
    simp only [tel, hT]
    refine ⟨?_, ?_⟩
    · intro l hlt
      by_cases hli : l < doms.length
      · rw [List.getElem_append_left hli]; exact h1 l hli
      · have : l = doms.length := by simp at hlt; omega
        subst this
        rw [List.getElem_append_right (Nat.le_refl _)]
        simpa [hl.1] using hstep.1
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
        exact (h2 b hb).liftN
      · simp at ha; subst ha; exact hstep.2

theorem target_closed (hS : S.Scoped pa.length) (hial : ia.length = S.indices.length)
    (hpa : ∀ a ∈ pa, a.ClosedN n) (hia : ∀ a ∈ ia, a.ClosedN n) (j : Nat) :
    (S.target pa ia j).ClosedN (n + j) := by
  apply VExpr.ClosedN.instOuter_closed
  · simpa [(S.tel_length pa ia j).2] using hS.fields_getD j
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact closed_map_liftN hpa j a ha
    · exact (S.tel_closed hS hial hpa hia j).2 a ha

end SingletonLayout

namespace PropElim
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- Scoping of an elimination: closed heads, scoped constructor indices, and minor premises
of closed motives and branches are closed. -/
structure Closed (S : SingletonLayout) (params : List VExpr) (E : PropElim) : Prop where
  scope : S.Scoped params.length
  params_closed : ∀ j (h : j < params.length), (params[j]).ClosedN j
  family : E.family.ClosedN 0
  elimHead : E.elimHead.ClosedN 0
  ctorIndices : ∀ e ∈ E.ctorIndices, e.ClosedN (params.length + S.fields.length)
  ctorIndices_length : E.ctorIndices.length = S.indices.length
  minorOf : ∀ M b, M.ClosedN params.length → b.ClosedN (params.length + S.fields.length) →
    (E.minorOf M b).ClosedN params.length

theorem value_closed (hC : Closed S params E) {j : Nat} (hj : j < S.fields.length) :
    (value S params E j).ClosedN 0 := by
  have hmaj : (majorTy S params E).ClosedN (params.length + S.indices.length) := by
    apply ClosedN.mkApps_closed (hC.family.mono (Nat.zero_le _))
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact bvarRange_closed (Nat.le_refl _) (by omega) a ha
    · exact bvarRange_closed (by omega) (Nat.le_refl _) a ha
  have hpa : ∀ a ∈ genericPa S params, a.ClosedN (params.length + S.indices.length + 1) :=
    bvarRange_closed (Nat.le_refl _) (by omega)
  have hia : ∀ a ∈ genericIa S, a.ClosedN (params.length + S.indices.length + 1) :=
    bvarRange_closed (by omega) (by omega)
  have hscG : S.Scoped (genericPa S params).length := by
    simpa [genericPa] using hC.scope
  have hmot : (motive S params E j).ClosedN params.length := by
    apply ClosedN.wrapLams_closed
    · intro i hi
      by_cases hiI : i < S.indices.length
      · rw [List.getElem_append_left hiI]; exact hC.scope.indices i hiI
      · have : i = S.indices.length := by simp at hi; omega
        subst this
        rw [List.getElem_append_right (Nat.le_refl _)]
        simpa using hmaj
    · apply ClosedN.wrapForalls_closed
      · intro l hl
        have := (S.tel_closed hscG (by simp [genericIa]) hpa hia j).1 l hl
        simpa [Nat.add_assoc] using this
      · have := S.target_closed hscG (by simp [genericIa]) hpa hia j
        simpa [(S.tel_length _ _ j).1, Nat.add_assoc] using this
  have hbr : (branch S params E j).ClosedN (params.length + S.fields.length) := by
    apply ClosedN.wrapLams_closed
    · intro l hl
      have := (S.tel_closed (n := params.length + S.fields.length)
        (by simpa [branchPa] using hC.scope) (by simp [hC.ctorIndices_length])
        (bvarRange_closed (Nat.le_refl _) (by omega)) hC.ctorIndices j).1 l hl
      exact this
    · show _ < _
      simp [(S.tel_length _ _ j).1]
      omega
  apply ClosedN.wrapLams_closed
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hiP : i < params.length
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hiP]
      simpa using hC.params_closed i hiP
    · by_cases hiI : i < params.length + S.indices.length
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
        have := hC.scope.indices (i - params.length) (by omega)
        simpa [show params.length + (i - params.length) = i by omega] using this
      · have : i = params.length + S.indices.length := by omega
        subst this
        rw [List.getElem_append_right (by simp)]
        simpa using hmaj
  · simp only [List.length_append, List.length_singleton, Nat.zero_add]
    apply ClosedN.mkApps_closed (hC.elimHead.mono (Nat.zero_le _))
    intro a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with (ha | ha | ha) | ha
    · exact hpa a ha
    · subst ha; exact hmot.liftN
    · subst ha; exact (hC.minorOf _ _ hmot hbr).liftN
    · exact bvarRange_closed (by omega) (Nat.le_refl _) a ha

/-- The reconstruction commutes with substitution of the occurrence, given closedness of the
extraction functions it actually uses. -/
theorem occ_subst (hC : Closed S params E) (hsc : S.Scoped ps.length)
    (hidxl : idx.length = S.indices.length) (τ : VExpr.Subst) :
    ∀ i, i ≤ S.fields.length →
      (occ S params E ps idx m i).1.map (·.subst τ) =
        (occ S params E (ps.map (·.subst τ)) (idx.map (·.subst τ)) (m.subst τ) i).1 ∧
      (occ S params E ps idx m i).2.map (·.subst τ) =
        (occ S params E (ps.map (·.subst τ)) (idx.map (·.subst τ)) (m.subst τ) i).2 := by
  intro i
  induction i with
  | zero => intro _; simp [occ]
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hi)
    simp only [occ]
    split
    · rename_i k hs
      have hk := hsc.slot_lt i k hs
      have hX := VExpr.instOuter_subst_closed (S.indices.getD k default) (ps ++ idx.take k)
        (by simpa [hidxl, Nat.min_eq_left (Nat.le_of_lt hk)] using hsc.indices_getD k) τ
      simp only [List.map_append, List.map_cons, List.map_nil, ih1, ih2, VExpr.eqReflApp,
        VExpr.subst_app, VExpr.subst_const, VExpr.subst_sort, hX, List.map_take]
      refine ⟨by first | trivial | rfl, ?_⟩
      congr 2
      simp [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases idx[k]? <;> rfl
    · simp only [List.map_append, List.map_cons, List.map_nil, ih1, ih2, VExpr.subst_mkApps,
        (value_closed hC (j := i) hi).subst_eq .zero]
      exact ⟨by first | trivial | rfl, by first | trivial | rfl⟩

end PropElim
end Lean4Lean
