import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ConstructorEnvironment

/-!
# Validity of the stripped-rule restoration environment

Restored recursor rules are validated in `stripRecursorRules outEnv names`,
which re-adds every restored recursor with an empty rule list.  This file
transports the checking invariant of the restored environment `outEnv` to
the stripped environment.  Stripping overwrites existing entries, so the
transport rests on an overwriting lemma for well-formed `SMap`s and on
the fact that replacing a kernel constant by one with the same name,
safety, universe parameters and type preserves `Aligned`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

/-! ### Overwriting entries of a well-formed `SMap` -/

/-- A key of a constant map can be overwritten without leaving
well-formedness: either the map is still in its first stage, or the key does
not live in the stage-one hash map. -/
def SMapOverwritable (s : ConstMap) (k : Name) : Prop :=
  s.stage₁ = true ∨ ¬ k ∈ s.map₁

theorem SMapOverwritable.insert {s : ConstMap} {k : Name}
    (h : SMapOverwritable s k) (m : Name) (v : ConstantInfo) :
    SMapOverwritable (s.insert m v) k := by
  rcases s with ⟨_ | _, m₁, m₂⟩
  · rcases h with h | h
    · cases h
    · exact Or.inr h
  · exact Or.inl rfl

theorem SMapOverwritable.of_find?_none {s : ConstMap} {k : Name}
    (h : s.find? k = none) : SMapOverwritable s k := by
  rcases s with ⟨_ | _, m₁, m₂⟩
  · right
    intro hk
    simp only [SMap.find?] at h
    cases e : m₂.find? k <;> rw [e] at h <;> simp at h
    exact h hk
  · exact Or.inl rfl

theorem _root_.Lean.SMap.WF.insert_of_overwritable {s : ConstMap} {k : Name}
    (h : s.WF) (ho : SMapOverwritable s k) (v : ConstantInfo) :
    (s.insert k v).WF := by
  rcases s with ⟨_ | _, m₁, m₂⟩
  · rcases ho with ho | ho
    · cases ho
    refine ⟨h.map₂.insert, nofun, fun {a} ha => ?_⟩
    change (m₂.insert k v).contains a = true at ha
    rw [PersistentHashMap.find?_isSome, h.map₂.find?_insert] at ha
    by_cases hka : k = a
    · subst hka
      exact ho
    · have hka' : (k == a) = false := by simpa using hka
      rw [hka'] at ha
      exact h.disjoint (by
        change m₂.contains a = true
        rw [PersistentHashMap.find?_isSome]
        exact ha)
  · refine ⟨h.map₂, h.stage, fun {a} ha => ?_⟩
    have hempty := h.stage rfl
    change m₂.contains a = true at ha
    simp only at hempty
    subst hempty
    rw [PersistentHashMap.find?_isSome, PersistentHashMap.WF.empty.find?_eq] at ha
    simp at ha

/-- Every key of a well-formed constant map can be updated, possibly by a
representation other than `SMap.insert`. -/
theorem _root_.Lean.SMap.WF.exists_update {s : ConstMap} (h : s.WF) (k : Name)
    (v : ConstantInfo) :
    ∃ s' : ConstMap, s'.WF ∧
      ∀ x, s'.find? x = if k == x then some v else s.find? x := by
  by_cases ho : SMapOverwritable s k
  · exact ⟨s.insert k v, h.insert_of_overwritable ho v, fun _ => h.find?_insert⟩
  rcases s with ⟨_ | _, m₁, m₂⟩
  · have hk : k ∈ m₁ := by
      simp only [SMapOverwritable, not_or, Bool.false_eq_true, not_false_eq_true,
        true_and, Decidable.not_not] at ho
      exact ho
    have hk₂ : m₂.find? k = none := by
      cases e : m₂.find? k
      · rfl
      · exact absurd hk (h.disjoint (by
          change m₂.contains k = true
          rw [PersistentHashMap.find?_isSome, e]
          rfl))
    refine ⟨⟨false, m₁.insert k v, m₂⟩, ⟨h.map₂, nofun, fun {a} ha hmem => ?_⟩, ?_⟩
    · rw [Std.HashMap.mem_insert] at hmem
      rcases hmem with hka | hmem
      · have hka' : k = a := by simpa using hka
        subst hka'
        change m₂.contains k = true at ha
        rw [PersistentHashMap.find?_isSome, hk₂] at ha
        cases ha
      · exact h.disjoint ha hmem
    · intro x
      simp only [SMap.find?]
      rw [Std.HashMap.getElem?_insert]
      by_cases hkx : k = x
      · subst hkx
        simp [hk₂]
      · have : (k == x) = false := by simpa using hkx
        simp [this]
  · exact absurd (Or.inl rfl) ho

/-! ### Replacing a constant by one with the same header -/

/-- Two kernel constants agree on everything `Aligned` observes: name,
safety, universe parameters and type. -/
structure SameConstantHeader (ci ci' : ConstantInfo) : Prop where
  name : ci.name = ci'.name
  safety : ci.safety = ci'.safety
  levelParams : ci.levelParams = ci'.levelParams
  type : ci.type = ci'.type

theorem TrConstant.ofSameHeader (H : TrConstant safety venv ci ci')
    (h : SameConstantHeader ci ci₂) : TrConstant safety venv ci₂ ci' := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h.safety ▸ h1, h.levelParams ▸ h2, ?_⟩
  rw [← h.levelParams, ← h.type]
  exact h3

/-- Every entry of an aligned constant map is stored under its own name. -/
theorem Aligned.keyed (H : Aligned safety C venv)
    (h : C.find? name = some ci) : ci.name = name := by
  induction H with
  | empty => simp at h
  | ignoreConst H₀ _ _ hname ih
  | const H₀ _ _ _ hname ih =>
    rw [H₀.map_wf.find?_insert] at h
    split at h
    · rename_i heq
      cases h
      rw [hname]
      simpa using heq
    · exact ih h
  | defeq _ ih => exact ih h
  | projections _ ih => exact ih h
  | eliminators _ ih => exact ih h
  | mapExt _ _ heq ih => exact ih (by rw [heq]; exact h)

private theorem find?_insert_eq_of_ne {C : ConstMap} (hwf : C.WF)
    {m y : Name} (hne : y ≠ m) (v : ConstantInfo) :
    (C.insert m v).find? y = C.find? y := by
  rw [hwf.find?_insert]
  have : (m == y) = false := by simpa using Ne.symm hne
  simp [this]

private theorem find?_insert_self {C : ConstMap} (hwf : C.WF)
    (m : Name) (v : ConstantInfo) : (C.insert m v).find? m = some v := by
  rw [hwf.find?_insert]
  simp

/-- `Aligned` is insensitive to replacing one entry by a constant with the
same header. -/
theorem Aligned.replaceHeader (H : Aligned safety C venv)
    (hfind : C.find? n = some ci) (hsame : SameConstantHeader ci ci₂)
    {C' : ConstMap} (hwf : C'.WF) (hn : C'.find? n = some ci₂)
    (hother : ∀ y, y ≠ n → C'.find? y = C.find? y) :
    Aligned safety C' venv := by
  induction H generalizing C' ci with
  | empty => simp at hfind
  | @ignoreConst C₀ venv₀ m ci₀ H₀ hm hs hname ih =>
    have hwf₀ := H₀.map_wf
    by_cases hmn : n = m
    · subst hmn
      rw [find?_insert_self hwf₀] at hfind
      cases hfind
      have hA : Aligned safety (C₀.insert n ci₂) venv₀ :=
        H₀.ignoreConst hm (by rw [← hsame.safety]; exact hs)
          (by rw [← hsame.name]; exact hname)
      refine hA.mapExt hwf fun y => ?_
      by_cases hy : y = n
      · subst hy; rw [find?_insert_self hwf₀, hn]
      · rw [find?_insert_eq_of_ne hwf₀ hy, hother y hy,
          find?_insert_eq_of_ne hwf₀ hy]
    · rw [find?_insert_eq_of_ne hwf₀ hmn] at hfind
      obtain ⟨D, hD, hDfind⟩ := hwf₀.exists_update n ci₂
      have hDn : D.find? n = some ci₂ := by rw [hDfind]; simp
      have hDo : ∀ y, y ≠ n → D.find? y = C₀.find? y := by
        intro y hy
        rw [hDfind]
        have : (n == y) = false := by simpa using Ne.symm hy
        simp [this]
      have hAD := ih hfind hsame hD hDn hDo
      have hDm : D.find? m = none := by rw [hDo m (Ne.symm hmn)]; exact hm
      refine (hAD.ignoreConst hDm hs hname).mapExt hwf fun y => ?_
      by_cases hym : y = m
      · subst hym
        rw [find?_insert_self hD, hother y (Ne.symm hmn), find?_insert_self hwf₀]
      · rw [find?_insert_eq_of_ne hD hym]
        by_cases hyn : y = n
        · subst hyn; rw [hDn, hn]
        · rw [hDo y hyn, hother y hyn, find?_insert_eq_of_ne hwf₀ hym]
  | @const C₀ venv₀ m ci₀ ci' venv₁ H₀ hm htr hadd hname ih =>
    have hwf₀ := H₀.map_wf
    by_cases hmn : n = m
    · subst hmn
      rw [find?_insert_self hwf₀] at hfind
      cases hfind
      have hA : Aligned safety (C₀.insert n ci₂) venv₁ :=
        H₀.const hm (htr.ofSameHeader hsame) hadd
          (by rw [← hsame.name]; exact hname)
      refine hA.mapExt hwf fun y => ?_
      by_cases hy : y = n
      · subst hy; rw [find?_insert_self hwf₀, hn]
      · rw [find?_insert_eq_of_ne hwf₀ hy, hother y hy,
          find?_insert_eq_of_ne hwf₀ hy]
    · rw [find?_insert_eq_of_ne hwf₀ hmn] at hfind
      obtain ⟨D, hD, hDfind⟩ := hwf₀.exists_update n ci₂
      have hDn : D.find? n = some ci₂ := by rw [hDfind]; simp
      have hDo : ∀ y, y ≠ n → D.find? y = C₀.find? y := by
        intro y hy
        rw [hDfind]
        have : (n == y) = false := by simpa using Ne.symm hy
        simp [this]
      have hAD := ih hfind hsame hD hDn hDo
      have hDm : D.find? m = none := by rw [hDo m (Ne.symm hmn)]; exact hm
      refine (hAD.const hDm htr hadd hname).mapExt hwf fun y => ?_
      by_cases hym : y = m
      · subst hym
        rw [find?_insert_self hD, hother y (Ne.symm hmn), find?_insert_self hwf₀]
      · rw [find?_insert_eq_of_ne hD hym]
        by_cases hyn : y = n
        · subst hyn; rw [hDn, hn]
        · rw [hDo y hyn, hother y hyn, find?_insert_eq_of_ne hwf₀ hym]
  | defeq _ ih => exact (ih hfind hsame hwf hn hother).defeq
  | projections _ ih => exact (ih hfind hsame hwf hn hother).projections
  | eliminators _ ih => exact (ih hfind hsame hwf hn hother).eliminators
  | mapExt _ _ heq ih =>
    exact ih (by rw [heq]; exact hfind) hsame hwf hn
      (fun y hy => by rw [hother y hy, heq])

/-! ### The lookups of the stripped environment -/

/-- The effect of stripping on one lookup: a recursor loses its rules, every
other lookup is unchanged. -/
def stripRulesOpt : Option ConstantInfo → Option ConstantInfo
  | some (.recInfo r) => some (.recInfo { r with rules := [] })
  | o => o

theorem stripRulesOpt_idem (o : Option ConstantInfo) :
    stripRulesOpt (stripRulesOpt o) = stripRulesOpt o := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> rfl

theorem stripRulesOpt_of_not_rec {o : Option ConstantInfo}
    (h : ∀ r, o ≠ some (.recInfo r)) : stripRulesOpt o = o := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | r⟩ <;> try rfl
  exact absurd rfl (h r)

theorem stripRulesOpt_eq_some {o : Option ConstantInfo}
    (h : stripRulesOpt o = some ci) :
    o = some ci ∨ ∃ r, o = some (.recInfo r) ∧ ci = .recInfo { r with rules := [] } := by
  rcases o with _ | ⟨ci₀⟩
  · cases h
  · cases ci₀ with
    | recInfo r => exact Or.inr ⟨r, rfl, (Option.some.inj h).symm⟩
    | _ => exact Or.inl h

theorem sameConstantHeader_stripRules (r : RecursorVal) :
    SameConstantHeader (.recInfo r) (.recInfo { r with rules := [] }) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem Kernel.Environment.find?_eq_constants {env : Environment}
    (hwf : env.constants.WF) (name : Name) :
    env.find? name = env.constants.find? name := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]

/-- One stripping step. -/
theorem stripRecursorRules_cons (env : Environment) (n : Name) (ns : List Name) :
    stripRecursorRules env (n :: ns) =
      stripRecursorRules (match env.find? n with
        | some (.recInfo info) => env.add (.recInfo { info with rules := [] })
        | _ => env) ns := rfl

/-- Specification of `stripRecursorRules` on an aligned environment
whose stripped names can be overwritten. -/
theorem stripRecursorRules_spec : ∀ (names : List Name) (env : Environment),
    Aligned safety env.constants venv →
    (∀ x ∈ names, SMapOverwritable env.constants x) →
    Aligned safety (stripRecursorRules env names).constants venv ∧
    (stripRecursorRules env names).quotInit = env.quotInit ∧
    ∀ x, (stripRecursorRules env names).constants.find? x =
      if x ∈ names then stripRulesOpt (env.constants.find? x)
      else env.constants.find? x
  | [], env, hal, _ => ⟨hal, rfl, fun x => by simp; rfl⟩
  | n :: ns, env, hal, hov => by
    have hwf := hal.map_wf
    have hstep : ∃ env', stripRecursorRules env (n :: ns) = stripRecursorRules env' ns ∧
        Aligned safety env'.constants venv ∧
        (∀ x ∈ ns, SMapOverwritable env'.constants x) ∧
        env'.quotInit = env.quotInit ∧
        ∀ x, env'.constants.find? x =
          if x = n then stripRulesOpt (env.constants.find? x)
          else env.constants.find? x := by
      rw [stripRecursorRules_cons]
      split
      · rename_i info hinfo
        rw [Kernel.Environment.find?_eq_constants hwf] at hinfo
        have hname : info.name = n := hal.keyed hinfo
        let ci₂ : ConstantInfo := .recInfo { info with rules := [] }
        have hkey : ci₂.name = n := hname
        have hov' : SMapOverwritable env.constants n := hov n (by simp)
        have hwf' : (env.constants.insert n ci₂).WF := hwf.insert_of_overwritable hov' ci₂
        refine ⟨_, rfl, ?_, ?_, rfl, ?_⟩
        · change Aligned safety (env.constants.insert ci₂.name ci₂) venv
          rw [hkey]
          refine hal.replaceHeader hinfo (sameConstantHeader_stripRules info) hwf'
            (find?_insert_self hwf n ci₂) fun y hy => find?_insert_eq_of_ne hwf hy ci₂
        · intro x hx
          exact (hov x (by simp [hx])).insert _ _
        · intro x
          change (env.constants.insert ci₂.name ci₂).find? x = _
          rw [hkey]
          by_cases hx : x = n
          · subst hx
            rw [find?_insert_self hwf, if_pos rfl, hinfo]
            rfl
          · rw [find?_insert_eq_of_ne hwf hx, if_neg hx]
      · rename_i hnot
        refine ⟨_, rfl, hal, fun x hx => hov x (by simp [hx]), rfl, ?_⟩
        intro x
        by_cases hx : x = n
        · subst hx
          rw [if_pos rfl, stripRulesOpt_of_not_rec]
          intro r hr
          rw [← Kernel.Environment.find?_eq_constants hwf] at hr
          exact hnot r hr
        · rw [if_neg hx]
    obtain ⟨env', heq, hal', hov', hq, hfind⟩ := hstep
    obtain ⟨hal'', hq', hfind'⟩ := stripRecursorRules_spec ns env' hal' hov'
    rw [heq]
    refine ⟨hal'', hq'.trans hq, fun x => ?_⟩
    rw [hfind', hfind x]
    by_cases hx : x = n
    · subst hx
      by_cases hxs : x ∈ ns
      · simp [hxs, stripRulesOpt_idem]
      · simp [hxs]
    · by_cases hxs : x ∈ ns
      · simp [hx, hxs]
      · simp [hx, hxs]

/-- Consequences of the lookup specification of a stripped constant map. -/
theorem stripLookup_cases {S O : ConstMap} {names : List Name}
    (hspec : ∀ x, S.find? x = if x ∈ names then stripRulesOpt (O.find? x) else O.find? x)
    (h : S.find? x = some ci) :
    O.find? x = some ci ∨ x ∈ names ∧
      ∃ r, O.find? x = some (.recInfo r) ∧ ci = .recInfo { r with rules := [] } := by
  rw [hspec] at h
  split at h
  · rcases stripRulesOpt_eq_some h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by assumption, h⟩
  · exact Or.inl h

theorem stripLookup_nonrec {S O : ConstMap} {names : List Name}
    (hspec : ∀ x, S.find? x = if x ∈ names then stripRulesOpt (O.find? x) else O.find? x)
    (h : O.find? x = some ci) (hci : ∀ r, ci ≠ .recInfo r) :
    S.find? x = some ci := by
  rw [hspec]
  split
  · rw [stripRulesOpt_of_not_rec, h]
    rw [h]
    intro r hr
    exact hci r (Option.some.inj hr)
  · exact h

theorem stripLookup_not_mem {S O : ConstMap} {names : List Name}
    (hspec : ∀ x, S.find? x = if x ∈ names then stripRulesOpt (O.find? x) else O.find? x)
    (hx : x ∉ names) : S.find? x = O.find? x := by
  rw [hspec, if_neg hx]

namespace VerifyInductive

/-! ### Restored recursor names are fresh -/

theorem FreshExtension.overwritable
    (H : FreshExtension env entries outEnv)
    (h : SMapOverwritable env.constants x) :
    SMapOverwritable outEnv.constants x := by
  induction H with
  | nil => exact h
  | cons _ _ ih => exact ih (h.insert _ _)

theorem SourceFamilyRestoration.freshExtensionWithRecursor
    (H : SourceFamilyRestoration result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv ∧
      ∃ e ∈ entries, e.name =
        auxRec.getD (Lean.mkRecName indType.name) (Lean.mkRecName indType.name) := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hwf H.header.fresh
  have hwfHeader := constantsWF_add_checked hwf hheaderFresh
  have Hconstructors' : FoldSteps
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors'.constructorFreshExtension hwfHeader with
    ⟨constructors, Hconstructors⟩
  have hwfConstructors : H.constructorEnv.constants.WF :=
    Hconstructors.targetWF hwfHeader
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hwfConstructors H.recursor.restored.fresh
  have hrecName : recursor.name =
      auxRec.getD (Lean.mkRecName indType.name) (Lean.mkRecName indType.name) :=
    H.recursor.restored.restoration.name.trans H.recursor.restored.mappedName
  rw [htarget]
  exact ⟨header :: constructors ++ [recursor],
    FreshExtension.cons hheaderFresh
      (Hconstructors.append (.cons hrecFresh .nil)),
    recursor, by simp, hrecName⟩

theorem FoldSteps.inductiveFreshExtensionWithRecursors
    (H : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv ∧
      ∀ t ∈ types, ∃ e ∈ entries, e.name =
        auxRec.getD (Lean.mkRecName t.name) (Lean.mkRecName t.name) := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep _Htail ih =>
    rcases Hstep.restored.freshExtensionWithRecursor hwf with
      ⟨headEntries, Hhead, e, he, hname⟩
    rcases ih (Hhead.targetWF hwf) with ⟨tailEntries, Htail, htail⟩
    refine ⟨headEntries ++ tailEntries, Hhead.append Htail, ?_⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨e, by simp [he], hname⟩
    · rcases htail t ht with ⟨e', he', hname'⟩
      exact ⟨e', by simp [he'], hname'⟩

theorem FoldSteps.recursorFreshExtensionWithNames
    (H : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv ∧
      ∀ n ∈ names, ∃ e ∈ entries, e.name = auxRec.getD n n := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries, hnames⟩
    have hname : ci.name = _ :=
      Hstep.restored.restoration.name.trans Hstep.restored.mappedName
    refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
    intro n hn
    simp only [List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact ⟨ci, by simp, hname⟩
    · rcases hnames n hn with ⟨e, he, hname'⟩
      exact ⟨e, by simp [he], hname'⟩

/-- Every restored recursor name is fresh in the source environment. -/
theorem NestedRestorationFolds.restoredRecursorNamesFresh
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (hwf : sourceEnv.constants.WF)
    (hx : x ∈ Lean4Lean.restoredRecursorNames auxRec types auxRecNames) :
    sourceEnv.find? x = none := by
  rcases H.inductives.inductiveFreshExtensionWithRecursors hwf with
    ⟨primaryEntries, Hprimary, hprimary⟩
  rcases H.auxiliaries.recursorFreshExtensionWithNames (Hprimary.targetWF hwf) with
    ⟨auxiliaryEntries, Hauxiliary, hauxiliary⟩
  have Htrace := Hprimary.append Hauxiliary
  simp only [Lean4Lean.restoredRecursorNames, List.map_append, List.map_map,
    List.mem_append, List.mem_map, Function.comp_def] at hx
  rcases hx with ⟨t, ht, rfl⟩ | ⟨n, hn, rfl⟩
  · rcases hprimary t ht with ⟨e, he, hname⟩
    rw [← hname]
    exact Htrace.sourceFresh hwf (by simp [he])
  · rcases hauxiliary n hn with ⟨e, he, hname⟩
    rw [← hname]
    exact Htrace.sourceFresh hwf (by simp [he])

/-! ### Validity of the stripped environment -/

/-- The stripped-rule restoration environment satisfies the full checking
invariant against the installed environment `installedVEnv` of the block
installation `canonical`, given the alignment of
every new visible recursor of the stripped map.  The local invariants,
constructor owners and projection registry are transported from
`localValidOfInstallation`; base recursors and the quotient facts come from the
source environment, since every stripped name is fresh there. -/
theorem NestedRestorationFolds.validOfInstallation_of_shapes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv))
    (Hactual : FreshExtension c.env actualEntries outEnv)
    (canonical : BlockInstallation c.safety c.env sourceVEnv types ctors recursors
      sourceDecl.projectionEntries canonicalProdEnv installedVEnv)
    (hperm : actualEntries ~ (types ++ ctors ++ recursors).map Prod.fst)
    (htypeValues : types.map Prod.snd = sourceDecl.typeConstants)
    (hctorValues : ctors.map Prod.snd = sourceDecl.constructorConstants)
    (hvalidSource : CheckingEnv.Valid c.safety c.env sourceVEnv)
    (Hshapes : ∀ name rec,
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames auxRec sourceTypes auxRecNames)).constants.find?
          name = some (.recInfo rec) →
      c.env.constants.find? name = none →
      RecursorAlignmentCore installedVEnv rec ∧
      KLikeRecursor (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames auxRec sourceTypes auxRecNames)).constants
        installedVEnv rec ∧
      ∃ info, (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames auxRec sourceTypes auxRecNames)).constants.find?
          rec.getMajorInduct = some (.inductInfo info))
    (htels : CtorTelescopes c.safety outEnv installedVEnv) :
    CheckingEnv.Valid c.safety
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames auxRec sourceTypes auxRecNames))
      installedVEnv := by
  obtain ⟨hcore, howners, horigins⟩ :=
    Hrestored.localValidOfInstallation Hlower Hc Hprod Hsource Hmetadata Hsources
      Harity hempty Hactual canonical hperm hvalidSource
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  have houtWF : outEnv.constants.WF := hcore.tr.map_wf
  generalize hnames : Lean4Lean.restoredRecursorNames auxRec sourceTypes auxRecNames = names
    at Hshapes ⊢
  have hfresh : ∀ x ∈ names, c.env.constants.find? x = none := by
    intro x hx
    rw [← hnames] at hx
    have := Hrestored.restoredRecursorNamesFresh hsourceWF hx
    rwa [Kernel.Environment.find?_eq_constants hsourceWF] at this
  have hov : ∀ x ∈ names, SMapOverwritable outEnv.constants x := fun x hx =>
    Hactual.overwritable (SMapOverwritable.of_find?_none (hfresh x hx))
  obtain ⟨hSal, hSquot, hspec⟩ :=
    stripRecursorRules_spec names outEnv hcore.tr.aligned hov
  generalize Lean4Lean.stripRecursorRules outEnv names = S at Hshapes hSal hSquot hspec ⊢
  have hSwf : S.constants.WF := hSal.map_wf
  have hfindS : ∀ x, S.find? x = S.constants.find? x :=
    Kernel.Environment.find?_eq_constants hSwf
  have hfindO : ∀ x, outEnv.find? x = outEnv.constants.find? x :=
    Kernel.Environment.find?_eq_constants houtWF
  have hcasesE : ∀ {x ci}, S.find? x = some ci →
      outEnv.find? x = some ci ∨
        ∃ r, outEnv.find? x = some (.recInfo r) ∧
          ci = .recInfo { r with rules := [] } := by
    intro x ci h
    rw [hfindS] at h
    rw [hfindO]
    rcases stripLookup_cases hspec h with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hnonrecE : ∀ {x ci}, outEnv.find? x = some ci → (∀ r, ci ≠ .recInfo r) →
      S.find? x = some ci := by
    intro x ci h hci
    rw [hfindS]
    rw [hfindO] at h
    exact stripLookup_nonrec hspec h hci
  have hpres : ∀ {n ci}, c.env.constants.find? n = some ci →
      S.constants.find? n = some ci := by
    intro n ci h
    have hn : n ∉ names := fun hn => by rw [hfresh n hn] at h; cases h
    rw [stripLookup_not_mem hspec hn]
    exact Hactual.preservesSourceMapFind hsourceWF h
  have hvalidCore : CheckingEnv.ValidCore c.safety S installedVEnv := {
    tr := {
      aligned := hSal
      wf := hcore.tr.wf
      of_value := by
        intro name ci v hfind hs hv
        rcases hcasesE hfind with h | ⟨r, _, rfl⟩
        · exact hcore.tr.of_value h hs hv
        · cases hv }
    hasPrimitives := hcore.hasPrimitives
    safePrimitives := by
      intro n ci hfind hprim
      rcases hcasesE hfind with h | ⟨r, h, rfl⟩
      · exact hcore.safePrimitives h hprim
      · have := hcore.safePrimitives h hprim
        exact this }
  have howners' : ConstructorOwnersPresent S := by
    intro name info h
    rcases hcasesE h with h | ⟨r, _, hr⟩
    · rcases howners name info h with ⟨owner, ho, hrest⟩
      exact ⟨owner, hnonrecE ho (fun _ h => by cases h), hrest⟩
    · cases hr
  have hrecursors : RecursorEnvCoherent c.safety S.constants installedVEnv := by
    refine hvalidSource.recursors.extend hpres ?_ canonical.le
      (fun df hdf => Or.inl (canonical.defeqs df hdf))
    intro n rec hfind hs
    cases hc : c.env.constants.find? n with
    | none => exact Or.inr (Hshapes n rec hfind hc)
    | some ci =>
      have h := hpres hc
      rw [hfind] at h
      cases h
      exact Or.inl rfl
  have hquot : S.quotInit = true → QuotEnvCoherent S.constants installedVEnv := by
    intro hq
    rw [hSquot, Hactual.quotInit_eq] at hq
    exact (hvalidSource.quot hq).extend hpres canonical.le hrecursors.heads
  have hpresEnv : ∀ {n ci}, c.env.find? n = some ci → S.find? n = some ci := by
    intro n ci h
    rw [hfindS]
    exact hpres (by rwa [Kernel.Environment.find?_eq_constants hsourceWF] at h)
  have horiginsS : InductInfosFromDecl c.env.constants S.constants sourceDecl :=
    horigins.transfer
      (fun h => by
        rcases stripLookup_cases hspec h with h | ⟨_, _, _, h⟩
        · exact h
        · cases h)
      (fun h => stripLookup_nonrec hspec h nofun)
      (fun h => stripLookup_nonrec hspec h nofun)
  have htypesAdded : sourceVEnv.addConstVals sourceDecl.typeConstants =
      some canonical.venvTypes := by
    rw [← htypeValues]; exact canonical.abstract_types
  have hctorsAdded : canonical.venvTypes.addConstVals sourceDecl.constructorConstants =
      some canonical.venvCtors := by
    rw [← hctorValues]; exact canonical.abstract_ctors
  have hctorsLE : canonical.venvCtors ≤ installedVEnv :=
    VEnv.addEliminators_addProjections_le.trans (VEnv.addConstVals_le canonical.abstract_recursors)
  have hreg : InstalledBlocks.DeclRegistered installedVEnv sourceDecl canonical.eliminators := {
    typeUvars := by
      intro type htype
      rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types type htype with
        ⟨_, _, Htype⟩
      rw [Htype.header.uvars, Hsource.uvars]
    constructorUvars := Lean4Lean.VerifyInductive.TrInductDeclCore.constructorUvars Hsource
    family := fun i hi => ((VEnv.addConstVals_le hctorsAdded).trans hctorsLE).constants
      (VEnv.addConstVals_get htypesAdded
        (List.mem_map.mpr ⟨sourceDecl.types[i], List.getElem_mem hi, rfl⟩))
    ctor := fun i k hi hk => hctorsLE.constants
      (VEnv.addConstVals_get hctorsAdded (by
        simp only [VInductDecl.constructorConstants, List.mem_flatMap]
        exact ⟨_, List.getElem_mem hi, List.getElem_mem hk⟩))
    projections := fun e he => (VEnv.addConstVals_le canonical.abstract_recursors).projections
      (VEnv.addProjections_iff.mpr (.inl ⟨e, he, rfl, rfl⟩))
    eliminators := fun e he => (VEnv.addConstVals_le canonical.abstract_recursors).eliminators
      (VEnv.addProjections_le.eliminators (VEnv.addEliminators_iff.mpr (.inl he))) }
  have hblocks : InstalledBlocks c.safety S installedVEnv .headers := by
    refine hvalidSource.blocks.addCtorStage Hheaders.sourcePresent hsourceWF hvalidCore.tr
      hpresEnv canonical.le horiginsS ?_ ?_ howners' (InstalledBlocks.newRecursors c.env S)
      (fun hf hnone => (InstalledBlocks.mem_newRecursors hSwf).mpr ⟨_, hf, hnone⟩) ?_ ?_ ?_
      canonical.eliminators hreg ?_
      (htels.ofCtors fun h => by
        rcases hcasesE h with h | ⟨r, _, he⟩
        · exact h
        · cases he)
    · intro T hT
      obtain ⟨v, hv, hnone⟩ := Hrestored.cover Hlower Hc Hprod Hsource Hmetadata Hsources Harity
        Hc.checking.constructorOwners hempty T hT
      refine ⟨v, ?_, hnone⟩
      rw [hfindS]
      exact stripLookup_nonrec hspec (by rwa [← hfindO]) nofun
    · have := VEnv.addConstVals_names_nodup htypesAdded
      simpa [VInductDecl.typeConstants, Function.comp_def] using this
    · intro r hr
      obtain ⟨n, h1, h2⟩ := (InstalledBlocks.mem_newRecursors hSwf).mp hr
      have hn : r.name = n := hvalidCore.tr.find?_name h1
      rw [hn]; exact ⟨h1, h2⟩
    · intro r hr
      obtain ⟨n, h1, h2⟩ := (InstalledBlocks.mem_newRecursors hSwf).mp hr
      obtain ⟨-, -, info, hmajor⟩ := Hshapes n r (by rwa [← hfindS])
        (by rwa [Kernel.Environment.find?_eq_constants hsourceWF] at h2)
      exact ⟨info, by rw [hfindS]; exact hmajor⟩
    · intro r hr _
      obtain ⟨n, h1, h2⟩ := (InstalledBlocks.mem_newRecursors hSwf).mp hr
      obtain ⟨hcore', hk, -⟩ := Hshapes n r (by rwa [← hfindS])
        (by rwa [Kernel.Environment.find?_eq_constants hsourceWF] at h2)
      exact ⟨hcore', hk⟩
    · intro S' info hp
      rw [VEnv.addConstVals_projections canonical.abstract_recursors] at hp
      rcases VEnv.addProjections_iff.mp hp with ⟨e, he, rfl, rfl⟩ | hold
      · exact .inr he
      · left
        rw [VEnv.addEliminators_projections, VEnv.addConstVals_projections hctorsAdded,
          VEnv.addConstVals_projections htypesAdded] at hold
        exact hold
  exact hvalidCore.toValid hblocks hrecursors.heads hquot

end VerifyInductive
end Lean4Lean
