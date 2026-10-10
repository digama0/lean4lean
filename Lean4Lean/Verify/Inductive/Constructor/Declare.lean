import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Environment.Checker

/-! # Constructor installation: `declareConstructors`

`AddInductive.declareConstructors` adds the kernel constructors of the block, family by family,
one checked name at a time. Its effect on the constant map is the insertion of the block's
constructor infos (`ctorInfos`), all fresh and with distinct names
(`AddInductive.declareConstructors.WF`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The kernel constructors of one family, from position `k` on. -/
def ctorInfosFrom (stats : AddInductive.InductiveStats) (lparams : List Name) (isUnsafe : Bool)
    (t : InductiveType) : Nat → List Constructor → List ConstructorVal
  | _, [] => []
  | k, ctor :: ctors => AddInductive.constructorInfo stats lparams isUnsafe t k ctor ::
      ctorInfosFrom stats lparams isUnsafe t (k + 1) ctors

/-- The kernel constructors of one family. -/
def familyCtorInfos (stats : AddInductive.InductiveStats) (lparams : List Name) (isUnsafe : Bool)
    (t : InductiveType) : List ConstructorVal :=
  ctorInfosFrom stats lparams isUnsafe t 0 t.ctors

/-- The kernel constructors of the block, in block order. -/
def ctorInfos (stats : AddInductive.InductiveStats) (lparams : List Name) (isUnsafe : Bool)
    (indTypes : List InductiveType) : List ConstructorVal :=
  indTypes.flatMap (familyCtorInfos stats lparams isUnsafe)

theorem ctorInfosFrom_length : ∀ (k : Nat) (ctors : List Constructor),
    (ctorInfosFrom stats lparams isUnsafe t k ctors).length = ctors.length
  | _, [] => rfl
  | k, _ :: ctors => by simp [ctorInfosFrom, ctorInfosFrom_length (k + 1) ctors]

theorem ctorInfosFrom_getElem : ∀ (k : Nat) (ctors : List Constructor) (i : Nat)
    (hi : i < (ctorInfosFrom stats lparams isUnsafe t k ctors).length),
    (ctorInfosFrom stats lparams isUnsafe t k ctors)[i] =
      AddInductive.constructorInfo stats lparams isUnsafe t (k + i)
        (ctors[i]'(by simpa [ctorInfosFrom_length] using hi))
  | _, [], _, hi => by simp [ctorInfosFrom] at hi
  | k, ctor :: ctors, 0, _ => rfl
  | k, ctor :: ctors, i + 1, hi => by
    simp only [ctorInfosFrom, List.getElem_cons_succ]
    rw [ctorInfosFrom_getElem (k + 1) ctors i]
    simp [Nat.add_assoc, Nat.add_comm 1 i]

theorem familyCtorInfos_length :
    (familyCtorInfos stats lparams isUnsafe t).length = t.ctors.length :=
  ctorInfosFrom_length 0 t.ctors

theorem familyCtorInfos_getElem (i : Nat) (hi : i < (familyCtorInfos stats lparams isUnsafe t).length) :
    (familyCtorInfos stats lparams isUnsafe t)[i] =
      AddInductive.constructorInfo stats lparams isUnsafe t i
        (t.ctors[i]'(by simpa [familyCtorInfos_length] using hi)) := by
  have := ctorInfosFrom_getElem (stats := stats) (lparams := lparams) (isUnsafe := isUnsafe)
    (t := t) 0 t.ctors i hi
  simp only [Nat.zero_add] at this
  exact this

theorem mem_ctorInfosFrom : ∀ {k : Nat} {ctors : List Constructor} {cval : ConstructorVal},
    cval ∈ ctorInfosFrom stats lparams isUnsafe t k ctors →
    ∃ i, ∃ ctor ∈ ctors, cval = AddInductive.constructorInfo stats lparams isUnsafe t i ctor
  | _, [], _, h => by simp [ctorInfosFrom] at h
  | k, ctor :: ctors, cval, h => by
    simp only [ctorInfosFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨k, ctor, List.mem_cons_self, rfl⟩
    · obtain ⟨i, c, hc, rfl⟩ := mem_ctorInfosFrom h
      exact ⟨i, c, List.mem_cons_of_mem _ hc, rfl⟩

theorem mem_ctorInfos {cval : ConstructorVal}
    (h : cval ∈ ctorInfos stats lparams isUnsafe indTypes) :
    ∃ t ∈ indTypes, ∃ i, ∃ ctor ∈ t.ctors,
      cval = AddInductive.constructorInfo stats lparams isUnsafe t i ctor := by
  obtain ⟨t, ht, h⟩ := List.mem_flatMap.mp h
  obtain ⟨i, ctor, hctor, rfl⟩ := mem_ctorInfosFrom h
  exact ⟨t, ht, i, ctor, hctor, rfl⟩

theorem ctorInfosFrom_names : ∀ (k : Nat) (ctors : List Constructor),
    (ctorInfosFrom stats lparams isUnsafe t k ctors).map (·.name) = ctors.map (·.name)
  | _, [] => rfl
  | k, _ :: ctors => by
    simp only [ctorInfosFrom, List.map_cons, ctorInfosFrom_names (k + 1) ctors]
    rfl

theorem ctorInfos_names :
    (ctorInfos stats lparams isUnsafe indTypes).map (·.name) =
      indTypes.flatMap fun t => t.ctors.map (·.name) := by
  simp only [ctorInfos, List.map_flatMap, familyCtorInfos]
  congr 1; funext t; exact ctorInfosFrom_names 0 t.ctors

/-- A name absent after inserting a fresh constant was absent before and differs from it. -/
private theorem find?_add_none {E : Environment} (hwf : E.constants.WF) {ci : ConstantInfo}
    (hfresh : E.find? ci.name = none) {n : Name} (h : (E.add ci).find? n = none) :
    E.find? n = none ∧ n ≠ ci.name := by
  have hnone : E.constants.find? ci.name = none := by
    rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  have hwf' := hwf.insert ci.name ci hnone
  change SMap.find?' (E.constants.insert ci.name ci) n = none at h
  rw [hwf'.find?'_eq_find?, hwf.find?_insert] at h
  split at h
  · cases h
  · rename_i hne
    refine ⟨by rwa [Kernel.Environment.find?, hwf.find?'_eq_find?], fun he => hne ?_⟩
    simp [he]

/-- What the constructor fold of one family establishes. -/
theorem declareFamilyFold (stats : AddInductive.InductiveStats) (lparams : List Name)
    (isUnsafe allow : Bool) (t : InductiveType) :
    ∀ (ctors : List Constructor) (k : Nat) (E : Environment) (r : Nat × Environment),
    E.constants.WF →
    List.foldlM (m := Except Exception) (fun (x : Nat × Environment) ctor => do
        Kernel.Environment.checkName x.2 ctor.name allow
        pure (x.1 + 1, AddInductive.addConstant x.2 (.ctorInfo
          (AddInductive.constructorInfo stats lparams isUnsafe t x.1 ctor)))) (k, E) ctors =
      .ok r →
    r.2.constants = insertConsts E.constants
      ((ctorInfosFrom stats lparams isUnsafe t k ctors).map .ctorInfo) ∧
    r.2.quotInit = E.quotInit ∧
    (∀ cval ∈ ctorInfosFrom stats lparams isUnsafe t k ctors,
      E.find? cval.name = none ∧
      (Kernel.Environment.primitives.contains cval.name → allow)) ∧
    ((ctorInfosFrom stats lparams isUnsafe t k ctors).map (·.name)).Nodup
  | [], k, E, r, _, h => by
    cases h; exact ⟨rfl, rfl, by simp [ctorInfosFrom], by simp [ctorInfosFrom]⟩
  | ctor :: ctors, k, E, r, hwf, h => by
    rw [List.foldlM_cons] at h
    cases hcheck : Kernel.Environment.checkName E ctor.name allow with
    | error e => rw [hcheck] at h; cases h
    | ok u =>
    rw [hcheck] at h
    obtain ⟨hfresh, hprim⟩ := checkName.WF hwf ctor.name allow u hcheck
    let ci : ConstantInfo := .ctorInfo (AddInductive.constructorInfo stats lparams isUnsafe t k ctor)
    have hname : ci.name = ctor.name := rfl
    have hnone : E.constants.find? ci.name = none := by
      rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
    have hwf' : (E.add ci).constants.WF := hwf.insert ci.name ci hnone
    obtain ⟨hmap, hquot, hfr, hnd⟩ :=
      declareFamilyFold stats lparams isUnsafe allow t ctors (k + 1) (E.add ci) r hwf' h
    refine ⟨hmap, hquot, ?_, ?_⟩
    · intro cval hcval
      simp only [ctorInfosFrom, List.mem_cons] at hcval
      rcases hcval with rfl | hcval
      · exact ⟨hfresh, hprim⟩
      · obtain ⟨h1, h2⟩ := hfr cval hcval
        exact ⟨(find?_add_none (ci := ci) hwf hfresh h1).1, h2⟩
    · simp only [ctorInfosFrom, List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, hnd⟩
      obtain ⟨cval, hcval, he⟩ := List.mem_map.mp hmem
      exact (find?_add_none (ci := ci) hwf hfresh (hfr cval hcval).1).2 (he.trans hname.symm)

/-- What the constructor fold of the block establishes. -/
theorem declareBlockFold (stats : AddInductive.InductiveStats) (lparams : List Name)
    (isUnsafe allow : Bool) :
    ∀ (types : List InductiveType) (E : Environment) (r : Environment),
    E.constants.WF →
    List.foldlM (m := Except Exception) (fun (env : Environment) (indType : InductiveType) => do
        let (_, env) ← indType.ctors.foldlM (init := (0, env)) fun (x : Nat × Environment) ctor => do
          Kernel.Environment.checkName x.2 ctor.name allow
          pure (x.1 + 1, AddInductive.addConstant x.2 (.ctorInfo
            (AddInductive.constructorInfo stats lparams isUnsafe indType x.1 ctor)))
        pure env) E types = .ok r →
    r.constants = insertConsts E.constants
      ((ctorInfos stats lparams isUnsafe types).map .ctorInfo) ∧
    r.quotInit = E.quotInit ∧
    (∀ cval ∈ ctorInfos stats lparams isUnsafe types,
      E.find? cval.name = none ∧
      (Kernel.Environment.primitives.contains cval.name → allow)) ∧
    ((ctorInfos stats lparams isUnsafe types).map (·.name)).Nodup
  | [], E, r, _, h => by cases h; exact ⟨rfl, rfl, by simp [ctorInfos], by simp [ctorInfos]⟩
  | t :: types, E, r, hwf, h => by
    rw [List.foldlM_cons] at h
    cases hp : List.foldlM (m := Except Exception) (fun (x : Nat × Environment) ctor => do
        Kernel.Environment.checkName x.2 ctor.name allow
        pure (x.1 + 1, AddInductive.addConstant x.2 (.ctorInfo
          (AddInductive.constructorInfo stats lparams isUnsafe t x.1 ctor)))) (0, E) t.ctors with
    | error e => rw [hp] at h; cases h
    | ok p =>
    rw [hp] at h
    change List.foldlM (m := Except Exception) _ p.2 types = Except.ok r at h
    obtain ⟨hmap, hquot, hfr, hnd⟩ :=
      declareFamilyFold stats lparams isUnsafe allow t t.ctors 0 E p hwf hp
    have hwfp : p.2.constants.WF := by
      rw [hmap]
      refine insertConsts_wf hwf (fun ci hci => ?_) (by rw [List.map_map]; exact hnd)
      obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
      have := (hfr cval hcval).1
      rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at this
    obtain ⟨hmap', hquot', hfr', hnd'⟩ :=
      declareBlockFold stats lparams isUnsafe allow types p.2 r hwfp h
    have hfrE : ∀ cval ∈ ctorInfosFrom stats lparams isUnsafe t 0 t.ctors,
        E.constants.find? cval.name = none := fun cval hcval => by
      have := (hfr cval hcval).1
      rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at this
    have hnew : ∀ cval ∈ ctorInfos stats lparams isUnsafe types,
        E.find? cval.name = none ∧
          cval.name ∉ (ctorInfosFrom stats lparams isUnsafe t 0 t.ctors).map (·.name) := by
      intro cval hcval
      have h1 := (hfr' cval hcval).1
      rw [Kernel.Environment.find?, hwfp.find?'_eq_find?, hmap] at h1
      refine ⟨?_, fun hmem => ?_⟩
      · have : E.constants.find? cval.name = none := by
          by_contra hsome
          obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hsome
          rw [insertConsts_find?_mono_of_fresh hwf.map₂ (fun ci hci => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hci; exact hfrE c hc) hv] at h1
          cases h1
        rwa [Kernel.Environment.find?, hwf.find?'_eq_find?]
      · obtain ⟨c, hc, he⟩ := List.mem_map.mp hmem
        have := insertConsts_find?_self hwf (cis := (ctorInfosFrom stats lparams isUnsafe t 0
          t.ctors).map .ctorInfo) (fun ci hci => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hci; exact hfrE c hc)
          (by rw [List.map_map]; exact hnd) (.ctorInfo c) (List.mem_map_of_mem hc)
        simp only [ConstantInfo.name] at this
        change (insertConsts E.constants _).find? c.name = _ at this
        rw [he, h1] at this
        cases this
    refine ⟨?_, hquot'.trans hquot, ?_, ?_⟩
    · rw [hmap', hmap]
      simp [ctorInfos, familyCtorInfos, insertConsts, List.foldl_append]
    · intro cval hcval
      simp only [ctorInfos, List.flatMap_cons, List.mem_append] at hcval
      rcases hcval with hcval | hcval
      · exact hfr cval hcval
      · exact ⟨(hnew cval hcval).1, (hfr' cval hcval).2⟩
    · simp only [ctorInfos, List.flatMap_cons, List.map_append, List.nodup_append]
      refine ⟨hnd, hnd', fun a ha b hb hab => ?_⟩
      obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hb
      exact (hnew cval hcval).2 (hab ▸ ha)

/-- The constructor installation: the constant map gains exactly the block's constructor
infos, whose names are distinct and absent from the header environment (and nonprimitive
unless primitives are allowed). -/
theorem AddInductive.declareConstructors.WF {c : AddInductive.Context}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    (hwf : c.env.constants.WF) :
    (AddInductive.declareConstructors stats indTypes isUnsafe c).WF fun ctorEnv =>
      ctorEnv.constants = insertConsts c.env.constants
        ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map .ctorInfo) ∧
      ctorEnv.quotInit = c.env.quotInit ∧
      (∀ cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList,
        c.env.find? cval.name = none ∧
        (Kernel.Environment.primitives.contains cval.name → c.allowPrimitive)) ∧
      ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name)).Nodup := by
  intro r h
  unfold AddInductive.declareConstructors at h
  rw [← Array.foldlM_toList] at h
  exact declareBlockFold stats c.lparams isUnsafe c.allowPrimitive indTypes.toList c.env r hwf h

/-- The header fold installs a primitive name only when primitives are allowed. -/
theorem declareInductiveTypeInfos.allowsPrimitives (allow : Bool) :
    ∀ (infos : List InductiveVal) (E r : Environment), E.constants.WF →
    AddInductive.declareInductiveTypeInfos allow infos E = .ok r →
    ∀ info ∈ infos, Kernel.Environment.primitives.contains info.name → allow = true
  | [], _, _, _, _ => by simp
  | info :: infos, E, r, hwf, h => by
    simp only [AddInductive.declareInductiveTypeInfos] at h
    cases hc : Kernel.Environment.checkName E info.name allow with
    | error e => rw [hc] at h; cases h
    | ok u =>
      rw [hc] at h
      obtain ⟨hfresh, hprim⟩ := checkName.WF hwf info.name allow u hc
      have hnone : E.constants.find? (ConstantInfo.inductInfo info).name = none := by
        rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
      have hwf' : (AddInductive.addConstant E (.inductInfo info)).constants.WF :=
        hwf.insert _ _ hnone
      intro i hi hp
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hprim hp
      · exact declareInductiveTypeInfos.allowsPrimitives allow infos _ r hwf' h i hi hp

theorem AddInductive.declareInductiveTypes.allowsPrimitives {c : AddInductive.Context}
    (stats : AddInductive.InductiveStats) (nparams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (hwf : c.env.constants.WF) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested isUnsafe c).WF
      fun _ => ∀ info ∈ (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList,
        Kernel.Environment.primitives.contains info.name → c.allowPrimitive = true :=
  fun r h => declareInductiveTypeInfos.allowsPrimitives c.allowPrimitive _ c.env r hwf h

end VerifyInductive
end Lean4Lean
