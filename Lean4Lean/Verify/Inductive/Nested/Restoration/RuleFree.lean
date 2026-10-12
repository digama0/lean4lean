import Lean4Lean.Verify.Inductive.Nested.Install.Permutation
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyTypes
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyKernel
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyRecursors
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledRun
import Lean4Lean.Verify.Inductive.Nested.Install.DependencyOrder

/-! # The rule-free stage of a restored nested block

The recursor-rule validation pass checks the restored rules in the output environment with the
new recursors' rules removed (`stripRecursorRules`). Its model is the recursor stage of the
restored declaration with every recursor's rules removed (`RuleFreeStage`,
`Validation/Stripped.lean`), stated over a step witness `AddInduct` whose output map is an
`insertConsts`. The stripped environment re-inserts each recursor, so its constant map is not
structurally an `insertConsts` of the block's constants. This file builds the rule-free stage
over `S0`, the source environment extended by the stripped block (`ruleFreeEnv`), shows that
the stripped environment has the same lookups (`stripRecursorRules_find?`, `ruleFreeEnv_find?`),
and transfers the checking invariant along that extensional equality
(`CheckingEnv.Valid.mapExt`). -/

namespace Lean.SMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

theorem insert_stage₁ (s : SMap α β) (k : α) (v : β) : (s.insert k v).stage₁ = s.stage₁ := by
  unfold insert; split <;> rfl

/-- After an insertion outside the first stage, the key is in the persistent stage. -/
theorem insert_map₂_contains_self {s : SMap α β} (h : s.map₂.WF) (hst : s.stage₁ = false)
    (k : α) (v : β) : (s.insert k v).map₂.contains k := by
  unfold insert; split
  · simp_all
  · rw [PersistentHashMap.find?_isSome, h.find?_insert]; simp

/-- An insertion keeps the persistent stage's keys. -/
theorem insert_map₂_contains {s : SMap α β} (h : s.map₂.WF) {x : α} (hx : s.map₂.contains x)
    (k : α) (v : β) : (s.insert k v).map₂.contains x := by
  unfold insert; split
  · exact hx
  · rw [PersistentHashMap.find?_isSome] at hx ⊢
    rw [h.find?_insert]; split <;> simp_all

/-- Replacing the value of a key of the persistent stage (or any key in the first stage) keeps
the map well formed. -/
theorem WF.insert_replace {s : SMap α β} (h : s.WF) {k : α} (v : β)
    (hk : s.stage₁ = true ∨ s.map₂.contains k) : (s.insert k v).WF := by
  unfold insert; split
  · exact ⟨h.map₂, h.stage, fun h1 => by have := h.stage rfl; simp_all [PersistentHashMap.find?_isSome, PersistentHashMap.WF.empty.find?_eq]⟩
  · rename_i m₁ m₂
    refine ⟨h.map₂.insert .., nofun, fun {a} h1 => ?_⟩
    rcases hk with hk | hk
    · cases hk
    rw [PersistentHashMap.find?_isSome, h.map₂.find?_insert] at h1
    by_cases hka : k = a
    · subst hka; exact h.disjoint hk
    · simp [hka] at h1
      exact h.disjoint (by rw [PersistentHashMap.find?_isSome]; simpa using h1)

end Lean.SMap

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- A recursor with its rules removed, at the stripped names. -/
def stripRecCI (names : List Name) (x : Name) (ci : ConstantInfo) : ConstantInfo :=
  if x ∈ names then
    match ci with
    | .recInfo r => .recInfo { r with rules := [] }
    | ci => ci
  else ci

theorem stripRecCI_cons_of_ne {names : List Name} {n x : Name} (h : x ≠ n) (ci : ConstantInfo) :
    stripRecCI (n :: names) x ci = stripRecCI names x ci := by
  simp [stripRecCI, h]

theorem stripRecCI_nonrec {names : List Name} {x : Name} {ci : ConstantInfo}
    (h : ∀ r, ci ≠ .recInfo r) : stripRecCI names x ci = ci := by
  unfold stripRecCI; split
  · cases ci with
    | recInfo r => exact absurd rfl (h r)
    | _ => rfl
  · rfl

theorem stripRecCI_stripped {names : List Name} {x : Name} (r : RecursorVal) :
    stripRecCI names x (.recInfo { r with rules := [] }) = .recInfo { r with rules := [] } := by
  unfold stripRecCI; split <;> rfl

/-- **The lookups of the stripped environment**: a named recursor is found with its rules
removed, every other constant unchanged. -/
theorem stripRecursorRules_find? :
    ∀ (names : List Name) (env : Environment), env.constants.WF →
      (∀ x ci, env.constants.find? x = some ci → ci.name = x) →
      (∀ x ∈ names, env.constants.stage₁ = true ∨ env.constants.map₂.contains x) →
      (stripRecursorRules env names).constants.WF ∧
      ∀ x, (stripRecursorRules env names).constants.find? x =
        (env.constants.find? x).map (stripRecCI names x)
  | [], env, hwf, _, _ => ⟨hwf, fun x => by
      change env.constants.find? x = _
      cases env.constants.find? x <;> simp [stripRecCI]⟩
  | n :: names, env, hwf, hname, hrepl => by
    have hstep : stripRecursorRules env (n :: names) = stripRecursorRules
        (match env.find? n with
          | some (.recInfo info) => env.add (.recInfo { info with rules := [] })
          | _ => env) names := rfl
    rw [hstep]
    have hfindn : env.find? n = env.constants.find? n := by
      rw [Kernel.Environment.find?, hwf.find?'_eq_find?]
    cases hfn : env.constants.find? n with
    | none =>
      rw [hfindn, hfn]
      obtain ⟨hwf', hf⟩ := stripRecursorRules_find? names env hwf hname
        (fun x hx => hrepl x (.tail _ hx))
      refine ⟨hwf', fun x => ?_⟩
      rw [hf x]
      by_cases hx : x = n
      · subst hx; rw [hfn]; rfl
      · cases env.constants.find? x <;> simp [stripRecCI_cons_of_ne hx]
    | some ci =>
      rw [hfindn, hfn]
      cases ci with
      | recInfo info =>
        dsimp only
        have hnm : info.name = n := hname n _ hfn
        let ci' : ConstantInfo := .recInfo { info with rules := [] }
        have hconst : (env.add ci').constants = env.constants.insert n ci' := by
          change env.constants.insert ci'.name ci' = _
          rw [show ci'.name = n from hnm]
        have hwf1 : (env.add ci').constants.WF := by
          rw [hconst]; exact hwf.insert_replace ci' (hrepl n (.head _))
        have hfind1 : ∀ x, (env.add ci').constants.find? x =
            if n = x then some ci' else env.constants.find? x := by
          intro x; rw [hconst, hwf.find?_insert]; simp
        have hname1 : ∀ x c, (env.add ci').constants.find? x = some c → c.name = x := by
          intro x c h
          rw [hfind1] at h
          split at h
          · cases h; rename_i h'; subst h'; exact hnm
          · exact hname x c h
        have hrepl1 : ∀ x ∈ names, (env.add ci').constants.stage₁ = true ∨
            (env.add ci').constants.map₂.contains x := by
          intro x hx
          rw [hconst, SMap.insert_stage₁]
          rcases hrepl x (.tail _ hx) with h | h
          · exact .inl h
          · exact .inr (SMap.insert_map₂_contains hwf.map₂ h n ci')
        obtain ⟨hwf', hf⟩ := stripRecursorRules_find? names (env.add ci') hwf1 hname1 hrepl1
        refine ⟨hwf', fun x => ?_⟩
        rw [hf x, hfind1 x]
        by_cases hx : x = n
        · subst hx; simp [hfn, ci', stripRecCI]
        · rw [if_neg (Ne.symm hx)]
          cases env.constants.find? x <;> simp [stripRecCI_cons_of_ne hx]
      | _ =>
        obtain ⟨hwf', hf⟩ := stripRecursorRules_find? names env hwf hname
          (fun x hx => hrepl x (.tail _ hx))
        refine ⟨hwf', fun x => ?_⟩
        rw [hf x]
        by_cases hx : x = n
        · subst hx; rw [hfn]
          simp only [Option.map_some]
          rw [stripRecCI_nonrec (by intro r h; cases h), stripRecCI_nonrec (by intro r h; cases h)]
        · cases env.constants.find? x <;> simp [stripRecCI_cons_of_ne hx]

/-! ### The rule-free environment -/

/-- Inserting a list of constants keeps the first-stage flag. -/
theorem insertConsts_stage₁ : ∀ (C : ConstMap) (cis : List ConstantInfo),
    (insertConsts C cis).stage₁ = C.stage₁
  | _, [] => rfl
  | C, ci :: cis => by
    rw [insertConsts_cons, insertConsts_stage₁, SMap.insert_stage₁]

theorem insertConsts_map₂_contains_of : ∀ {C : ConstMap} {cis : List ConstantInfo} {x : Name},
    C.map₂.WF → C.map₂.contains x → (insertConsts C cis).map₂.contains x
  | _, [], _, _, h => h
  | C, d :: ds, x, hwf, h => by
    rw [insertConsts_cons]
    exact insertConsts_map₂_contains_of (SMap.insert_map₂ hwf)
      (SMap.insert_map₂_contains hwf h d.name d)

/-- Outside the first stage, inserted constants land in the persistent stage. -/
theorem insertConsts_map₂_contains : ∀ {C : ConstMap} {cis : List ConstantInfo}, C.map₂.WF →
    C.stage₁ = false → ∀ ci ∈ cis, (insertConsts C cis).map₂.contains ci.name
  | _, [], _, _, _, h => by cases h
  | C, d :: ds, hwf, hst, ci, hci => by
    rw [insertConsts_cons]
    have hwf' := SMap.insert_map₂ (k := d.name) (v := d) hwf
    have hst' : (C.insert d.name d).stage₁ = false := by rw [SMap.insert_stage₁, hst]
    rcases List.mem_cons.mp hci with rfl | hci
    · exact insertConsts_map₂_contains_of hwf' (SMap.insert_map₂_contains_self hwf hst _ _)
    · exact insertConsts_map₂_contains hwf' hst' ci hci

/-- The source environment extended by a list of constants, one `add` each. -/
def addConstsEnv (env : Environment) (cis : List ConstantInfo) : Environment :=
  cis.foldl (fun e ci => e.add ci) env

theorem addConstsEnv_constants : ∀ (env : Environment) (cis : List ConstantInfo),
    (addConstsEnv env cis).constants = insertConsts env.constants cis
  | _, [] => rfl
  | env, ci :: cis => addConstsEnv_constants (env.add ci) cis

theorem addConstsEnv_quotInit : ∀ (env : Environment) (cis : List ConstantInfo),
    (addConstsEnv env cis).quotInit = env.quotInit
  | _, [] => rfl
  | env, ci :: cis => addConstsEnv_quotInit (env.add ci) cis

/-- The constants of a block with the named recursors' rules removed. -/
def stripEntries (names : List Name) (entries : List ConstantInfo) : List ConstantInfo :=
  entries.map fun ci => stripRecCI names ci.name ci

theorem stripRecCI_name (names : List Name) (x : Name) (ci : ConstantInfo) :
    (stripRecCI names x ci).name = ci.name := by
  unfold stripRecCI; split
  · split <;> rfl
  · rfl

/-- **The stripped environment and the rule-free environment have the same lookups.** -/
theorem stripRecursorRules_find?_eq_strip {source outEnv : Environment}
    {entries : List ConstantInfo} {names : List Name}
    (hsourceWF : source.constants.WF)
    (hsourceNames : ∀ x ci, source.constants.find? x = some ci → ci.name = x)
    (hfresh : ∀ ci ∈ entries, source.constants.find? ci.name = none)
    (hnodup : (entries.map (·.name)).Nodup)
    (hmap : outEnv.constants = insertConsts source.constants entries)
    (hnames : ∀ x ∈ names, x ∈ entries.map (·.name)) :
    (stripRecursorRules outEnv names).constants.WF ∧
    (addConstsEnv source (stripEntries names entries)).constants.WF ∧
    (∀ x, (stripRecursorRules outEnv names).constants.find? x =
      (addConstsEnv source (stripEntries names entries)).constants.find? x) ∧
    ∀ x, (stripRecursorRules outEnv names).constants.find? x =
      (outEnv.constants.find? x).map (stripRecCI names x) := by
  have houtWF : outEnv.constants.WF := by
    rw [hmap]; exact insertConsts_wf hsourceWF hfresh hnodup
  have hstripNames : (stripEntries names entries).map (·.name) = entries.map (·.name) := by
    simp [stripEntries, stripRecCI_name]
  have hfresh' : ∀ ci ∈ stripEntries names entries, source.constants.find? ci.name = none := by
    intro ci hci
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hci
    rw [stripRecCI_name]; exact hfresh d hd
  have hnodup' : ((stripEntries names entries).map (·.name)).Nodup := by
    rw [hstripNames]; exact hnodup
  have hS0WF : (addConstsEnv source (stripEntries names entries)).constants.WF := by
    rw [addConstsEnv_constants]; exact insertConsts_wf hsourceWF hfresh' hnodup'
  have houtNames : ∀ x ci, outEnv.constants.find? x = some ci → ci.name = x := by
    intro x ci h
    rw [hmap] at h
    rcases insertConsts_find? hsourceWF hfresh hnodup h with h | ⟨_, h⟩
    · exact hsourceNames x ci h
    · exact h
  have hrepl : ∀ x ∈ names, outEnv.constants.stage₁ = true ∨ outEnv.constants.map₂.contains x := by
    intro x hx
    rw [hmap, insertConsts_stage₁]
    cases hst : source.constants.stage₁
    · right
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp (hnames x hx)
      exact insertConsts_map₂_contains hsourceWF.map₂ hst ci hci
    · exact .inl rfl
  obtain ⟨hstripWF, hstrip⟩ := stripRecursorRules_find? names outEnv houtWF houtNames hrepl
  refine ⟨hstripWF, hS0WF, fun x => ?_, hstrip⟩
  rw [hstrip x, addConstsEnv_constants, hmap]
  by_cases hx : ∃ ci ∈ entries, ci.name = x
  · obtain ⟨ci, hci, rfl⟩ := hx
    rw [insertConsts_find?_self hsourceWF hfresh hnodup ci hci]
    have h := insertConsts_find?_self hsourceWF hfresh' hnodup' _
      (List.mem_map_of_mem (f := fun ci => stripRecCI names ci.name ci) hci)
    rw [stripRecCI_name] at h
    rw [h]; rfl
  · have hne : ∀ ci ∈ entries, ci.name ≠ x := fun ci hci h => hx ⟨ci, hci, h⟩
    have hne' : ∀ ci ∈ stripEntries names entries, ci.name ≠ x := by
      intro ci hci
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hci
      rw [stripRecCI_name]; exact hne d hd
    cases hs : source.constants.find? x with
    | none =>
      rw [insertConsts_find?_none hsourceWF.map₂ hne hs,
        insertConsts_find?_none hsourceWF.map₂ hne' hs]; rfl
    | some c =>
      rw [insertConsts_find?_mono hsourceWF.map₂ hne hs,
        insertConsts_find?_mono hsourceWF.map₂ hne' hs]
      have hxn : x ∉ names := by
        intro hxn
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (hnames x hxn)
        rw [hfresh d hd] at hs; cases hs
      simp [stripRecCI, hxn]

/-! ### Transport from the output to the rule-free environment -/

theorem stripRecCI_eq_inductInfo {names : List Name} {x : Name} {ci : ConstantInfo}
    {v : InductiveVal} : stripRecCI names x ci = .inductInfo v ↔ ci = .inductInfo v := by
  unfold stripRecCI; split
  · cases ci <;> simp
  · rfl

theorem stripRecCI_eq_ctorInfo {names : List Name} {x : Name} {ci : ConstantInfo}
    {v : ConstructorVal} : stripRecCI names x ci = .ctorInfo v ↔ ci = .ctorInfo v := by
  unfold stripRecCI; split
  · cases ci <;> simp
  · rfl

/-- A recursor value with its rules removed. -/
abbrev _root_.Lean.RecursorVal.stripRules (r : RecursorVal) : RecursorVal := { r with rules := [] }

/-- A model recursor with its rules removed. -/
abbrev _root_.Lean4Lean.VRecursor.stripRules (r : VRecursor) : VRecursor := { r with rules := [] }

/-- **Stripped recursor translation**: removing the rules of a recursor and of its model
keeps the translation, in any constant map. -/
theorem TrRecursor.stripRules {safety : DefinitionSafety} {envC envR : VEnv} {m m' : ConstMap}
    {rval : RecursorVal} {r : VRecursor} (H : TrRecursor safety envC envR m rval r) :
    TrRecursor safety envC envR m' rval.stripRules r.stripRules where
  tr := H.tr
  all := H.all
  numParams := H.numParams
  numMotives := H.numMotives
  numMinors := H.numMinors
  numIndices := H.numIndices
  k := H.k
  rules := .nil

theorem consts_stripEntries (ivals : List (InductiveVal × List ConstructorVal))
    (rvals : List RecursorVal) :
    stripEntries (rvals.map (·.name)) (AddInduct.consts ivals rvals) =
      AddInduct.consts ivals (rvals.map RecursorVal.stripRules) := by
  have hnr : ∀ (l : List ConstantInfo), (∀ ci ∈ l, ∀ r, ci ≠ .recInfo r) →
      l.map (fun ci => stripRecCI (rvals.map (·.name)) ci.name ci) = l := by
    intro l hl
    conv => rhs; rw [← List.map_id l]
    exact List.map_congr_left fun ci hci => stripRecCI_nonrec (hl ci hci)
  simp only [stripEntries, AddInduct.consts, List.map_append]
  congr 1
  · congr 1
    · exact hnr _ (by intro ci hci r h; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hci; cases h)
    · exact hnr _ (by
        intro ci hci r h
        obtain ⟨_, _, hc⟩ := List.mem_flatMap.mp hci
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc; cases h)
  · simp only [List.map_map]
    apply List.map_congr_left
    intro r hr
    have hmem : (ConstantInfo.recInfo r).name ∈ rvals.map (·.name) := List.mem_map_of_mem hr
    show stripRecCI _ (ConstantInfo.recInfo r).name (.recInfo r) = _
    unfold stripRecCI
    rw [if_pos hmem]; rfl

/-- The rule-free model recursor of a kernel recursor and its translated constant. -/
def ruleFreeRecursor (rv : RecursorVal) (v : VConstVal) : VRecursor where
  toVConstVal := v
  all := rv.all
  numParams := rv.numParams
  numMotives := rv.numMotives
  numMinors := rv.numMinors
  numIndices := rv.numIndices
  k := rv.k
  rules := []

theorem ruleFreeRecursors_spec {safety : DefinitionSafety} {envP envR : VEnv} {m : ConstMap} :
    ∀ {rvals : List RecursorVal} {vs : List VConstVal},
      List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
        TrConstVal safety envP (.recInfo rv) v ∧ v.toVConstant.WF envP) rvals vs →
      (List.zipWith ruleFreeRecursor rvals vs).map (·.toVConstVal) = vs ∧
      List.Forall₂ (TrRecursor safety envP envR m) (rvals.map RecursorVal.stripRules)
        (List.zipWith ruleFreeRecursor rvals vs) ∧
      ∀ r ∈ List.zipWith ruleFreeRecursor rvals vs,
        r.rules = [] ∧ r.toVConstVal.toVConstant.WF envP
  | [], [], .nil => ⟨rfl, .nil, by simp⟩
  | rv :: rvs, v :: vs, .cons h t => by
    obtain ⟨h1, h2, h3⟩ := ruleFreeRecursors_spec (envR := envR) (m := m) t
    refine ⟨by simp [h1, ruleFreeRecursor], .cons ⟨h.1, rfl, rfl, rfl, rfl, rfl, rfl, .nil⟩ h2, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨rfl, h.2⟩
    · exact h3 r hr

/-- **The rule-free stage of a block installation.** From the step data of an inductive block
installed into `outEnv` (its kernel constants, translations and stages) and the facts of
`RuleFreeStage` at the output, the block with every recursor's rules removed is installed into
the rule-free environment `addConstsEnv env (stripEntries names entries)`, whose lookups are
those of `stripRecursorRules outEnv names`; so the stripped environment is a valid checking
environment, and a checker environment if the source is, of the recursor stage. -/
theorem stripRecursorRules.validOfBlock {safety : DefinitionSafety} {env outEnv : Environment}
    {venv envT envC envR : VEnv} {decl : VInductDecl} {vs : List VConstVal}
    {ivals : List (InductiveVal × List ConstructorVal)} {rvals : List RecursorVal}
    {entries : List ConstantInfo}
    (hin : CheckingEnv.Valid safety env venv)
    (hT : decl.addTypes venv = some envT) (hC : decl.addCtors envT = some envC)
    (hR : (decl.addProjs envC).addConstVals vs = some envR)
    (htypes : List.Forall₂ (fun iv t => TrIndType safety venv envT iv.1 iv.2 t) ivals decl.types)
    (hrecs : List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
      TrConstVal safety (decl.addProjs envC) (.recInfo rv) v ∧
        v.toVConstant.WF (decl.addProjs envC)) rvals vs)
    (hperm : entries.Perm (AddInduct.consts ivals rvals))
    (hfresh : ∀ ci ∈ AddInduct.consts ivals rvals, env.constants.find? ci.name = none)
    (hnodupEntries : (entries.map (·.name)).Nodup)
    (hmap : outEnv.constants = insertConsts env.constants entries)
    (hquot : outEnv.quotInit = env.quotInit)
    (henvP : (decl.addProjs envC).WF)
    (hnonprimitive : ∀ ci ∈ AddInduct.consts ivals rvals,
      ¬ Kernel.Environment.primitives.contains ci.name)
    (hlisted : ListedConstructorsPresent env)
    (htypeUvars : ∀ T ∈ decl.types, T.uvars = decl.uvars)
    (hctorUvars : ∀ c ∈ decl.constructorConstants, c.uvars = decl.uvars)
    (horigins : InductInfosFromDecl env.constants outEnv.constants decl)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none)
    (howners : ConstructorOwnersPresent outEnv)
    (hrecMajor : ∀ r ∈ rvals, ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info))
    (hk : ∀ r ∈ rvals, r.k = false)
    (hshapes : ∀ r ∈ rvals, safety ≤ (ConstantInfo.recInfo r).safety →
      ∃ cnparams indLevels ctorParams, Nonempty (VRecursorShape envR r.name r.levelParams.length
        r.numParams cnparams r.numMotives r.numMinors r.numIndices r.getMajorInduct indLevels
        ctorParams)) :
    CheckingEnv.Valid safety (stripRecursorRules outEnv (rvals.map (·.name))) envR ∧
      (CheckerEnv safety env venv →
        CheckerEnv safety (stripRecursorRules outEnv (rvals.map (·.name))) envR) := by
  let names := rvals.map (·.name)
  let recs0 := List.zipWith ruleFreeRecursor rvals vs
  let decl0 : VInductDecl := { decl with recs := recs0 }
  let rvals0 := rvals.map RecursorVal.stripRules
  let S0 := addConstsEnv env (stripEntries names entries)
  have hrecs0 := ruleFreeRecursors_spec (envR := envR) (m := S0.constants) hrecs
  have hsourceWF : env.constants.WF := hin.tr.map_wf
  have hsourceNames : ∀ x ci, env.constants.find? x = some ci → ci.name = x := by
    intro x ci h
    exact hin.tr.find?_name (by rw [Kernel.Environment.find?, hsourceWF.find?'_eq_find?]; exact h)
  have hfreshE : ∀ ci ∈ entries, env.constants.find? ci.name = none :=
    fun ci hci => hfresh ci (hperm.mem_iff.mp hci)
  have hnamesE : ∀ x ∈ names, x ∈ entries.map (·.name) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    refine List.mem_map.mpr ⟨.recInfo r, hperm.mem_iff.mpr ?_, rfl⟩
    simp [AddInduct.consts, hr]
  obtain ⟨hstripWF, hS0WF, hfindEq, hstripFind⟩ := stripRecursorRules_find?_eq_strip
    hsourceWF hsourceNames hfreshE hnodupEntries hmap hnamesE
  have houtWF : outEnv.constants.WF := by
    rw [hmap]; exact insertConsts_wf hsourceWF hfreshE hnodupEntries
  have hS0map : ∀ x, S0.constants.find? x = (outEnv.constants.find? x).map (stripRecCI names x) :=
    fun x => (hfindEq x).symm.trans (hstripFind x)
  have hS0find : ∀ x, S0.find? x = (outEnv.find? x).map (stripRecCI names x) := by
    intro x
    rw [Kernel.Environment.find?, Kernel.Environment.find?, hS0WF.find?'_eq_find?,
      houtWF.find?'_eq_find?, hS0map]
  have hind : ∀ {x v}, outEnv.find? x = some (.inductInfo v) → S0.find? x = some (.inductInfo v) := by
    intro x v h; rw [hS0find, h]; simp [stripRecCI_eq_inductInfo]
  have hind' : ∀ {x v}, S0.find? x = some (.inductInfo v) → outEnv.find? x = some (.inductInfo v) := by
    intro x v h; rw [hS0find] at h
    cases h' : outEnv.find? x <;> rw [h'] at h <;> simp at h
    rw [stripRecCI_eq_inductInfo.mp h]
  have hctor : ∀ {x v}, outEnv.find? x = some (.ctorInfo v) → S0.find? x = some (.ctorInfo v) := by
    intro x v h; rw [hS0find, h]; simp [stripRecCI_eq_ctorInfo]
  have hctor' : ∀ {x v}, S0.find? x = some (.ctorInfo v) → outEnv.find? x = some (.ctorInfo v) := by
    intro x v h; rw [hS0find] at h
    cases h' : outEnv.find? x <;> rw [h'] at h <;> simp at h
    rw [stripRecCI_eq_ctorInfo.mp h]
  have hindMap : ∀ {x v}, outEnv.constants.find? x = some (.inductInfo v) →
      S0.constants.find? x = some (.inductInfo v) := by
    intro x v h; rw [hS0map, h]; simp [stripRecCI_eq_inductInfo]
  have hindMap' : ∀ {x v}, S0.constants.find? x = some (.inductInfo v) →
      outEnv.constants.find? x = some (.inductInfo v) := by
    intro x v h; rw [hS0map] at h
    cases h' : outEnv.constants.find? x <;> rw [h'] at h <;> simp at h
    rw [stripRecCI_eq_inductInfo.mp h]
  have hctorMap : ∀ {x v}, outEnv.constants.find? x = some (.ctorInfo v) →
      S0.constants.find? x = some (.ctorInfo v) := by
    intro x v h; rw [hS0map, h]; simp [stripRecCI_eq_ctorInfo]
  have hconsts0 : AddInduct.consts ivals rvals0 = stripEntries names (AddInduct.consts ivals rvals) :=
    (consts_stripEntries ivals rvals).symm
  have hmem0 : ∀ ci ∈ AddInduct.consts ivals rvals0, ∃ d ∈ AddInduct.consts ivals rvals,
      ci.name = d.name := by
    intro ci hci
    rw [hconsts0] at hci
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hci
    exact ⟨d, hd, stripRecCI_name _ _ _⟩
  have hrulesNone : ∀ (rs : List VRecursor) (e : VEnv), (∀ r ∈ rs, r.rules = []) →
      rs.foldlM (init := e) (fun e r => r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru)
        = some e := by
    intro rs
    induction rs with
    | nil => intro e _; rfl
    | cons r rs ih =>
      intro e hr
      simp only [List.foldlM_cons, hr r (.head _), List.foldlM_nil]
      exact ih e fun r' h' => hr r' (.tail _ h')
  have hrules0 : ∀ r ∈ decl0.recs, r.rules = [] := fun r hr => (hrecs0.2.2 r hr).1
  let H0 : AddInduct safety env.constants venv decl0 S0.constants envR := {
    ivals := ivals
    rvals := rvals0
    envT := envT
    envC := envC
    envR := envR
    stT := hT
    stC := hC
    stR := by
      rw [VInductDecl.addRecs_eq_addConstVals]
      show (decl.addProjs envC).addConstVals (recs0.map (·.toVConstVal)) = _
      rw [hrecs0.1]; exact hR
    stP := hrulesNone _ _ hrules0
    types := htypes
    recs := hrecs0.2.1
    order := stripEntries names entries
    order_perm := by rw [hconsts0]; exact hperm.map _
    fresh := by
      intro ci hci
      obtain ⟨d, hd, hname⟩ := hmem0 ci hci
      rw [hname]; exact hfresh d hd
    map_eq := addConstsEnv_constants _ _ }
  have F : RuleFreeStage safety env venv decl0 S0 envR H0 := {
    rules_empty := hrules0
    quotInit := addConstsEnv_quotInit _ _
    envP_wf := henvP
    recs_wf := fun r hr => (hrecs0.2.2 r hr).2
    nonprimitive := by
      intro ci hci
      obtain ⟨d, hd, hname⟩ := hmem0 ci hci
      rw [hname]; exact hnonprimitive d hd
    listedPresent := hlisted
    typeUvars := htypeUvars
    constructorUvars := hctorUvars
    origins := by
      intro familyName familyInfo h
      rcases horigins familyName familyInfo (hindMap' h) with hold | ⟨idx, hn, ⟨A⟩⟩
      · exact .inl hold
      · refine .inr ⟨idx, hn, ⟨{ A with
          lookup := hindMap A.lookup
          constructor := fun i hi => let ⟨D⟩ := A.constructor i hi
            ⟨{ D with lookup := hctorMap D.lookup }⟩ }⟩⟩
    cover := by
      intro T hT
      obtain ⟨v, hv, hnone⟩ := hcover T hT
      exact ⟨v, hind hv, hnone⟩
    owners := by
      intro name info h
      obtain ⟨owner, hown, hrest⟩ := howners name info (hctor' h)
      exact ⟨owner, hind hown, hrest⟩
    recMajor := by
      intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      obtain ⟨info, hinfo⟩ := hrecMajor r' hr'
      exact ⟨info, hind hinfo⟩
    recK := by
      intro r hr _
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      exact KLikeRecursor.of_k_false (hk r' hr')
    recShapes := by
      intro r hr hsafe
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      obtain ⟨cnparams, indLevels, ctorParams, S⟩ := hshapes r' hr' hsafe
      exact ⟨⟨cnparams, indLevels, ctorParams, S, nofun⟩, nofun⟩ }
  have hstripQuot : ∀ (ns : List Name) (e : Environment),
      (stripRecursorRules e ns).quotInit = e.quotInit := by
    intro ns
    induction ns with
    | nil => intro e; rfl
    | cons n ns ih =>
      intro e
      show (stripRecursorRules (match e.find? n with
          | some (.recInfo info) => e.add (.recInfo { info with rules := [] })
          | _ => e) ns).quotInit = _
      rw [ih]
      split <;> rfl
  have hq : (stripRecursorRules outEnv names).quotInit = S0.quotInit := by
    rw [hstripQuot, hquot]; exact (addConstsEnv_quotInit _ _).symm
  exact ⟨stripRecursorRules.checkingValid hin H0 F hstripWF (fun n => (hfindEq n).symm) hq,
    fun C => stripRecursorRules.checkerEnv C H0 F hstripWF (fun n => (hfindEq n).symm) hq⟩

/-! ### The stripped environment of a nested run -/

theorem FoldSteps.recursorInfos_names {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name} :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names sourceEnv
        targetEnv),
      (FoldSteps.recursorInfos H).map (·.name) = names.map fun n => auxRec.getD n n
  | _, _, _, .nil => rfl
  | _, _, _, .cons h t => by
    simp only [FoldSteps.recursorInfos, List.map_cons, FoldSteps.recursorInfos_names t]
    rw [h.restored.restoration.name, h.restored.mappedName]

theorem FoldSteps.inductiveRecs_names {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name} :
    ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types sourceEnv
        targetEnv),
      (FoldSteps.inductiveRecs H).map (·.name) =
        types.map fun t => auxRec.getD (Lean.mkRecName t.name) (Lean.mkRecName t.name)
  | _, _, _, .nil => rfl
  | _, _, _, .cons h t => by
    simp only [FoldSteps.inductiveRecs, List.map_cons, FoldSteps.inductiveRecs_names t]
    rw [h.restored.recursor.restored.restoration.name, h.restored.recursor.restored.mappedName]

/-- The restored recursors of a run are those the rule pass strips. -/
theorem NestedRestorationFolds.rvals_names {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {auxRecNames : List Name} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) :
    H.rvals.map (·.name) = restoredRecursorNames auxRec types auxRecNames := by
  simp only [NestedRestorationFolds.rvals, List.map_append, FoldSteps.inductiveRecs_names,
    FoldSteps.recursorInfos_names, restoredRecursorNames, List.map_map, Function.comp_def]

/-- **The stripped restored environment of a nested run** is a valid checking environment
of the rule-free recursor stage `B.recursorVEnv` (and a checker environment). No premise mentions
the restored rules: the recursors are the base's translated recursor constants
(`RestoredBlockBase.rvalsTranslated`), and the shapes are their telescopes (`hshapes`). -/
theorem NestedRun.strippedValid {ves : VEnvs} {res : ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType} {decl : VInductDecl}
    {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes (ves.venv (if isUnsafe then .unsafe else .safe))
      decl lparams nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (B : RestoredBlockBase E.restoration (ves.venv (if isUnsafe then .unsafe else .safe)) decl
      lparams nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.loweredDecl = E.lowered.loweredDecl) (wf : ves.WF sourceProdEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Hparameters : decl.SourceParameterWF (ves.venv (if isUnsafe then .unsafe else .safe)))
    (hk : ∀ r ∈ E.restoration.rvals, r.k = false)
    (hshapes : ∀ r ∈ E.restoration.rvals,
      (if isUnsafe then DefinitionSafety.unsafe else .safe) ≤ (ConstantInfo.recInfo r).safety →
      ∃ cnparams indLevels ctorParams, Nonempty (VRecursorShape B.recursorVEnv r.name
        r.levelParams.length r.numParams cnparams r.numMotives r.numMinors r.numIndices
        r.getMajorInduct indLevels ctorParams)) :
    CheckingEnv.Valid (if isUnsafe then .unsafe else .safe) (stripRecursorRules outEnv
        (restoredRecursorNames (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv ∧
      (CheckerEnv (if isUnsafe then .unsafe else .safe) sourceProdEnv
          (ves.venv (if isUnsafe then .unsafe else .safe)) →
        CheckerEnv (if isUnsafe then .unsafe else .safe) (stripRecursorRules outEnv
          (restoredRecursorNames (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
            sourceTypes (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1))
          B.recursorVEnv) := by
  have hin : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe) sourceProdEnv
      (ves.venv (if isUnsafe then .unsafe else .safe)) := wf.toCheckingValid _
  have hwf : sourceProdEnv.constants.WF := hin.tr.map_wf
  have hlisted : ListedConstructorsPresent sourceProdEnv := by
    have h := E.lowered.constructors.headers.sourcePresent
    rw [E.lowered_c, E.context_env] at h
    exact h
  have hcoreE : TrInductDeclCore (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
      sourceTypes isUnsafe decl E.sourceCore.envTypes E.sourceCore.envCtors := by
    have h := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at h
    exact h
  have hcore : TrInductDeclCore (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
      sourceTypes isUnsafe decl B.install.venvTypes B.install.venvCtors :=
    B.sourceTranslations.core B.typesSource B.uvars B.numParams B.unsafeEq B.typesAdded
      B.constructorsAdded
  have hTeq : E.sourceCore.envTypes = B.install.venvTypes :=
    Option.some.inj (hcoreE.typesAdded.symm.trans hcore.typesAdded)
  obtain ⟨hperm, hfresh, hmap, hquot⟩ := E.restoration.kernelOrder hwf
  have Hexact := E.restoration.freshExtensionExact hwf
  obtain ⟨primitiveEntries, Hprim⟩ := E.primitiveSafe
  have hnonprimitive : ∀ ci ∈ AddInduct.consts E.restoration.ivals E.restoration.rvals,
      ¬ Kernel.Environment.primitives.contains ci.name := fun ci hci =>
    Hexact.transferForallSameTarget Hprim.fresh hwf Hprim.nonprimitive ci
      (hperm.mem_iff.mpr hci)
  have henvP : (decl.addProjs B.install.venvCtors).WF :=
    VEnv.WF.inductProjections (block := ⟨decl.typeConstants, decl.constructorConstants, [], [],
        decl.projectionEntries⟩)
      hin.tr.wf (TrInductDeclCore.envCtorsWF hcore hin.tr.wf)
      (TrInductDeclCore.sourceNames_nodup hcore)
      (TrInductDeclCore.typeHeadersWF hcore) (TrInductDeclCore.constructorUvars hcore)
      (TrInductDeclCore.constructorsWF hcore) Hparameters Hparameters.rawCtorShape
      rfl rfl rfl hcore.typesAdded hcore.ctorsAdded
  have htypeUvars : ∀ T ∈ decl.types, T.uvars = decl.uvars := by
    intro T hT
    rcases Lean4Lean.List.Forall₂.forall_exists_r hcore.types T hT with ⟨_, _, HT⟩
    rw [HT.header.uvars, hcore.uvars]
  have htypes := E.trTypes B hB
  rw [hTeq] at htypes
  have hR : (decl.addProjs B.install.venvCtors).addConstVals
      (B.sourceRecursors ++ B.auxiliaryRecursors) = some B.recursorVEnv := by
    have h := B.install.recursorsAdded.abstract
    rw [B.recursorValues] at h
    exact h
  have Howners : ConstructorOwnersPresent sourceProdEnv := wf.constructorOwners
  have h := stripRecursorRules.validOfBlock hin
    (by rw [VInductDecl.addTypes_eq_addConstVals]; exact hcore.typesAdded)
    (by rw [VInductDecl.addCtors_eq_addConstVals]; exact hcore.ctorsAdded)
    hR htypes B.rvalsTranslated hperm hfresh (Hexact.namesNodup hwf) hmap hquot henvP
    hnonprimitive hlisted htypeUvars (TrInductDeclCore.constructorUvars hcore)
    (E.inductInfosFromDecl B hB Hsources Howners) (E.cover B hB Hsources Howners)
    (E.constructorOwnersPresent Howners) (E.recMajor wf Hsources) hk hshapes
  rw [NestedRestorationFolds.rvals_names] at h
  exact h

end VerifyInductive
end Lean4Lean
