import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Std.SMap
import Lean4Lean.Declaration

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]

def _root_.Lean.ConstantInfo.safety (ci : ConstantInfo) : DefinitionSafety :=
  if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] (ci.value! (allowOpaque := true)) ci'.value

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

/-- The step an abstract environment takes when `ci`, modelled by `ci'`, is added.

At safety levels where the declaration is visible the constant is added; where it is not, the
environment is unchanged, matching `TrEnv'.ignore`. Stating this rather than just `venv ≤ venv'`
is what lets a caller see *which* constant a step added. -/
def VEnv.AddConst (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VConstant) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    TrConstant safety venv ci ci' ∧ ci'.WF venv ∧ venv.addConst ci.name ci' = some venv'
  else
    venv' = venv

theorem VEnv.AddConst.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddConst venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddConst at H; split at H
  · exact addConst_le H.2.2
  · exact H ▸ VEnv.LE.rfl

/-- As `VEnv.AddConst`, for a definition: the constant is added and then its defining equation,
matching `TrEnv'.defn`. -/
def VEnv.AddDef (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VDefVal) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    ∃ base, TrDefVal safety venv ci ci' ∧ ci'.WF venv ∧
      venv.addConst ci.name ci'.toVConstant = some base ∧
      venv' = base.addDefEq ci'.toDefEq
  else
    venv' = venv

theorem VEnv.AddDef.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddDef venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddDef at H; split at H
  · obtain ⟨base, _, _, hadd, rfl⟩ := H
    exact (addConst_le hadd).trans (VEnv.addDefEq_le ..)
  · exact H ▸ VEnv.LE.rfl

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → VEnv → Prop)
    (m : ConstMap) (env : VEnv) : Prop :=
  ∃ levelParams type env',
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    m.find? name = none ∧
    env.addConst name ci' = some env' ∧
    P (m.insert name ci) env'

theorem AddQuot1.to_addQuot
    (H1 : ∀ m env, P m env → f env = some env')
    (m env) (H : AddQuot1 name kind ci' P m env) :
    env.addConst name ci' >>= f = some env' := by
  let ⟨_, _, _, h1, _, h2, h3⟩ := H
  simpa using ⟨_, h2, H1 _ _ h3⟩

theorem AddQuot1.le
    (H1 : ∀ m env, P m env → env ≤ env₀)
    (m env) (H : AddQuot1 name kind ci' P m env) : env ≤ env₀ :=
  let ⟨_, _, _, _, _, h2, h3⟩ := H
  .trans (VEnv.addConst_le h2) (H1 _ _ h3)

def AddQuot (m₁ m₂ : ConstMap) (env₁ env₂ : VEnv) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m₁) (env := env₁) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotIndConst (· = m₂ ∧ ·.addDefEq quotDefEq = env₂)

nonrec theorem AddQuot.to_addQuot (H : AddQuot m₁ m₂ env₁ env₂) : env₁.addQuot = some env₂ :=
  open AddQuot1 in (to_addQuot <| to_addQuot <| to_addQuot <| to_addQuot (by simp)) _ _ H

nonrec theorem AddQuot.le (H : AddQuot m₁ m₂ env₁ env₂) : env₁ ≤ env₂ :=
  open AddQuot1 in (le <| le <| le <| le fun _ _ h => h.2 ▸ VEnv.addDefEq_le) _ _ H

/-! ### Inserting a block of constants into the constant map

`insertConsts` is the `SMap` fold the kernel performs for every constant of a block.
Its lemmas need only well-formedness of the starting map, freshness of the block's names
in it and their duplicate-freedom. -/

/-- Insert a block of constant infos into the constant map, keyed by name. -/
def insertConsts (C : ConstMap) (cis : List ConstantInfo) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name ci) C

theorem insertConsts_cons {C : ConstMap} {ci : ConstantInfo} {cis : List ConstantInfo} :
    insertConsts C (ci :: cis) = insertConsts (C.insert ci.name ci) cis := rfl

/-- Fresh, duplicate-free names stay fresh after inserting the head of the block. -/
theorem insertConsts_fresh_tail {C : ConstMap} {ci : ConstantInfo} {cis : List ConstantInfo}
    (wf : C.map₂.WF) (hfr : ∀ d ∈ ci :: cis, C.find? d.name = none)
    (hnd : ((ci :: cis).map (·.name)).Nodup) :
    ∀ d ∈ cis, (C.insert ci.name ci).find? d.name = none := by
  rw [List.map_cons, List.nodup_cons] at hnd
  intro d hd
  exact SMap.find?_insert_none wf (fun e => hnd.1 (e ▸ List.mem_map_of_mem hd)) (hfr d (.tail _ hd))

theorem insertConsts_wf : ∀ {cis : List ConstantInfo} {C : ConstMap}, C.WF →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup → (insertConsts C cis).WF
  | [], _, hC, _, _ => hC
  | ci :: cis, C, hC, hfr, hnd => by
    rw [insertConsts_cons]
    refine insertConsts_wf (hC.insert _ _ (hfr _ (.head _)))
      (insertConsts_fresh_tail hC.map₂ hfr hnd) ?_
    rw [List.map_cons, List.nodup_cons] at hnd; exact hnd.2

theorem insertConsts_find?_mono {cis : List ConstantInfo} {C : ConstMap} {x v} (wf : C.map₂.WF)
    (hne : ∀ ci ∈ cis, ci.name ≠ x) (h : C.find? x = some v) :
    (insertConsts C cis).find? x = some v := by
  unfold insertConsts
  exact SMap.insertList_find?_mono (nm := (·.name)) (val := id) wf hne h

/-- A constant resolvable before inserting a block of fresh names is still resolvable, to
the same value, afterwards. -/
theorem insertConsts_find?_mono_of_fresh {cis : List ConstantInfo} {C : ConstMap} {x v}
    (wf : C.map₂.WF) (hfr : ∀ ci ∈ cis, C.find? ci.name = none) (h : C.find? x = some v) :
    (insertConsts C cis).find? x = some v :=
  insertConsts_find?_mono wf (fun ci hci e => by have := hfr ci hci; rw [e, h] at this; cases this) h

theorem insertConsts_find?_none : ∀ {cis : List ConstantInfo} {C : ConstMap} {x}, C.map₂.WF →
    (∀ ci ∈ cis, ci.name ≠ x) → C.find? x = none → (insertConsts C cis).find? x = none
  | [], _, _, _, _, h => h
  | ci :: cis, C, x, wf, hne, h => by
    rw [insertConsts_cons]
    exact insertConsts_find?_none (SMap.insert_map₂ wf) (fun d hd => hne d (.tail _ hd))
      (SMap.find?_insert_none wf (hne ci (.head _)) h)

/-- A constant resolvable after inserting a block was resolvable before, or is one of the
block's constants under its own name. -/
theorem insertConsts_find? : ∀ {cis : List ConstantInfo} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertConsts C cis).find? name = some ci →
    C.find? name = some ci ∨ ci ∈ cis ∧ ci.name = name
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    rw [insertConsts_cons] at h
    have hnd' := hnd; rw [List.map_cons, List.nodup_cons] at hnd'
    rcases insertConsts_find? (hC.insert _ _ (hfr _ (.head _)))
        (insertConsts_fresh_tail hC.map₂ hfr hnd) hnd'.2 h with h | ⟨he, h1⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h; exact .inr ⟨.head _, by simpa using hb⟩
      · exact .inl h
    · exact .inr ⟨.tail _ he, h1⟩

/-- Every constant of an inserted block resolves to itself under its name. -/
theorem insertConsts_find?_self : ∀ {cis : List ConstantInfo} {C : ConstMap}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    ∀ ci ∈ cis, (insertConsts C cis).find? ci.name = some ci
  | [], _, _, _, _, _, h => by cases h
  | d :: ds, C, hC, hfr, hnd, ci, hci => by
    rw [insertConsts_cons]
    have hnd' := hnd; rw [List.map_cons, List.nodup_cons] at hnd'
    rcases List.mem_cons.1 hci with rfl | hci'
    · refine insertConsts_find?_mono (hC.insert _ _ (hfr _ (.head _))).map₂
        (fun e he heq => hnd'.1 (heq ▸ List.mem_map_of_mem he)) ?_
      rw [hC.find?_insert, if_pos (by simp)]
    · exact insertConsts_find?_self (hC.insert _ _ (hfr _ (.head _)))
        (insertConsts_fresh_tail hC.map₂ hfr hnd) hnd'.2 ci hci'

/-! ### Translation of an inductive block -/

/-- Translation of one type former with its constructors, at safety level `safety`. The
type former's `inductInfo` translates in the environment before the block (`env₁`); the
constructors' `ctorInfo`s in the environment holding the type formers (`envT`), where their
types are meaningful, and their `numParams + numFields` is the Π-arity of the model type,
which is how the kernel's `nfields` reaches the ι bookkeeping (`AddInduct.ctor_find`).
`ival.ctors` lists exactly the translated constructors. -/
structure TrIndType (safety : DefinitionSafety) (env₁ envT : VEnv) (ival : InductiveVal)
    (cvals : List ConstructorVal) (t : VInductiveType) : Prop where
  tr : TrConstVal safety env₁ (.inductInfo ival) t.toVConstVal
  ctor_names : ival.ctors = cvals.map (·.name)
  ctors : List.Forall₂ (fun cval c => TrConstVal safety envT (.ctorInfo cval) c ∧
    cval.numParams + cval.numFields = c.type.piArity) cvals t.ctors

/-- Translation of one recursor, at safety level `safety`: its `recInfo` in the environment
holding the type formers and constructors (`envC`), the telescope split and `k` flag copied,
and its rules matched one-to-one with the model's, each firing on the same constructor
(whose parameter count is read off its `ctorInfo` in the final map `m₂`, so that the
auxiliary recursors of nested blocks, which fire on older constructors, are covered) with
the same field count and a reduct translating in the environment holding the recursors
(`envR`, since reducts mention the recursors of the block). -/
structure TrRecursor (safety : DefinitionSafety) (envC envR : VEnv) (m₂ : ConstMap)
    (rval : RecursorVal) (r : VRecursor) : Prop where
  tr : TrConstVal safety envC (.recInfo rval) r.toVConstVal
  all : r.all = rval.all
  numParams : r.numParams = rval.numParams
  numMotives : r.numMotives = rval.numMotives
  numMinors : r.numMinors = rval.numMinors
  numIndices : r.numIndices = rval.numIndices
  k : r.k = rval.k
  rules : List.Forall₂ (fun rule ru => ru.ctor = rule.ctor ∧ ru.nfields = rule.nfields ∧
    (∃ cval : ConstructorVal,
      m₂.find? rule.ctor = some (.ctorInfo cval) ∧ ru.ctorParams = cval.numParams) ∧
    TrExprS envR rval.levelParams [] rule.rhs ru.rhs) rval.rules r.rules

/-- The constants an inductive block adds to the constant map, by kind: all type formers,
all constructors (in block order), all recursors. This is the model's stage order
(`VInductDecl.consts`); the kernel inserts them in this order for a non-nested block
(`Inductive/Add.lean`, `run`) and type by type — each type former, its constructors, its
recursor, then the auxiliary recursors — for a nested one (`Environment.addInductive`), so
`AddInduct` records the actual insertion order separately (`order`). -/
def AddInduct.consts (ivals : List (InductiveVal × List ConstructorVal))
    (rvals : List RecursorVal) : List ConstantInfo :=
  ivals.map (.inductInfo ·.1) ++ ivals.flatMap (·.2.map .ctorInfo) ++ rvals.map .recInfo

/-- Refinement witness that translating an inductive declaration extends the constant
map `m₁ → m₂` and model environment `env₁ → env₂` coherently, at safety level `safety`,
in the `AddQuot`/`TrDefBlock` idiom: it records the kernel-side data (`ivals`, `rvals`),
the four successful stages of `VEnv.addInduct` (`stT`…`stP`, with their intermediate
environments), the translation of each type former, constructor and recursor at the
stage where the kernel checks it (`types`, `recs`), freshness of every inserted name in
`m₁`, and that `m₂` is the insertion of the block's constants in the order the kernel
inserted them (`order`, a permutation of `consts`). Everything else — `env_eq`, `wf`,
`find?_mono`, `value_find`, `rec_find`, `rec_reg`, `ctor_find` — is derived below. -/
structure AddInduct (safety : DefinitionSafety) (m₁ : ConstMap) (env₁ : VEnv)
    (decl : VInductDecl) (m₂ : ConstMap) (env₂ : VEnv) where
  ivals : List (InductiveVal × List ConstructorVal)
  rvals : List RecursorVal
  envT : VEnv
  envC : VEnv
  envR : VEnv
  stT : decl.addTypes env₁ = some envT
  stC : decl.addCtors envT = some envC
  stR : decl.addRecs envC = some envR
  stP : decl.addRules envR = some env₂
  types : List.Forall₂ (fun iv t => TrIndType safety env₁ envT iv.1 iv.2 t) ivals decl.types
  recs : List.Forall₂ (TrRecursor safety envC envR m₂) rvals decl.recs
  /-- The block's constants in the order the kernel inserted them. -/
  order : List ConstantInfo
  order_perm : order.Perm (AddInduct.consts ivals rvals)
  fresh : ∀ ci ∈ AddInduct.consts ivals rvals, m₁.find? ci.name = none
  map_eq : m₂ = insertConsts m₁ order

namespace AddInduct

variable {safety : DefinitionSafety} {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {decl : VInductDecl}

theorem env_eq (H : AddInduct safety m₁ env₁ decl m₂ env₂) : env₁.addInduct decl = some env₂ := by
  rw [VEnv.addInduct, VInductDecl.addTypesCtorsRecs, VInductDecl.addTypesCtors, H.stT]
  simp [H.stC, H.stR, H.stP]

theorem addTypesCtors (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    decl.addTypesCtors env₁ = some H.envC := by
  rw [VInductDecl.addTypesCtors, H.stT]; simp [H.stC]

theorem addTypesCtorsRecs (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    decl.addTypesCtorsRecs env₁ = some H.envR := by
  rw [VInductDecl.addTypesCtorsRecs, H.addTypesCtors]; simp [H.stR]

theorem le (H : AddInduct safety m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ := VEnv.addInduct_le H.env_eq
theorem leR (H : AddInduct safety m₁ env₁ decl m₂ env₂) : H.envR ≤ env₂ := VEnv.addRules_le H.stP

/-- Membership in the block's constants, by kind. -/
theorem mem_consts {ivals : List (InductiveVal × List ConstructorVal)} {rvals : List RecursorVal}
    {ci : ConstantInfo} : ci ∈ consts ivals rvals ↔
      (∃ iv ∈ ivals, ci = .inductInfo iv.1) ∨
      (∃ iv ∈ ivals, ∃ cval ∈ iv.2, ci = .ctorInfo cval) ∨
      (∃ rval ∈ rvals, ci = .recInfo rval) := by
  simp only [consts, List.mem_append, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ((⟨iv, hiv, rfl⟩ | ⟨iv, hiv, cval, hcval, rfl⟩) | ⟨rval, hrval, rfl⟩)
    · exact .inl ⟨iv, hiv, rfl⟩
    · exact .inr (.inl ⟨iv, hiv, cval, hcval, rfl⟩)
    · exact .inr (.inr ⟨rval, hrval, rfl⟩)
  · rintro (⟨iv, hiv, rfl⟩ | ⟨iv, hiv, cval, hcval, rfl⟩ | ⟨rval, hrval, rfl⟩)
    · exact .inl (.inl ⟨iv, hiv, rfl⟩)
    · exact .inl (.inr ⟨iv, hiv, cval, hcval, rfl⟩)
    · exact .inr ⟨rval, hrval, rfl⟩

/-- The block's constants carry no value, in particular none for δ-reduction. -/
theorem novalue {ivals : List (InductiveVal × List ConstructorVal)} {rvals : List RecursorVal} :
    ∀ ci ∈ consts ivals rvals, ci.value? = none ∧ ci.deltaValue? = none := by
  intro ci hci
  rcases mem_consts.1 hci with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem types_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (H.ivals.map (·.1.name)) = decl.types.map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.tr.2) H.types

theorem ctors_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    ((H.ivals.flatMap (·.2)).map (·.name)) = (decl.types.flatMap (·.ctors)).map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.1.2)
    (List.Forall₂.flatMap (fun _ _ h => h.ctors) H.types)

theorem recs_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (H.rvals.map (·.name)) = decl.recs.map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.tr.2) H.recs

/-- The names of the block's constants, in insertion order. -/
theorem consts_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (consts H.ivals H.rvals).map (·.name) =
      decl.types.map (·.name) ++ (decl.types.flatMap (·.ctors)).map (·.name) ++
        decl.recs.map (·.name) := by
  rw [← H.types_names, ← H.ctors_names, ← H.recs_names]
  simp only [consts, List.map_append, List.map_map, List.map_flatMap, Function.comp_def]
  rfl

/-- The names of the block's constants are distinct: each stage's names are distinct
(the `addConst` folds succeed) and a later stage's names are fresh in the environment
where the earlier stages' names are already bound. -/
theorem names_nodup (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    ((consts H.ivals H.rvals).map (·.name)).Nodup := by
  rw [H.consts_names, List.nodup_append, List.nodup_append]
  refine ⟨⟨VEnv.addTypes_nodup H.stT, VEnv.addCtors_nodup H.stC, fun a ha b hb hab => ?_⟩,
    VEnv.addRecs_nodup H.stR, fun a ha b hb hab => ?_⟩
  · subst hab
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
    obtain ⟨c, hc, hcn⟩ := List.mem_map.1 hb
    obtain ⟨t', ht', hc'⟩ := List.mem_flatMap.1 hc
    have h1 := VEnv.addTypes_find H.stT t ht
    have h2 := VEnv.addCtors_fresh H.stC t' ht' c hc'
    rw [hcn, h1] at h2; cases h2
  · subst hab
    obtain ⟨r, hr, hrn⟩ := List.mem_map.1 hb
    have h2 := VEnv.addRecs_fresh H.stR r hr
    rw [hrn] at h2
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
      have h1 := (VEnv.addCtors_le H.stC).constants (VEnv.addTypes_find H.stT t ht)
      rw [h1] at h2; cases h2
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
      obtain ⟨t', ht', hc'⟩ := List.mem_flatMap.1 hc
      have h1 := VEnv.addCtors_find H.stC t' ht' c hc'
      rw [h1] at h2; cases h2

/-- Freshness, in the kernel's insertion order. -/
theorem order_fresh (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    ∀ ci ∈ H.order, m₁.find? ci.name = none :=
  fun ci h => H.fresh ci (H.order_perm.mem_iff.1 h)

/-- Distinctness of the names, in the kernel's insertion order. -/
theorem order_nodup (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (H.order.map (·.name)).Nodup :=
  (H.order_perm.map _).nodup_iff.2 H.names_nodup

/-- Adding an inductive block preserves constant-map well-formedness. -/
theorem wf (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF) : m₂.WF :=
  H.map_eq ▸ insertConsts_wf wf H.order_fresh H.order_nodup

/-- A constant resolvable before adding an inductive block is still resolvable, to the
same value, afterwards: every name the block inserts is fresh in `m₁`. -/
theorem find?_mono {x v} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₁.find? x = some v) : m₂.find? x = some v := by
  rw [H.map_eq]; exact insertConsts_find?_mono_of_fresh wf.map₂ H.order_fresh h

/-- A constant resolvable after adding an inductive block was resolvable before, or is
one of the block's constants under its own name. -/
theorem find? {name ci} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₂.find? name = some ci) :
    m₁.find? name = some ci ∨ ci ∈ consts H.ivals H.rvals ∧ ci.name = name := by
  rw [H.map_eq] at h
  rcases insertConsts_find? wf H.order_fresh H.order_nodup h with h | ⟨hci, hn⟩
  · exact .inl h
  · exact .inr ⟨H.order_perm.mem_iff.1 hci, hn⟩

/-- Every constant of the block resolves to itself in `m₂`. -/
theorem find?_self {ci} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (hci : ci ∈ consts H.ivals H.rvals) : m₂.find? ci.name = some ci := by
  rw [H.map_eq]
  exact insertConsts_find?_self wf H.order_fresh H.order_nodup ci (H.order_perm.mem_iff.2 hci)

/-- A constant with a δ-value resolvable after the block was resolvable before: the
block's constants have none. -/
theorem value_find {name : Name} {ci : ConstantInfo} {v : Expr}
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₂.find? name = some ci) (hv : ci.deltaValue? = some v) : m₁.find? name = some ci := by
  rcases H.find? wf h with h | ⟨hci, _⟩
  · exact h
  · rw [(novalue ci hci).2] at hv; cases hv

/-- A kernel recursor resolvable after the block was resolvable before, or is one of the
block's recursors: then some `r ∈ decl.recs` carries its name and telescope split, and
every kernel rule has a model rule with the same constructor (of the parameter count read
off its `ctorInfo` in `m₂`), the same field count, and a closed reduct translating the
kernel rule's reduct. This is what ties a kernel recursor lookup to `VEnv.addInduct_pat`. -/
theorem rec_find {recName : Name} {rval : RecursorVal}
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₂.find? recName = some (.recInfo rval)) :
    m₁.find? recName = some (.recInfo rval) ∨
    ∃ r ∈ decl.recs,
      r.name = recName ∧ r.getMajorIdx = rval.getMajorIdx ∧ r.numParams = rval.numParams ∧
      r.numMotives = rval.numMotives ∧ r.numMinors = rval.numMinors ∧
      r.numIndices = rval.numIndices ∧
      ∀ rule ∈ rval.rules, ∃ ru ∈ r.rules,
        ru.ctor = rule.ctor ∧ ru.nfields = rule.nfields ∧
        (∃ cval : ConstructorVal,
          m₂.find? rule.ctor = some (.ctorInfo cval) ∧ ru.ctorParams = cval.numParams) ∧
        ru.rhs.Closed ∧ TrExprS env₂ rval.levelParams [] rule.rhs ru.rhs := by
  rcases H.find? wf h with h | ⟨hci, hname⟩
  · exact .inl h
  · right
    rcases mem_consts.1 hci with ⟨_, _, h'⟩ | ⟨_, _, _, _, h'⟩ | ⟨_, hrval, h'⟩ <;> cases h'
    obtain ⟨r, hr, htr⟩ := H.recs.forall_exists_l _ hrval
    refine ⟨r, hr, htr.tr.2.symm.trans hname, ?_, htr.numParams, htr.numMotives,
      htr.numMinors, htr.numIndices, fun rule hrule => ?_⟩
    · simp only [VRecursor.getMajorIdx, RecursorVal.getMajorIdx, htr.numParams, htr.numMotives,
        htr.numMinors, htr.numIndices]
    · obtain ⟨ru, hru, h1, h2, h3, h4⟩ := htr.rules.forall_exists_l rule hrule
      exact ⟨ru, hru, h1, h2, h3, VEnv.addRules_closed H.stP r hr ru hru, h4.mono H.leR⟩

/-- The theory→kernel dual of `rec_find`: each `r ∈ decl.recs` is registered in `m₂` as a
kernel `recInfo` under `r.name`, with the same telescope split, and each of its rules is
found (keyed by constructor, uniquely by `VInductDecl.WF.rules_nodup`) among the kernel
recursor's rules, with the same field count, the constructor's parameter count, and a
reduct translating the kernel rule's. -/
theorem rec_reg {r : VRecursor} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (hwf : decl.WF env₁) (hr : r ∈ decl.recs) :
    ∃ rval : RecursorVal,
      m₂.find? r.name = some (.recInfo rval) ∧
      r.getMajorIdx = rval.getMajorIdx ∧ r.numParams = rval.numParams ∧
      r.numMotives = rval.numMotives ∧ r.numMinors = rval.numMinors ∧
      r.numIndices = rval.numIndices ∧
      ∀ ru ∈ r.rules, ∃ rule : RecursorRule,
        rval.rules.find? (·.ctor == ru.ctor) = some rule ∧ ru.nfields = rule.nfields ∧
        (∃ cval : ConstructorVal,
          m₂.find? ru.ctor = some (.ctorInfo cval) ∧ ru.ctorParams = cval.numParams) ∧
        TrExprS env₂ rval.levelParams [] rule.rhs ru.rhs := by
  obtain ⟨rval, hrval, htr⟩ := H.recs.forall_exists_r r hr
  have hmem : ConstantInfo.recInfo rval ∈ consts H.ivals H.rvals :=
    mem_consts.2 (.inr (.inr ⟨rval, hrval, rfl⟩))
  refine ⟨rval, ?_, ?_, htr.numParams, htr.numMotives, htr.numMinors, htr.numIndices,
    fun ru hru => ?_⟩
  · have := H.find?_self wf hmem; rwa [htr.tr.2] at this
  · simp only [VRecursor.getMajorIdx, RecursorVal.getMajorIdx, htr.numParams, htr.numMotives,
      htr.numMinors, htr.numIndices]
  · obtain ⟨rule, hrule, h1, h2, h3, h4⟩ := htr.rules.forall_exists_r ru hru
    have hnd : (rval.rules.map (·.ctor)).Nodup := by
      rw [List.Forall₂.map_eq (fun _ _ h => h.1.symm) htr.rules]; exact hwf.rules_nodup r hr
    refine ⟨rule, ?_, h2, by rw [h1]; exact h3, h4.mono H.leR⟩
    rw [h1]; exact List.find?_eq_of_nodup_map hnd rule hrule

/-- A kernel constructor resolvable after the block was resolvable before, or is one of
the block's constructors: then it has a rule in one of the block's recursors, with the
constructor's parameter count (`rules_own_params`) and field count (its type's Π-arity is
`ctorParams + nfields` by `rules_ctor_shape`, and `numParams + numFields` by `TrIndType`). -/
theorem ctor_find {ctorName : Name} {cval : ConstructorVal}
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF) (hwf : decl.WF env₁)
    (h : m₂.find? ctorName = some (.ctorInfo cval)) :
    m₁.find? ctorName = some (.ctorInfo cval) ∨
    ∃ t ∈ decl.types, ∃ c ∈ t.ctors, c.name = ctorName ∧
      ∃ r ∈ decl.recs, ∃ ru ∈ r.rules,
        ru.ctor = ctorName ∧ ru.ctorParams = cval.numParams ∧ ru.nfields = cval.numFields ∧
        r.numParams = cval.numParams := by
  rcases H.find? wf h with h' | ⟨hci, hname⟩
  · exact .inl h'
  · right
    rcases mem_consts.1 hci with ⟨_, _, h'⟩ | ⟨iv, hiv, _, hcval, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
    obtain ⟨t, ht, htr⟩ := H.types.forall_exists_l iv hiv
    obtain ⟨c, hc, hctr, harity⟩ := htr.ctors.forall_exists_l _ hcval
    have hcn : c.name = ctorName := hctr.2.symm.trans hname
    obtain ⟨r, hr, ru, hru, hruc⟩ := hwf.ctors_have_rules t ht c hc
    have hown : ru.ctorParams = r.numParams := hwf.rules_own_params r hr ru hru
    obtain ⟨rval, -, hrtr⟩ := H.recs.forall_exists_r r hr
    obtain ⟨rule, -, h1, -, ⟨cval'', hcf, hcp⟩, -⟩ := hrtr.rules.forall_exists_r ru hru
    rw [← h1, hruc, hcn, h] at hcf; cases hcf
    obtain ⟨ci, hci', hcs⟩ := hwf.rules_ctor_shape H.envC H.addTypesCtors r hr ru hru
    rw [hruc, VEnv.addCtors_find H.stC t ht c hc] at hci'; cases hci'
    refine ⟨t, ht, c, hc, hcn, r, hr, ru, hru, hruc.trans hcn, hcp, ?_, hown.symm.trans hcp⟩
    have := hcs.1; omega

end AddInduct

/-- Insert a whole block of definitions into the constant map. -/
def insertDefs (C : ConstMap) (cis : List DefinitionVal) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name (.defnInfo ci)) C

variable (safety : DefinitionSafety) (env env' : VEnv) in
/-- Translation data for a mutual block: the headers are translated against the environment
before the block is added, the values against the environment that already has every constant
of the block, mirroring the kernel adding them all as axioms first. -/
def TrDefBlock (cis : List DefinitionVal) (cis' : List VDefVal) : Prop :=
  List.Forall₂ (fun ci ci' =>
    TrConstVal safety env (.defnInfo ci) ci'.toVConstVal ∧
    TrExprS env' ci.levelParams [] ci.value ci'.value) cis cis'

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' {} false .empty
  | ignore :
    C.find? ci.name = none → ¬safety ≤ ci.safety →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci' = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  /-- A mutual block, and an unsafe definition as the one-element case. -/
  | mutualDef {cis : List DefinitionVal} {cis' : List VDefVal} :
    TrDefBlock safety env env' cis cis' →
    -- the block's names are distinct; `addMutual` checks this, as does lean4#14632
    (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci' ∈ cis', ci'.toVConstant.WF env) →
    env.addConsts cis' = some env' →
    (∀ ci' ∈ cis', ci'.WF env') →
    TrEnv' C Q env →
    TrEnv' (insertDefs C cis) Q (env'.addDefEqs cis')
  | thm {ci' : VDefVal} :
    TrDefVal safety env (.thmInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  | opaque {ci' : VDefVal} :
    TrDefVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    AddInduct safety C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | mutualDef _ _ _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .mutualDef h2 h3 h4⟩
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.env_eq⟩
