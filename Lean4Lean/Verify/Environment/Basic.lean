import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas

namespace Lean4Lean
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
  TrExprS env ci.levelParams [] ci.value! ci'.value

variable (safety : DefinitionSafety) (env : VEnv) in
def TrOpaqueVal (ci : OpaqueVal) (ci' : VDefVal) : Prop :=
  TrConstVal safety env (.opaqueInfo ci) ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] ci.value ci'.value

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

/-- This definition is essentially a `sorry`: it should relate `addInductive`'s
effect on the constant map to `VEnv.addInduct` (which is itself a `sorry`,
see `Lean4Lean.Theory.Inductive`), but it currently has no constructors, so the
`TrEnv'.induct` case below can never fire and environments containing inductives
are outside the verified `TrEnv` relation. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  -- TODO

nonrec theorem AddInduct.to_addInduct
    (H : AddInduct m₁ env₁ decl m₂ env₂) : env₁.addInduct decl = some env₂ :=
  nomatch H

def ConstMap.addMutualDefinitions (C : ConstMap) (vs : List DefinitionVal) : ConstMap :=
  vs.foldl (fun C v => C.insert v.name (.defnInfo v)) C

def mutualOpaqueHeader (v : DefinitionVal) : OpaqueVal := {
  v.toConstantVal with
  value := v.value
  isUnsafe := v.safety == .unsafe
  all := v.all }

def ConstMap.addMutualOpaqueHeaders (C : ConstMap) (vs : List DefinitionVal) : ConstMap :=
  vs.foldl (fun C v => C.insert v.name (.opaqueInfo (mutualOpaqueHeader v))) C

def ConstMap.MutualFresh (C : ConstMap) (vs : List DefinitionVal) : Prop :=
  (∀ v ∈ vs, C.find? v.name = none) ∧ (vs.map (fun v => v.name)).Nodup

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' {} false .empty
  | block :
    C.find? ci.name = none →
    ¬safety ≤ ci.safety →
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
  | theorem {ci' : VDefVal} :
    TrDefVal safety env (.thmInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  | unsafeDefn {ci' : VDefVal} :
    TrConstVal safety env (.defnInfo ci) ci'.toVConstVal →
    C.find? ci.name = none → ci'.toVConstant.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrExprS env' ci.levelParams [] ci.value ci'.value →
    ci'.WF env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  | opaque {ci' : VDefVal} :
    TrOpaqueVal safety env ci ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | mutual :
    List.Forall₂ (fun v v' =>
      TrConstVal safety env (.defnInfo v) v'.toVConstVal) vs vs' →
    ConstMap.MutualFresh C vs →
    (∀ v' ∈ vs', v'.toVConstant.WF env) →
    env.addMutualHeaders vs' = some headers →
    (∀ v' ∈ vs', headers.constants v'.name = some v'.toVConstant) →
    List.Forall₂ (fun v v' =>
      TrExprS headers v.levelParams [] v.value v'.value) vs vs' →
    (∀ v' ∈ vs', v'.WF headers) →
    TrEnv' C Q env →
    TrEnv' (ConstMap.addMutualDefinitions C vs) Q (headers.addMutualDefEqs vs')
  | mutualCheck :
    List.Forall₂ (fun v v' =>
      TrConstVal safety env (.opaqueInfo (mutualOpaqueHeader v)) v'.toVConstVal) vs vs' →
    ConstMap.MutualFresh C vs →
    (∀ v' ∈ vs', v'.toVConstant.WF env) →
    env.addMutualHeaders vs' = some headers →
    TrEnv' C Q env →
    TrEnv' (ConstMap.addMutualOpaqueHeaders C vs) Q headers
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    AddInduct C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

private theorem VEnv.WF.addMutualHeaders
    {env headers : VEnv} {vs' : List VDefVal}
    (H : env.WF)
    (htypes : ∀ v' ∈ vs', v'.toVConstant.WF env)
    (hadd : env.addMutualHeaders vs' = some headers) : headers.WF := by
  obtain ⟨ds, H⟩ := H
  induction vs' generalizing env headers ds with
  | nil =>
    simp [VEnv.addMutualHeaders] at hadd
    subst headers
    exact ⟨ds, H⟩
  | cons v vs ih =>
    cases hhead : env.addConst v.name v.toVConstant with
    | none => simp [VEnv.addMutualHeaders, hhead] at hadd
    | some next =>
      simp [VEnv.addMutualHeaders, hhead] at hadd
      apply ih (env := next) (ds := .axiom v.toVConstVal :: ds) ?_ hadd
      · exact .decl (.axiom (htypes v (by simp)) hhead) H
      · intro w hw
        exact (htypes w (by simp [hw])).mono (VEnv.addConst_le hhead)

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | @block _ _ _ ci _ _ _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl (VDecl.WF.block (n := ci.name))⟩
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | «theorem» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | unsafeDefn h1 _ h2 h3 _ h4 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .unsafeDef h2 (this ▸ h3) h4⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | «mutual» _ _ htypes hadd hcontains _ hbodies _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .mutual htypes hadd hcontains hbodies⟩
  | mutualCheck _ _ htypes hadd _ ih =>
    exact ih.addMutualHeaders htypes hadd
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | induct _ h _ _ => exact nomatch h
