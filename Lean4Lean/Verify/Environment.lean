import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

def isAsSafeAs : DefinitionSafety → ConstantInfo → Bool
  | .unsafe, _ => true
  | .partial, ci => !ci.isUnsafe
  | .safe, ci => !ci.isUnsafe && !ci.isPartial

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  isAsSafeAs safety ci ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] ci.value! ci'.value

def AddQuot1 (env : VEnv) (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → Prop)
    (m : ConstMap) : Prop :=
  ∃ levelParams type,
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    P (m.insert name ci)

def AddQuot (env : VEnv) (m1 m2 : ConstMap) : Prop :=
  AddQuot1 env ``Quot .type quotConst (m := m1) <|
  AddQuot1 env ``Quot.mk .ctor quotMkConst <|
  AddQuot1 env ``Quot.lift .lift quotLiftConst <|
  AddQuot1 env ``Quot.ind .ind quotMkConst (Eq m2)

inductive AddInduct (m1 : ConstMap) (decl : VInductDecl) (m2 : ConstMap) : Prop
  -- TODO

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' {} false .empty
  | block :
    ¬isAsSafeAs safety ci →
    env.addConst ci.name none = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env'
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    ci'.WF env →
    env.addConst ci.name (some ci') = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    ci'.WF env →
    env.addConst ci.name (some ci'.toVConstant) = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  | opaque {ci' : VDefVal} :
    TrDefVal safety env (.opaqueInfo ci) ci' →
    ci'.WF env →
    env.addConst ci.name (some ci'.toVConstant) = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    AddQuot env C C' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    env.addInduct decl = some env' →
    AddInduct C decl C' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.WF (H : TrEnv' C Q env venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | block _ h _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .block h⟩
  | «axiom» _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | «opaque» h1 h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | quot h1 h2 _ _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2⟩
  | induct h1 h2 _ _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2⟩

nonrec theorem TrEnv.WF (H : TrEnv safety env venv) : venv.WF := H.WF
