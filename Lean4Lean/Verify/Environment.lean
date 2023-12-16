import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas

namespace Lean4Lean
open Lean

def isAsSafeAs : DefinitionSafety → ConstantInfo → Bool
  | .unsafe, _ => true
  | .partial, ci => !ci.isUnsafe
  | .safe, ci => !ci.isUnsafe && !ci.isPartial

def TrConstant (safety : DefinitionSafety) (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  isAsSafeAs safety ci ∧ ci.levelParams.length = ci'.uvars ∧
  TrExpr ci.levelParams [] ci.type ci'.type

def TrConstVal (safety : DefinitionSafety) (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety ci ci'.toVConstant ∧ ci.name = ci'.name

def TrDefVal (safety : DefinitionSafety) (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety ci ci'.toVConstVal ∧
  TrExpr ci.levelParams [] ci.value! ci'.value

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → Prop)
    (m : ConstMap) : Prop :=
  ∃ levelParams type,
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe ci ci' ∧
    P (m.insert name ci)

def AddQuot (m1 m2 : ConstMap) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m1) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotMkConst (Eq m2)

def AddInduct (m1 : ConstMap) (decl : VInductDecl) (m2 : ConstMap) : Prop := sorry

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' {} false .empty
  | block :
    ¬isAsSafeAs safety ci →
    env.addConst ci.name none = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env'
  | axiom :
    TrConstant safety (.axiomInfo ci) ci' →
    ci'.WF env →
    env.addConst ci.name (some ci') = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety (.defnInfo ci) ci' →
    ci'.WF env →
    env.addConst ci.name (some ci'.toVConstant) = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  | opaque {ci' : VDefVal} :
    TrDefVal safety (.opaqueInfo ci) ci' →
    ci'.WF env →
    env.addConst ci.name (some ci'.toVConstant) = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    AddQuot C C' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    env.addInduct decl = some env' →
    AddInduct C decl C' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.header.quotInit venv

theorem TrEnv'.WF (H : TrEnv' C Q env venv) : ∃ ds, venv.WF ds := by
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

nonrec theorem TrEnv.WF (H : TrEnv safety env venv) : ∃ ds, venv.WF ds := H.WF

theorem TrEnv.ordered (H : TrEnv safety env venv) : venv.Ordered :=
  let ⟨_, H⟩ := H.WF; H.ordered
