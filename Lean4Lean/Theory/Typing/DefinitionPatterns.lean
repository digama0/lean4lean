import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Pattern

/-! Concrete stored delta patterns of ordinary definitions. The right-hand
side is the actual installed value, and lookup fixes one value per name. -/

namespace Lean4Lean.VEnv
variable {env extended : VEnv} {value : VDefVal}

/-- Both the constant and its exact defining equation were installed. -/
def DefinitionRegistered (env : VEnv) (value : VDefVal) : Prop :=
  env.constants value.name = some value.toVConstant ∧ env.defeqs value.toDefEq

/-- Actual definition values produce constant-head delta patterns. -/
inductive DefinitionPattern (registry : Name → Option VDefVal) :
    (p : Pattern) → p.RHS × p.Check → Prop where
  | intro {value : VDefVal} (hlookup : registry value.name = some value)
      (hclosed : value.value.Closed) :
      DefinitionPattern registry (.const value.name) (.fixed value.value hclosed, .true)

namespace DefinitionPattern

variable {registry : Name → Option VDefVal}

end DefinitionPattern
end Lean4Lean.VEnv
