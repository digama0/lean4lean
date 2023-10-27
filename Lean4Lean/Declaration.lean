import Lean.Declaration


namespace Lean
namespace ReducibilityHints

def lt' : ReducibilityHints → ReducibilityHints → Bool -- lean4#2750
  | _,           .opaque     => false
  | .abbrev,     _           => false
  | .opaque,     _           => true
  | _,           .abbrev     => true
  | .regular d₁, .regular d₂ => d₁ < d₂
