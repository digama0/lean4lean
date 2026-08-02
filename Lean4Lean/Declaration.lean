import Lean.Declaration


namespace Lean

/--
The value of a constant for the purpose of delta reduction: definitions and theorems have one,
opaques do not. This mirrors the C++ `constant_info::has_value()`/`get_value()` pair.

This is deliberately *not* `ConstantInfo.value?`, whose meaning changed in lean4#12973: it now
excludes theorems, but `constant_info::has_value()` was left untouched by that PR, so the kernel
still delta-unfolds theorems: `type_checker::is_delta` uses this predicate to select candidates,
and `instantiate_value_lparams` uses it before reading their values.
-/
def ConstantInfo.deltaValue? : ConstantInfo → Option Expr
  | .defnInfo {value, ..} => some value
  | .thmInfo {value, ..} => some value
  | _ => none

namespace ReducibilityHints

def lt' : ReducibilityHints → ReducibilityHints → Bool -- lean4#2750
  | _,           .opaque     => false
  | .abbrev,     _           => false
  | .opaque,     _           => true
  | _,           .abbrev     => true
  | .regular d₁, .regular d₂ => d₁ < d₂
