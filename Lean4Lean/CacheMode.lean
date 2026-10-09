import Lean.Data.Json.FromToJson
import Lean4Lean.Theory.Typing.Strengthening.Cancel

/-! # Cache modes of the type checker

The checker keeps inference caches, `whnf` caches, an equivalence manager and a failure cache.
In the default mode, `CacheMode.scoped`, every binder puts them back to their state before the
binder when it is closed (`TypeChecker.State.leaveScope`), so that no conversion fact outlives the
binder under which it was found. In `CacheMode.global` they are kept for the whole run, as in the
C++ kernel. The global mode is sound only if context strengthening holds, and it can be selected
only with a `GlobalCacheLicense`, a proof of strengthening for every well-formed environment with
canonical `Eq`, of which no inhabitant is known (section 5 of the design notes and
`divergences.md`). -/

namespace Lean4Lean

/-- A proof of context strengthening for every well-formed environment with canonical `Eq`.
No inhabitant is known; see the strengthening study. -/
structure GlobalCacheLicense : Type where
  ok : ∀ env : VEnv, env.WF → env.HasCanonicalEq → env.Strengthening

/-- How the checker's context-relative caches behave across binders: `scoped` restores them when
a binder is closed; `global` keeps them for the whole run, as the C++ kernel does, and needs a
`GlobalCacheLicense`. The mode is a runtime tag; the license is a proof and is erased. -/
inductive CacheMode where
  | scoped
  | global (license : GlobalCacheLicense)

namespace CacheMode

instance : Inhabited CacheMode := ⟨.scoped⟩

/-- Whether the mode keeps the caches across binders. -/
def isGlobal : CacheMode → Bool
  | .scoped => false
  | .global _ => true

instance : Repr CacheMode where
  reprPrec
    | .scoped, _ => "Lean4Lean.CacheMode.scoped"
    | .global _, _ => "Lean4Lean.CacheMode.global _"

/-- Only the scoped mode can be read from a configuration: a global mode needs a
`GlobalCacheLicense`, which is a proof and has no inhabitant. -/
instance : Lean.FromJson CacheMode where
  fromJson?
    | .str "scoped" => .ok .scoped
    | .str "global" => .error "the global cache mode needs a GlobalCacheLicense \
        (a proof of context strengthening), which cannot be given in a configuration"
    | j => .error s!"expected \"scoped\" for the cache mode, got {j}"

instance : Lean.ToJson CacheMode where
  toJson
    | .scoped => "scoped"
    | .global _ => "global"

end CacheMode

end Lean4Lean
