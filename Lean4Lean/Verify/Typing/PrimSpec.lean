import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Environment.Basic

/-!
# Environment extension for the primitive invariant

`HasPrimitives` is a name-keyed table of specifications, so extending the environment is a
single theorem: every spec whose name differs from the one being added transfers by
monotonicity, and the one that matches is the caller's obligation.

This sits below the declaration checker so that the primitive proofs, which live above it, can
use it without a cycle.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-- Primitive specifications transport along an extension that preserves
lookup of their own name. Their typing and equality conclusions are monotone. -/
theorem PrimSpec.Holds.extend {env env' : VEnv} {s : PrimSpec} {n : Name}
    (H : s.Holds env n) (le : env ≤ env')
    (same : env'.constants n = env.constants n) : s.Holds env' n := by
  have old : env'.contains n → env.contains n := fun ⟨_, h⟩ => ⟨_, same ▸ h⟩
  have new {m} : env.contains m → env'.contains m := fun ⟨_, h⟩ => ⟨_, le.constants h⟩
  cases s with
  | containsImplies ns => exact fun h m hm => new (H (old h) m hm)
  | typeEq => exact fun _ h => H _ (same ▸ h)
  | reflectsNatNat =>
    exact fun h => ⟨(H (old h)).1.mono le, fun a => ((H (old h)).2 a).mono le⟩
  | reflectsNatNatNat =>
    exact fun h => ⟨(H (old h)).1.mono le, fun a b => ((H (old h)).2 a b).mono le⟩
  | reflectsNatNatBool =>
    exact fun h => ⟨(H (old h)).1.mono le, fun a b => ((H (old h)).2 a b).mono le⟩
  | reflectsBitwise =>
    exact fun h => ⟨fun _ hc => (H (old h)).1 _ (same ▸ hc),
      fun env'' hle => (H (old h)).2 env'' (le.trans hle)⟩
  | stringOfList =>
    intro _ h
    obtain ⟨h1, h2, h3⟩ := H _ (same ▸ h)
    exact ⟨h1, h2.mono le, h3.mono le⟩

theorem PrimSpec.Holds.addConst {env env' : VEnv} {s : PrimSpec} {n : Name}
    (H : s.Holds env n) (hne : name ≠ n)
    (hadd : env.addConst name ci = some env') : s.Holds env' n :=
  H.extend (VEnv.addConst_le hadd) (VEnv.addConst_constants_of_ne hadd hne)

theorem PrimSpec.Holds.addDefEq {env : VEnv} {s : PrimSpec} {n : Name}
    (H : s.Holds env n) : s.Holds (env.addDefEq df) n :=
  H.extend VEnv.addDefEq_le rfl

theorem PrimSpec.Holds.addProjections {env : VEnv} {s : PrimSpec} {n : Name}
    (H : s.Holds env n) : s.Holds (env.addProjections entries) n :=
  H.extend VEnv.addProjections_le (by simp)

theorem PrimSpec.Holds.addEliminator {env : VEnv} {s : PrimSpec} {n : Name}
    (H : s.Holds env n) : s.Holds (env.addEliminator block schema) n :=
  H.extend VEnv.addEliminator_le rfl

theorem VEnv.HasPrimitives.addEliminator {env : VEnv} (H : env.HasPrimitives) :
    (env.addEliminator block schema).HasPrimitives :=
  fun p hp => (H p hp).addEliminator

theorem VEnv.HasPrimitives.addProjections {env : VEnv} (H : env.HasPrimitives) :
    (env.addProjections entries).HasPrimitives :=
  fun p hp => (H p hp).addProjections

/-- The single environment-extension theorem for `HasPrimitives`. Every spec whose name differs
from the one being added transfers by monotonicity; the one that matches -- at most one, since
`primSpecs` is keyed by name -- is the caller's obligation. Adding a non-primitive discharges it
vacuously. -/
theorem VEnv.HasPrimitives.addConstDefEq {env env' : VEnv} (H : env.HasPrimitives)
    (hadd : env.addConst name ci = some env')
    (hnew : ∀ p ∈ primSpecs, name = p.1 → p.2.Holds (env'.addDefEq df) p.1) :
    (env'.addDefEq df).HasPrimitives := fun p hp =>
  if h : name = p.1 then hnew p hp h
  else ((H p hp).addConst h hadd).addDefEq

theorem primitives_eq : Environment.primitives = .ofList (primSpecs.map (·.1)) := rfl

theorem List.nodup_keys_unique {α β} [DecidableEq α] : ∀ {l : List (α × β)},
    (l.map (·.1)).Nodup → ∀ {a b : α × β}, a ∈ l → b ∈ l → a.1 = b.1 → a = b
  | [], _, _, _, h, _, _ => nomatch h
  | p :: l, hn, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨_, hb, hab.symm⟩ hn.1
    · exact absurd ⟨_, ha, hab⟩ hn.1
    · exact List.nodup_keys_unique hn.2 ha hb hab

theorem primSpecs_nodup : (primSpecs.map (·.1)).Nodup := by decide

/-- Since `primSpecs` is keyed by name, the obligation left by `addConstDefEq` concerns exactly
the entry for the name being added. -/
theorem VEnv.HasPrimitives.addPrimitiveDefEq {env env' : VEnv} (H : env.HasPrimitives)
    (hadd : env.addConst name ci = some env')
    {s₀ : PrimSpec} (hmem : (name, s₀) ∈ primSpecs)
    (hnew : s₀.Holds (env'.addDefEq df) name) :
    (env'.addDefEq df).HasPrimitives :=
  H.addConstDefEq hadd fun p hp h => by
    cases List.nodup_keys_unique primSpecs_nodup hmem hp h
    exact hnew

theorem mem_primSpecs_contains {p : Name × PrimSpec} (h : p ∈ primSpecs) :
    Environment.primitives.contains p.1 := by
  simp [primitives_eq, NameSet.contains, NameSet.ofList]; exact ⟨_, h⟩

theorem VEnv.HasPrimitives.addConstDefEq_of_not_primitive {env env' : VEnv}
    (H : env.HasPrimitives) (hname : Environment.primitives.contains name = false)
    (hadd : env.addConst name ci = some env') :
    (env'.addDefEq df).HasPrimitives :=
  H.addConstDefEq hadd fun p hp h => absurd (h ▸ hname) (by simp [mem_primSpecs_contains hp])

theorem VEnv.HasPrimitives.addConst {env env' : VEnv} (H : env.HasPrimitives)
    (hname : Environment.primitives.contains name = false)
    (hadd : env.addConst name ci = some env') : env'.HasPrimitives := fun p hp =>
  (H p hp).addConst (fun h => absurd (h ▸ hname) (by simp [mem_primSpecs_contains hp])) hadd

theorem VEnv.HasPrimitives.addDefEq {env : VEnv} (H : env.HasPrimitives) :
    (env.addDefEq df).HasPrimitives := fun p hp => (H p hp).addDefEq


end Lean4Lean
