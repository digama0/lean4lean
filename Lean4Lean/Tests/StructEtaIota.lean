import Lean4Lean.Environment

/-!
Recursor reduction on a major premise of structure type that is not a constructor application
(`Lean4Lean.toCtorWhenStruct`, `expandEtaStruct`). The major premise is expanded to the
constructor applied to the parameters of its type and to its projections, as
`to_cnstr_when_structure` does in the C++ kernel.

Each theorem below is accepted by the C++ kernel (it is elaborated here) and is re-added under a
fresh name through `Lean4Lean.addDecl`. The parameter count of the expansion is read off the
type of the major premise, which applies the structure to exactly its parameters.
-/

namespace Lean4Lean.Tests.StructEtaIota

open Lean

structure Pair (α : Type u) (β : Type v) where
  fst : α
  snd : β

structure Triple (α : Sort u) where
  a : α
  b : α
  c : Nat

theorem prodEta (p : Nat × Bool) :
    @Prod.rec Nat Bool (fun _ => Nat) (fun a _ => a) p = p.1 := rfl

theorem pairEta.{u, v} (α : Type u) (β : Type v) (p : Pair α β) :
    @Pair.rec α β (fun _ => β) (fun _ b => b) p = p.snd := rfl

/-- The parameter `α : Sort u` makes the structure universe `max 1 u`, which is never zero. -/
theorem tripleEta.{u} (α : Sort u) (t : Triple α) :
    @Triple.rec α (fun _ => Nat) (fun _ _ c => c) t = t.c := rfl

/-- The major premise is an application of a function returning a structure. -/
theorem appEta (f : Nat → Pair Nat Nat) (n : Nat) :
    @Pair.rec Nat Nat (fun _ => Nat) (fun a _ => a) (f n) = (f n).fst := rfl

def readd (n : Name) : MetaM Unit := do
  let env ← getEnv
  let some (.thmInfo v) := env.find? n | throwError "missing {n}"
  let decl := Declaration.thmDecl { v with name := n.appendAfter "_copy" }
  match Lean4Lean.addDecl env.toKernelEnv decl with
  | .error e => throwError "Lean4Lean.addDecl rejected {n}: {← (e.toMessageData {}).toString}"
  | .ok _ => pure ()

#eval do
  for n in [``prodEta, ``pairEta, ``tripleEta, ``appEta] do
    readd n

end Lean4Lean.Tests.StructEtaIota
