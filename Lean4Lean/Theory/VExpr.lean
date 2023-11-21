import Lean
import Lean4Lean.Theory.VLevel

namespace Lean4Lean

open Lean (Name FVarId)

inductive VExpr where
  | bvar (deBruijnIndex : Nat)
  | sort (u : VLevel)
  | const (declName : Name) (us : List VLevel)
  | app (fn arg : VExpr)
  | lam (binderType body : VExpr)
  | forallE (binderType body : VExpr)

def liftVar (i : Nat) (k := 0) : Nat := if i < k then i else i + 1

namespace VExpr

def lift : VExpr → (k :_:= 0) → VExpr
  | .bvar i, k => .bvar (liftVar i k)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift k) (arg.lift k)
  | .lam ty body, k => .lam (ty.lift k) (body.lift (k+1))
  | .forallE ty body, k => .forallE (ty.lift k) (body.lift (k+1))

variable (ls : List VLevel) in
def instL : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (·.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

def inst : VExpr → VExpr → (k :_:= 0) → VExpr
  | .bvar i, e, k =>
    if i < k then .bvar i else if i = k then e else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app fn arg, e, k => .app (fn.inst e k) (arg.inst e k)
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst (lift e) (k+1))
  | .forallE ty body, e, k => .forallE (ty.inst e k) (body.inst (lift e) (k+1))
