import Batteries.Lean.Expr
import Lean4Lean.Std.Control
import Lean4Lean.Std.ToExpr
import Lean4Lean.Theory.VEnv
import Lean4Lean.Inductive.Reduce

namespace Lean4Lean

namespace Meta
open Lean Meta Elab Term

def expandProj (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr := do
  let failed {α} : Unit → MetaM α := fun _ => do
    throwError "invalid projection{indentExpr (mkProj structName idx e)}"
  let ival ← getConstInfoInduct structName
  let [ctor] := ival.ctors | failed ()
  let ctorInfo ← getConstInfoCtor ctor
  unless idx < ctorInfo.numFields do failed ()
  let args : Array Term ← (Array.range ctorInfo.numFields).mapM fun _ => do
    `($(mkIdent (← mkFreshId)):ident)
  let args' ← args.mapM fun x => `(Lean.Parser.Term.funBinder| $x)
  let casesOn := mkCIdent (mkCasesOnName structName)
  TermElabM.run' do
    let stx ← `($casesOn:ident $(← e.toSyntax) fun $args'* => $(args[idx]!))
    elabTerm stx (← inferType (.proj structName idx e))

partial def expandExpr (e : Expr) : MetaM Expr :=
  Meta.transform e
    (pre := fun
      | .mdata _ e => return .visit e
      | .proj s i e => return .continue (← expandProj s i e)
      | e@(.mvar _) => return .continue (← instantiateMVars e)
      | _ => return .continue)

variable (ls : List Name) (fvarToIdx : FVarIdMap Nat) in
partial def ofExpr : Expr → (k :_:= 0) → MetaM VExpr
  | .bvar i, _ => return .bvar i
  | .sort u, _ => return .sort (← VLevel.ofLevel ls u)
  | .const c us, _ => return .const c (← liftM <| us.mapM (VLevel.ofLevel ls))
  | .app fn arg, k => return .app (← ofExpr fn k) (← ofExpr arg k)
  | .lam _ ty body _, k => return .lam (← ofExpr ty k) (← ofExpr body (k+1))
  | .forallE _ ty body _, k => return .forallE (← ofExpr ty k) (← ofExpr body (k+1))
  | .mdata _ e, k => ofExpr e k
  | .lit l, k => ofExpr l.toConstructor k
  | .letE _ _ value body _, k => return (← ofExpr body (k+1)).inst (← ofExpr value k)
  | e@(.proj ..), _ => throwError "invalid expression {e}"
  | e@(.mvar ..), _ => throwError "expression contains metavariables {e}"
  | .fvar e, k => do
    if let some i := fvarToIdx.find? e then return .bvar (i+k)
    let lctx ← getLCtx
    let some e := (do (← lctx.find? e).value?) | throwError "undeclared free var {Expr.fvar e}"
    ofExpr e

deriving instance ToExpr for VLevel
deriving instance ToExpr for VExpr
deriving instance ToExpr for VConstant
deriving instance ToExpr for VDefEq

def toVExprWrapper (bis : Option (TSyntaxArray ``Parser.Term.funBinder))
    (x : FVarIdMap Nat → TermElabM α) : TermElabM α := do
  withLevelNames [] <|
  elabFunBinders (bis.getD #[]) none fun xs _ =>
  withAutoBoundImplicit <|
  x <|
  xs.foldr (fun fvar (n, m) => (n+1, m.insert fvar.fvarId! n)) (0, ({}:FVarIdMap Nat)) |>.2

def elabForVExpr (e : Expr) : TermElabM Expr := do
  let e ← levelMVarToParam e
  if ← logUnassignedUsingErrorInfos (← getMVars e) then throwAbortCommand
  expandExpr e

def toVExprCore (bis : Option (TSyntaxArray ``Parser.Term.funBinder))
    (e : Term) : TermElabM (Nat × VExpr) := do
  toVExprWrapper bis fun map => do
    let e ← elabForVExpr (← elabTerm e none)
    let ls := (← getLevelNames).reverse
    return (ls.length, ← ofExpr ls map e)

syntax "vexpr(" atomic(Parser.Term.funBinder* " ⊢ ")? term ")" : term

elab_rules : term
  | `(vexpr($[$bis* ⊢]? $e:term)) => return toExpr (← toVExprCore bis e).2

syntax "vconst(" atomic(Parser.Term.funBinder* " ⊢ ")? term ")" : term

elab_rules : term
  | `(vconst($[$bis* ⊢]? $e:term)) => do
    let (n, ve) ← toVExprCore bis e
    return toExpr (⟨n, ve⟩ : VConstant)

syntax "vdefeq(" atomic(Parser.Term.funBinder* " ⊢ ")?
  atomic(Parser.Term.funBinder* " => ")? term " ≡ " term ")" : term

elab_rules : term
  | `(vdefeq($[$bis* ⊢]? $[$args* =>]? $e₁:term ≡ $e₂:term)) => do
    toVExprWrapper bis fun map => do
      let (e₁, e₂) ← match args with
        | some args => pure (← `(fun $args* => $e₁), ← `(fun $args* => $e₂))
        | none => pure (e₁, e₂)
      let e₁ ← elabTerm e₁ none
      let ty ← inferType e₁
      let e₂ ← elabTerm e₂ ty
      let e₁ ← elabForVExpr e₁
      let e₂ ← elabForVExpr e₂
      let ty ← elabForVExpr ty
      let ls := (← getLevelNames).reverse
      return toExpr {
        uvars := ls.length
        lhs := ← ofExpr ls map e₁
        rhs := ← ofExpr ls map e₂
        type := ← ofExpr ls map ty
      : VDefEq }
