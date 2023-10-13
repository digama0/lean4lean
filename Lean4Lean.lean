import Lean4Lean.Environment

open Lean Elab Command

namespace CollectPartial

structure State where
  visited : NameSet := {}
  opaques : Array (List Expr) := #[]

abbrev M := ReaderT Environment $ StateT State MetaM

partial def collect (stack : List Expr) (c : Name) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM (collect (mkConst c::stack))
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    match env.find? c with
    | some (ConstantInfo.ctorInfo _)
    | some (ConstantInfo.recInfo _)
    | some (ConstantInfo.inductInfo _)
    | some (ConstantInfo.quotInfo _)   =>
      pure ()
    | some (ConstantInfo.defnInfo v)
    | some (ConstantInfo.thmInfo v)    =>
      unless ← Meta.isProp v.type do collectExpr v.value
    | some (ConstantInfo.axiomInfo v)
    | some (ConstantInfo.opaqueInfo v) =>
      unless ← Meta.isProp v.type do
        modify fun s => { s with opaques := s.opaques.push (mkConst c:: stack) }
    | none                             =>
      modify fun s => { s with opaques := s.opaques.push (mkConst c:: stack) }

end CollectPartial

elab "#print" "partial" name:ident : command => do
  let constName ← resolveGlobalConstNoOverloadWithInfo name
  let env ← getEnv
  let (_, s) ← liftTermElabM <| ((CollectPartial.collect [] constName).run env).run {}
  if s.opaques.isEmpty then
    logInfo m!"'{constName}' does not use any partial definitions"
  else
    logInfo m!"'{constName}' depends on opaques: {s.opaques.toList}"

#print partial Environment.addDecl'
