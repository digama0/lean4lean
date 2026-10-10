import Lean4Lean.Theory.Inductive.Formation

/-! # Guarded iota closure

Closure under application and lambda telescopes for the abstract guarded-iota judgment.
Existing qualified names are retained for compatibility.
-/

namespace Lean4Lean

open Lean hiding Environment Exception

namespace VerifyInductive

/-- The guarded-iota judgment follows source-visible constant support.
Primitive projection nodes contribute the support of their source major. -/
theorem VExpr.SourceConstFree.guardedIota
    (H : VExpr.SourceConstFree recursors e) :
    VExpr.GuardedIota recursors fieldVars depth e := by
  induction H generalizing depth with
  | bvar => exact .bvar
  | sort => exact .sort
  | const name levels fresh => exact .const fresh
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | proj _ _ _ ihMajor => exact .proj ihMajor
  | lam _ _ ihDomain ihBody =>
      exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody =>
      exact .forallE ihDomain ihBody

/-- Closing a guarded body over recursor-free domains preserves the guard,
with the body checked beneath exactly the number of introduced binders. -/
theorem VExpr.GuardedIota.wrapLams
    {recursors : List Name} {fieldVars : List Nat}
    {domains : List VExpr} {body : VExpr} {depth : Nat}
    (hdomains : ∀ dom ∈ domains, dom.SourceConstFree recursors)
    (hbody : body.GuardedIota recursors fieldVars
      (depth + domains.length)) :
    (VExpr.wrapLams domains body).GuardedIota recursors fieldVars depth := by
  induction domains generalizing depth with
  | nil => simpa [VExpr.wrapLams] using hbody
  | cons dom domains ih =>
      simp only [VExpr.wrapLams, List.foldr_cons]
      apply VExpr.GuardedIota.lam
      · exact VExpr.SourceConstFree.guardedIota
          (hdomains dom (by simp))
      · apply ih
        · intro inner hinner
          exact hdomains inner (by simp [hinner])
        · simpa [Nat.add_assoc, Nat.add_comm 1 domains.length] using hbody

theorem VExpr.GuardedIota.mkApps
    {recursors : List Name} {fieldVars : List Nat} {depth : Nat}
    {fn : VExpr} {args : List VExpr}
    (hfn : fn.GuardedIota recursors fieldVars depth)
    (hargs : ∀ arg ∈ args,
      arg.GuardedIota recursors fieldVars depth) :
    (VExpr.mkApps fn args).GuardedIota recursors fieldVars depth := by
  induction args generalizing fn with
  | nil => simpa [VExpr.mkApps] using hfn
  | cons arg args ih =>
      rw [VExpr.mkApps]
      apply ih
      · exact .app hfn (hargs arg (by simp))
      · intro inner hinner
        exact hargs inner (by simp [hinner])

/-- The executable iota RHS applies a minor variable first to every
constructor field and then to the generated recursive results. Once those
two argument groups are guarded, the complete spine is guarded. -/
theorem VExpr.GuardedIota.minorRhs
    {recursors : List Name} {fieldVars : List Nat} {depth minorVar : Nat}
    {fieldArgs recursiveResults : List VExpr}
    (hfields : ∀ arg ∈ fieldArgs,
      arg.GuardedIota recursors fieldVars depth)
    (hresults : ∀ result ∈ recursiveResults,
      result.GuardedIota recursors fieldVars depth) :
    (VExpr.mkApps (.bvar minorVar) (fieldArgs ++ recursiveResults)).GuardedIota
      recursors fieldVars depth := by
  apply VExpr.GuardedIota.mkApps .bvar
  intro arg harg
  rcases List.mem_append.mp harg with hfield | hresult
  · exact hfields arg hfield
  · exact hresults arg hresult

/-- Canonical guarded shape of a generated higher-order recursive result:
zero or more recursor-free lambda domains close a recursor application whose
major premise is an application of a designated constructor field. -/
theorem VExpr.GuardedIota.recCallWrapped
    {recursors : List Name} {fieldVars : List Nat} {depth : Nat}
    {domains : List VExpr} {recursor : Name} {levels : List VLevel}
    {init : List VExpr} {major : VExpr}
    (hdomains : ∀ dom ∈ domains, dom.SourceConstFree recursors)
    (hrecursor : recursor ∈ recursors)
    (hargs : ∀ arg ∈ init ++ [major],
      arg.GuardedIota recursors fieldVars (depth + domains.length))
    (hmajor : major.IsFieldApp fieldVars (depth + domains.length)) :
    (VExpr.wrapLams domains <|
      VExpr.mkApps (.const recursor levels) (init ++ [major])).GuardedIota
      recursors fieldVars depth := by
  apply VExpr.GuardedIota.wrapLams hdomains
  exact .recCall hrecursor hargs hmajor

end VerifyInductive
end Lean4Lean
