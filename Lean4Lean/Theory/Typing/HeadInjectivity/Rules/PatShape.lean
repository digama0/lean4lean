import Lean4Lean.Theory.Typing.SignatureVars

/-! The pattern shape of computation rules.

A computation rule has the pattern shape when its left-hand side is
`wrapLams doms (mkApps head args)` whose arguments are either absent (a
definition) or leading arguments followed by a constructor-application major
whose trailing arguments are distinct bound variables, every binder occurring
as a bare leading argument or among those trailing variables. This file defines
the shape and proves it for every restored generated recursor equation;
`Rules/Coverage.lean` derives that such an equation is never a bare constant.
Purely syntactic: no typing. -/

namespace Lean4Lean

/-- Arguments of a rule's left-hand side under `n` binders: either no arguments (a
definition), or leading arguments followed by a major `mkApps (const ctor ls) (ms ++ fs)`
whose trailing arguments `fs` are distinct bound variables, such that every binder
`x < n` occurs as a bare leading argument `bvar x` or in `fs`. -/
def PatArgs (n : Nat) (args : List VExpr) : Prop :=
  (args = [] ∧ n = 0) ∨
  ∃ (lead : List VExpr) (ctor : Name) (ls : List VLevel) (ms : List VExpr) (fs : List Nat),
    args = lead ++ [VExpr.mkApps (.const ctor ls) (ms ++ fs.map .bvar)] ∧
    fs.Nodup ∧ (∀ i ∈ fs, i < n) ∧
    ∀ x < n, VExpr.bvar x ∈ lead ∨ x ∈ fs

/-- A rule whose left-hand side is a lambda-wrapped application of `head` to pattern
arguments; the right-hand side and the type are wrapped by the same binder domains. -/
structure VDefEq.PatShape (df : VDefEq) (head : VExpr) : Prop where
  shape : ∃ doms args body T, df.lhs = VExpr.wrapLams doms (VExpr.mkApps head args) ∧
    df.rhs = VExpr.wrapLams doms body ∧ df.type = VExpr.wrapForalls doms T ∧
    PatArgs doms.length args

theorem VExpr.wrapLams_mkApps_snoc_ne_const {ds as : List VExpr} {f a : VExpr} :
    VExpr.wrapLams ds (VExpr.mkApps f (as ++ [a])) ≠ .const n ls := by
  cases ds with
  | cons => simp [VExpr.wrapLams]
  | nil =>
    simp only [VExpr.wrapLams, List.foldr_nil, VExpr.mkApps, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    nofun

/-- The head of a lambda-wrapped constant spine. -/
theorem VExpr.stripLams_wrapLams_mkApps_head {ds args : List VExpr} :
    (VExpr.wrapLams ds (VExpr.mkApps (.const n ls) args)).stripLams.getAppFnArgs.1 =
      .const n ls := by
  rw [VExpr.stripLams_wrapLams]
  cases args with
  | nil => rfl
  | cons a as =>
    rw [show VExpr.mkApps (.const n ls) (a :: as) = VExpr.mkApps (.app (.const n ls) a) as
      from rfl]
    have : ∀ (f : VExpr) (as : List VExpr),
        (VExpr.mkApps (.app f a) as).stripLams = VExpr.mkApps (.app f a) as := by
      intro f as
      induction as generalizing f a with
      | nil => rfl
      | cons b bs ih => exact ih _ _
    rw [this, VExpr.getAppFnArgs, VExpr.getAppFnArgs_go_mkApps]
    rfl

namespace InductiveSignature

/-- The head that restoration produces from a generated recursor head: recursor constants
are renamed, abstract eliminator heads are kept. -/
def Restoration.headOf (r : Restoration) : VExpr → VExpr
  | .const n ls => .const (r.recursorName n) ls
  | e => e

/-- Restoring a generated constructor application keeps its trailing field
variables, provided no specialization consumes more than `np` arguments. -/
theorem Restoration.ctorApp_fields {r : Restoration}
    (hparams : ∀ h ∈ r.heads, h.nparams ≤ np) {output : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) (vars np offset ++ vars nf 0)) = some output) :
    ∃ name' levels' ms, output = VExpr.mkApps (.const name' levels') (ms ++ vars nf 0) := by
  change Restoration.expr.go r (VExpr.mkApps (.const name levels) _) [] = _ at h
  rw [restoration_mkApps] at h
  simp [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars] at h
  simp only [Restoration.expr.go] at h
  split at h
  · rename_i spec hspec
    have hle := hparams spec (List.mem_of_find?_eq_some hspec)
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · cases h
      rw [List.drop_append_of_le_length (by simpa [vars] using hle), ← List.append_assoc]
      exact ⟨_, _, _, rfl⟩
  · cases h
    exact ⟨_, _, _, rfl⟩

/-- Restoration of a generated recursor equation, for either head mode, yields the
pattern shape. The leading parameters, motives and minors stay bare variables,
indices are restored arbitrarily (they are ignored by the pattern), and the
major keeps its trailing field variables. The left-hand side has at least one argument,
so it is never a bare constant. -/
theorem Instance.equation_patShape_strong {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) (mode : HeadMode) {r : Restoration} {df : VDefEq}
    (hparams : ∀ h ∈ r.heads, h.nparams ≤ s.params.length)
    (hhead : ∀ n ls, g.recursorHead mode s.constructors[index].owner = .const n ls →
      ∀ h ∈ r.heads, h.auxiliary ≠ n)
    (he : r.equation (g.equation index mode) = some df) :
    df.PatShape (r.headOf (g.recursorHead mode s.constructors[index].owner)) ∧
      ∀ n ls, df.lhs ≠ .const n ls := by
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts he
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  let head := g.recursorHead mode ctor.owner
  obtain ⟨ds', l, rb, t, hl', _, _, hel, her, het, hlen⟩ :=
    restored_common_telescope (domains := domains) hl hr ht
  have hdomlen : domains.length = s.params.length + extra + nf := by
    simp only [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList]
    simp only [nf, extra]
    omega
  have hl0 : r.expr (VExpr.mkApps head
      (vars (s.params.length + extra) nf ++ indices ++ [major])) = some l := hl'
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at hl0
  rw [restoration_mkApps] at hl0
  simp only [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars, bind, Option.bind_eq_some_iff,
    List.append_nil] at hl0
  obtain ⟨a, ⟨a1, ⟨_, h1, indices', hi, h2⟩, a3, hm, h3⟩, hout⟩ := hl0
  cases Option.some.inj h1
  cases Option.some.inj h2
  cases Option.some.inj h3
  simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hm
  obtain ⟨major', hmajor, _, rfl, rfl⟩ := hm
  have hgo : Restoration.expr.go r head
      (vars (s.params.length + extra) nf ++ indices' ++ [major']) =
      some (VExpr.mkApps (r.headOf head) (vars (s.params.length + extra) nf ++ indices' ++ [major'])) := by
    have hh := hhead
    simp only [head]
    cases mode with
    | recursor =>
      have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
        apply List.find?_eq_none.mpr
        intro spec hs
        simpa only [beq_iff_eq] using hh _ _ rfl spec hs
      simp [Instance.recursorHead, Restoration.expr.go, hnone, Restoration.headOf]
    | elim block first => rfl
  rw [hgo, Option.some.injEq] at hout
  subst hout
  obtain ⟨cn, cl, ms, rfl⟩ := Restoration.ctorApp_fields hparams hmajor
  refine ⟨⟨⟨ds', _, rb, t, hel, her, het, .inr ⟨vars (s.params.length + extra) nf ++ indices',
    cn, cl, ms, (List.range nf).reverse, ?_, ?_, ?_, ?_⟩⟩⟩, fun n ls h => ?_⟩
  rotate_left 4
  · rw [hel] at h
    exact VExpr.wrapLams_mkApps_snoc_ne_const h
  · rw [InductiveSignature.vars_zero]
  · exact List.nodup_reverse.mpr (List.nodup_range)
  · intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    omega
  · intro x hx
    rw [hlen, hdomlen] at hx
    by_cases hxf : x < nf
    · exact .inr (by simpa using hxf)
    · exact .inl (List.mem_append_left _ (InductiveSignature.mem_vars (by omega) (by omega)))

end InductiveSignature
end Lean4Lean
