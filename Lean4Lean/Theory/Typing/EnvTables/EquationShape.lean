import Lean4Lean.Theory.Typing.EnvTables.OfWF

/-!
# Shapes of installed recursor equations

A restored recursor equation is a lambda telescope over the parameters, motives, minors
and constructor fields; its left body applies the recursor to the parameter, motive and minor
variables, to arbitrary index expressions, and to a constructor application whose trailing
arguments are the field variables. Restoration may specialize the constructor's parameters
(nested auxiliaries), but never touches the field variables.
-/

namespace Lean4Lean.EnvTables
open _root_.Lean4Lean.EnvTables.VEnv InductiveSignature

/-- Restoration of a constructor application with parameter and field variables. -/
theorem restored_ctorApp {r : Restoration} {np e nf : Nat}
    (hparams : ∀ h ∈ r.heads, h.nparams = np) {name : Name} {levels : List VLevel}
    {out : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) (vars np (e + nf) ++ vars nf 0)) = some out) :
    (r.heads.find? (fun h => h.auxiliary == name) = none ∧
      out = VExpr.mkApps (.const (r.recursorName name) levels) (vars np (e + nf) ++ vars nf 0)) ∨
    (∃ spec ∈ r.heads, r.heads.find? (fun h => h.auxiliary == name) = some spec ∧
      levels.length = spec.uvars ∧
      out = VExpr.mkApps (.const spec.target (spec.levels.map (·.inst levels)))
        (spec.arguments.map (fun arg => instantiateParams (arg.instL levels) (vars np (e + nf)))
          ++ vars nf 0)) := by
  change Restoration.expr.go r (VExpr.mkApps (.const name levels) _) [] = _ at h
  rw [restoration_mkApps] at h
  simp only [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars, bind, Option.bind_some, pure,
    List.append_nil] at h
  simp only [Restoration.expr.go] at h
  split at h
  · rename_i spec hspec
    have hmem := List.mem_of_find?_eq_some hspec
    have hnp := hparams spec hmem
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · rename_i hcond
      cases h
      refine .inr ⟨spec, hmem, hspec, ?_, ?_⟩
      · simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.or_eq_true, not_or] at hcond
        exact Classical.not_not.mp hcond.1
      · rw [hnp, List.take_left' (InductiveSignature.length_vars np (e + nf)), List.drop_left' (InductiveSignature.length_vars np (e + nf))]
  · rename_i hnone
    cases h
    exact .inl ⟨hnone, rfl⟩

theorem compilationRestoration_nparams {source : VInductDecl}
    {aux : List ContainerSpecialization} :
    ∀ h ∈ (compilationRestoration source aux).heads, h.nparams = source.nparams := by
  intro h hh
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hh
  simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at ha
  rcases ha with rfl | ⟨c, _, rfl⟩ <;> rfl

/-- The shape of one restored recursor equation of a finite compilation. -/
theorem CompilationData.rule_shape
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} {env : VEnv} {src exp : VInductDecl} {df : VDefEq}
    (hdata : CompilationData env src exp s g aux block)
    (index : Fin s.constructors.size)
    (hrestore : (compilationRestoration src aux).equation (g.equation index) = some df) :
    ∃ (Ds idx : List VExpr) (R major : VExpr),
      df.lhs = VExpr.wrapLams Ds (VExpr.mkApps
        (.const ((compilationRestoration src aux).recursorName
          (g.recursorName s.constructors[index].owner)) (VLevel.params g.uvars))
        (vars (s.params.length + (s.families.size + s.constructors.size))
          s.constructors[index].fields.length ++ idx ++ [major])) ∧
      df.rhs = VExpr.wrapLams Ds R ∧
      Ds.length = s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].fields.length ∧
      idx.length = s.constructors[index].indices.length ∧
      df.uvars = g.uvars ∧
      (((compilationRestoration src aux).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none ∧
        major = VExpr.mkApps (.const ((compilationRestoration src aux).recursorName
          s.constructors[index].name) g.levels)
          (vars s.params.length (s.families.size + s.constructors.size +
            s.constructors[index].fields.length) ++ vars s.constructors[index].fields.length 0)) ∨
      (∃ spec ∈ (compilationRestoration src aux).heads,
        (compilationRestoration src aux).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some spec ∧
        g.levels.length = spec.uvars ∧
        major = VExpr.mkApps (.const spec.target (spec.levels.map (·.inst g.levels)))
          (spec.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
            (vars s.params.length (s.families.size + s.constructors.size +
              s.constructors[index].fields.length))) ++
            vars s.constructors[index].fields.length 0))) := by
  let r := compilationRestoration src aux
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨Ds, lBody, rBody, tBody, hlBody, _, _, hel, her, _, hlen⟩ :=
    restored_common_telescope hl hr ht
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let np := s.params.length
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
    apply List.find?_eq_none.mpr
    intro spec hs
    simpa only [beq_iff_eq] using hdata.heads_not_recursors ctor.owner spec hs
  change r.expr (VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
    (vars (np + extra) nf ++ indices ++ [g.constructorApp ctor extra 0])) = some lBody at hlBody
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at hlBody
  rw [restoration_mkApps] at hlBody
  simp only [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars, List.mapM_cons, List.mapM_nil, bind,
    Option.bind_eq_some_iff, pure, Option.some.injEq] at hlBody
  obtain ⟨_, ⟨_, ⟨_, rfl, idx', hi, rfl⟩, _, ⟨major', hmajor, _, rfl, rfl⟩, rfl⟩, hout⟩ := hlBody
  simp only [List.append_nil, Restoration.expr.go, hnone] at hout
  have hidx : idx'.length = ctor.indices.length := by
    have := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hi)
    simpa [indices] using this.symm
  have hparams : ∀ h ∈ r.heads, h.nparams = np := by
    intro h hh
    rw [compilationRestoration_nparams h hh, ← hdata.nparams, ← hdata.model.nparams]
  have hmaj := restored_ctorApp (e := extra) hparams (by
    simpa only [Instance.constructorApp, Nat.add_zero] using hmajor)
  refine ⟨Ds, idx', rBody, major', ?_, her, ?_, hidx, ?_, hmaj⟩
  · rw [hel, ← Option.some.inj hout]
  · rw [hlen]
    simp [Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes]
    omega
  · simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at hrestore
    obtain ⟨_, _, _, _, _, _, he⟩ := hrestore
    cases he
    rfl

end Lean4Lean.EnvTables
