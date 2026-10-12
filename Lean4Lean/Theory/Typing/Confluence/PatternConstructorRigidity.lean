import Lean4Lean.Theory.Typing.ProjectionRigidity
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Theory.Typing.RecursorRegistration

/-! # Rigidity of the constructors of registered patterns

The constructor of a registered ι rule (`VEnv.IsPatCtor`) is rigid, and so is the type former
its type returns (`VEnv.CtorResultRigid`): a registered pattern comes from an `induct` step of
the history (`WF'.pats_origin`); its rule's constructor is a constructor of that declaration,
rigid with its family by `WF'.inductCtorRigid`/`WF'.inductTypeRigid`, or the constructor of a
container's own registered rule (`CompiledInductive.rule_ctor_cases`), handled by the same
argument on the strictly shorter history before the declaration (`WF'.patCtor_provenance`).

These are the facts the confluence engine's pattern table (`Params.pat_ctor_rigid`) and the
major-family lemmas (`RecursorRegistered.major_not_pi`) read. -/

namespace Lean4Lean
namespace VEnv

theorem _root_.Lean4Lean.SimplePattern.iota_toPattern_inj {a a' c c' : Name} {b b' d d' : Nat}
    (H : (SimplePattern.iota a b c d).toPattern = (SimplePattern.iota a' b' c' d').toPattern) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  simp only [SimplePattern.toPattern, Pattern.app.injEq] at H
  obtain ⟨h1, h2⟩ := Pattern.varN_const_inj H.1
  obtain ⟨h3, h4⟩ := Pattern.varN_const_inj H.2
  exact ⟨h1, h2, h3, h4⟩

/-- The result type former of a direct constructor of a declaration. -/
theorem _root_.Lean4Lean.VInductDecl.RawCtorShape.forallResult_head {decl : VInductDecl}
    {type : VInductiveType} {ctor : VConstVal} (H : decl.RawCtorShape type ctor) :
    ctor.type.forallResult.getAppFnArgs.1 = .const type.name (VLevel.params decl.uvars) := by
  obtain ⟨doms, result, heq, -, -, hhead⟩ := H
  rw [heq, VExpr.forallResult_wrapForalls, ← hhead]
  congr 1
  cases result with
  | forallE A B => simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at hhead
  | _ => rfl

/-- **Direct provenance of a pattern constructor**, by strong induction on the history: the
constructor of a registered ι rule is a constructor of an `induct` step of the history, with
its raw shape (its type returns its family), the declaration installed below `env`. A rule's
constructor that is a container's (`CompiledInductive.rule_ctor_cases`) is the constructor of
the container's own rule, registered strictly earlier. -/
theorem WF'.patCtor_provenance : ∀ {ds : List VDecl} {env : VEnv}, env.WF' ds →
    ∀ {c : Name}, IsPatCtor env c →
    ∃ (decl : VInductDecl) (type : VInductiveType) (ctor : VConstVal) (env₀ env₁ : VEnv),
      VDecl.induct decl ∈ ds ∧ type ∈ decl.types ∧ ctor ∈ type.ctors ∧ ctor.name = c ∧
      decl.RawCtorShape type ctor ∧ decl.WF env₀ ∧ env₀.addInduct decl = some env₁ ∧
      env₁ ≤ env := by
  suffices ∀ n, ∀ {ds : List VDecl}, ds.length = n → ∀ {env : VEnv}, env.WF' ds →
      ∀ {c : Name}, IsPatCtor env c →
      ∃ (decl : VInductDecl) (type : VInductiveType) (ctor : VConstVal) (env₀ env₁ : VEnv),
        VDecl.induct decl ∈ ds ∧ type ∈ decl.types ∧ ctor ∈ type.ctors ∧ ctor.name = c ∧
        decl.RawCtorShape type ctor ∧ decl.WF env₀ ∧ env₀.addInduct decl = some env₁ ∧
        env₁ ≤ env from
    fun {ds env} H {c} hc => this ds.length rfl H hc
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro ds hn env H c hc
  obtain ⟨p, rr, recN, M, N, hp, rfl⟩ := hc
  obtain ⟨decl, ds₀, env₀, env₁, hsuf, H₀, hdecl, hadd, hle, rec, hrec, ru, hru, -, hpe, -⟩ :=
    H.pats_origin hp
  obtain ⟨-, -, rfl, -⟩ := SimplePattern.iota_toPattern_inj hpe
  have hmem : VDecl.induct decl ∈ ds := hsuf.subset (List.mem_cons_self ..)
  obtain ⟨block, hcomp, hrecs⟩ := hdecl.recsCompiled
  rcases hcomp.rule_ctor_cases hrecs.1 hrec hru with ⟨ctor, hctor, hname⟩ | hpat
  · obtain ⟨type, htype, hctor'⟩ := List.mem_flatMap.1 hctor
    obtain ⟨base, expanded, s, g, auxiliaries, -, hdata, -⟩ := hcomp.exists_compilation
    obtain ⟨-, -, -, -, -, hraw⟩ := hdata.sourceParameters
    exact ⟨decl, type, ctor, env₀, env₁, hmem, htype, hctor', hname.symm,
      hraw type htype ctor hctor', hdecl, hadd, hle⟩
  · have hlt : ds₀.length < ds.length := by
      have := hsuf.length_le
      simp at this
      omega
    obtain ⟨decl', type, ctor, env₀', env₁', hmem', htype, hctor, hname, hraw, hdecl', hadd', hle'⟩ :=
      ih ds₀.length (hn ▸ hlt) rfl H₀ hpat
    exact ⟨decl', type, ctor, env₀', env₁', ((List.suffix_cons _ _).trans hsuf).subset hmem',
      htype, hctor, hname, hraw, hdecl', hadd', hle'.trans ((addInduct_le hadd).trans hle)⟩

/-- **Pattern constructors and their families are rigid.** -/
theorem WF'.patCtor_rigid_resultRigid {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    {c : Name} (hc : IsPatCtor env c) : env.Rigid c ∧ env.CtorResultRigid c := by
  obtain ⟨decl, type, ctor, env₀, env₁, hmem, htype, hctor, rfl, hraw, -, hadd, hle⟩ :=
    H.patCtor_provenance hc
  refine ⟨H.inductCtorRigid hmem htype hctor, ctor.toVConstant,
    hle.constants (addInduct_ctor_find hadd htype hctor), type.name, VLevel.params decl.uvars,
    hraw.forallResult_head, ⟨_, hle.constants (addInduct_type_find hadd htype)⟩,
    H.inductTypeRigid hmem htype⟩

/-- The constructor of a registered ι rule is rigid. -/
theorem WF.patCtor_rigid' {env : VEnv} (henv : env.WF) {c : Name} (h : IsPatCtor env c) :
    env.Rigid c :=
  let ⟨_, H⟩ := henv; (H.patCtor_rigid_resultRigid h).1

/-- The constructor of a registered ι rule returns an application of a present rigid type
former. -/
theorem WF.patCtor_resultRigid {env : VEnv} (henv : env.WF) {c : Name} (h : IsPatCtor env c) :
    env.CtorResultRigid c :=
  let ⟨_, H⟩ := henv; (H.patCtor_rigid_resultRigid h).2

end VEnv
end Lean4Lean
