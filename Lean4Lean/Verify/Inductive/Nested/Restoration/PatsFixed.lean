import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Theory.Typing.PatsIota
import Lean4Lean.Theory.Inductive.RestorationInterpretation

/-! # Registered ι rules are fixed by interpretations of fresh names

Every registered pattern of a well-formed environment is the ι entry of a rule of an installed
block (`VEnv.WF'.pats_origin`): its key names the recursor and the rule's constructor, both
constants of the environment, and its reduct is the rule's closed template applied to holes,
the template being typed in the block's recursor stage. So an interpretation that only moves
names absent from the environment fixes the key's constants and the reduct's fixed term
(`VEnv.WF.pats_fixed_of_avoid`). -/

namespace Lean4Lean

open Lean (Name)

/-- The closed template of a rule of a freshly installed well-formed declaration avoids the
names absent from the resulting environment. -/
theorem VEnv.addInduct_rule_templateAvoids {env env' : VEnv} (hW : env.WF)
    {decl : VInductDecl} (hdecl : decl.WF env) (hadd : env.addInduct decl = some env')
    {names : List Name} (Hfresh : ∀ name ∈ names, env'.constants name = none)
    {rec : VRecursor} (hrec : rec ∈ decl.recs) {ru : VRecRule} (hru : ru ∈ rec.rules) :
    ru.rhs.containsAnyConst names = false := by
  obtain ⟨block, base, expanded, s, g, aux, hcomp, hrecsOf, hWF, -, -, -, df, hdf, hOf⟩ :=
    hdecl.rule_block hrec hru
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
  have hPstage : decl.addTypesCtorsProjs env = some (decl.addProjs envC) :=
    VEnv.addTypesCtorsProjs_eq_some (Option.bind_eq_some_iff.2 ⟨envT, hT, hC⟩)
  have hRstage : decl.addTypesCtorsProjsRecs env = some envR := by
    unfold VInductDecl.addTypesCtorsProjsRecs; rw [hPstage]; exact hR
  have hordR : VEnv.Ordered envR :=
    VEnv.addRecs_ordered hdecl hPstage (VEnv.addTypesCtorsProjs_ordered hW.ordered hdecl hPstage)
      hR
  have hfreshR : ∀ n ∈ names, envR.constants n = none :=
    fun n hn => (VEnv.addRules_le hP).constants_eq_none_left (Hfresh n hn)
  have hwf := VInductDecl.WF.block_rules_wf hcomp hrecsOf hWF hRstage df hdf
  have := (VEnv.IsDefEq.noFreshConsts' hordR hfreshR CtxAvoidsConsts.nil hwf.2).1
  rwa [hOf.1] at this

/-- **The registered ι entries of a well-formed environment, with what an interpretation of
fresh names needs.** Each is the ι entry of a rule whose recursor and constructor are constants
of the environment and whose template avoids every name absent from it. -/
theorem VEnv.WF'.pats_iota_avoid {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    {names : List Name} (Hfresh : ∀ name ∈ names, env.constants name = none)
    {p rr} (hp : env.pats p rr) :
    ∃ (rec : VRecursor) (ru : VRecRule) (hc : ru.rhs.Closed)
      (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
        (ru.ctorParams + ru.nfields)).toPattern),
      e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
        rec.numParams rec.numMotives rec.numMinors rec.numIndices ru.ctorParams ru.nfields
        ru.rhs hc, .true) ∧
      ru.rhs.containsAnyConst names = false ∧
      (∃ ci, env.constants rec.name = some ci) ∧ (∃ ci, env.constants ru.ctor = some ci) := by
  obtain ⟨decl, ds₀, env₀, env₁, -, hwf', hdecl, hadd, hle, rec, hrec, ru, hru, hc, e, hrr⟩ :=
    H.pats_origin hp
  have hfresh₁ : ∀ n ∈ names, env₁.constants n = none :=
    fun n hn => hle.constants_eq_none_left (Hfresh n hn)
  obtain ⟨ci, hci, -⟩ := VEnv.addInduct_rule_ctor hdecl hadd hrec hru
  exact ⟨rec, ru, hc, e, hrr,
    VEnv.addInduct_rule_templateAvoids ⟨ds₀, hwf'⟩ hdecl hadd hfresh₁ hrec hru,
    ⟨_, hle.constants (VEnv.addInduct_rec_find hadd hrec)⟩, ⟨ci, hle.constants hci⟩⟩

theorem Pattern.ConstsFixed_varN {I : VEnv.Interpretation} {q : Pattern} :
    ∀ k, (q.varN k).ConstsFixed I ↔ q.ConstsFixed I
  | 0 => Iff.rfl
  | k + 1 => by simp only [Pattern.varN, Pattern.ConstsFixed]; exact ConstsFixed_varN k

theorem Pattern.RHS.FixedTermsFixed_foldl_var {I : VEnv.Interpretation} {p : Pattern} :
    ∀ (l : List p.Path) (f : p.RHS),
      ((l.map Pattern.RHS.var).foldl Pattern.RHS.app f).FixedTermsFixed I ↔ f.FixedTermsFixed I
  | [], _ => Iff.rfl
  | x :: l, f => by
    rw [List.map_cons, List.foldl_cons, FixedTermsFixed_foldl_var l]
    simp [Pattern.RHS.FixedTermsFixed]

/-- **Registered ι rules are fixed by an interpretation of fresh names.** An interpretation
that leaves every name outside `names` alone (constant, renaming, projection owner) keeps the
key constants and the reduct's fixed terms of every rule of a well-formed environment in which
`names` are fresh. -/
theorem VEnv.WF.pats_fixed_of_avoid {env : VEnv} (henv : env.WF) {I : VEnv.Interpretation}
    {names : List Name} (Hfresh : ∀ name ∈ names, env.constants name = none)
    (hc : ∀ c, c ∉ names → I.consts c = none) (hr : ∀ c, c ∉ names → I.rename c = c)
    (hpo : ∀ c, c ∉ names → I.projOwner c = c) :
    ∀ p rr, env.pats p rr → p.ConstsFixed I ∧ rr.1.FixedTermsFixed I ∧
      rr.2.FixedTermsFixed I := by
  intro p rr hp
  obtain ⟨ds, H⟩ := henv
  obtain ⟨rec, ru, hcl, rfl, hrr, havoid, ⟨_, hrecC⟩, ⟨_, hctorC⟩⟩ :=
    H.pats_iota_avoid Hfresh hp
  subst hrr
  have hnot : ∀ {n ci}, env.constants n = some ci → n ∉ names := by
    intro n ci h hn; rw [Hfresh n hn] at h; cases h
  refine ⟨?_, ?_, trivial⟩
  · simp only [SimplePattern.toPattern, Pattern.ConstsFixed, Pattern.ConstsFixed_varN]
    exact ⟨⟨hc _ (hnot hrecC), hr _ (hnot hrecC)⟩, ⟨hc _ (hnot hctorC), hr _ (hnot hctorC)⟩⟩
  · show (SimplePattern.iotaRHS' _ _ _ _ _ _ _ _).FixedTermsFixed I
    unfold SimplePattern.iotaRHS'
    rw [Pattern.RHS.FixedTermsFixed_foldl_var]
    exact VEnv.Interpretation.expr_eq_self_of_avoid hc hr hpo havoid

end Lean4Lean
