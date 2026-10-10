import Lean4Lean.Verify.Inductive.Rules.IotaPatTyped
import Lean4Lean.Verify.Inductive.Rules.EquationWF
import Lean4Lean.Verify.Inductive.Recursor.Metadata
import Lean4Lean.Verify.Inductive.Recursor.Signature.RecursiveShapeTranslations
import Lean4Lean.Verify.Inductive.Recursor.Signature.Constructors

/-! Translation of a rule's type and left-hand side to the generator's equation
(`RecursorInstallation.RuleAlignment.typeTranslation`, `lhsTranslation`), and the reduction of the
generator body translations to their right-hand side component
(`equationBodyTranslationsOfClosedRhs`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-! ### Generator-side syntax -/

theorem RuleLhs.wrapForalls_app_inj : ∀ {l₁ l₂ : List VExpr} {f₁ a₁ f₂ a₂ : VExpr},
    VExpr.wrapForalls l₁ (.app f₁ a₁) = VExpr.wrapForalls l₂ (.app f₂ a₂) →
      l₁ = l₂ ∧ VExpr.app f₁ a₁ = .app f₂ a₂
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, _, _, h => by simp [VExpr.wrapForalls] at h
  | _ :: _, [], _, _, _, _, h => by simp [VExpr.wrapForalls] at h
  | x :: xs, y :: ys, _, _, _, _, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.forallE.injEq] at h
    obtain ⟨hl, hr⟩ := RuleLhs.wrapForalls_app_inj (l₁ := xs) (l₂ := ys) h.2
    exact ⟨by rw [h.1, hl], hr⟩

/-- A generated minor is a telescope over its fields and induction hypotheses
of the motive at the constructor. -/
theorem RuleLhs.minor_split {s : InductiveSignature}
    (g : InductiveSignature.Instance s) (index : Fin s.constructors.size) :
    ∃ domains nh, domains.length = s.constructors[index].fields.length + nh ∧
      g.minor s.constructors[index] index =
        VExpr.wrapForalls domains (VExpr.mkApps
          (.bvar (s.constructors[index].fields.length + nh + index.val +
            (s.families.size - 1 - s.constructors[index].owner.val)))
          (s.constructors[index].indices.map (fun e =>
              ((e.instL g.levels).liftN nh).liftN (s.families.size + index.val)
                (s.constructors[index].fields.length + nh)) ++
            [g.constructorApp s.constructors[index] (s.families.size + index.val) nh])) := by
  refine ⟨_, _, ?_, rfl⟩
  simp [InductiveSignature.insertBinders, InductiveSignature.fieldTypes]

/-- The residual of a generated minor, weakened past the later minors, is the
generated equation type weakened past the induction hypotheses. -/
theorem RuleLhs.minorResidual_liftN {s : InductiveSignature}
    (g : InductiveSignature.Instance s) (index : Fin s.constructors.size) (nh : Nat) :
    (VExpr.mkApps
      (.bvar (s.constructors[index].fields.length + nh + index.val +
        (s.families.size - 1 - s.constructors[index].owner.val)))
      (s.constructors[index].indices.map (fun e =>
          ((e.instL g.levels).liftN nh).liftN (s.families.size + index.val)
            (s.constructors[index].fields.length + nh)) ++
        [g.constructorApp s.constructors[index] (s.families.size + index.val) nh])).liftN
      (s.constructors.size - index.val) (s.constructors[index].fields.length + nh) =
    (g.equationTypeBody index).liftN nh := by
  have hidx := index.isLt
  simp only [InductiveSignature.Instance.equationTypeBody,
    InductiveSignature.Instance.equationIndices, InductiveSignature.Instance.equationMajor,
    InductiveSignature.Instance.constructorApp, VExpr.liftN_mkApps, List.map_append,
    List.map_map, List.map_cons, List.map_nil]
  congr 1
  · simp only [VExpr.liftN, liftVar]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1
    omega
  · congr 1
    · apply List.map_congr_left
      intro e _
      simp only [Function.comp_def]
      rw [VExpr.liftN'_liftN_hi, VExpr.liftN_liftN_comm _ _ _ _ _ (Nat.zero_le _)]
      rw [show s.families.size + index.val + (s.constructors.size - index.val) =
        s.families.size + s.constructors.size by omega]
    · simp only [List.cons.injEq, and_true]
      have e1 := InductiveSignature.vars_map_liftN_hi (count := s.params.length)
        (below := s.families.size + index.val + s.constructors[index].fields.length + nh)
        (n := s.constructors.size - index.val) (k := s.constructors[index].fields.length + nh)
        (by omega)
      have e2 := InductiveSignature.vars_map_liftN_lo (count := s.constructors[index].fields.length)
        (below := nh)
        (n := s.constructors.size - index.val) (k := s.constructors[index].fields.length + nh)
        (by omega)
      have e3 := InductiveSignature.vars_map_liftN_hi (count := s.params.length)
        (below := s.families.size + s.constructors.size + s.constructors[index].fields.length + 0)
        (n := nh) (k := 0) (Nat.zero_le _)
      have e4 := InductiveSignature.vars_map_liftN_hi (count := s.constructors[index].fields.length)
        (below := 0) (n := nh) (k := 0) (Nat.zero_le _)
      rw [e1, e2, e3, e4]
      rw [show s.families.size + index.val + s.constructors[index].fields.length + nh +
          (s.constructors.size - index.val) =
        s.families.size + s.constructors.size + s.constructors[index].fields.length + 0 + nh by
          omega]
      simp [VExpr.liftN]

theorem RuleLhs.abstractList_mem_bvar {fvs : List FVarId} (hnd : fvs.Nodup)
    {fv : FVarId} (h : fv ∈ fvs) :
    ∃ j, j < fvs.length ∧ (Expr.fvar fv).abstractList fvs = .bvar j := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨fvs.length - 1 - j, by omega, by simpa using Expr.abstractList_fvar_getElem hnd j hj (k := 0)⟩

theorem RuleLhs.ofFn_bvar_take (N n : Nat) (h : n ≤ N) :
    List.take n (List.ofFn fun i : Fin N => Expr.bvar (N - 1 - i)) =
      List.ofFn fun i : Fin n => Expr.bvar ((N - n) + (n - 1 - i)) := by
  apply List.ext_getElem
  · simp [h]
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    congr 1
    simp at h2
    omega

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

theorem RecursorInstallation.RuleAlignment.typeTranslation
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size) :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (H.canonicalGeneration.equationDomains ⟨recursorMinorOffset indTypes owner + i, hk⟩) [])
      ((Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats A.rule.target).2)
        A.rule.sourceConstructorMajor).abstractList A.rule.binders)
      (H.canonicalGeneration.equationTypeBody ⟨recursorMinorOffset indTypes owner + i, hk⟩) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let expected := Expr.app
    (mkAppN H.recInfos[owner]!.motive
      (AddInductive.getIIndices stats A.rule.target).2)
    A.rule.sourceConstructorMajor
  rcases A.equationFrame with ⟨F⟩
  obtain ⟨_hk, hown, hnf⟩ := A.generatedConstructor
  have D := F.domains_defeq hk hnf
  obtain ⟨Y, HY⟩ := F.type_translation.defeqDFC H.outVEnvWF (abstractForallContext.isDefEq D)
  suffices hY : Y = H.canonicalGeneration.equationTypeBody ⟨minorIdx, hk⟩ by
    rw [← hY]; exact HY
  rcases A.installedSelectedMinorAlignedResidual with
    ⟨T, S, traversal, HS, _hypothesisOrigins,
      fieldDomains, hypothesisDomains, targetResidual,
      _hhypothesisStats, _hhypothesisRecInfos, hconstructor,
      htraversalFields, hfieldFVars, hclosedTargets, _hselectedOwner,
      hvalid, hmotiveApp, hsourceFields, hsourceHypotheses,
      hfields, hhypotheses, hminorType,
      HsourceResidual, _HsourceResidualType⟩
  have hfieldClosure := A.alignedMotiveAppFieldClosure S traversal
    hconstructor hclosedTargets hvalid
      hmotiveApp hsourceFields
  have hsourceAligned := A.alignedPositiveResidualSource S HS traversal
    hmotiveApp hfieldClosure hsourceFields hsourceHypotheses
  let remaining := T.minors.drop minorIdx
  have hremainingSourceLength :
      (A.rule.minors_bound.fvars.drop minorIdx).length = remaining.length := by
    simp [remaining, A.rule.minors_bound.length_fvars, T.minors_length]
  let sourceOuter := T.params ++ T.motives ++ T.minors.take minorIdx
  have HsourceResidual' : TrExprS H.outVEnv Us
      (abstractForallContext
        (sourceOuter ++ (fieldDomains ++ hypothesisDomains)) [])
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size))
      targetResidual := by
    simpa [sourceOuter, abstractForallContext, List.reverse_append,
      List.map_append, List.append_assoc] using HsourceResidual
  have Hinserted₀ := Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
    (outer := sourceOuter) (inner := fieldDomains ++ hypothesisDomains)
    H.outVEnvWF.orderedStrong HsourceResidual' remaining
  have hinnerLength : (fieldDomains ++ hypothesisDomains).length =
      A.rule.allArgs.size + A.rule.recursiveArgs.size := by
    simp [hfields, hhypotheses]
  have hsourceAligned' := hsourceAligned
  simp only [minorIdx, hremainingSourceLength] at hsourceAligned'
  rw [hinnerLength] at Hinserted₀
  rw [hsourceAligned'] at Hinserted₀
  dsimp only at Hinserted₀
  have HYweak := HY.weakBV H.outVEnvWF.orderedStrong
    (abstractForallContext.bvLift hypothesisDomains
      (abstractForallContext
        (H.canonicalGeneration.equationDomains ⟨minorIdx, hk⟩) []))
  rw [abstractForallContext_append, hhypotheses] at HYweak
  have hlift := HYweak.uniqueCtx (abstractForallContext.isUniqueCtx ?_) Hinserted₀
  rotate_left
  · have hlen : (H.canonicalGeneration.equationDomains ⟨minorIdx, hk⟩).length =
        A.rule.binders.length := A.equationDomains_length hk
    simp only [List.length_append, hlen]
    simp [remaining, sourceOuter, hhypotheses, hfields, RecursorRuleSyntax.binders,
      T.params_length, T.motives_length, T.minors_length, FVarArrayIn.length_fvars]
    omega
  obtain ⟨tf, ta, htargetApp⟩ : ∃ tf ta, targetResidual = .app tf ta := by
    rw [hmotiveApp] at HsourceResidual
    simp only [Expr.abstractList_app] at HsourceResidual
    cases HsourceResidual
    exact ⟨_, _, rfl⟩
  obtain ⟨-, -, hminors⟩ := H.telescope_groups howner T
  have hkm : minorIdx < T.minors.length := by
    rw [hminors, InductiveSignature.Instance.length_minors]; exact hk
  rw [getElem!_pos T.minors _ hkm] at hminorType
  have hget : T.minors[minorIdx] =
      H.canonicalGeneration.minor H.generationSignature.constructors[minorIdx] minorIdx := by
    rw [List.getElem_of_eq hminors hkm]
    exact InductiveSignature.Instance.minors_getElem _ _ hk
  rw [hget] at hminorType
  obtain ⟨doms, nh, hdomsLen, hsplit⟩ :=
    RuleLhs.minor_split H.canonicalGeneration ⟨minorIdx, hk⟩
  simp only [Fin.getElem_fin] at hsplit hdomsLen
  rw [hsplit, VExpr.mkApps_snoc, htargetApp] at hminorType
  obtain ⟨hdoms, hres⟩ := RuleLhs.wrapForalls_app_inj hminorType
  have hnf' : (H.generationSignature.constructors[minorIdx]).fields.length =
      A.rule.allArgs.size := hnf
  have hnh : nh = A.rule.recursiveArgs.size := by
    have := congrArg List.length hdoms
    simp only [List.length_append, hfields, hhypotheses, hdomsLen, hnf'] at this
    omega
  subst hnh
  have hrem : remaining.length = H.generationSignature.constructors.size - minorIdx := by
    simp [remaining, hminors, InductiveSignature.Instance.length_minors]
  rw [htargetApp, ← hres, ← VExpr.mkApps_snoc, hrem, ← hnf'] at hlift
  have key := RuleLhs.minorResidual_liftN H.canonicalGeneration ⟨minorIdx, hk⟩
    A.rule.recursiveArgs.size
  simp only [Fin.getElem_fin] at key
  rw [key] at hlift
  exact VExpr.liftN_inj.mp hlift

theorem RecursorInstallation.RuleAlignment.lhsTranslation
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size) :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (H.canonicalGeneration.equationDomains ⟨recursorMinorOffset indTypes owner + i, hk⟩) [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders)
      (H.canonicalGeneration.equationLhsBody ⟨recursorMinorOffset indTypes owner + i, hk⟩) := by
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.equationFrame with ⟨F⟩
  obtain ⟨_hk, hown, hnf⟩ := A.generatedConstructor
  have D := F.domains_defeq hk hnf
  obtain ⟨L, HL⟩ := F.lhs_translation.defeqDFC H.outVEnvWF (abstractForallContext.isDefEq D)
  suffices hL : L = H.canonicalGeneration.equationLhsBody ⟨minorIdx, hk⟩ by
    rw [← hL]; exact HL
  have HY := A.typeTranslation hk
  have hownerIdx : (AddInductive.getIIndices stats A.rule.target).1 = owner :=
    (checkPositivityStep.getIIndices.fst_eq_of_valid A.typing.target_valid).trans A.typing_owner
  rcases htarget : AddInductive.getIIndices stats A.rule.target with ⟨ownerIdx, indices⟩
  rw [htarget] at hownerIdx HY
  dsimp only at hownerIdx HY
  subst ownerIdx
  obtain ⟨recLevels, leadingArgs, ctorLevels, ctorArgs, hLeq, hrecLevels, -, Hleading, -⟩ :=
    A.rule.translatedLhsResidual htarget HL
  have HL' := HL
  simp only [RecursorRuleSyntax.sourceLhsBody, htarget, Expr.abstractList_app] at HL'
  simp only [Expr.abstractList_app] at HY
  rw [InductiveSignature.Instance.equationTypeBody, VExpr.mkApps_snoc] at HY
  cases HY with
  | app _ _ HY1 HY2 =>
  cases HL' with
  | app _ _ HL1 HL2 =>
  have hmajor := TrExprS.unique HL2 HY2
  subst hmajor
  rw [VExpr.mkApps_snoc] at hLeq
  injection hLeq with hhead _
  subst hhead
  rw [Expr.abstractList_mkAppN, Expr.mkAppN_eq_mkAppList] at HY1
  obtain ⟨motiveT, idxY, HmotiveT, HidxY, hY1⟩ := checkPositivityStep.TrExprS.mkAppList_inv HY1
  have hdomainsLength : (H.canonicalGeneration.equationDomains ⟨minorIdx, hk⟩).length =
      A.rule.binders.length := A.equationDomains_length hk
  have hbindersNodup : A.rule.binders.Nodup := A.rule.binders_nodup
  have hrec : owner < H.recInfos.size := A.minorOrigin.owner_lt
  have hmotiveLt : owner < (H.recInfos.map (·.motive)).size := by simpa using hrec
  obtain ⟨hmotiveFVars, hmotiveFVar⟩ := A.rule.motives_bound.getElem_eq_fvar owner hmotiveLt
  have hmotive : H.recInfos[owner]!.motive =
      .fvar (A.rule.motives_bound.fvars[owner]'hmotiveFVars) := by
    rw [← hmotiveFVar]; simp [getElem!_pos, hrec]
  have hmem : A.rule.motives_bound.fvars[owner]'hmotiveFVars ∈ A.rule.binders := by
    unfold RecursorRuleSyntax.binders
    exact List.mem_append_left _ <| List.mem_append_left _ <|
      List.mem_append_right _ (List.getElem_mem hmotiveFVars)
  obtain ⟨j, hj, hjeq⟩ := RuleLhs.abstractList_mem_bvar hbindersNodup hmem
  rw [hmotive, hjeq] at HmotiveT
  have hmotiveT := TrExprS.bvar_eq_of_abstractForallContext HmotiveT
    (lt_of_lt_of_eq hj hdomainsLength.symm)
  subst hmotiveT
  have hidx := congrArg VExpr.getAppFnArgs hY1
  simp only [VExpr.getAppFnArgs_mkApps_bvar, Prod.mk.injEq] at hidx
  obtain ⟨-, hidxY⟩ := hidx
  subst hidxY
  obtain ⟨pmm, idxL, rfl, Hpmm, HidxL⟩ := checkPositivityStep.List.Forall₂.split_left Hleading
  have hidxL := TrExprS.forall₂_uniqueS HidxL HidxY
  subst hidxL
  let n := stats.params.size + (H.recInfos.map (·.motive)).size +
    (H.recInfos.flatMap (·.minors)).size
  have hbindersLength : A.rule.binders.length = n + A.rule.allArgs.size := by
    simp [n, RecursorRuleSyntax.binders, FVarArrayIn.length_fvars]
    omega
  have hsource :
      (stats.params.map fun arg => arg.abstractList A.rule.binders).toList ++
        ((H.recInfos.map (·.motive)).map fun arg => arg.abstractList A.rule.binders).toList ++
        ((H.recInfos.flatMap (·.minors)).map fun arg => arg.abstractList A.rule.binders).toList =
      List.ofFn fun j : Fin n => Expr.bvar (A.rule.allArgs.size + (n - 1 - j)) := by
    have hsplit : (((stats.params ++ H.recInfos.map (·.motive) ++
          H.recInfos.flatMap (·.minors) ++ A.rule.allArgs).map
          fun arg => arg.abstractList A.rule.binders).toList) =
        ((stats.params.map fun arg => arg.abstractList A.rule.binders).toList ++
          ((H.recInfos.map (·.motive)).map fun arg => arg.abstractList A.rule.binders).toList ++
          ((H.recInfos.flatMap (·.minors)).map fun arg => arg.abstractList A.rule.binders).toList) ++
        (A.rule.allArgs.map fun arg => arg.abstractList A.rule.binders).toList := by
      simp only [Array.map_append, Array.toList_append]
    have h := congrArg (List.take n) (hsplit.symm.trans A.rule.abstractedBinders_eq)
    rw [List.take_left' (by simp only [n, List.length_append, Array.length_toList,
        Array.size_map]), RuleLhs.ofFn_bvar_take _ _ (by omega),
      show A.rule.binders.length - n = A.rule.allArgs.size by omega] at h
    exact h
  rw [hsource] at Hpmm
  have hpmm := TrExprS.shiftedBvarSpine_eq Hpmm
    (Nat.le_of_eq (hbindersLength.symm.trans hdomainsLength.symm))
  subst hpmm
  have hn : n = H.generationSignature.params.length +
      (H.generationSignature.families.size + H.generationSignature.constructors.size) := by
    simp only [n, H.params_size_eq, H.motives_size_eq, H.minors_size_eq]
    omega
  have hlevels := R.recursorHeaders.recursorLevelsTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have hrecLevels' : recLevels = VLevel.params H.canonicalGeneration.uvars :=
    Option.some.inj (hrecLevels.symm.trans hlevels)
  have hname : H.canonicalGeneration.recursorName
      H.generationSignature.constructors[minorIdx].owner =
      mkRecName indTypes[owner]!.name := by
    refine (H.generator.names _).trans ?_
    have hfam := H.generator.familyName _
      (Fin.isLt H.generationSignature.constructors[minorIdx].owner)
    show (H.generator.signature.families[
      (H.generationSignature.constructors[minorIdx].owner : Nat)]'(Fin.isLt _)).name.str "rec" = _
    rw [hfam]
    have hown' : (H.generationSignature.constructors[minorIdx].owner : Nat) = owner := hown
    rw [hown']
    rfl
  rw [hn, hrecLevels', ← hnf]
  simp only [InductiveSignature.Instance.equationLhsBody,
    InductiveSignature.Instance.recursorHead, Fin.getElem_fin, hname]
  rw [VExpr.mkApps_snoc]

/-- A rule body whose binder abstraction translates in a context of exactly
the rule's binders has no loose bound variables. -/
theorem RuleLhs.closed_of_abstractedTranslation {env : VEnv} {Us : List Name}
    {domains : List VExpr} {binders : List FVarId} {body : Expr} {out : VExpr}
    (hlen : domains.length = binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains []) (body.abstractList binders) out) :
    Closed body := by
  have h := Htr.closed
  simp only [abstractForallContext_bvars, VLCtx.bvars, hlen, Nat.add_zero] at h
  exact Expr.closed_of_abstractList (depth := 0) (by simpa using h)

theorem RecursorInstallation.RuleAlignment.sourceRhsBody_closed
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    Closed A.rule.sourceRhsBody := by
  rcases A.equationFrame with ⟨F⟩
  obtain ⟨hk, -, hnf⟩ := A.generatedConstructor
  have hlen := (F.domains_defeq hk hnf).length_eq
  simp only [List.length_reverse] at hlen
  exact RuleLhs.closed_of_abstractedTranslation (hlen.trans (A.equationDomains_length hk))
    F.rhs_translation

/-- The generator body translations reduce to the RHS component. -/
theorem RecursorInstallation.RuleAlignment.equationBodyTranslationsOfRhs
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size)
    (Hrhs : TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (H.canonicalGeneration.equationDomains ⟨recursorMinorOffset indTypes owner + i, hk⟩) [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders)
      (H.canonicalGeneration.equationRhsBody ⟨recursorMinorOffset indTypes owner + i, hk⟩)) :
    A.EquationBodyTranslations hk :=
  ⟨A.lhsTranslation hk, Hrhs, A.typeTranslation hk⟩

/-- The generator body translations from a closed translation of the
installed rule RHS to the generator's equation RHS. -/
theorem RecursorInstallation.RuleAlignment.equationBodyTranslationsOfClosedRhs
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size)
    (Htr : TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      ((H.generated.entry owner howner).info.rules[i]'A.sourceRule_lt).rhs
      (H.canonicalGeneration.equation ⟨recursorMinorOffset indTypes owner + i, hk⟩).rhs) :
    A.EquationBodyTranslations hk :=
  A.equationBodyTranslationsOfRhs hk (A.rhsResidualOfClosed hk A.sourceRhsBody_closed Htr)

end
end VerifyInductive
end Lean4Lean
