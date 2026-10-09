import Lean4Lean.Theory.Inductive

namespace Lean4Lean

namespace VExpr

@[simp] theorem containsAnyConst_liftN
    (e : VExpr) (names : List Lean.Name) (n k : Nat) :
    (e.liftN n k).containsAnyConst names = e.containsAnyConst names := by
  induction e generalizing k <;>
    simp [VExpr.liftN, VExpr.containsAnyConst, *]

theorem containsAnyConst_inst_eq_false
    (body arg : VExpr) (k : Nat)
    (hbody : body.containsAnyConst names = false)
    (harg : arg.containsAnyConst names = false) :
    (body.inst arg k).containsAnyConst names = false := by
  induction body generalizing k <;>
    simp_all [VExpr.inst, VExpr.containsAnyConst]
  case bvar i =>
    simp only [VExpr.instVar]
    split
    · rfl
    · split
      · simpa using harg
      · rfl

end VExpr

/-- Every type stored in a local typing context avoids `names`. -/
def CtxAvoidsConsts (names : List Lean.Name) (Gamma : List VExpr) : Prop :=
  ∀ type ∈ Gamma, type.containsAnyConst names = false

theorem CtxAvoidsConsts.cons
    (H : CtxAvoidsConsts names Gamma)
    (hA : A.containsAnyConst names = false) :
    CtxAvoidsConsts names (A :: Gamma) := by
  intro type htype
  simp only [List.mem_cons] at htype
  rcases htype with rfl | htype
  · exact hA
  · exact H type htype

theorem Lookup.noConsts
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : Lookup Gamma index type) :
    type.containsAnyConst names = false := by
  induction H with
  | zero =>
      simp only [VExpr.containsAnyConst_liftN]
      exact Hctx _ (by simp)
  | @succ Gamma index type domain H ih =>
      have htail : CtxAvoidsConsts names Gamma := by
        intro current hcurrent
        exact Hctx current (by simp [hcurrent])
      simpa using VExpr.containsAnyConst_liftN
        (e := type) (names := names) 1 0 |>.trans (ih htail)

/-- A typing derivation cannot introduce a selected constant when the
environment declarations used by `constDF`/`extra`, the local context, and
all directly looked-up constants avoid it.  The result is simultaneous for
both endpoints and the inferred type because eta/beta expose type syntax. -/
theorem VEnv.IsDefEq.noConsts
    (Htypes : OnTypes env fun _ e A =>
      e.containsAnyConst names = false ∧
      A.containsAnyConst names = false)
    (Hfresh : ∀ {name ci}, env.constants name = some ci → name ∉ names)
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : env.IsDefEq U Gamma lhs rhs type) :
    lhs.containsAnyConst names = false ∧
    rhs.containsAnyConst names = false ∧
    type.containsAnyConst names = false := by
  induction H with
  | bvar Hlookup =>
      exact ⟨rfl, rfl, Hlookup.noConsts Hctx⟩
  | symm _ ih =>
      specialize ih Hctx
      exact ⟨ih.2.1, ih.1, ih.2.2⟩
  | trans _ _ ihLeft ihRight =>
      specialize ihLeft Hctx
      specialize ihRight Hctx
      exact ⟨ihLeft.1, ihRight.2.1, ihLeft.2.2⟩
  | sortDF => exact ⟨rfl, rfl, rfl⟩
  | @constDF c ci levels levels' Gamma Hlookup _ _ _ _ =>
      have hname : names.contains c = false := by
        exact Bool.eq_false_iff.mpr fun hcontains =>
          Hfresh Hlookup (by simpa using hcontains)
      have htype := (Htypes.1 Hlookup).choose_spec.1
      exact ⟨hname, hname, by simpa using htype⟩
  | elimDF _ _ _ _ _ _ _ ih =>
      exact ⟨rfl, rfl, (ih Hctx).1⟩
  | elimIota _ _ _ _ _ _ _ ihLeft ihRight =>
      exact ⟨(ihLeft Hctx).1, (ihRight Hctx).1, (ihLeft Hctx).2.2⟩
  | appDF _ _ ihFn ihArg =>
      specialize ihFn Hctx
      specialize ihArg Hctx
      rcases ihFn with ⟨hfn, hfn', hforall⟩
      rcases ihArg with ⟨harg, harg', hA⟩
      simp only [VExpr.containsAnyConst,
        Bool.or_eq_false_iff] at hforall
      exact ⟨Bool.or_eq_false_iff.mpr ⟨hfn, harg⟩,
        Bool.or_eq_false_iff.mpr ⟨hfn', harg'⟩,
        VExpr.containsAnyConst_inst_eq_false _ _ _ hforall.2 harg⟩
  | @projDF typeName info levels params index sourceMajor fieldType Gamma
      fieldLevel major indexArgs major'
      hinfo hlevels huvars hparams hindices hfield hfieldTyping
      hmajor hmajor' _ _ ihField ihMajor ihMajor' =>
      specialize ihField Hctx
      specialize ihMajor Hctx
      specialize ihMajor' Hctx
      have howner :=
        (VExpr.containsAnyConst_mkApps_eq_false_iff
          (.const typeName levels) (params ++ indexArgs)).mp ihMajor.2.2
      have hname : names.contains typeName = false := by
        simpa [VExpr.containsAnyConst] using howner.1
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff]
      exact ⟨⟨hname, ihMajor.2.1⟩,
        ⟨hname, ihMajor'.2.1⟩, ihField.1⟩
  | lamDF _ _ ihType ihBody =>
      specialize ihType Hctx
      rcases ihType with ⟨hA, hA', _⟩
      rcases ihBody (Hctx.cons hA) with ⟨hbody, hbody', hB⟩
      exact ⟨Bool.or_eq_false_iff.mpr ⟨hA, hbody⟩,
        Bool.or_eq_false_iff.mpr ⟨hA', hbody'⟩,
        Bool.or_eq_false_iff.mpr ⟨hA, hB⟩⟩
  | forallEDF _ _ ihType ihBody =>
      specialize ihType Hctx
      rcases ihType with ⟨hA, hA', _⟩
      rcases ihBody (Hctx.cons hA) with ⟨hbody, hbody', _⟩
      exact ⟨Bool.or_eq_false_iff.mpr ⟨hA, hbody⟩,
        Bool.or_eq_false_iff.mpr ⟨hA', hbody'⟩, rfl⟩
  | defeqDF _ _ ihType ihTerm =>
      specialize ihType Hctx
      specialize ihTerm Hctx
      exact ⟨ihTerm.1, ihTerm.2.1, ihType.2.1⟩
  | beta _ _ ihBody ihArg =>
      specialize ihArg Hctx
      rcases ihArg with ⟨harg, harg', hA⟩
      rcases ihBody (Hctx.cons hA) with ⟨hbody, _, hB⟩
      exact ⟨Bool.or_eq_false_iff.mpr
          ⟨Bool.or_eq_false_iff.mpr ⟨hA, hbody⟩, harg⟩,
        VExpr.containsAnyConst_inst_eq_false _ _ _ hbody harg',
        VExpr.containsAnyConst_inst_eq_false _ _ _ hB harg'⟩
  | eta _ ih =>
      specialize ih Hctx
      rcases ih with ⟨he, he', hforall⟩
      simp only [VExpr.containsAnyConst,
        Bool.or_eq_false_iff] at hforall
      refine ⟨Bool.or_eq_false_iff.mpr ⟨hforall.1,
          Bool.or_eq_false_iff.mpr ⟨?_, rfl⟩⟩,
        he', Bool.or_eq_false_iff.mpr hforall⟩
      simpa using he
  | proofIrrel _ _ _ ihProof ihLeft ihRight =>
      specialize ihProof Hctx
      specialize ihLeft Hctx
      specialize ihRight Hctx
      exact ⟨ihLeft.1, ihRight.1, ihProof.1⟩
  | extra Hdf _ _ =>
      have hstored := Htypes.2 Hdf
      exact ⟨by simpa using hstored.1.1,
        by simpa using hstored.2.1,
        by simpa using hstored.1.2⟩
  | projIota _ _ _ _ ihProj ihField =>
      specialize ihProj Hctx
      specialize ihField Hctx
      exact ⟨ihProj.1, ihField.1, ihProj.2.2⟩
  | structEta _ _ _ _ _ ihE ihCtor =>
      specialize ihE Hctx
      specialize ihCtor Hctx
      exact ⟨ihCtor.1, ihE.1, ihE.2.2⟩
  | unitLike _ _ _ _ _ _ ihE ihE' =>
      specialize ihE Hctx
      specialize ihE' Hctx
      exact ⟨ihE.1, ihE'.1, ihE.2.2⟩

/-- All declarations stored in an ordered environment avoid names which are
absent from that environment.  The proof follows the same well-founded
environment induction as `VEnv.Ordered.closed`. -/
theorem VEnv.Ordered.onTypes_noFreshConsts
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none) :
    OnTypes env fun _ e A =>
      e.containsAnyConst names = false ∧
      A.containsAnyConst names = false := by
  let motive := fun (current : VEnv) (_ : Nat) (e A : VExpr) =>
    ∀ selected : List Lean.Name,
      (∀ name ∈ selected, current.constants name = none) →
      e.containsAnyConst selected = false ∧
      A.containsAnyConst selected = false
  have Hall : OnTypes env (motive env) := Henv.induction motive
    (fun Hle Hsupport selected hfresh => by
      apply Hsupport selected
      intro name hname
      exact Hle.constants_eq_none_left (hfresh name hname))
    (fun Hordered Hstored Htyping selected hfresh => by
      have Hstored' :=
        Hstored.mono VEnv.LE.rfl (fun H => H selected hfresh)
      have Hresult := Htyping.noConsts Hstored' (fun hlookup hname => by
        rw [hfresh _ hname] at hlookup
        contradiction) (by
        intro type htype
        simp at htype)
      exact ⟨Hresult.1, Hresult.2.2⟩)
  exact Hall.mono VEnv.LE.rfl (fun H => H names Hfresh)

/-- Usable derivation-level form of `onTypes_noFreshConsts`. -/
theorem VEnv.IsDefEq.noFreshConsts
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : env.IsDefEq U Gamma lhs rhs type) :
    lhs.containsAnyConst names = false ∧
    rhs.containsAnyConst names = false ∧
    type.containsAnyConst names = false := by
  apply H.noConsts (Henv.onTypes_noFreshConsts Hfresh)
  · intro name ci hlookup hname
    rw [Hfresh name hname] at hlookup
    contradiction
  · exact Hctx

theorem VEnv.Ordered.ctxNoFreshConsts
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none) :
    ∀ {Gamma}, OnCtx Gamma (env.IsType U) → CtxAvoidsConsts names Gamma
  | [], _ => by
      intro type htype
      simp at htype
  | A :: Gamma, ⟨Htail, _level, Htype⟩ => by
      have HtailFree := Henv.ctxNoFreshConsts Hfresh Htail
      have HA := Htype.noFreshConsts Henv Hfresh HtailFree
      exact HtailFree.cons HA.1

/-- A well-formed expression in a well-formed context cannot mention a name
which is absent from its ordered environment. -/
theorem VExpr.WF.noFreshConsts
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : OnCtx Gamma (env.IsType U))
    (H : VExpr.WF env U Gamma e) :
    e.containsAnyConst names = false := by
  rcases H with ⟨type, Htyping⟩
  exact (Htyping.noFreshConsts Henv Hfresh
    (Henv.ctxNoFreshConsts Hfresh Hctx)).1

end Lean4Lean
