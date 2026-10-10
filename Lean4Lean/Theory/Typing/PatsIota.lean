import Lean4Lean.Theory.Typing.EnvLemmas

namespace Lean4Lean
namespace VEnv

open VExpr

/-!
# The pattern population invariant `PatsIota`

Every registered pattern of a well-formed environment is a `SimplePattern.iota` redex whose
recursor head is a registered `RecHeaded` constant of a spine arity fixed by the recursor
name, whose constructor is a registered `CtorHeaded` constant, and whose reduct is determined
by the pattern. The invariant comes from `VInductDecl.WF` and the stage lemmas of
`addInduct`. It is the engine of the `Params` instance of `InductiveParams.lean` and of the
rigidity of type formers and structures (`ProjectionRigidity.lean`): a pattern head is a
recursor name, fresh when registered.
-/

/-- Each `VDecl.WF` step either leaves `pats` unchanged (`axiom`/`def`/`opaque`/
`example`/`quot`) or is the `addInduct` of a well-formed declaration `d = .induct decl`. -/
theorem _root_.Lean4Lean.VDecl.WF.pats_eq_or_induct' {env d env'} (h : VDecl.WF env d env') :
    env'.pats = env.pats ∨
      ∃ decl, d = .induct decl ∧ decl.WF env ∧ env.addInduct decl = some env' := by
  cases h with
  | «axiom» _ h2 => exact .inl (addConst_pats h2)
  | «def» _ h2 => exact .inl (by rw [addDefEq_pats]; exact addConst_pats h2)
  | mutualDef _ h2 _ => exact .inl (by rw [addDefEqs_pats]; exact addConsts_pats h2)
  | «opaque» _ h2 => exact .inl (addConst_pats h2)
  | «example» _ => exact .inl rfl
  | quot _ h2 => exact .inl (addQuot_pats h2)
  | induct h1 h2 => exact .inr ⟨_, rfl, h1, h2⟩

/-- Each `VDecl.WF` step either leaves `pats` unchanged (`axiom`/`def`/`opaque`/
`example`/`quot`) or is an `addInduct` of a well-formed declaration. -/
theorem _root_.Lean4Lean.VDecl.WF.pats_eq_or_induct {env d env'} (h : VDecl.WF env d env') :
    env'.pats = env.pats ∨ ∃ decl, decl.WF env ∧ env.addInduct decl = some env' := by
  rcases h.pats_eq_or_induct' with heq | ⟨decl, -, hdecl, hind⟩
  · exact .inl heq
  · exact .inr ⟨decl, hdecl, hind⟩

/-- Origin of a registered pattern entry along a `WF'` chain: some step of `ds` is the
`addInduct` of a well-formed `decl`, and the entry is exactly the ι entry of one rule of
one recursor of `decl`, key and reduct both read off that rule. First step of the
deferred ι subject-reduction proof. -/
theorem WF'.pats_origin {ds : List VDecl} {env : VEnv} (H : env.WF' ds) {p rr}
    (hp : env.pats p rr) :
    ∃ (decl : VInductDecl) (ds₀ : List VDecl) (env₀ env₁ : VEnv),
      (VDecl.induct decl :: ds₀) <:+ ds ∧ env₀.WF' ds₀ ∧ decl.WF env₀ ∧
      env₀.addInduct decl = some env₁ ∧ env₁ ≤ env ∧
      ∃ rec ∈ decl.recs, ∃ ru ∈ rec.rules, ∃ (hc : ru.rhs.Closed)
        (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
          (ru.ctorParams + ru.nfields)).toPattern),
        e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
          rec.numParams rec.numMotives rec.numMinors rec.numIndices ru.ctorParams ru.nfields
          ru.rhs hc, .true) := by
  induction H with
  | empty => exact (hp : False).elim
  | @decl d env' ds env hd H ih =>
    suffices key : env.pats p rr ∨ ∃ decl, d = .induct decl ∧ decl.WF env ∧
        env.addInduct decl = some env' ∧
        ∃ rec ∈ decl.recs, ∃ ru ∈ rec.rules, ∃ (hc : ru.rhs.Closed)
          (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
            (ru.ctorParams + ru.nfields)).toPattern),
          e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
            rec.numParams rec.numMotives rec.numMinors rec.numIndices ru.ctorParams ru.nfields
            ru.rhs hc, .true) by
      rcases key with hold | ⟨decl, rfl, hdecl, hind, rest⟩
      · obtain ⟨decl, ds₀, env₀, env₁, hsuf, hwf', hdecl, hadd, hle, rest⟩ := ih hold
        exact ⟨decl, ds₀, env₀, env₁, hsuf.trans (List.suffix_cons _ _), hwf', hdecl, hadd,
          hle.trans hd.le, rest⟩
      · exact ⟨decl, ds, env, env', List.suffix_refl _, H, hdecl, hind, .rfl, rest⟩
    rcases hd.pats_eq_or_induct' with heq | ⟨decl, hd_eq, hdecl, hind⟩
    · exact .inl (heq ▸ hp)
    · rcases addInduct_pats_origin' hind hp with hold | rest
      · exact .inl hold
      · exact .inr ⟨decl, hd_eq, hdecl, hind, rest⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    obtain ⟨decl, ds₀, env₀, env₁, hsuf, hwf', hdecl, hadd, hle, rest⟩ :=
      ihCtors (by simpa only [VEnv.addProjections_pats] using hp)
    exact ⟨decl, ds₀, env₀, env₁, hsuf, hwf', hdecl, hadd, hle.trans addProjections_le, rest⟩

/-! ### The population invariant -/

/-- The pattern-registry invariant of a well-formed environment: every registered
pattern is a `SimplePattern.iota` redex whose recursor head is a registered constant
with a `RecHeaded` type (`shape`), the recursor name determines the spine arity `M`
(`arity`), the constructor is a registered constant with a `CtorHeaded` type
(`ctor_shape`), and a pattern determines its reduct (`functional`). -/
structure PatsIota (env : VEnv) : Prop where
  shape : ∀ {p rr}, env.pats p rr →
    ∃ recN M ctorN N c,
      p = (SimplePattern.iota recN M ctorN N).toPattern ∧ env.constants recN = some c ∧
      c.type.RecHeaded
  arity : ∀ {recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂},
    env.pats (SimplePattern.iota recN M₁ c₁ N₁).toPattern rr₁ →
    env.pats (SimplePattern.iota recN M₂ c₂ N₂).toPattern rr₂ → M₁ = M₂
  ctor_shape : ∀ {recN M ctorN N rr},
    env.pats (SimplePattern.iota recN M ctorN N).toPattern rr →
    ∃ ci, env.constants ctorN = some ci ∧ ci.type.CtorHeaded
  functional : ∀ {p rr rr'}, env.pats p rr → env.pats p rr' → rr = rr'

/-- A recursor head of one ι redex is never the constructor of another (or the same)
ι redex: the constant would have to be both `RecHeaded` and `CtorHeaded`. -/
theorem PatsIota.rec_ne_ctor {env : VEnv} (H : env.PatsIota)
    {R M C N r₁ R₂ M₂ C₂ N₂ r₂}
    (h1 : env.pats (SimplePattern.iota R M C N).toPattern r₁)
    (h2 : env.pats (SimplePattern.iota R₂ M₂ C₂ N₂).toPattern r₂) : R ≠ C₂ := by
  intro heq
  obtain ⟨recN, M', ctorN, N', c, hf, hc, hrec⟩ := H.shape h1
  obtain ⟨rfl, -, -, -⟩ := iota_toPattern_inj hf
  obtain ⟨ci, hci, hctor⟩ := H.ctor_shape h2
  subst heq; rw [hc] at hci; cases hci
  exact hrec.not_ctorHeaded hctor

/-- `PatsIota` is preserved by any step that leaves `pats` unchanged and only grows
`constants` (the non-`induct` `VDecl.WF` steps). -/
theorem PatsIota.of_le {env env' : VEnv} (H : env.PatsIota)
    (hpats : env'.pats = env.pats) (hle : env ≤ env') : env'.PatsIota := by
  constructor
  · intro p rr hp; rw [hpats] at hp
    obtain ⟨recN, M, ctorN, N, c, hform, hc, hrec⟩ := H.shape hp
    exact ⟨recN, M, ctorN, N, c, hform, hle.constants hc, hrec⟩
  · intro recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂ h1 h2
    rw [hpats] at h1 h2; exact H.arity h1 h2
  · intro recN M ctorN N rr hp; rw [hpats] at hp
    obtain ⟨ci, hci, hctor⟩ := H.ctor_shape hp
    exact ⟨ci, hle.constants hci, hctor⟩
  · intro p rr rr' h1 h2
    rw [hpats] at h1 h2; exact H.functional h1 h2

/-- `PatsIota` is preserved by `addInduct` of a well-formed declaration: freshly
registered ι entries are keyed by a new `RecHeaded` recursor constant
(`rec_shape`) firing on a registered `CtorHeaded` constructor (`rules_ctor`); old and
new recursor names cannot collide (`addInduct_rec_fresh`); and two new entries with
the same key come from the same recursor (`addInduct_recs_name_inj`) and the same
rule (`rules_nodup`), hence coincide. -/
theorem PatsIota.induct {env env' : VEnv} {decl : VInductDecl} (H : env.PatsIota)
    (hwf : decl.WF env) (h : env.addInduct decl = some env') : env'.PatsIota := by
  have hle := addInduct_le h
  -- an old pattern's recursor is not a recursor of `decl`
  have hold_fresh : ∀ {recN M ctorN N rr},
      env.pats (SimplePattern.iota recN M ctorN N).toPattern rr →
      ∀ rec ∈ decl.recs, recN ≠ rec.name := by
    intro recN M ctorN N rr hp rec hrec heq
    obtain ⟨recN', M', ctorN', N', c, hf, hc, -⟩ := H.shape hp
    obtain ⟨rfl, -, -, -⟩ := iota_toPattern_inj hf
    subst heq
    have := addInduct_rec_fresh h hrec; rw [hc] at this; cases this
  constructor
  · intro p rr hp
    rcases addInduct_pats_origin h hp with hold | ⟨rec, hrec, ru, hru, hform⟩
    · obtain ⟨recN, M, ctorN, N, c, hf, hc, hrec⟩ := H.shape hold
      exact ⟨recN, M, ctorN, N, c, hf, hle.constants hc, hrec⟩
    · exact ⟨rec.name, rec.getMajorIdx, ru.ctor, ru.ctorParams + ru.nfields, _, hform,
        addInduct_rec_find h hrec, (hwf.rec_shape rec hrec).recHeaded⟩
  · intro recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂ h1 h2
    rcases addInduct_pats_origin h h1 with hold1 | ⟨ra, hra, rua, hrua, hfa⟩ <;>
      rcases addInduct_pats_origin h h2 with hold2 | ⟨rb, hrb, rub, hrub, hfb⟩
    · exact H.arity hold1 hold2
    · obtain ⟨hrn, -, -, -⟩ := iota_toPattern_inj hfb
      exact absurd hrn (hold_fresh hold1 rb hrb)
    · obtain ⟨hrn, -, -, -⟩ := iota_toPattern_inj hfa
      exact absurd hrn (hold_fresh hold2 ra hra)
    · obtain ⟨hrn_a, hm_a, -, -⟩ := iota_toPattern_inj hfa
      obtain ⟨hrn_b, hm_b, -, -⟩ := iota_toPattern_inj hfb
      have hab : ra = rb := addInduct_recs_name_inj h hra hrb (by rw [← hrn_a, ← hrn_b])
      rw [hm_a, hm_b, hab]
  · intro recN M ctorN N rr hp
    rcases addInduct_pats_origin h hp with hold | ⟨rec, hrec, ru, hru, hform⟩
    · obtain ⟨ci, hci, hctor⟩ := H.ctor_shape hold
      exact ⟨ci, hle.constants hci, hctor⟩
    · obtain ⟨-, -, rfl, -⟩ := iota_toPattern_inj hform
      obtain ⟨ci, hci, hcs⟩ := addInduct_rule_ctor hwf h hrec hru
      exact ⟨ci, hci, hcs.2⟩
  · intro p rr rr' hp hp'
    rcases addInduct_pats_origin' h hp with hold | ⟨ra, hra, rua, hrua, hca, ea, hea⟩ <;>
      rcases addInduct_pats_origin' h hp' with hold' | ⟨rb, hrb, rub, hrub, hcb, eb, heb⟩
    · exact H.functional hold hold'
    · subst eb; exact absurd rfl (hold_fresh hold rb hrb)
    · subst ea; exact absurd rfl (hold_fresh hold' ra hra)
    · obtain ⟨hname, -, hctor, -⟩ := iota_toPattern_inj (ea.symm.trans eb)
      obtain rfl : ra = rb := addInduct_recs_name_inj h hra hrb hname
      obtain rfl : rua = rub := nodup_map_inj_on (hwf.rules_nodup ra hra) rua hrua rub hrub hctor
      subst ea; cases eb
      exact hea.trans heb.symm

/-- Every well-formed environment satisfies the pattern population invariant. -/
theorem WF.patsIota {env : VEnv} (H : env.WF) : env.PatsIota := by
  obtain ⟨ds, H⟩ := H
  induction H with
  | empty =>
    constructor
    · intro p rr h; exact (h : False).elim
    · intro _ _ _ _ _ _ _ _ _ h1 _; exact (h1 : False).elim
    · intro _ _ _ _ _ h; exact (h : False).elim
    · intro _ _ _ h _; exact (h : False).elim
  | decl hd _ ih =>
    rcases hd.pats_eq_or_induct with heq | ⟨decl, hwf, hind⟩
    · exact ih.of_le heq hd.le
    · exact ih.induct hwf hind
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    exact ihCtors.of_le (addProjections_pats _ _) addProjections_le

end VEnv
end Lean4Lean
