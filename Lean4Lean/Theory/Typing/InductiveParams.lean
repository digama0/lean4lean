import Lean4Lean.Theory.Typing.ChurchRosser

namespace Lean4Lean
namespace VEnv

open VExpr

/-!
# A concrete `Params` instance from `env.pats`

`VEnv.toParams` instantiates `ChurchRosser`'s abstract pattern-reduction relation
`Params.Pat` with the environment's own registered ι rules `env.pats`. Its engine is
the population invariant `VEnv.PatsIota` (every registered pattern is a
`SimplePattern.iota` redex with a registered recursor head of fixed arity), from
which `pat_simple`, `pat_app_l`, `pat_app_l_uniq` are proved; `pat_uniq`,
`pat_app_uniq`, `extra_pat` remain `IOTA-TODO`s (see the notes on `toParams`).
-/

/-! ### Environment-population lemmas

`env.pats` is populated only by `addRecRule` (through `addInduct`), which installs
`SimplePattern.iota`-shaped patterns; the other extensions leave it untouched. -/

/-- `addConst` leaves `pats` unchanged. -/
theorem addConst_pats {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.pats = env.pats := by
  rw [VEnv.addConst] at h; split at h
  · simp at h
  · injection h with h; subst h; rfl

/-- `addDefEq` leaves `pats` unchanged. -/
theorem addDefEq_pats {env : VEnv} {df} : (env.addDefEq df).pats = env.pats := rfl

/-- `addConsts` (a block of `addConst`s) leaves `pats` unchanged. -/
theorem addConsts_pats {env env' : VEnv} : ∀ {cis},
    env.addConsts cis = some env' → env'.pats = env.pats
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConsts_pats h2).trans (addConst_pats h1)

/-- `addDefEqs` (a block of `addDefEq`s) leaves `pats` unchanged. -/
theorem addDefEqs_pats : ∀ {cis : List VDefVal} {env : VEnv}, (env.addDefEqs cis).pats = env.pats
  | [], _ => rfl
  | ci :: cis, env => by
    show ((env.addDefEq ci.toDefEq).addDefEqs cis).pats = env.pats
    rw [addDefEqs_pats, addDefEq_pats]

/-- `addDefEqs` (a block of `addDefEq`s) only grows the environment. -/
theorem addDefEqs_le : ∀ {cis : List VDefVal} {env : VEnv}, env ≤ env.addDefEqs cis
  | [], _ => .rfl
  | ci :: cis, env => by
    show env ≤ (env.addDefEq ci.toDefEq).addDefEqs cis
    exact addDefEq_le.trans addDefEqs_le

/-- `addQuot` (a chain of `addConst`s and one `addDefEq`) leaves `pats` unchanged. -/
theorem addQuot_pats {env env' : VEnv} (h : env.addQuot = some env') : env'.pats = env.pats := by
  rw [VEnv.addQuot] at h
  obtain ⟨e1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e3, s3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e4, s4, h⟩ := Option.bind_eq_some_iff.1 h
  injection h with h; subst h
  rw [addDefEq_pats, addConst_pats s4, addConst_pats s3, addConst_pats s2, addConst_pats s1]

/-- A `foldlM` whose every step preserves `pats` preserves `pats`. -/
theorem foldlM_pats_preserved {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e a e'}, f e a = some e' → e'.pats = e.pats) :
    ∀ {l : List α} {init env' : VEnv}, l.foldlM f init = some env' → env'.pats = init.pats
  | [], _, _, h => by simp [List.foldlM] at h; exact h ▸ rfl
  | _ :: _, _, _, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h; rw [foldlM_pats_preserved hf h2, hf h1]

/-- Full specification of a successful `addConst`: the name was fresh, is now bound
to `ci`, and no other name changed. -/
theorem addConst_eq {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env.constants n = none ∧ env'.constants n = some ci ∧
    ∀ m, n ≠ m → env'.constants m = env.constants m := by
  rw [VEnv.addConst] at h; split at h
  · simp at h
  · rename_i hnone; injection h with h; subst h; exact ⟨hnone, by simp, fun m hm => by simp [hm]⟩

/-- In a successful `addConst` fold, every registered name was fresh w.r.t. the
starting environment. -/
theorem addConst_foldlM_fresh {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ a ∈ l, init.constants (nm a) = none
  | [], _, _, _, _, ha => by cases ha
  | b :: bs, init, final, h, a, ha => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hfresh_b, hspec_b, hother_b⟩ := addConst_eq h1
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact hfresh_b
    · have hrec := addConst_foldlM_fresh h2 a ha'
      by_cases hnn : nm b = nm a
      · rw [← hnn, hspec_b] at hrec; simp at hrec
      · rwa [hother_b (nm a) hnn] at hrec

/-- In a successful `addConst` fold, every registered name is present in the result. -/
theorem addConst_foldlM_reg {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ a ∈ l, ∃ c, final.constants (nm a) = some c
  | [], _, _, _, _, ha => by cases ha
  | b :: bs, init, final, h, a, ha => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, hspec_b, _⟩ := addConst_eq h1
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, (foldlM_le (fun hh => addConst_le hh) h2).constants hspec_b⟩
    · exact addConst_foldlM_reg h2 a ha'

/-- In a successful `addConst` fold, the naming function is injective on the list:
two elements with the same name coincide. -/
theorem addConst_foldlM_inj {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ a ∈ l, ∀ b ∈ l, nm a = nm b → a = b
  | [], _, _, _, _, ha, _, _, _ => by cases ha
  | c :: cs, init, final, h, a, ha, b, hb, hab => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, hspec_c, _⟩ := addConst_eq h1
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exfalso; have := addConst_foldlM_fresh h2 b hb'; rw [← hab, hspec_c] at this; simp at this
    · exfalso; have := addConst_foldlM_fresh h2 a ha'; rw [hab, hspec_c] at this; simp at this
    · exact addConst_foldlM_inj h2 a ha' b hb' hab

/-- `addRecRule` leaves `constants` unchanged (it only registers a `pat`). -/
theorem addRecRule_constants {env env' : VEnv} {r ru} (h : env.addRecRule r ru = some env') :
    env'.constants = env.constants := by
  unfold addRecRule at h; split at h
  · cases h; rfl
  · cases h

/-- A `foldlM` whose every step preserves `constants` preserves `constants`. -/
theorem foldlM_constants_preserved {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e a e'}, f e a = some e' → e'.constants = e.constants) :
    ∀ {l : List α} {init env' : VEnv}, l.foldlM f init = some env' → env'.constants = init.constants
  | [], _, _, h => by simp [List.foldlM] at h; exact h ▸ rfl
  | _ :: _, _, _, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [foldlM_constants_preserved hf h2, hf h1]

/-- Adding quotient constants only grows the environment. -/
theorem addQuot_le {env env' : VEnv} (h : env.addQuot = some env') : env ≤ env' := by
  rw [VEnv.addQuot] at h
  obtain ⟨e1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e3, s3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e4, s4, h⟩ := Option.bind_eq_some_iff.1 h
  injection h with h; subst h
  exact (addConst_le s1).trans <| (addConst_le s2).trans <| (addConst_le s3).trans <|
    (addConst_le s4).trans addDefEq_le

/-- A pattern present after one `addRecRule` is either an old one or exactly this
rule's ι redex. -/
theorem addRecRule_pats_inv {env env' : VEnv} {r ru p rr}
    (h : env.addRecRule r ru = some env') (hp : env'.pats p rr) :
    env.pats p rr ∨
    p = (SimplePattern.iota r.name r.getMajorIdx ru.ctor (r.numParams + ru.nfields)).toPattern := by
  unfold addRecRule at h; split at h
  · cases h; rcases hp with ⟨rfl, _⟩ | hp
    · exact .inr rfl
    · exact .inl hp
  · cases h

/-- Membership-tracking pattern inversion for a `foldlM`: a pattern present after the
fold is either present at the start or produced (with witness `a ∈ l`) by some step. -/
theorem foldlM_pats_inv_mem {α} {f : VEnv → α → Option VEnv} {motive : α → Pattern → Prop} {p rr} :
    ∀ {l : List α} {init final : VEnv},
      (∀ {e a e'}, a ∈ l → f e a = some e' → e'.pats p rr → e.pats p rr ∨ motive a p) →
      l.foldlM f init = some final → final.pats p rr → init.pats p rr ∨ ∃ a ∈ l, motive a p
  | [], _, _, _, h, hp => by simp [List.foldlM] at h; exact .inl (h ▸ hp)
  | a :: as, init, final, hf, h, hp => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rcases foldlM_pats_inv_mem (f := f) (motive := motive) (l := as)
        (fun {e a' e'} hm => hf (List.mem_cons_of_mem _ hm)) h2 hp with hp1 | ⟨a', ha', hm⟩
    · rcases hf (List.mem_cons_self ..) h1 hp1 with hp0 | hm0
      · exact .inl hp0
      · exact .inr ⟨a, List.mem_cons_self .., hm0⟩
    · exact .inr ⟨a', List.mem_cons_of_mem _ ha', hm⟩

/-- Origin of a pattern after `addInduct`: it is either old, or the ι redex of some
recursor rule `ru ∈ rec.rules` with `rec ∈ decl.recs`, with recursor name/arity and
constructor pinned to that rule. -/
theorem addInduct_pats_origin {env env' : VEnv} {decl : VInductDecl} {p rr}
    (h : env.addInduct decl = some env') (hp : env'.pats p rr) :
    env.pats p rr ∨ ∃ rec ∈ decl.recs, ∃ ru ∈ rec.rules,
      p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
            (rec.numParams + ru.nfields)).toPattern := by
  unfold VEnv.addInduct at h
  obtain ⟨env1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env3, s3, s4⟩ := Option.bind_eq_some_iff.1 h
  have e1p : env1.pats = env.pats := foldlM_pats_preserved (fun hh => addConst_pats hh) s1
  have e2p : env2.pats = env1.pats :=
    foldlM_pats_preserved (fun hh => foldlM_pats_preserved (fun hh2 => addConst_pats hh2) hh) s2
  have e3p : env3.pats = env2.pats := foldlM_pats_preserved (fun hh => addConst_pats hh) s3
  rcases foldlM_pats_inv_mem
      (motive := fun rec p => ∃ ru ∈ rec.rules,
        p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
              (rec.numParams + ru.nfields)).toPattern)
      (fun {e rec e'} _ hstep hpp =>
        foldlM_pats_inv_mem
          (motive := fun ru p =>
            p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
                  (rec.numParams + ru.nfields)).toPattern)
          (fun {e2 ru e2'} _ hstep2 hpp2 => addRecRule_pats_inv hstep2 hpp2) hstep hpp)
      s4 hp with hk | horigin
  · rw [e3p, e2p, e1p] at hk; exact .inl hk
  · exact .inr horigin

/-- A recursor of `decl` is fresh w.r.t. `env` (its name is not already registered). -/
theorem addInduct_rec_fresh {env env' : VEnv} {decl : VInductDecl} {rec}
    (h : env.addInduct decl = some env') (hrec : rec ∈ decl.recs) :
    env.constants rec.name = none := by
  unfold VEnv.addInduct at h
  obtain ⟨env1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env3, s3, s4⟩ := Option.bind_eq_some_iff.1 h
  have hfresh : env2.constants rec.name = none := addConst_foldlM_fresh s3 rec hrec
  have hle : env ≤ env2 := (foldlM_le (fun hh => addConst_le hh) s1).trans
    (foldlM_le (fun hh => foldlM_le (fun hh2 => addConst_le hh2) hh) s2)
  cases hnn : env.constants rec.name with
  | none => rfl
  | some c => rw [hle.constants hnn] at hfresh; simp at hfresh

/-- A recursor of `decl` is registered as a constant in the resulting environment. -/
theorem addInduct_rec_reg {env env' : VEnv} {decl : VInductDecl} {rec}
    (h : env.addInduct decl = some env') (hrec : rec ∈ decl.recs) :
    ∃ c, env'.constants rec.name = some c := by
  unfold VEnv.addInduct at h
  obtain ⟨env1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env3, s3, s4⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c, hc⟩ := addConst_foldlM_reg s3 rec hrec
  have hconst : env'.constants = env3.constants :=
    foldlM_constants_preserved
      (fun hh => foldlM_constants_preserved (fun hh2 => addRecRule_constants hh2) hh) s4
  exact ⟨c, by rw [hconst]; exact hc⟩

/-- Recursor names within one `decl` are distinct: two recursors sharing a name coincide. -/
theorem addInduct_recs_name_inj {env env' : VEnv} {decl : VInductDecl} {ra rb}
    (h : env.addInduct decl = some env') (hra : ra ∈ decl.recs) (hrb : rb ∈ decl.recs)
    (hname : ra.name = rb.name) : ra = rb := by
  unfold VEnv.addInduct at h
  obtain ⟨env1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env3, s3, s4⟩ := Option.bind_eq_some_iff.1 h
  exact addConst_foldlM_inj s3 ra hra rb hrb hname

/-- `SimplePattern.iota` is injective through `toPattern`. -/
theorem iota_toPattern_inj {r1 m1 c1 n1 r2 m2 c2 n2}
    (h : (SimplePattern.iota r1 m1 c1 n1).toPattern = (SimplePattern.iota r2 m2 c2 n2).toPattern) :
    r1 = r2 ∧ m1 = m2 ∧ c1 = c2 ∧ n1 = n2 := by
  simp only [SimplePattern.toPattern] at h
  injection h with hl hr
  obtain ⟨rfl, rfl⟩ := Pattern.varN_const_inj hl
  obtain ⟨rfl, rfl⟩ := Pattern.varN_const_inj hr
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The only application subpattern of an ι redex is its top-level one, whose left
factor is the recursor spine. -/
theorem app_subpattern_iota {r m c n a b}
    (hs : Subpattern (.app a b) ((SimplePattern.iota r m c n).toPattern)) :
    a = (Pattern.const r).varN m := by
  simp only [SimplePattern.toPattern] at hs
  cases hs with
  | refl => rfl
  | appL h => exact absurd h Pattern.not_app_subpattern_varN_const
  | appR h => exact absurd h Pattern.not_app_subpattern_varN_const

/-- Each `VDecl.WF` step either leaves `pats` unchanged (`axiom`/`def`/`opaque`/
`example`/`quot`) or is an `addInduct`. -/
theorem _root_.Lean4Lean.VDecl.WF.pats_eq_or_induct {env d env'} (h : VDecl.WF env d env') :
    env'.pats = env.pats ∨ ∃ decl, env.addInduct decl = some env' := by
  cases h with
  | «axiom» _ h2 => exact .inl (addConst_pats h2)
  | «def» _ h2 => exact .inl (by rw [addDefEq_pats]; exact addConst_pats h2)
  | mutualDef _ h2 _ => exact .inl (by rw [addDefEqs_pats]; exact addConsts_pats h2)
  | «opaque» _ h2 => exact .inl (addConst_pats h2)
  | «example» _ => exact .inl rfl
  | quot _ h2 => exact .inl (addQuot_pats h2)
  | induct _ h2 => exact .inr ⟨_, h2⟩

/-- Every `VDecl.WF` step only grows the environment. -/
theorem _root_.Lean4Lean.VDecl.WF.le {env d env'} (h : VDecl.WF env d env') : env ≤ env' := by
  cases h with
  | «axiom» _ h2 => exact addConst_le h2
  | «def» _ h2 => exact (addConst_le h2).trans addDefEq_le
  | mutualDef _ h2 _ => exact (VEnv.addConsts_le h2).trans addDefEqs_le
  | «opaque» _ h2 => exact addConst_le h2
  | «example» _ => exact .rfl
  | quot _ h2 => exact addQuot_le h2
  | induct _ h2 => exact addInduct_le h2

/-! ### The population invariant -/

/-- The pattern-registry invariant of a well-formed environment: every registered
pattern is a `SimplePattern.iota` redex whose recursor head is a registered constant
(`shape`), and the recursor name determines the spine arity `M` (`arity`). -/
structure PatsIota (env : VEnv) : Prop where
  shape : ∀ {p rr}, env.pats p rr →
    ∃ recN M ctorN N c,
      p = (SimplePattern.iota recN M ctorN N).toPattern ∧ env.constants recN = some c
  arity : ∀ {recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂},
    env.pats (SimplePattern.iota recN M₁ c₁ N₁).toPattern rr₁ →
    env.pats (SimplePattern.iota recN M₂ c₂ N₂).toPattern rr₂ → M₁ = M₂

/-- `PatsIota` is preserved by any step that leaves `pats` unchanged and only grows
`constants` (the non-`induct` `VDecl.WF` steps). -/
theorem PatsIota.of_le {env env' : VEnv} (H : env.PatsIota)
    (hpats : env'.pats = env.pats) (hle : env ≤ env') : env'.PatsIota := by
  constructor
  · intro p rr hp; rw [hpats] at hp
    obtain ⟨recN, M, ctorN, N, c, hform, hc⟩ := H.shape hp
    exact ⟨recN, M, ctorN, N, c, hform, hle.constants hc⟩
  · intro recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂ h1 h2
    rw [hpats] at h1 h2; exact H.arity h1 h2

/-- `PatsIota` is preserved by `addInduct`: freshly-registered ι patterns are
ι-shaped with the recursor as a new constant, and old/new recursor names cannot
collide. -/
theorem PatsIota.induct {env env' : VEnv} {decl : VInductDecl} (H : env.PatsIota)
    (h : env.addInduct decl = some env') : env'.PatsIota := by
  constructor
  · intro p rr hp
    rcases addInduct_pats_origin h hp with hold | ⟨rec, hrec, ru, hru, hform⟩
    · obtain ⟨recN, M, ctorN, N, c, hf, hc⟩ := H.shape hold
      exact ⟨recN, M, ctorN, N, c, hf, (addInduct_le h).constants hc⟩
    · obtain ⟨c, hc⟩ := addInduct_rec_reg h hrec
      exact ⟨rec.name, rec.getMajorIdx, ru.ctor, rec.numParams + ru.nfields, c, hform, hc⟩
  · intro recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂ h1 h2
    rcases addInduct_pats_origin h h1 with hold1 | ⟨ra, hra, rua, hrua, hfa⟩ <;>
      rcases addInduct_pats_origin h h2 with hold2 | ⟨rb, hrb, rub, hrub, hfb⟩
    · exact H.arity hold1 hold2
    · exfalso
      obtain ⟨recN', M', ctorN', N', cc, hf', hc'⟩ := H.shape hold1
      obtain ⟨hrn1, _, _, _⟩ := iota_toPattern_inj hf'
      obtain ⟨hrn2, _, _, _⟩ := iota_toPattern_inj hfb
      have hfresh := addInduct_rec_fresh h hrb
      rw [← hrn2] at hfresh; rw [← hrn1] at hc'; rw [hc'] at hfresh; simp at hfresh
    · exfalso
      obtain ⟨recN', M', ctorN', N', cc, hf', hc'⟩ := H.shape hold2
      obtain ⟨hrn1, _, _, _⟩ := iota_toPattern_inj hf'
      obtain ⟨hrn2, _, _, _⟩ := iota_toPattern_inj hfa
      have hfresh := addInduct_rec_fresh h hra
      rw [← hrn2] at hfresh; rw [← hrn1] at hc'; rw [hc'] at hfresh; simp at hfresh
    · obtain ⟨hrn_a, hm_a, _, _⟩ := iota_toPattern_inj hfa
      obtain ⟨hrn_b, hm_b, _, _⟩ := iota_toPattern_inj hfb
      have hab : ra = rb := addInduct_recs_name_inj h hra hrb (by rw [← hrn_a, ← hrn_b])
      rw [hm_a, hm_b, hab]

/-- Every well-formed environment satisfies the pattern population invariant. -/
theorem WF.patsIota {env : VEnv} (H : env.WF) : env.PatsIota := by
  obtain ⟨ds, H⟩ := H
  induction H with
  | empty =>
    constructor
    · intro p rr h; exact (h : False).elim
    · intro _ _ _ _ _ _ _ _ _ h1 _; exact (h1 : False).elim
  | decl hd _ ih =>
    rcases hd.pats_eq_or_induct with heq | ⟨decl, hind⟩
    · exact ih.of_le heq hd.le
    · exact ih.induct hind

/-! ### The discharged `Params` side conditions -/

/-- `Params.pat_simple` for `env.pats`: every registered pattern is a `SimplePattern`. -/
theorem WF.pat_simple {env : VEnv} (H : env.WF) {p rr} (hp : env.pats p rr) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  obtain ⟨recN, M, ctorN, N, _, hform, _⟩ := H.patsIota.shape hp
  exact ⟨.iota recN M ctorN N, hform⟩

/-- `Params.pat_app_l` for `env.pats`: the left factor of an ι redex's application
subpattern (the recursor spine) has no application subpattern of its own. -/
theorem WF.pat_app_l {env : VEnv} (H : env.WF) {p p₁ p₂ p₃ p₄ rr} (hp : env.pats p rr)
    (hs : Subpattern (.app p₁ p₂) p) : ¬ Subpattern (.app p₃ p₄) p₁ := by
  obtain ⟨recN, M, ctorN, N, _, rfl, _⟩ := H.patsIota.shape hp
  rw [app_subpattern_iota hs]
  exact Pattern.not_app_subpattern_varN_const

/-- `Params.pat_app_l_uniq` for `env.pats`: a variable-argument slot of one ι redex's
recursor spine never intersects another ι redex's recursor spine, since the recursor
name fixes the spine arity (`PatsIota.arity`). -/
theorem WF.pat_app_l_uniq {env : VEnv} (H : env.WF) {p r p' r' p₁ p₂ p₁' p₂' p₃}
    (hp : env.pats p r) (hp' : env.pats p' r')
    (hs : Subpattern (.app p₁ p₂) p) (hs' : Subpattern (.app p₁' p₂') p')
    (hv : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  have HI := H.patsIota
  obtain ⟨recN, M, ctorN, N, c, rfl, hc⟩ := HI.shape hp
  obtain ⟨recN', M', ctorN', N', c', rfl, hc'⟩ := HI.shape hp'
  have e1 : p₁ = (Pattern.const recN).varN M := app_subpattern_iota hs
  have e1' : p₁' = (Pattern.const recN').varN M' := app_subpattern_iota hs'
  subst e1 e1'
  obtain ⟨k, hk, hkk⟩ := Pattern.subpattern_varN_const hv
  cases k with
  | zero => simp [Pattern.varN] at hkk
  | succ i =>
    simp only [Pattern.varN] at hkk
    injection hkk with hkk; subst hkk
    cases hinter : ((Pattern.const recN').varN M').inter ((Pattern.const recN).varN i) with
    | none => rfl
    | some r₄ =>
      exfalso
      obtain ⟨hrr, hMi, _⟩ := Pattern.varN_const_inter hinter
      subst hrr
      have hMM : M = M' := HI.arity hp hp'
      omega

/-- The `Params` structure induced by a well-formed environment `env`, taking the
abstract reduction relation `Pat` to be `env.pats`. Three side conditions are
discharged from `VEnv.PatsIota`; the remaining three are `IOTA-TODO`s (see per-field
notes). -/
@[reducible] def toParams (env : VEnv) (henv : env.WF) (U : Nat) : Params where
  env := env
  henv := henv
  univs := U
  Pat := env.pats
  pat_simple := fun hp => henv.pat_simple hp
  -- IOTA-TODO(soundness): needs functionality of `env.pats` (a pattern determines its
  -- reduct), false while `VInductDecl.WF` lets two rules register the same iota pattern
  -- with different reducts; needs `VInductDecl.WF` to pin each rule's shape.
  pat_uniq := sorry
  -- `pat_wf` is the genuine content: recover a `Realizes` witness from `Check.OK` and
  -- feed it to `IsDefEq.pat`.
  pat_wf := fun {p r e m1 m2 Γ A} hpat hmatch hty hok =>
    let ⟨_, hr, hall⟩ := hok.exists_realizer (rel := fun a b t => IsDefEq env U Γ a b t)
    ⟨A, IsDefEq.pat hpat hmatch hty hr hall⟩
  pat_app_l := fun hp hs => henv.pat_app_l hp hs
  pat_app_l_uniq := fun hp hp' hs hs' hv => henv.pat_app_l_uniq hp hp' hs hs' hv
  -- IOTA-TODO(soundness): needs `recN ≠ ru.ctor`, false while `VInductDecl.WF` leaves
  -- `ru.ctor` an unconstrained `Name`; needs it to require `ru.ctor` be an actual
  -- constructor (hence a registered constant distinct from recursor names).
  pat_app_uniq := sorry
  -- IOTA-TODO(soundness): demands every `env.defeqs df` be realised by a registered
  -- pattern, but `addInduct` registers only ι patterns, never `SimplePattern.defn` (δ);
  -- false for any env with a `def`/quot until δ-rule registration also installs `.defn`.
  extra_pat := sorry

end VEnv
end Lean4Lean
