import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean

theorem VEnv.addConsts_le {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' → env ≤ env'
  | [], h => by cases h; exact .rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConsts_le h2)

theorem VEnv.addConst_eq_none {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

theorem VEnv.addConst_constants_eq {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') :
    env'.constants = fun n => if name = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

/-- A block of constants can be added as long as each name is fresh and the block has no
duplicates; the latter is what `addMutual`'s `found` set checks. -/
theorem VEnv.exists_addConsts {env : VEnv} : ∀ {cis : List VDefVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConsts cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConsts (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConsts, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

theorem VEnv.addConsts_congr {env : VEnv} : ∀ {cis cis' : List VDefVal},
    List.Forall₂ (fun a b => a.toVConstVal = b.toVConstVal) cis cis' →
    env.addConsts cis = env.addConsts cis'
  | [], [], _ => rfl
  | a :: _, b :: _, .cons h t => by
    have h1 : a.name = b.name := congrArg VConstVal.name h
    have h2 : a.toVConstant = b.toVConstant := congrArg VConstVal.toVConstant h
    show (env.addConst a.name a.toVConstant).bind _ = (env.addConst b.name b.toVConstant).bind _
    rw [h1, h2]
    cases env.addConst b.name b.toVConstant
    · rfl
    · exact VEnv.addConsts_congr t

theorem VEnv.addConsts_ordered {env env' : VEnv} : ∀ {cis}, Ordered env →
    (∀ ci ∈ cis, ci.toVConstant.WF env) → env.addConsts cis = some env' → Ordered env'
  | [], h, _, e => by cases e; exact h
  | _ :: _, h, hw, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine VEnv.addConsts_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (VEnv.addConst_le h1)

theorem VEnv.addConsts_constants {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' →
    ∀ ci ∈ cis, env'.constants ci.name = some ci.toVConstant
  | [], _, _, hc => nomatch hc
  | _ :: _, e, c, hc => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    cases hc with
    | head => exact (VEnv.addConsts_le h2).constants (VEnv.addConst_self h1)
    | tail _ hc => exact VEnv.addConsts_constants h2 c hc

theorem VEnv.addDefEqs_ordered : ∀ {env : VEnv} {cis}, Ordered env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) →
    (∀ ci ∈ cis, ci.WF env) → Ordered (env.addDefEqs cis)
  | _, [], h, _, _ => h
  | env, ci :: cis, h, hmem, hw => by
    have hci : ci.WF env := hw _ (.head _)
    have hord : Ordered (env.addDefEq ci.toDefEq) := by
      refine .defeq h ⟨?_, hci⟩
      simp [VDefVal.toDefEq]
      rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
      exact .const (hmem _ (.head _)) VLevel.id_WF (by simp)
    show Ordered ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine VEnv.addDefEqs_ordered hord (fun c hc => ?_) (fun c hc => ?_)
    · exact (VEnv.addDefEq_le (df := ci.toDefEq)).constants (hmem c (.tail _ hc))
    · exact (hw c (.tail _ hc)).mono VEnv.addDefEq_le

theorem VEnv.WF.ordered : WF env → Ordered env
  | ⟨ds, H⟩ => by
    induction H with | empty => exact .empty | decl h _ ih
    cases h with
    | «axiom» h1 h2 => exact .const ih h1 h2
    | @«def» env env' ci h1 h2 =>
      refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
      · simp [VDefVal.toDefEq]
        rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConst_self h2) VLevel.id_WF (by simp)
      · exact h1.mono (addConst_le h2)
    | mutualDef h0 h1 h2 =>
      exact VEnv.addDefEqs_ordered (VEnv.addConsts_ordered ih h0 h1)
        (VEnv.addConsts_constants h1) h2
    | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
    | «example» _ => exact ih
    | quot h1 h2 => exact addQuot_WF ih h1 h2
    | induct h1 h2 => exact addInduct_WF ih h1 h2

instance : CoeOut (VEnv.WF env) env.Ordered := ⟨(·.ordered)⟩

/-- Every `VDecl.WF` step only grows the environment. -/
theorem VDecl.WF.le {env d env'} (h : VDecl.WF env d env') : env ≤ env' := by
  cases h with
  | «axiom» _ h2 => exact VEnv.addConst_le h2
  | «def» _ h2 => exact (VEnv.addConst_le h2).trans VEnv.addDefEq_le
  | mutualDef _ h2 _ => exact (VEnv.addConsts_le h2).trans VEnv.addDefEqs_le
  | «opaque» _ h2 => exact VEnv.addConst_le h2
  | «example» _ => exact .rfl
  | quot _ h2 => exact VEnv.addQuot_le h2
  | induct _ h2 => exact VEnv.addInduct_le h2

/-- A well-formed prefix is a sub-environment. -/
theorem VEnv.WFPrefix.le {env env₀ : VEnv} (h : env.WFPrefix env₀) : env₀ ≤ env := by
  induction h with
  | rfl => exact .rfl
  | decl hd _ ih => exact ih.trans hd.le

/-- Subject reduction of the registered ι rules in every environment the strengthening
argument types a constant or a definitional axiom in (`VEnv.WF.strong`): a well-formed
prefix `env₁` of `env`, and the extensions of one by constants alone — same `defeqs`, same
`pats`, still inside `env`. These are the stage environments of an inductive step and the
intermediate environments of `addQuot`; a prefix already carries a prefix's `pats`. -/
def VEnv.PatsStrong (env : VEnv) : Prop :=
  ∀ env₁ env₀, env.WFPrefix env₁ → env₁ ≤ env₀ → env₀ ≤ env →
    env₀.defeqs = env₁.defeqs → env₀.pats = env₁.pats → Ordered env₀ → PatsStrongOn env₀

/-- `OnTypes (EnvStrong ·)` is carried along a fold over `addConst`, given the typing of every
added constant in the environment the fold starts from and subject reduction of the ι rules
in each environment it passes through (all of them extend `init` by constants alone). -/
theorem VEnv.foldlM_addConst_strong {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      (∀ {e : VEnv}, init ≤ e → e ≤ final → e.defeqs = init.defeqs → e.pats = init.pats →
        Ordered e → PatsStrongOn e) →
      Ordered init → OnTypes init (EnvStrong init) → (∀ a ∈ l, (ci a).WF init) →
      l.foldlM (fun e a => e.addConst (nm a) (ci a)) init = some final →
      OnTypes final (EnvStrong final)
  | [], _, _, _, _, IH, _, h => by simp [List.foldlM] at h; subst h; exact IH
  | a :: _, _, _, hpats, hord, IH, hwf, h => by
    simp only [List.foldlM] at h
    obtain ⟨env₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have hle₁ := addConst_le h₁
    have hle₂ := foldlM_le (fun hh => addConst_le hh) h₂
    have hd := addConst_defeqs h₁
    have hp := addConst_pats h₁
    exact foldlM_addConst_strong
      (fun hl hl' hd' hp' ho => hpats (hle₁.trans hl) hl' (hd'.trans hd) (hp'.trans hp) ho)
      (.const hord (hwf a (.head _)) h₁)
      (OnTypes.addConst hord IH (hpats .rfl (hle₁.trans hle₂) rfl rfl hord)
        (hwf a (.head _)) h₁)
      (fun b hb => (hwf b (.tail _ hb)).mono hle₁) h₂

/-- Adding a block of definitional axioms whose two sides are strongly typed in the
environment the block starts from leaves every constant and definitional axiom strongly
typed. -/
theorem VEnv.addDefEqs_strong : ∀ {env : VEnv} {cis : List VDefVal},
    OnTypes env (EnvStrong env) →
    (∀ ci ∈ cis, EnvStrong env ci.toDefEq.uvars ci.toDefEq.lhs ci.toDefEq.type ∧
      EnvStrong env ci.toDefEq.uvars ci.toDefEq.rhs ci.toDefEq.type) →
    OnTypes (env.addDefEqs cis) (EnvStrong (env.addDefEqs cis))
  | _, [], IH, _ => IH
  | env, ci :: _, IH, h => by
    show OnTypes ((env.addDefEq ci.toDefEq).addDefEqs _) _
    refine addDefEqs_strong (OnTypes.addDefEq IH (h _ (.head _)).1 (h _ (.head _)).2)
      fun c hc => ⟨(h c (.tail _ hc)).1.mono addDefEq_le, (h c (.tail _ hc)).2.mono addDefEq_le⟩

/-- Registering the ι rules of a block adds neither a constant nor a definitional axiom, so
strong typing of both survives stage 3 of `addInduct`. -/
theorem VEnv.addRules_strong {decl : VInductDecl} {envR env' : VEnv}
    (IH : OnTypes envR (EnvStrong envR)) (h : decl.addRules envR = some env') :
    OnTypes env' (EnvStrong env') := by
  unfold VInductDecl.addRules at h
  refine foldlM_inv (P := fun e => OnTypes e (EnvStrong e)) (fun _ _ _ _ hIH hf => ?_) IH h
  refine foldlM_inv (P := fun e => OnTypes e (EnvStrong e)) (fun _ _ _ _ hIH hf => ?_) hIH hf
  unfold addRecRule at hf
  split at hf
  · cases hf; exact OnTypes.addPat hIH
  · cases hf

/-- Adding the quotient constants and the quotient rule to a strong environment leaves every
constant and definitional axiom strongly typed. -/
theorem VEnv.addQuot_strong {env env' : VEnv} (hord : Ordered env)
    (IH : OnTypes env (EnvStrong env)) (hq : QuotReady env)
    (hpats : ∀ {e : VEnv}, env ≤ e → e ≤ env' → e.defeqs = env.defeqs → e.pats = env.pats →
      Ordered e → PatsStrongOn e)
    (h : env.addQuot = some env') : OnTypes env' (EnvStrong env') := by
  obtain ⟨q1, q2, q3, q4, w1, a1, w2, a2, w3, a3, w4, a4, wdf, rfl⟩ := addQuot_chain hq h
  have l1 := addConst_le a1; have l2 := addConst_le a2
  have l3 := addConst_le a3; have l4 := addConst_le a4
  have l5 : q4 ≤ q4.addDefEq quotDefEq := addDefEq_le
  have d1 := addConst_defeqs a1; have d2 := addConst_defeqs a2
  have d3 := addConst_defeqs a3; have d4 := addConst_defeqs a4
  have p1 := addConst_pats a1; have p2 := addConst_pats a2
  have p3 := addConst_pats a3; have p4 := addConst_pats a4
  have O1 : Ordered q1 := .const hord w1 a1
  have I1 := OnTypes.addConst hord IH
    (hpats .rfl (l1.trans (l2.trans (l3.trans (l4.trans l5)))) rfl rfl hord) w1 a1
  have O2 : Ordered q2 := .const O1 w2 a2
  have I2 := OnTypes.addConst O1 I1
    (hpats l1 (l2.trans (l3.trans (l4.trans l5))) d1 p1 O1) w2 a2
  have O3 : Ordered q3 := .const O2 w3 a3
  have I3 := OnTypes.addConst O2 I2
    (hpats (l1.trans l2) (l3.trans (l4.trans l5)) (d2.trans d1) (p2.trans p1) O2) w3 a3
  have O4 : Ordered q4 := .const O3 w4 a4
  have I4 := OnTypes.addConst O3 I3
    (hpats (l1.trans (l2.trans l3)) (l4.trans l5) (d3.trans (d2.trans d1))
      (p3.trans (p2.trans p1)) O3) w4 a4
  have P4 : PatsStrongOn _ := hpats (l1.trans (l2.trans (l3.trans l4))) l5
    (d4.trans (d3.trans (d2.trans d1))) (p4.trans (p3.trans (p2.trans p1))) O4
  exact OnTypes.addDefEq I4 (EnvStrong.of_hasType O4 I4 P4 wdf.1)
    (EnvStrong.of_hasType O4 I4 P4 wdf.2)

/-- Adding a well-formed inductive declaration to a strong environment leaves every constant
and definitional axiom strongly typed: the three constant stages by
`foldlM_addConst_strong`, each in the environment `VInductDecl.WF` types its constants in,
and the ι-rule stage by `addRules_strong`. -/
theorem VEnv.addInduct_strong {env env' : VEnv} {decl : VInductDecl}
    (hord : Ordered env) (IH : OnTypes env (EnvStrong env)) (hdecl : decl.WF env)
    (hpats : ∀ {e : VEnv}, env ≤ e → e ≤ env' → e.defeqs = env.defeqs → e.pats = env.pats →
      Ordered e → PatsStrongOn e)
    (h : env.addInduct decl = some env') : OnTypes env' (EnvStrong env') := by
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := addInduct_stages h
  have hTC : decl.addTypesCtors env = some envC := by
    unfold VInductDecl.addTypesCtors; rw [hT]; exact hC
  have leT := addTypes_le hT; have leC := addCtors_le hC
  have leR := addRecs_le hR; have leP := addRules_le hP
  have dT := addTypes_defeqs hT; have dC := addCtors_defeqs hC
  have pT := addTypes_pats hT; have pC := addCtors_pats hC
  have hordT := addTypes_ordered hord hdecl hT
  have hordC := addCtors_ordered hdecl hT hordT hC
  have IHT : OnTypes envT (EnvStrong envT) := by
    unfold VInductDecl.addTypes at hT
    exact foldlM_addConst_strong
      (fun hl hl' hd hpt ho => hpats hl (hl'.trans (leC.trans (leR.trans leP))) hd hpt ho)
      hord IH hdecl.types_wf hT
  have IHC : OnTypes envC (EnvStrong envC) := by
    have hcw : ∀ c ∈ decl.types.flatMap (·.ctors), c.toVConstant.WF envT := fun c hc => by
      obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
      exact hdecl.ctors_wf envT hT t ht c hc
    unfold VInductDecl.addCtors at hC
    exact foldlM_addConst_strong
      (fun hl hl' hd hpt ho => hpats (leT.trans hl) (hl'.trans (leR.trans leP))
        (hd.trans dT) (hpt.trans pT) ho)
      hordT IHT hcw hC
  have IHR : OnTypes envR (EnvStrong envR) := by
    have hrw := hdecl.recs_wf envC hTC
    unfold VInductDecl.addRecs at hR
    exact foldlM_addConst_strong
      (fun hl hl' hd hpt ho => hpats ((leT.trans leC).trans hl) (hl'.trans leP)
        (hd.trans (dC.trans dT)) (hpt.trans (pC.trans pT)) ho)
      hordC IHC hrw hR
  exact addRules_strong IHR hP

/-- Every constant and definitional axiom of a well-formed environment is strongly typed:
each is strengthened by `IsDefEq.strong'` in the environment it is typed in, then lifted by
monotonicity. The ι rules of that environment are supplied by the hypothesis. -/
theorem VEnv.WF.strong {env : VEnv} (H : env.WF) (hp : env.PatsStrong) :
    OnTypes env (EnvStrong env) := by
  have key : ∀ {ds e}, WF' ds e → env.WFPrefix e → OnTypes e (EnvStrong e) := by
    intro ds e H
    induction H with
    | empty => exact fun _ => ⟨nofun, nofun⟩
    | decl hd hwf ih =>
      intro hpre
      have hpre₀ := hpre.trans (.decl hd .rfl)
      have IH := ih hpre₀
      have hord := WF.ordered ⟨_, hwf⟩
      have htop := hpre.le
      clear ih hpre hwf
      cases hd with
      | «axiom» h1 h2 =>
        exact OnTypes.addConst hord IH
          (hp _ _ hpre₀ .rfl ((addConst_le h2).trans htop) rfl rfl hord) h1 h2
      | «opaque» h1 h2 =>
        exact OnTypes.addConst hord IH
          (hp _ _ hpre₀ .rfl ((addConst_le h2).trans htop) rfl rfl hord)
          (h1.isType (Γ := []) hord ⟨⟩) h2
      | «example» _ => exact IH
      | «def» h1 h2 =>
        have hisT := h1.isType (Γ := []) hord ⟨⟩
        have hle₁ := addConst_le h2
        have hle₂ := addDefEq_le.trans htop
        have hord₁ : Ordered _ := .const hord hisT h2
        have IH₁ := OnTypes.addConst hord IH
          (hp _ _ hpre₀ .rfl (hle₁.trans hle₂) rfl rfl hord) hisT h2
        have hpats₁ : PatsStrongOn _ :=
          hp _ _ hpre₀ hle₁ hle₂ (addConst_defeqs h2) (addConst_pats h2) hord₁
        refine OnTypes.addDefEq IH₁ (EnvStrong.of_hasType hord₁ IH₁ hpats₁ ?_)
          (EnvStrong.of_hasType hord₁ IH₁ hpats₁ (h1.mono hle₁))
        simp [VDefVal.toDefEq]
        rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConst_self h2) VLevel.id_WF (by simp)
      | mutualDef h0 h1 h2 =>
        have hle₁ := addConsts_le h1
        have hle₂ := addDefEqs_le.trans htop
        have hord₁ := addConsts_ordered hord h0 h1
        have IH₁ := foldlM_addConst_strong
          (nm := fun c : VDefVal => c.name) (ci := fun c : VDefVal => c.toVConstant)
          (fun hl hl' hd hpt ho => hp _ _ hpre₀ hl (hl'.trans hle₂) hd hpt ho)
          hord IH h0 h1
        have hpats₁ : PatsStrongOn _ :=
          hp _ _ hpre₀ hle₁ hle₂ (addConsts_defeqs h1) (addConsts_pats h1) hord₁
        refine addDefEqs_strong IH₁ fun c hc => ⟨EnvStrong.of_hasType hord₁ IH₁ hpats₁ ?_,
          EnvStrong.of_hasType hord₁ IH₁ hpats₁ (h2 c hc)⟩
        simp [VDefVal.toDefEq]
        rw [← ((h2 c hc).levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConsts_constants h1 c hc) VLevel.id_WF (by simp)
      | quot h1 h2 =>
        exact addQuot_strong hord IH h1
          (fun hl hl' hd hpt ho => hp _ _ hpre₀ hl (hl'.trans htop) hd hpt ho) h2
      | induct h1 h2 =>
        exact addInduct_strong hord IH h1
          (fun hl hl' hd hpt ho => hp _ _ hpre₀ hl (hl'.trans htop) hd hpt ho) h2
  obtain ⟨_, H⟩ := H
  exact key H .rfl

/-- Subject reduction of every registered ι rule in every well-formed prefix of `env` and in
the constant-only extensions of such a prefix — the environments in which constant types and
definitional axioms are strengthened. This is the thesis's regularity lemma for `⇝`
(`typesys.tex`, "Regularity continued"; `unique.tex`, "Regularity of reductions") and not a
consequence of `Ordered`, whose `defeq` step admits arbitrary well-typed axioms: under
`List Nat ≡ List Bool` the redex `List.rec Nat m n c (List.cons Bool true tl)` is well-typed
and its reduct is not. It is open: proving it needs inversion of the redex's typing and
injectivity of the block's type formers (`Injectivity.lean`, also open), which the
direct-block specification of `VInductDecl.WF` makes applicable — every rule fires on a
constructor of the eliminated type former, whose result type carries the constructor's
parameters and whose major premise carries the recursor's. -/
theorem VEnv.WF.patsStrong {env : VEnv} (H : env.WF) : env.PatsStrong := sorry

/-- A well-formed environment satisfies the hypotheses of the strong system: `Ordered`,
strong typing of its constants and definitional axioms, and subject reduction of its ι rules
(`VEnv.WF.patsStrong`, the deferred ι obligation). -/
theorem VEnv.WF.orderedStrong (H : WF env) : OrderedStrong env :=
  ⟨H.ordered, H.strong H.patsStrong, H.patsStrong _ _ .rfl .rfl .rfl rfl rfl H.ordered⟩

-- Every use of the strong system is therefore conditional on `VEnv.WF.patsStrong`.
instance : CoeOut (VEnv.WF env) env.OrderedStrong := ⟨(·.orderedStrong)⟩

/-! ### Origin of a well-formed environment's contents -/

namespace VEnv.WF'

/-- Every declaration of a well-formed list is a well-formed step `env₀ ⊢ d ⤳ env₁` from the
environment of the remaining suffix, and the environment it produces is a prefix of `env`. -/
theorem step_of_mem {ds : List VDecl} {env : VEnv} (H : env.WF' ds) {d : VDecl}
    (hd : d ∈ ds) :
    ∃ (ds₀ : List VDecl) (env₀ env₁ : VEnv),
      (d :: ds₀) <:+ ds ∧ env₀.WF' ds₀ ∧ VDecl.WF env₀ d env₁ ∧ env.WFPrefix env₁ := by
  induction H with
  | empty => cases hd
  | decl hwf H ih =>
    rcases List.mem_cons.1 hd with rfl | hd'
    · exact ⟨_, _, _, List.suffix_refl _, H, hwf, .rfl⟩
    · obtain ⟨ds₀, env₀, env₁, hs, h₀, h₁, hp⟩ := ih hd'
      exact ⟨ds₀, env₀, env₁, hs.trans (List.suffix_cons _ _), h₀, h₁, .decl hwf hp⟩

/-- An inductive block of a well-formed list was added by a well-formed `addInduct` step,
whose result is a sub-environment of `env`. -/
theorem induct_origin {ds : List VDecl} {env : VEnv} (H : env.WF' ds) {decl : VInductDecl}
    (hd : VDecl.induct decl ∈ ds) :
    ∃ env₀ env₁, decl.WF env₀ ∧ env₀.addInduct decl = some env₁ ∧ env₁ ≤ env := by
  obtain ⟨_, _, _, _, _, h, hp⟩ := H.step_of_mem hd
  cases h with | induct hdecl hadd => exact ⟨_, _, hdecl, hadd, hp.le⟩

/-- Every constant of a well-formed environment was introduced by exactly one step of its
declaration list: absent before that step, bound to its final value after it. -/
theorem consts_origin {ds : List VDecl} {env : VEnv} (H : env.WF' ds) {c : Name}
    {ci : VConstant} (hc : env.constants c = some ci) :
    ∃ (d : VDecl) (ds₀ : List VDecl) (env₀ env₁ : VEnv),
      (d :: ds₀) <:+ ds ∧ env₀.WF' ds₀ ∧ VDecl.WF env₀ d env₁ ∧ env₁ ≤ env ∧
      env₀.constants c = none ∧ env₁.constants c = some ci := by
  induction H with
  | empty => cases hc
  | @decl d env' ds env hwf H ih =>
    cases h₀ : env.constants c with
    | none => exact ⟨d, ds, env, env', List.suffix_refl _, H, hwf, .rfl, h₀, hc⟩
    | some ci₀ =>
      obtain rfl : ci₀ = ci := Option.some.inj ((hwf.le.constants h₀).symm.trans hc)
      obtain ⟨d₁, ds₀, env₀, env₁, hs, h₁, h₂, hle, h₃, h₄⟩ := ih h₀
      exact ⟨d₁, ds₀, env₀, env₁, hs.trans (List.suffix_cons _ _), h₁, h₂, hle.trans hwf.le,
        h₃, h₄⟩

/-- Every definitional axiom headed by a constant `c` has `c` declared, and is the only
definitional axiom headed by `c`. -/
private def DefEqsConst (env : VEnv) : Prop :=
  ∀ df c us, env.defeqs df → df.lhs = .const c us →
    env.constants c ≠ none ∧ ∀ df' us', env.defeqs df' → df'.lhs = .const c us' → df = df'

private theorem DefEqsConst.mono {env env' : VEnv} (H : DefEqsConst env) (hle : env ≤ env')
    (hd : env'.defeqs = env.defeqs) : DefEqsConst env' := by
  intro df c us h hl
  rw [hd] at h
  obtain ⟨hc, hu⟩ := H _ _ _ h hl
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hc
  exact ⟨by rw [hle.constants ha]; nofun, fun _ _ h' hl' => hu _ _ (hd ▸ h') hl'⟩

private theorem DefEqsConst.addDefEq {env : VEnv} {df₀ : VDefEq} {c₀ us₀}
    (H : DefEqsConst env) (hc : env.constants c₀ ≠ none)
    (hfresh : ∀ df us, env.defeqs df → df.lhs ≠ .const c₀ us)
    (hl : df₀.lhs = .const c₀ us₀) : DefEqsConst (env.addDefEq df₀) := by
  intro df c us h hl'
  rcases h with rfl | h
  · obtain rfl : c = c₀ := by rw [hl] at hl'; cases hl'; rfl
    refine ⟨hc, fun _ _ h' hl'' => ?_⟩
    rcases h' with rfl | h'
    · rfl
    · exact (hfresh _ _ h' hl'').elim
  · obtain ⟨hc', hu⟩ := H _ _ _ h hl'
    refine ⟨hc', fun _ _ h' hl'' => ?_⟩
    rcases h' with rfl | h'
    · obtain rfl : c = c₀ := by rw [hl] at hl''; cases hl''; rfl
      exact (hfresh _ _ h hl').elim
    · exact hu _ _ h' hl''

private theorem DefEqsConst.addDefEq_app {env : VEnv} {df₀ : VDefEq}
    (H : DefEqsConst env) (hl : ∀ c us, df₀.lhs ≠ .const c us) :
    DefEqsConst (env.addDefEq df₀) := by
  intro df c us h hl'
  rcases h with rfl | h
  · exact (hl _ _ hl').elim
  · obtain ⟨hc', hu⟩ := H _ _ _ h hl'
    refine ⟨hc', fun _ _ h' hl'' => ?_⟩
    rcases h' with rfl | h'
    · exact (hl _ _ hl'').elim
    · exact hu _ _ h' hl''

private theorem DefEqsConst.addDefEqs : ∀ {env : VEnv} {cis : List VDefVal},
    DefEqsConst env → (∀ ci ∈ cis, env.constants ci.name ≠ none) →
    (∀ ci ∈ cis, ∀ df us, env.defeqs df → df.lhs ≠ .const ci.name us) →
    (cis.map (·.name)).Nodup → DefEqsConst (env.addDefEqs cis)
  | _, [], H, _, _, _ => H
  | env, ci :: cis, H, hc, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show DefEqsConst ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine DefEqsConst.addDefEqs
      (H.addDefEq (hc _ (.head _)) (hfresh _ (.head _)) rfl)
      (fun c hm => hc c (.tail _ hm)) (fun c hm df us h hl => ?_) hnd.2
    rcases h with rfl | h
    · obtain ⟨h₁, -⟩ := VExpr.const.inj hl
      exact hnd.1 (h₁ ▸ List.mem_map_of_mem (f := (·.name)) hm)
    · exact hfresh c (.tail _ hm) _ _ h hl

private theorem defEqsConst {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    DefEqsConst env := by
  induction H with
  | empty => intro _ _ _ h; cases h
  | decl hwf _ ih =>
    cases hwf with
    | «axiom» _ h2 => exact ih.mono (addConst_le h2) (addConst_defeqs h2)
    | «opaque» _ h2 => exact ih.mono (addConst_le h2) (addConst_defeqs h2)
    | «example» _ => exact ih
    | induct _ h2 => exact ih.mono (addInduct_le h2) (addInduct_defeqs h2)
    | «def» _ h2 =>
      obtain ⟨hnone, hsome, -⟩ := addConst_eq h2
      refine (ih.mono (addConst_le h2) (addConst_defeqs h2)).addDefEq
        (by rw [hsome]; nofun) (fun _ _ h hl => ?_) rfl
      rw [addConst_defeqs h2] at h
      exact (ih _ _ _ h hl).1 hnone
    | mutualDef _ h2 _ =>
      have hd := addConsts_defeqs h2
      refine (ih.mono (addConsts_le h2) hd).addDefEqs
        (fun ci hm => by rw [addConsts_constants h2 ci hm]; nofun)
        (fun ci hm _ _ h hl => ?_) (addConst_foldlM_nodup h2)
      rw [hd] at h
      exact (ih _ _ _ h hl).1 (addConst_foldlM_fresh h2 ci hm)
    | quot _ h2 =>
      rw [VEnv.addQuot] at h2
      obtain ⟨e1, s1, h2⟩ := Option.bind_eq_some_iff.1 h2
      obtain ⟨e2, s2, h2⟩ := Option.bind_eq_some_iff.1 h2
      obtain ⟨e3, s3, h2⟩ := Option.bind_eq_some_iff.1 h2
      obtain ⟨e4, s4, h2⟩ := Option.bind_eq_some_iff.1 h2
      cases h2
      refine ((((ih.mono (addConst_le s1) (addConst_defeqs s1)).mono (addConst_le s2)
        (addConst_defeqs s2)).mono (addConst_le s3) (addConst_defeqs s3)).mono
        (addConst_le s4) (addConst_defeqs s4)).addDefEq_app fun _ _ h => ?_
      cases h

/-- A well-formed environment has at most one definitional axiom per constant head: its δ
rules are functional. -/
theorem defeqs_const_uniq {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    {df df' : VDefEq} (h : env.defeqs df) (h' : env.defeqs df') {c : Name}
    {us us' : List VLevel} (hlhs : df.lhs = .const c us) (hlhs' : df'.lhs = .const c us') :
    df = df' :=
  (defEqsConst H _ _ _ h hlhs).2 _ _ h' hlhs'

end VEnv.WF'
