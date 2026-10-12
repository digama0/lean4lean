import Lean4Lean.Theory.Typing.Confluence.EtaSpine

/-! # Inversion of joinable typings

A joinable typing of an application spine relates the spine's type to the declared telescope of
its head by a join (`HasTypeJ.mkApps_wrapForalls`): every conversion on the way is a join, and
joins of Π-types are injective (`FullCRDefEq.forallE_inv`) and stable under substitution
(`FullCRDefEq.instN`). -/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

theorem FullCRDefEq.refl_type (hΓ : OnCtx Γ (env.IsType univs)) (h : Γ ⊢ e : T) :
    Γ ⊢ T ≫≪ T :=
  let ⟨_, hT⟩ := h.isType henv.ordered hΓ; .refl hΓ hT

theorem HasTypeJ.app_inv (hΓ : OnCtx Γ (env.IsType univs)) (H : HasTypeJ Γ (.app f a) T) :
    ∃ A B, HasTypeJ Γ f (.forallE A B) ∧ HasTypeJ Γ a A ∧ Γ ⊢ B.inst a ≫≪ T := by
  generalize he : VExpr.app f a = e at H
  induction H with
  | const => cases he
  | app hf ha h => cases he; exact ⟨_, _, hf, ha, .refl_type hΓ h⟩
  | other hne => exact (hne _ _ he.symm).elim
  | defeq hAB _ _ ih =>
    obtain ⟨A, B, hf, ha, hj⟩ := ih hΓ he
    exact ⟨A, B, hf, ha, hj.trans hΓ hAB⟩

theorem HasTypeJ.const_inv (hΓ : OnCtx Γ (env.IsType univs)) (H : HasTypeJ Γ (.const c ls) T) :
    ∃ ci, env.constants c = some ci ∧ Γ ⊢ ci.type.instL ls ≫≪ T := by
  generalize he : VExpr.const c ls = e at H
  induction H with
  | const hc h => cases he; exact ⟨_, hc, .refl_type hΓ h⟩
  | app => cases he
  | other _ hne => exact (hne _ _ he.symm).elim
  | defeq hAB _ _ ih =>
    obtain ⟨ci, hc, hj⟩ := ih hΓ he
    exact ⟨ci, hc, hj.trans hΓ hAB⟩

theorem HasTypeJ.mkApps_head (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f T}, HasTypeJ Γ (VExpr.mkApps f args) T → ∃ T', HasTypeJ Γ f T'
  | [], _, _, H => ⟨_, H⟩
  | a :: as, f, _, H =>
    let ⟨_, H'⟩ := HasTypeJ.mkApps_head hΓ (f := .app f a) (args := as) H
    let ⟨_, _, hf, _⟩ := H'.app_inv hΓ
    ⟨_, hf⟩

/-- One step of a telescope: a join of Π-types instantiated at a typed argument. -/
theorem FullCRDefEq.forallE_inst (hΓ : OnCtx Γ (env.IsType univs))
    (H : Γ ⊢ .forallE X Y ≫≪ .forallE A B) (ha : Γ ⊢ a : A) :
    Γ ⊢ a : X ∧ Γ ⊢ Y.inst a ≫≪ B.inst a := by
  obtain ⟨hX, hY⟩ := H.forallE_inv hΓ
  have ha' : Γ ⊢ a : X := ha.defeqU_r henv hΓ (hX.defeq hΓ).symm
  exact ⟨ha', hY.inst0 ha'⟩

/-- **Joinable typing along a telescope.** If every joinable type of `f` joins the telescope
`∀ doms, body`, then every joinable type of `f args` joins `body` instantiated at `args`. -/
theorem HasTypeJ.mkApps_wrapForalls (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f doms body}, args.length = doms.length →
      Γ ⊢ f : VExpr.wrapForalls doms body →
      (∀ T', HasTypeJ Γ f T' → Γ ⊢ VExpr.wrapForalls doms body ≫≪ T') →
      ∀ T', HasTypeJ Γ (VExpr.mkApps f args) T' → Γ ⊢ body.instOuter args ≫≪ T' := by
  intro args
  induction args with
  | nil =>
    intro f doms body hlen _ hcond T' hJ
    cases doms with
    | nil => exact hcond T' hJ
    | cons => simp at hlen
  | cons a as ih =>
    intro f doms body hlen hf hcond T' hJ
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨_, hJa⟩ := HasTypeJ.mkApps_head hΓ (f := .app f a) (args := as) hJ
      obtain ⟨A, B, hJf, hJa', -⟩ := hJa.app_inv hΓ
      obtain ⟨had, -⟩ := (hcond _ hJf).forallE_inst hΓ hJa'.hasType
      have hfa : Γ ⊢ .app f a : (VExpr.wrapForalls ds body).inst a := HasType.app hf had
      rw [VExpr.wrapForalls_inst] at hfa
      have := ih (f := .app f a) (by simpa using hlen) hfa ?_ T' hJ
      · simpa [hlen] using this
      · intro T'' hJ''
        obtain ⟨A', B', hJf', hJa'', hB⟩ := hJ''.app_inv hΓ
        have ⟨_, hY⟩ := (hcond _ hJf').forallE_inst hΓ hJa''.hasType
        rw [← VExpr.wrapForalls_inst]
        exact hY.trans hΓ hB

/-- Two joinable telescopes of the same length have joinable bodies at arguments that a function
typed by the first telescope accepts. -/
theorem FullCRDefEq.wrapForalls_instOuter (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f doms doms' body body'}, args.length = doms.length → doms'.length = doms.length →
      Γ ⊢ f : VExpr.wrapForalls doms body → VExpr.WF env univs Γ (VExpr.mkApps f args) →
      Γ ⊢ VExpr.wrapForalls doms body ≫≪ VExpr.wrapForalls doms' body' →
      Γ ⊢ body.instOuter args ≫≪ body'.instOuter args := by
  intro args
  induction args with
  | nil =>
    intro f doms doms' body body' hlen hlen' _ _ H
    cases doms with
    | nil => cases doms' with
      | nil => exact H
      | cons => simp at hlen'
    | cons => simp at hlen
  | cons a as ih =>
    intro f doms doms' body body' hlen hlen' hf hwf H
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
    cases doms' with
    | nil => simp at hlen'
    | cons d' ds' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen hlen'
      have hfa : VExpr.WF env univs Γ (.app f a) :=
        VExpr.WF.of_mkApps henv.orderedStrong hΓ (f := .app f a) (by simpa [VExpr.mkApps] using hwf)
      obtain ⟨A, B, hf', ha'⟩ := hfa.app_inv henv.orderedStrong hΓ
      have ⟨⟨_, hdA⟩, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
      have had : Γ ⊢ a : d := ha'.defeqU_r henv hΓ ⟨_, hdA.symm⟩
      obtain ⟨hdd, -⟩ := H.forallE_inv hΓ
      have had' : Γ ⊢ a : d' := had.defeqU_r henv hΓ (hdd.defeq hΓ)
      obtain ⟨-, hY⟩ := H.forallE_inst hΓ had'
      have hfa' : Γ ⊢ .app f a : (VExpr.wrapForalls ds body).inst a := HasType.app hf had
      have hY' : Γ ⊢ (VExpr.wrapForalls ds body).inst a ≫≪ (VExpr.wrapForalls ds' body').inst a := hY
      rw [VExpr.wrapForalls_inst] at hfa'
      rw [VExpr.wrapForalls_inst, VExpr.wrapForalls_inst] at hY'
      have := ih (f := .app f a) (by simpa using hlen) (by simpa [hlen] using hlen') hfa'
        (by simpa [VExpr.mkApps] using hwf) hY'
      simpa [hlen, hlen'] using this

omit [Params] in
theorem VExpr.instOuter_forallE (A B : VExpr) :
    ∀ args : List VExpr, ∃ B', (VExpr.forallE A B).instOuter args = .forallE (A.instOuter args) B'
  | [] => ⟨_, rfl⟩
  | a :: as => by
    simp only [VExpr.instOuter_cons, VExpr.inst]
    obtain ⟨B', h⟩ := VExpr.instOuter_forallE (A.inst a as.length) (B.inst a (as.length + 1)) as
    exact ⟨B', h⟩

/-- Full reduction of a lambda telescope applied to as many arguments as it has binders. -/
theorem FullReduction.mkApps_wrapLams :
    ∀ {args doms : List VExpr} {body : VExpr}, args.length = doms.length →
      FullReduction Γ (VExpr.mkApps (VExpr.wrapLams doms body) args) (body.instOuter args)
  | [], [], _, _ => .rfl
  | a :: as, d :: ds, body, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have h1 : FullReduction Γ (VExpr.mkApps (.app (.lam d (VExpr.wrapLams ds body)) a) as)
        (VExpr.mkApps ((VExpr.wrapLams ds body).inst a) as) :=
      FullReduction.mkApps (.tail .rfl (.core (.beta .rfl .rfl))) (FullReduction.forall₂_rfl _)
    rw [VExpr.wrapLams_inst, Nat.zero_add] at h1
    have h2 := FullReduction.mkApps_wrapLams (Γ := Γ) (args := as)
      (doms := VExpr.instDomains ds a 0) (body := body.inst a ds.length) (by simpa using h)
    have := h1.trans h2
    simp only [VExpr.instOuter_cons, h]
    exact this
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp at h

/-- **Joinable typing of the major of a recursor application**: the major of
`r recArgs M`, with the recursor's type a telescope `∀ pre, ∀ (x : dm), br`, has a joinable type
joining `dm` instantiated at `recArgs`. -/
theorem HasTypeJ.major_join (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants rn = some ⟨u, VExpr.wrapForalls pre (.forallE dm br)⟩)
    (hlen : recArgs.length = pre.length)
    (H : HasTypeJ Γ (.app (VExpr.mkApps (.const rn L) recArgs) M) T) :
    ∃ X, HasTypeJ Γ M X ∧ Γ ⊢ (dm.instL L).instOuter recArgs ≫≪ X := by
  obtain ⟨X, Y, hJf, hJM, -⟩ := H.app_inv hΓ
  obtain ⟨_, hJc⟩ := HasTypeJ.mkApps_head hΓ hJf
  obtain ⟨ci, hci, -⟩ := hJc.const_inv hΓ
  rw [hc] at hci; cases hci
  obtain ⟨_, hw, hl⟩ := hJc.hasType.const_inv henv.orderedStrong hΓ
  rw [hc] at hw; cases hw
  have hct : Γ ⊢ .const rn L : VExpr.wrapForalls (pre.map (·.instL L))
      (.forallE (dm.instL L) (br.instL L)) := by
    have := HasType.const (Γ := Γ) hc hl.1 hl.2
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using this
  have hj := HasTypeJ.mkApps_wrapForalls hΓ (by simpa using hlen) hct (fun T' hJ' => by
    obtain ⟨ci, hci, hj⟩ := hJ'.const_inv hΓ
    rw [hc] at hci; cases hci
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using hj) _ hJf
  obtain ⟨B', hB'⟩ := VExpr.instOuter_forallE (dm.instL L) (br.instL L) recArgs
  rw [hB'] at hj
  exact ⟨X, hJM, (hj.forallE_inv hΓ).1⟩

/-- **Joinable typing of a saturated application of a constant** with a telescope type. -/
theorem HasTypeJ.const_spine_join (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants cn = some ⟨u, VExpr.wrapForalls Ds Rs⟩)
    (hlen : B.length = Ds.length)
    (H : HasTypeJ Γ (VExpr.mkApps (.const cn cl) B) X) :
    Γ ⊢ (Rs.instL cl).instOuter B ≫≪ X := by
  obtain ⟨_, hJc⟩ := HasTypeJ.mkApps_head hΓ H
  obtain ⟨_, hw, hl⟩ := hJc.hasType.const_inv henv.orderedStrong hΓ
  rw [hc] at hw; cases hw
  have hct : Γ ⊢ .const cn cl : VExpr.wrapForalls (Ds.map (·.instL cl)) (Rs.instL cl) := by
    have := HasType.const (Γ := Γ) hc hl.1 hl.2
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using this
  exact HasTypeJ.mkApps_wrapForalls hΓ (by simpa using hlen) hct (fun T' hJ' => by
    obtain ⟨ci, hci, hj⟩ := hJ'.const_inv hΓ
    rw [hc] at hci; cases hci
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using hj) _ H

end Lean4Lean.VEnv
