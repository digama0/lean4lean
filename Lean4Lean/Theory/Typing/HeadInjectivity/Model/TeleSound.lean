import Lean4Lean.Theory.Typing.HeadInjectivity.Model.BetaSpine

/-! # Soundly equal telescopes

Two closed Pi telescopes `wrapForalls D₁ R₁` and `wrapForalls D₂ R₂` whose observations subsume
each other (as the soundness of a conversion between them gives) have domainwise related
binders: typed keys along a prefix of the one are typed keys along the prefix of the other
(`tele_sound_keys`), and at every typed valuation of a prefix by arguments the next domains
have the same type class and observations subsuming each other (`tele_sound_dom`). This is how
the field binders of a normalized constructor type are related to those of the installed
constructor constant, which the compilation records as definitionally equal. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem closedN_wrapForalls : ∀ {ds : List VExpr} {b : VExpr} {k : Nat},
    (VExpr.wrapForalls ds b).ClosedN k →
      b.ClosedN (k + ds.length) ∧ ∀ i (h : i < ds.length), (ds[i]).ClosedN (k + i)
  | [], _, _, h => ⟨h, nofun⟩
  | d :: ds, b, k, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := closedN_wrapForalls (ds := ds) h2
    refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using h3, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := h4 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- The observation sets of covered keys are covered by those of the keys. -/
theorem extS_covers : ∀ {keys' keys : List Key},
    List.Forall₂ (fun (k' k : Key) => k'.1 = k.1 ∧ k'.2.1 = k.2.1 ∧ Covers k.2.2 k'.2.2)
      keys' keys →
    ∀ m o, extS .empty keys' m o → ∃ o', extS .empty keys m o' ∧ o' ≼ o := by
  intro keys'
  induction keys' using List.reverseRecOn with
  | nil =>
    intro keys h; cases h
    intro m o h; exact absurd h (by simp [extS, ObSets.empty])
  | snoc keys' k' ih =>
    intro keys h
    obtain ⟨ks, k, rfl, h', hk⟩ := forall₂_snoc_inv h
    intro m o ho
    rw [extS_snoc] at ho
    rw [extS_snoc]
    cases m with
    | zero =>
      obtain ⟨z, hz, l⟩ := hk.2.2 o ho
      exact ⟨z, hz, l⟩
    | succ m => exact ih h' m o ho

theorem wrapForalls_split {D : List VExpr} {R : VExpr} {j : Nat} (hj : j < D.length) :
    VExpr.wrapForalls D R =
      .wrapForalls (D.take j) (.forallE D[j] (.wrapForalls (D.drop (j + 1)) R)) := by
  conv => lhs; rw [← List.take_append_drop j D, List.drop_eq_getElem_cons hj]
  rw [VExpr.wrapForalls_append]; rfl

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- One domain of two telescopes whose observations are subsumed one way, at typed keys along
both prefixes. -/
theorem tele_sound_step {D₁ D₂ : List VExpr} {R₁ R₂ : VExpr} (hpi₂ : PiSD env U Δ [] D₂ R₂)
    (hsub : Ob.Sub (Obs' .id .empty (.wrapForalls D₁ R₁)) (Obs' .id .empty (.wrapForalls D₂ R₂)))
    {j : Nat} (hj₁ : j < D₁.length) (hj₂ : j < D₂.length) {keys : List Key}
    {σ' : VExpr.Subst} {S' : ObSets}
    (hTK₁ : TeleKeys env U Δ .id .empty (D₁.take j) keys σ' S')
    (hTK₂ : TeleKeys env U Δ .id .empty (D₂.take j) keys σ' S') :
    TyCls env U Δ (D₁[j].subst σ') = TyCls env U Δ (D₂[j].subst σ') ∧
    Ob.Sub (Obs' σ' S' D₁[j]) (Obs' σ' S' D₂[j]) := by
  have e₁ := wrapForalls_split (R := R₁) hj₁
  have e₂ := wrapForalls_split (R := R₂) hj₂
  have hkl : keys.length = j := by
    rw [hTK₁.length]; simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj₁)]
  obtain ⟨-, w, hDj⟩ := DomsSD.take_getElem hpi₂.doms j hj₂
  rw [List.append_nil] at hDj
  have hDjTy : env.HasType U (D₂.take j).reverse D₂[j] (.sort w) := hDj.1.defeq.hasType.1
  have hds₂ : DomsSD env U Δ [] (D₂.take j) := hpi₂.doms.take j
  have hctx : CtxSD env U Δ [] (D₂.take j).reverse := by
    have := DomsSD.ctxSD (L := []) (Γ := []) hds₂ .nil
    simpa using this
  obtain ⟨ys₀, hσ', hS', hyl₀, -, -⟩ := hTK₁.data
  have hyl₀' : ys₀.length = j := by
    rw [hyl₀]; simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj₁)]
  -- transfer of an observation of the Pi type at `j` from the first telescope to the second
  have transfer : ∀ z, Obs' σ' S' (.forallE D₁[j] (.wrapForalls (D₁.drop (j + 1)) R₁)) z →
      ∃ ys z' keys', z' ≼ z ∧
        List.Forall₂ (fun (k' k : Key) => k'.1 = k.1 ∧ k'.2.1 = k.2.1 ∧ Covers k.2.2 k'.2.2)
          keys' keys ∧
        Ctx.SubstEq env U Δ (VExpr.argSubst ys) σ' (D₂.take j).reverse ∧
        TV env U Δ (D₂.take j).reverse (VExpr.argSubst ys) (extS .empty keys') ∧
        TV env U Δ (D₂.take j).reverse σ' (extS .empty keys') ∧
        Obs' (VExpr.argSubst ys) (extS .empty keys')
          (.forallE D₂[j] (.wrapForalls (D₂.drop (j + 1)) R₂)) z' := by
    intro z hz
    have h1 := tele_obs hTK₁ hz
    rw [← e₁] at h1
    obtain ⟨o', ho', l⟩ := hsub _ h1
    obtain ⟨keys', z', rfl, hkk, lz⟩ := Le.piCodChain_inv l
    rw [e₂] at ho'
    have hkl' : keys'.length = j := by rw [List.Forall₂.length_eq hkk, hkl]
    have htl : (D₂.take j).length = j := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj₂)]
    obtain ⟨keys'', ys, hT, -, hky, hz'⟩ := tele_split (Nat.le_of_eq (hkl'.trans htl.symm)) ho'
    rw [hkl', List.take_of_length_le (Nat.le_of_eq htl)] at hT
    rw [hkl', List.drop_eq_nil_of_le (Nat.le_of_eq htl)] at hz'
    simp only [VExpr.wrapForalls, List.foldr_nil] at hz'
    have hcls : List.Forall₂ (fun (k : Key) y => k.2.1 y) keys ys :=
      forall₂_zip (fun _ _ _ h1 h2 => h1.2.1 ▸ h2) hkk hky
    have W' := hTK₂.substEq henv hΔ (v := .id) hds₂ .nil hcls
    rw [List.append_nil] at W'
    have W'' : Ctx.SubstEq env U Δ (VExpr.argSubst ys) σ' (D₂.take j).reverse :=
      SubstEq.symm henv hΔ W'
    obtain ⟨Wy, tvy⟩ := hT.typed henv hΔ hds₂ .nil TV.empty
    rw [List.append_nil] at Wy tvy
    have hyl : ys.length = j := by rw [← List.Forall₂.length_eq hky, hkl']
    have hout : ∀ x, (D₂.take j).reverse.length ≤ x →
        σ' x = (ys.foldl VExpr.Subst.cons VExpr.Subst.id) x := by
      intro x hx
      rw [List.length_reverse, htl] at hx
      show σ' x = VExpr.argSubst ys x
      rw [hσ', VExpr.argSubst_ge _ (by omega)]
      show VExpr.argSubst ys₀ x = _
      rw [VExpr.argSubst_ge _ (by omega), hyl, hyl₀']
    have tvσ : TV env U Δ (D₂.take j).reverse σ' (extS .empty keys') := by
      have := TV.transfer henv hΔ (Γ := []) hctx (by simpa using W') (by simpa using hout)
        (by simpa using tvy)
      simpa using this
    exact ⟨ys, z', keys', lz, hkk, W'', tvy, tvσ, hz'⟩
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨ys, z', keys', lz, -, W'', -, -, hz'⟩ := transfer _ (Obs.piDom (A := D₁[j])
      (B := .wrapForalls (D₁.drop (j + 1)) R₁))
    rw [lz.piDom_inv] at hz'
    have e := Obs.piDom_mem hz'
    rw [e]
    exact TyCls.eq_of_defeq (hDjTy.substDF henv W''.wf hΔ W'')
  · obtain ⟨ys, z', keys', lz, hkk, W'', tvy, tvσ, hz'⟩ :=
      transfer _ (Obs.piDomOb (B := .wrapForalls (D₁.drop (j + 1)) R₁) hx)
    obtain ⟨x', rfl, lx⟩ := lz.piDomOb_inv
    have hx' := Obs.piDomOb_mem hz'
    obtain ⟨x'', hx'', l''⟩ := (hDj.2 _ _ _ W'' tvy tvσ).1 _ hx'
    obtain ⟨x₃, hx₃, l₃⟩ := hx''.mono_le (S' := S') fun i o h => by
      rw [hS']
      exact extS_covers hkk i o h
    exact ⟨x₃, hx₃, l₃.trans (l''.trans lx)⟩

/-- Typed keys along a prefix of the first telescope are typed keys along the prefix of the
second. -/
theorem tele_sound_keys {D₁ D₂ : List VExpr} {R₁ R₂ : VExpr}
    (hpi₂ : PiSD env U Δ [] D₂ R₂)
    (hsub₁ : Ob.Sub (Obs' .id .empty (.wrapForalls D₁ R₁)) (Obs' .id .empty (.wrapForalls D₂ R₂)))
    (hlen : D₁.length = D₂.length) :
    ∀ j, j ≤ D₁.length → ∀ {keys : List Key} {σ' : VExpr.Subst} {S' : ObSets},
      TeleKeys env U Δ .id .empty (D₁.take j) keys σ' S' →
      TeleKeys env U Δ .id .empty (D₂.take j) keys σ' S' := by
  intro j
  induction j with
  | zero =>
    intro _ keys σ' S' h
    simp only [List.take_zero] at h ⊢
    cases h; exact .nil
  | succ j ih =>
    intro hj keys σ' S' h
    have hj₁ : j < D₁.length := by omega
    have hj₂ : j < D₂.length := by omega
    rw [List.take_succ_eq_append_getElem hj₁] at h
    have hkl : keys.length = j + 1 := by
      rw [h.length]; simp [List.length_take, Nat.min_eq_left hj]
    obtain ⟨kpre, k, rfl⟩ : ∃ kpre k, keys = kpre ++ [k] := by
      rcases List.eq_nil_or_concat keys with rfl | ⟨kpre, k, rfl⟩
      · simp at hkl
      · exact ⟨kpre, k, List.concat_eq_append⟩
    have hpl : (D₁.take j).length = kpre.length := by
      simp at hkl; simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj₁)]; omega
    obtain ⟨σ₁, S₁, h1, h2⟩ := TeleKeys.split hpl h
    have h1' := ih (by omega) h1
    obtain ⟨eT, hsubj⟩ := tele_sound_step henv hΔ hpi₂ hsub₁ hj₁ hj₂ h1 h1'
    cases h2 with
    | cons hc hy hK hb h3 =>
      cases h3
      rw [List.take_succ_eq_append_getElem hj₂]
      have := TeleKeys.snoc h1' (eT ▸ hc) hy (fun k hk => (hK k hk).mono_le hsubj) hb
      rwa [← eT] at this

/-- **Domains of soundly equal telescopes** at a typed valuation of a prefix by arguments: the
next domains have the same type class and observations subsuming each other. -/
theorem tele_sound_dom {D₁ D₂ : List VExpr} {R₁ R₂ : VExpr} {T : VExpr}
    (hcl₁ : ∀ i (hi : i < D₁.length), (D₁[i]).ClosedN i)
    (hcl₂ : ∀ i (hi : i < D₂.length), (D₂[i]).ClosedN i)
    (hS : SoundAt env U Δ [] (.wrapForalls D₁ R₁) (.wrapForalls D₂ R₂) T)
    (hpi₁ : PiSD env U Δ [] D₁ R₁) (hpi₂ : PiSD env U Δ [] D₂ R₂) (hlen : D₁.length = D₂.length)
    {as : List VExpr} {Sx : ObSets} (hj : as.length < D₁.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst as) (D₁.take as.length).reverse)
    (tv : TV env U Δ (D₁.take as.length).reverse (VExpr.argSubst as) Sx) :
    TyCls env U Δ (D₁[as.length].subst (VExpr.argSubst as)) =
      TyCls env U Δ (D₂[as.length].subst (VExpr.argSubst as)) ∧
    Ob.Sub (Obs' (VExpr.argSubst as) Sx D₁[as.length]) (Obs' (VExpr.argSubst as) Sx D₂[as.length]) ∧
    Ob.Sub (Obs' (VExpr.argSubst as) Sx D₂[as.length])
      (Obs' (VExpr.argSubst as) Sx D₁[as.length]) := by
  have hS0 := hS .id .id .empty .nil TV.empty TV.empty
  have hsub₁ := hS0.1
  have hsub₂ := hS0.2.1
  have hj₂ : as.length < D₂.length := by omega
  have hclT : ∀ i (hi : i < (D₁.take as.length).length), ((D₁.take as.length)[i]).ClosedN i := by
    intro i hi
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    exact hcl₁ i (by omega)
  have htl : as.length = (D₁.take as.length).length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  -- typed keys along the prefix at the arguments, with the given demands
  have keysOf : ∀ G : List (List Ob), G.length = as.length →
      (∀ m (hm : m < G.length), ∀ y ∈ G[m], Sx m y) →
      ∃ keys S', TeleKeys env U Δ .id .empty (D₁.take as.length) keys (VExpr.argSubst as) S' ∧
        TeleKeys env U Δ .id .empty (D₂.take as.length) keys (VExpr.argSubst as) S' ∧
        (∀ m (hm : m < G.length), ∀ y ∈ G[m], S' m y) ∧ (∀ m y, S' m y → Sx m y) := by
    intro G hGl hGS
    obtain ⟨keys, S', hTK, hkl, hS', hkeys⟩ := tele_compact hclT htl W tv G.reverse
      (by rw [List.length_reverse, hGl]; exact htl) (fun i Fi hFi y hy => by
        have hil : i < G.length := by
          have := (List.getElem?_eq_some_iff.1 hFi).1; simpa using this
        rw [List.getElem?_reverse hil, List.getElem?_eq_getElem (by omega)] at hFi
        cases hFi
        have := hGS (G.length - 1 - i) (by omega) y hy
        rwa [hGl, htl] at this)
    refine ⟨keys, S', hTK, tele_sound_keys henv hΔ hpi₂ hsub₁ hlen _ (Nat.le_of_lt hj) hTK,
      fun m hm y hy => ?_, fun m y hy => ?_⟩
    · have hmD : m < (D₁.take as.length).length := by rw [← htl, ← hGl]; exact hm
      have hkD : (D₁.take as.length).length - 1 - m < keys.length := by omega
      refine (hS' m keys[_] (List.getElem?_eq_getElem hkD) hmD y).2 ?_
      refine (hkeys _ _ (List.getElem?_eq_getElem hkD)).1 G[m] ?_ y hy
      rw [List.getElem?_reverse (by omega), List.getElem?_eq_getElem (by omega)]
      congr 2; omega
    · by_cases hm : m < (D₁.take as.length).length
      · have hkD : (D₁.take as.length).length - 1 - m < keys.length := by omega
        have := (hS' m keys[_] (List.getElem?_eq_getElem hkD) hm y).1 hy
        have h2 := (hkeys _ _ (List.getElem?_eq_getElem hkD)).2.1 y this
        rwa [show (D₁.take as.length).length - 1 - ((D₁.take as.length).length - 1 - m) = m by
          omega] at h2
      · exfalso
        have hout := hTK.outer (m - (D₁.take as.length).length)
        rw [show m - (D₁.take as.length).length + (D₁.take as.length).length = m by omega] at hout
        rw [hout.2] at hy
        exact hy
  obtain ⟨keys₀, S₀, hTK₁, hTK₂, -, -⟩ := keysOf ((List.range as.length).map fun _ => [])
    (by simp) (fun m hm y hy => by simp at hy)
  refine ⟨(tele_sound_step henv hΔ hpi₂ hsub₁ hj hj₂ hTK₁ hTK₂).1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨G, hGl, hGS, hG⟩ := Obs.compact_all (hcl₁ _ hj) (τs := [x])
      (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hx)
    obtain ⟨keys, S', hTK₁, hTK₂, hGS', hSx⟩ := keysOf G hGl hGS
    have hx' : Obs' (VExpr.argSubst as) S' D₁[as.length] x :=
      hG S' hGS' x (List.mem_singleton_self _)
    obtain ⟨x', hx', l⟩ := (tele_sound_step henv hΔ hpi₂ hsub₁ hj hj₂ hTK₁ hTK₂).2 _ hx'
    exact ⟨x', hx'.mono fun m y hy => hSx m y hy, l⟩
  · obtain ⟨G, hGl, hGS, hG⟩ := Obs.compact_all (hcl₂ _ hj₂) (τs := [x])
      (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hx)
    obtain ⟨keys, S', hTK₁, hTK₂, hGS', hSx⟩ := keysOf G hGl hGS
    have hx' : Obs' (VExpr.argSubst as) S' D₂[as.length] x :=
      hG S' hGS' x (List.mem_singleton_self _)
    obtain ⟨x', hx', l⟩ := (tele_sound_step henv hΔ hpi₁ hsub₂ hj₂ hj hTK₂ hTK₁).2 _ hx'
    exact ⟨x', hx'.mono fun m y hy => hSx m y hy, l⟩

end

end Model
end VEnv
end Lean4Lean
