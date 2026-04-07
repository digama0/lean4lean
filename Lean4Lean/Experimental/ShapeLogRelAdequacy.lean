import Lean4Lean.Experimental.ShapeLogRel

-- example : Unit := sorry set_option warn.sorry false -- so I don't forget

namespace Lean4Lean

namespace SExpr
variable [Params]

def LR2.Adequate (Γ₀ Γ : List SExpr) (ρ : Valuation) (M N A : SExpr) (m a : Shape n) :=
  (∀ {{σ σ'}}, LR2.SubstWF Γ₀ σ σ' Γ ρ →
    (LR2 Γ₀).Val2 (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    (LR2 Γ₀).Val2 (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}}, LR2.SubstWF Γ₀ σ σ Γ ρ → (LR2 Γ₀).Val2 (M.subst σ) (N.subst σ) (A.subst σ) m a

theorem LR2.Adequate.left : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => ⟨fun _ _ W => ⟨(h1 W).1, (h1 W).1⟩, fun _ W => (LR2 _).symm (h1 W).1⟩

theorem LR2.Adequate.symm : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ N M A m a
  | ⟨h1, h2⟩ => ⟨fun _ _ W => (h1 W).symm, fun _ W => (LR2 _).symm (h2 W)⟩

theorem LR2.Adequate.trans :
    Adequate Γ₀ Γ ρ M₁ M₂ A m a → Adequate Γ₀ Γ ρ M₂ M₃ A m a → Adequate Γ₀ Γ ρ M₁ M₃ A m a
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    ⟨fun _ _ W => ⟨(a1 W).1, (b1 W).2⟩, fun _ W => (LR2 _).trans (a2 W) (b2 W)⟩

theorem LR2.Adequate.cons
    (ihA : ∀ {ρ n} {m a : Shape n}, LE_Interp ρ m A → LE_Interp ρ a (.sort u) →
      m.HasType a → Adequate Γ₀ Γ ρ A A' (sort u) m a)
    (HA : Γ ⊢ A ≡ A' : .sort u)
    {{k : Nat}} {{a₁ p : Shape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁ A)
    (hx : Γ₀ ⊢ x ≡ x' : A.subst σ) (hv : (LR2 Γ₀).Val2 x x' (A.subst σ) p a₁)
    (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) : SubstWF Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p) := by
  have valTyA {nd : Nat} {ad : Shape nd} (hAd : LE_Interp ρ ad A)
      (hAd_type : ad.HasType .type) (W₀ : LR2.SubstWF Γ₀ σ σ Γ ρ) :
      (LR2 Γ₀).ValTy2 (A.subst σ) (A.subst σ) ad := by
    have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W₀.fits).2 hAd
    have v2 := ((ihA hA' hSort hmem').2 W₀)
    have vt := (LR2 Γ₀).left_ty <| (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
      (.mono_r hSort.le_sort .sort hmem') ((LR2 Γ₀).toType (LR2 Γ₀).sort) v2
    exact (LR2.ValTy2.lift le_n hAd_type).1 <| (LR2 Γ₀).mono_r_2_ty le_a
      (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 hAd_type)
      (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType vt
  refine W.cons ⟨hx, fun _ a' ha' => ?_⟩
  · have ha'_ρ := LE_Interp.weak_iff.mp ha'
    refine ⟨fun ht => ?_, fun m' hm' ht => ?_⟩
    · have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.fits).2 ha'_ρ
      have v2 := ((ihA hA' hSort hmem').1 W).1
      have vt := (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
        (.mono_r hSort.le_sort .sort hmem') ((LR2 Γ₀).toType (LR2 Γ₀).sort) v2
      refine ⟨u, ht, HA.hasType.1.subst W.toSubstEq,
        (ha'_ρ.subst_nil W).1, (ha'_ρ.subst_nil W).2, ?_⟩
      exact (LR2.ValTy2.lift le_n ht).1 <| (LR2 Γ₀).mono_r_2_ty le_a
        (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 ht)
        (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType vt
    · have ⟨k', le_n, le_k, hle⟩ := LE_Interp.bvar_iff.mp hm'
      have ht' := (Shape.HasType.lift le_n).2 ht
      have hp' := (Shape.HasType.lift le_k).2 hp
      have a₁_type := Shape.lift_type ▸ (Shape.HasType.lift le_k).2 hp.isType
      have a'_type := Shape.lift_type ▸ (Shape.HasType.lift le_n).2 ht.isType
      have hc := ((LE_Interp.lift le_k).2 hA₁).compat ((LE_Interp.lift le_n).2 ha'_ρ)
      have hj := Shape.Join.mk hc
      have ⟨le_a₁_j, le_a'_j⟩ := (hj _).1 .rfl
      have j_type := a₁_type.join hj a'_type
      have vtJ := (LR2 Γ₀).join_ty hc a₁_type a'_type
        ((LR2.ValTy2.lift le_k hp.isType).2 (valTyA hA₁ hp.isType W.left))
        ((LR2.ValTy2.lift le_n ht.isType).2 (valTyA ha'_ρ ht.isType W.left))
      have hp_j := j_type.mono_r le_a₁_j hp'
      exact (LR2.Val2.lift le_n ht).1 <|
        (LR2 Γ₀).mono_r_2 le_a'_j ht' j_type <|
        (LR2 Γ₀).mono_l hle (.mono_r le_a'_j j_type ht') hp_j <|
        (LR2 Γ₀).mono_r_1 le_a₁_j hp' hp_j vtJ <|
        (LR2.Val2.lift le_k hp).2 hv

/-- Combined adequacy theorem: proves all three parts simultaneously.
Merges Agda's adequacySub2, adequacyEqSub2, and adequacyConvSub2. -/
theorem LR2.adequacy (H : Γ ⊢ M ≡ N : A)
    (hM : LE_Interp (n := n) ρ m M) (hA : LE_Interp ρ a A) (hmem : m.HasType a) :
    Adequate Γ₀ Γ ρ M N A m a := by
  replace H := H.strong; induction H generalizing ρ n m a with
  | bvar h =>
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩
    · exact and_self_iff.2 (((W h).2 a hA).2 hM hmem)
    · exact (LR2 Γ₀).left (((W h).2 a hA).2 hM hmem)
  | symm H ih =>
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have hN := (LE_Interp.sound H.defeq W.fits).1.2 hM
    · exact ((ih hN hA hmem).1 W).symm
    · exact (LR2 Γ₀).symm ((ih hN hA hmem).2 W)
  | trans _ H1 H2 ihA ih1 ih2 =>
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have he₂ := (LE_Interp.sound H1.defeq W.fits).1.1 hM
    · exact ⟨((ih1 hM hA hmem).1 W).1, ((ih2 he₂ hA hmem).1 W).2⟩
    · exact (LR2 Γ₀).trans ((ih1 hM hA hmem).2 W) ((ih2 he₂ hA hmem).2 W)
  | sort => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩
  | const => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩
  | appDF => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩
  | @lamDF Γ A A' u B v body body' HA HB HBody ihA ihB ihBody =>
    suffices ∀ {X Y X' Y' σ σ'},
        LE_Interp ρ m (.lam X Y) → LR2.SubstWF Γ₀ σ σ' Γ ρ →
        (∀ {k np} {p : Shape np} {mb ab : Shape k},
          (ρ.push p).Fits Γ₀ (A :: Γ) →
          LE_Interp (ρ.push p) mb Y → LE_Interp (ρ.push p) ab B → mb.HasType ab →
          LR2.Adequate Γ₀ (A :: Γ) (ρ.push p) Y Y' B mb ab) →
        (LR2 Γ₀).Val2 (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a from
      ⟨fun σ σ' W => ⟨
        this hM W fun _ hMb hBb hmb => (ihBody hMb hBb hmb).left,
        this ((LE_Interp.sound (.lamDF HA.defeq HBody.defeq) W.fits).1.1 hM) W fun W hMb' hBb hmb =>
          (ihBody ((LE_Interp.sound HBody.defeq W).1.2 hMb') hBb hmb).symm.left⟩,
      fun σ W => this hM W fun _ => ihBody⟩
    intro X Y X' Y' σ σ' hTerm W IH
    suffices ∀ n' b (f : ShapeFun _), n = n' + 1 → a ≍ (.forallE b f : Shape (n'+1)) →
        (LR2 Γ₀).Val2 (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      cases hmem.unfold with
      | bot hm =>
        cases hm.unfold with
        | forallE => exact this _ _ _ rfl .rfl
        | _ => cases n <;> trivial
      | sort | forallE => (try cases n) <;> cases hTerm; rename_i h _ _; simp [Shape.LE.def] at h
      | lam => exact this _ _ _ rfl .rfl
    rintro k a₁ a₂ rfl ⟨⟩
    have .forallE aty := hmem.isType.unfold
    have ⟨v, hBsort⟩ := HBody.defeq.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      HA.defeq.hasType.1.subst W.left.toSubstEq
    have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      hBsort.subst (W.left.toSubstEq.lift hTypA)
    have hA1 := hA.forallE_inv.1
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA.defeq W.left.fits).2 hA1
    have cons := LR2.Adequate.cons ihA HA.defeq
    refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl, hTypA, ?_, hTypB, ?_, ?_⟩
    · refine (LR2.ValTy2.lift le_n aty.1.isType).1 <| (LR2 Γ₀).mono_r_2_ty le_a
        (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 aty.1.isType)
        (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType ?_
      exact (LR2 Γ₀).left_ty <| (LR2 Γ₀).toType <|
      (LR2 Γ₀).mono_r_1 hSort.le_sort hmem' (.mono_r hSort.le_sort .sort hmem')
        ((LR2 Γ₀).toType (LR2 Γ₀).sort) ((ihA hA' hSort hmem').2 W.left)
    · simp [LR2S.PiEdge2, inst_lift_cons]
      refine have := ?_; ⟨this, fun _ _ hp ha hv => this hp ha hv⟩
      intro x x' p hp ha hv
      have ⟨n', ab, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.sound HB.defeq (cons hp hA1 ha hv W).fits).2 (hA.forallE_inv.2 _ hp)
      have ρ_le : (ρ.push p).LE (ρ.push (n := n') p.lift) :=
        (Valuation.LE.push' le (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ .rfl⟩
      have iB' := iB.mono_l ρ_le
      have iv' := iv.mono_l ρ_le
      refine (LR2.ValTy2.lift le (aty.2 _ hp)).1 <| (LR2 Γ₀).mono_r_2_ty le'
        (Shape.lift_type ▸ (Shape.HasType.lift le).2 (aty.2 _ hp))
        (Shape.HasType.mono_r iv.le_sort .sort hmb).toType ?_
      exact (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 iv'.le_sort hmb
        (.mono_r iv'.le_sort .sort hmb) ((LR2 Γ₀).toType (LR2 Γ₀).sort)
        ((ihB iB' iv' hmb).1 (cons ((Shape.HasType.lift le).2 hp) ((LE_Interp.lift le).2 hA1)
        ha ((Val2.lift le hp).2 hv) W.left) |>.1)
    cases hmem.unfold with | bot => trivial | lam htm
    have beta {X Y t : SExpr} {σ} : Γ₀ ⊢ .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
        Y.subst (σ.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    all_goals
      rw [inst_lift_cons]
      have hBb_sd := hA.forallE_inv.2 _ hp
      replace IH W := IH W ((hTerm.lam_inv htm.2.1).2 _ hp) hBb_sd (htm.2.2 p hp)
    · have W' := cons hp hA1 ha hv W.left
      constructor
      · exact ((LR2 Γ₀).whr beta beta).2 <| ((IH W'.fits).1 W').1
      · have vtAA' : (LR2 Γ₀).ValTy2 (A.subst σ) (A.subst σ') a₁ := by
          refine (LR2.ValTy2.lift le_n aty.1.isType).1 ?_
          refine (LR2 Γ₀).mono_r_2_ty le_a
            (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 aty.1.isType)
            (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType ?_
          exact (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
            (.mono_r hSort.le_sort .sort hmem') ((LR2 Γ₀).toType (LR2 Γ₀).sort)
            ((ihA hA' hSort hmem').1 W |>.1)
        have ha' : Γ₀ ⊢ x ≡ x' : A.subst σ' := (HA.defeq.hasType.1.subst W.toSubstEq).defeqDF ha
        have hv' := (LR2 Γ₀).conv vtAA' hv
        have ⟨n', _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HB.defeq W'.fits).2 hBb_sd
        have ρ_le : (ρ.push p).LE (ρ.push (n := n') p.lift) :=
          (Valuation.LE.push' le (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ .rfl⟩
        have iB' := iB.mono_l ρ_le
        have iv' := iv.mono_l ρ_le
        have vtBB : (LR2 Γ₀).ValTy2 (B.subst (σ.cons x)) (B.subst (σ'.cons x)) (a₂.app p) := by
          refine (LR2.ValTy2.lift le (aty.2 _ hp)).1 ?_
          refine (LR2 Γ₀).mono_r_2_ty le'
            (Shape.lift_type ▸ (Shape.HasType.lift le).2 (aty.2 _ hp))
            (Shape.HasType.mono_r (iv.mono_l ρ_le).le_sort .sort hmb).toType ?_
          refine (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 iv'.le_sort hmb
            (.mono_r iv'.le_sort .sort hmb) ((LR2 Γ₀).toType (LR2 Γ₀).sort)
            ((ihB iB' iv' hmb).1 ?_ |>.1)
          exact cons ((Shape.HasType.lift le).2 hp)
            ((LE_Interp.lift le).2 hA1) (ha.hasType.1)
            ((Val2.lift le hp).2 ((LR2 Γ₀).left hv)) W
        refine ((LR2 Γ₀).whr beta beta).2 <| (LR2 Γ₀).conv ((LR2 Γ₀).symm_ty vtBB) ?_
        exact ((IH W'.fits).1 (cons hp hA1 ha' hv' W.symm.left)).2
    · have W' := cons hp hA1 ha hv W
      exact ((LR2 Γ₀).whr beta beta).2 <|
        (LR2 _).trans ((IH W'.fits).2 W'.left) ((IH W'.fits).1 W').2
  | forallEDF => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩
  | @defeqDF Γ A' B' u' _ _ Hty He ihTy ihE =>
    -- Hty : A' ≡ B' : .sort u',  He : e1 ≡ e2 : A'
    -- goal: three-part result at type B'
    -- hA : LE_Interp ρ a B', convert to A' via type equality
    have tyConv : ∀ {{σ}}, LR2.SubstWF Γ₀ σ σ Γ ρ →
        (LR2 Γ₀).ValTy2 (A'.subst σ) (B'.subst σ) a := by
      intro σ W
      have hA' := (LE_Interp.sound Hty.defeq W.fits).1.2 hA
      have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ :=
        (LE_Interp.sound Hty.defeq W.fits).2 hA'
      have hAB' := (LR2 Γ₀).toType ((LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
          (Shape.HasType.mono_r hSort.le_sort .sort hmem')
          ((LR2 Γ₀).toType (LR2 Γ₀).sort)
          ((ihTy hA'' hSort hmem').2 W))
      exact (LR2.ValTy2.lift le_n hmem.isType).1
        ((LR2 Γ₀).mono_r_2_ty le_a
          (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 hmem.isType)
          (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType hAB')
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩
    · have hA' := (LE_Interp.sound Hty.defeq W.left.fits).1.2 hA
      have hAB := tyConv W.left
      exact ⟨(LR2 Γ₀).conv hAB ((ihE hM hA' hmem).1 W).1,
             (LR2 Γ₀).conv hAB ((ihE hM hA' hmem).1 W).2⟩
    · have hA' := (LE_Interp.sound Hty.defeq W.fits).1.2 hA
      exact (LR2 Γ₀).conv (tyConv W) ((ihE hM hA' hmem).2 W)
  | beta => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩
  | eta => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩
  | proofIrrel => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩
  | extra => exact ⟨fun _ _ _ => ⟨sorry, sorry⟩, fun _ _ => sorry⟩

/-- Wraps the first conjunct of `adequacy` into a full `DefEq` bundle.
From `Val2 (M.subst σ) (M.subst σ') (A.subst σ) m a` we recover the
`HasType`, `IsDefEq`, and `LE_Interp .nil` fields using sorry'd lemmas. -/
theorem LR2.adequacy_defeq (H : Γ ⊢ M ≡ N : A)
    (hM : LE_Interp (n := n) ρ m M) (hA : LE_Interp ρ a A) (hmem : m.HasType a)
    {σ σ'} (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) :
    (LR2 Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a :=
  ⟨hmem, H.hasType.1.subst W.toSubstEq, (hM.subst_nil W).1, (hM.subst_nil W).2, (hA.subst_nil W).1,
    ((LR2.adequacy H hM hA hmem).1 W).1⟩

/-- Wraps the second conjunct of `adequacy` into a full `DefEq` bundle.
From `Val2 (M.subst σ) (N.subst σ) (A.subst σ) m a`. -/
theorem LR2.adequacy_defeq_2 (H : Γ ⊢ M ≡ N : A)
    (hM : LE_Interp (n := n) ρ m M) (hN : LE_Interp ρ m N) (hA : LE_Interp ρ a A)
    (hmem : m.HasType a) {σ} (W : LR2.SubstWF Γ₀ σ σ Γ ρ) :
      (LR2 Γ₀).DefEq (M.subst σ) (N.subst σ) (A.subst σ) m a :=
  ⟨hmem, H.subst W.toSubstEq, (hM.subst_nil W).1, (hN.subst_nil W).1, (hA.subst_nil W).1,
    (LR2.adequacy H hM hA hmem).2 W⟩
