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

theorem LR2.Adequate.bot (ha : a.HasType .type) : Adequate Γ₀ Γ ρ M N A .bot a :=
  ⟨fun _ _ _ => ⟨(LR2 _).bot ha, (LR2 _).bot ha⟩, fun _ _ => (LR2 _).bot ha⟩

theorem LR2.Adequate.fits
    (H : ρ.Fits Γ₀ Γ → Adequate Γ₀ Γ ρ M N A m a) : Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.fits).1 W, fun _ W => (H W.fits).2 W⟩

theorem LR2.Adequate.refl
    (H : ∀ {{σ σ'}}, LR2.SubstWF Γ₀ σ σ' Γ ρ →
      (LR2 Γ₀).Val2 (M.subst σ) (M.subst σ') (A.subst σ) m a) :
    Adequate Γ₀ Γ ρ M M A m a := ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

theorem LR2.Adequate.left : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => .refl fun _ _ W => (h1 W).1

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
    (W : SubstWF Γ₀ σ σ' Γ ρ) : SubstWF Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p) := by
  refine W.cons ⟨hx, fun _ a' ha' => ?_⟩
  have ha' := LE_Interp.weak_iff.mp ha'
  refine ⟨fun ht => ?_, fun m' hm' ht => ?_⟩
  · refine ⟨u, ht, HA.hasType.1.subst W.toSubstEq, (ha'.subst_nil W).1, (ha'.subst_nil W).2, ?_⟩
    have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.fits).2 ha'
    refine (ValTy2.lift le_n ht).1 <| (LR2 Γ₀).mono_r_2_ty le_a
      (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 ht)
      (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType ?_
    exact (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
      (.mono_r hSort.le_sort .sort hmem') .sort ((ihA hA' hSort hmem').1 W).1
  · have ⟨k', le_n, le_k, hle⟩ := LE_Interp.bvar_iff.mp hm'
    have ht' := (Shape.HasType.lift le_n).2 ht
    have hp' := (Shape.HasType.lift le_k).2 hp
    have hta₁ := Shape.lift_type ▸ (Shape.HasType.lift le_k).2 hp.isType
    have hta' := Shape.lift_type ▸ (Shape.HasType.lift le_n).2 ht.isType
    have hc := ((LE_Interp.lift le_k).2 hA₁).compat ((LE_Interp.lift le_n).2 ha')
    have hj := Shape.Join.mk hc
    have ⟨hj1, hj2⟩ := (hj _).1 .rfl
    have hJ := hta₁.join hj hta'
    have hJ' := hJ.mono_r hj1 hp'
    refine (Val2.lift le_n ht).1 <|
      (LR2 Γ₀).mono_r_2 hj2 ht' hJ <|
      (LR2 Γ₀).mono_l hle (.mono_r hj2 hJ ht') hJ' <|
      (LR2 Γ₀).mono_r_1 hj1 hp' hJ' ?_ <| (Val2.lift le_k hp).2 hv
    have valTyA {nd : Nat} {a : Shape nd} (hA : LE_Interp ρ a A) (ha : a.HasType .type) :
        (LR2 Γ₀).ValTy2 (A.subst σ) (A.subst σ) a :=
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.left.fits).2 hA
      have v2 := ((ihA hA' hSort hmem').2 W.left)
      have vt := (LR2 Γ₀).left_ty <| (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
        (.mono_r hSort.le_sort .sort hmem') .sort v2
      (ValTy2.lift le_n ha).1 <| (LR2 Γ₀).mono_r_2_ty le_a
        (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 ha)
        (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType vt
    refine (LR2 Γ₀).join_ty hc hta₁ hta' ?_ ?_
    · exact (ValTy2.lift le_k hp.isType).2 (valTyA hA₁ hp.isType)
    · exact (ValTy2.lift le_n ht.isType).2 (valTyA ha' ht.isType)

/-- Extract `ValTy2` from a `Val2` at sort type, lifting through `InterpTyped` shape data.
Corresponds to Agda's `EqVal2-U-to-EqValTy2` composed with the shape lifting chain. -/
theorem LR2.toValTy (le_n : n ≤ n') (le_a : b.lift (n := n) (m := n') ≤ m)
    (ht : b.HasType .type) (hSort : LE_Interp ρ a (.sort u)) (hmem' : m.HasType a)
    (H : (LR2 Γ₀).Val2 M N (.sort u) m a) :
    (LR2 Γ₀).ValTy2 M N b := by
  refine (LR2.ValTy2.lift le_n ht).1 ?_
  refine (LR2 Γ₀).mono_r_2_ty le_a
    (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 ht)
    (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType ?_
  exact (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
    (.mono_r hSort.le_sort .sort hmem') .sort H

/-- Combined adequacy theorem: proves all three parts simultaneously.
Merges Agda's adequacySub2, adequacyEqSub2, and adequacyConvSub2. -/
theorem LR2.adequacy (H : Γ ⊢ M ≡ N : A)
    (hM : LE_Interp (n := n) ρ m M) (hA : LE_Interp ρ a A) (hmem : m.HasType a) :
    Adequate Γ₀ Γ ρ M N A m a := by
  replace H := H.strong; induction H generalizing ρ n m a with
  | bvar h => exact .refl fun _ _ W => ((W h).2 a hA).2 hM hmem
  | symm H ih => exact .fits fun W => (ih ((LE_Interp.sound H.defeq W).1.2 hM) hA hmem).symm
  | trans _ H1 H2 ihA ih1 ih2 =>
    exact .fits fun W => (ih1 hM hA hmem).trans (ih2 ((LE_Interp.sound H1.defeq W).1.1 hM) hA hmem)
  | @sort _ l =>
    suffices (LR2 Γ₀).Val2 (.sort l) (.sort l) (.sort l.succ) m a from
      ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
    cases hmem.unfold with
    | bot hm =>
      cases hm.unfold with
      | forallE => let .sort h := hA; simp [Shape.LE.def] at h
      | _ => cases n <;> trivial
    | sort => cases n <;> trivial
    | _ => let .sort h := hM; simp [Shape.LE.def] at h
  | const => cases hM; exact .bot hmem.isType
  | @appDF Γ A u B v F F' X X' pat HA HB Hf Ha HBa ihA ihB ihf iha ihBa =>
    cases hM with | bot => exact .bot hmem.isType | @app _ _ f _ x _ _ hif hia le_m
    suffices ∀ {F F' X X' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        Γ ⊢ F ≡ F' : A.forallE B → Γ ⊢ X ≡ X' : A → Γ ⊢ B.inst X ≡ B.inst X' : .sort v →
        LE_Interp ρ f F → LE_Interp ρ x X → LE_Interp ρ a (B.inst X) →
        (∀ {n'} {mf af : Shape n'}, LE_Interp ρ mf F → LE_Interp ρ af (.forallE A B) →
          mf.HasType af → Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af) →
        (∀ {n'} {ma aa : Shape n'}, LE_Interp ρ ma X → LE_Interp ρ aa A →
          ma.HasType aa → Adequate Γ₀ Γ ρ X X' A ma aa) →
        (∀ {n'} {mb av : Shape n'}, LE_Interp ρ mb (B.inst X) → LE_Interp ρ av (.sort v) →
          mb.HasType av → Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) →
        (LR2 Γ₀).Val2 (.subst (.app F X) σ) (.subst (.app F' X') σ')
          (.subst (B.inst X) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => this W Hf.defeq Ha.defeq HBa.defeq hif hia hA ihf iha ihBa⟩
      · exact this W Hf.defeq.hasType.1 Ha.defeq.hasType.1 HBa.defeq.hasType.1 hif hia hA
          (fun hf hPi hmf => (ihf hf hPi hmf).left)
          (fun ha hA hma => (iha ha hA hma).left)
          (fun hB hv hmb => (ihBa hB hv hmb).left)
      · refine (LR2 _).conv ((LR2 _).symm_ty ?_) <| this W
          Hf.defeq.hasType.2 Ha.defeq.hasType.2 HBa.defeq.hasType.2
          ((LE_Interp.sound Hf.defeq W.fits).1.1 hif) ((LE_Interp.sound Ha.defeq W.fits).1.1 hia)
          ((LE_Interp.sound HBa.defeq W.fits).1.1 hA)
          (fun hf hPi hmf => ?_) (fun ha hA hma => ?_) (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBa.defeq W.fits).2 hA
          exact toValTy le le' hmem.isType iv hmb ((ihBa iB iv hmb).2 W.left)
        · exact (ihf ((LE_Interp.sound Hf.defeq W.left.fits).1.2 hf) hPi hmf).symm.left
        · exact (iha ((LE_Interp.sound Ha.defeq W.left.fits).1.2 ha) hA hma).symm.left
        · exact (ihBa ((LE_Interp.sound HBa.defeq W.left.fits).1.2 hB) hv hmb).symm.left
    intro F F' X X' σ σ' W hF hX hBa hif hia hA ihf iha ihBa
    have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ := (LE_Interp.sound hF W.left.fits).2 hif
    have Af := ihf hf' hPi hmf
    by_cases hm0 : mf = .bot
    · subst hm0; cases (Shape.lift_le_bot le_nf).1 le_mf
      cases Shape.le_bot.1 (Shape.bot_app ▸ le_m)
      exact (LR2 _).bot hmem.isType
    cases hPi with | bot => cases hm0 hmf.bot_r | forallE haA hbA hd hiB le
    cases hmf.unfold with simp [Shape.LE.def] at le | bot => cases hm0 rfl | lam hg
    simp at le_nf
    have hA := (LE_Interp.lift le_nf).2 hA
    have ⟨_, le_x', hx'_a₁, hgx2⟩ := hg.2.1 x.lift
    have hia' := LE_Interp.mono le_x' ((LE_Interp.lift le_nf).2 hia)
    have hax' := (LE_Interp.forallE haA hbA hd hiB (Shape.LE.def.2 le)).forallE_inv.2 hia'
    have hJ := Shape.Join.mk (hA.compat hax')
    have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
    have hgx' := hg.2.2 _ hx'_a₁
    have hJ_t := (Shape.lift_type ▸ (Shape.HasType.lift le_nf).2 hmem.isType).join hJ hgx'.isType
    have hmem_k := (Shape.HasType.lift le_nf).2 hmem
    rw [subst_inst]
    refine (LR2.Val2.lift le_nf hmem).1 <| (LR2 Γ₀).mono_r_2 hJ1 hmem_k hJ_t.toType ?_
    refine (LR2 Γ₀).mono_l ?_ (.mono_r hJ1 hJ_t hmem_k) (.mono_r hJ2 hJ_t hgx') ?_
    · exact (Shape.lift_mono le_m).trans
        (.trans (Shape.lift_app ▸ Shape.app_mono_l le_mf _) hgx2)
    refine (LR2 Γ₀).mono_r_1 hJ2 hgx' (.mono_r hJ2 hJ_t hgx') ?_ ?_
    · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
        (LE_Interp.sound hBa W.left.fits).2 (hA.join hJ hax')
      exact (LR2 Γ₀).left_ty <| subst_inst ▸
        toValTy le_j le_j' hJ_t hSj hmj ((ihBa hBj hSj hmj).2 W.left)
    · obtain ⟨_, _, _, _, red, _, _, _, _, valPi⟩ := (LR2 _).trans (Af.2 W.left) (Af.1 W).2
      cases WHNF.forallE.whRedS red
      have Aa := iha hia' (.mono le.1 haA) hx'_a₁
      have va_cross := (LR2 _).trans (Aa.2 W.left) (Aa.1 W).2
      exact (LR2 _).trans
        (valPi.2 hx'_a₁ (hX.subst W.toSubstEq).hasType.1 ((LR2 _).left va_cross))
        (valPi.1 hx'_a₁ (hX.subst W.toSubstEq) va_cross).2
  | @lamDF Γ A A' u B v body body' HA HB HBody ihA ihB ihBody =>
    suffices ∀ {X Y X' Y' σ σ'},
        LE_Interp ρ m (.lam X Y) → SubstWF Γ₀ σ σ' Γ ρ →
        (∀ {k np} {p : Shape np} {mb ab : Shape k},
          (ρ.push p).Fits Γ₀ (A :: Γ) →
          LE_Interp (ρ.push p) mb Y → LE_Interp (ρ.push p) ab B → mb.HasType ab →
          Adequate Γ₀ (A :: Γ) (ρ.push p) Y Y' B mb ab) →
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
    have cons := Adequate.cons ihA HA.defeq
    cases hmem.unfold with | bot => trivial | lam htm
    refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl, hTypA, ?_, hTypB, ?_, ?_⟩
    · exact (LR2 Γ₀).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
        ((ihA hA' hSort hmem').2 W.left)
    · simp [LR2S.PiEdge2, inst_lift_cons]
      refine have := ?_; ⟨this, fun _ _ hp ha hv => this hp ha hv⟩
      intro x x' p hp ha hv
      have W' := cons hp hA1 ha hv W.left
      have ⟨n', ab, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.sound HB.defeq W'.fits).2 (hA.forallE_inv'.2 p)
      exact toValTy le le' (aty.2 _ hp) iv hmb ((ihB iB iv hmb).1 W').1
    have beta {X Y t : SExpr} {σ} : Γ₀ ⊢ .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
        Y.subst (σ.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    all_goals
      rw [inst_lift_cons]
      have hBb_sd := hA.forallE_inv'.2 p
      replace IH W := IH W ((hTerm.lam_inv htm.2.1).2 hp) hBb_sd (htm.2.2 p hp)
    · have W' := cons hp hA1 ha hv W.left
      constructor
      · exact ((LR2 Γ₀).whr beta beta).2 <| ((IH W'.fits).1 W').1
      · have vtAA' := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        have ha' : Γ₀ ⊢ x ≡ x' : A.subst σ' := (HA.defeq.hasType.1.subst W.toSubstEq).defeqDF ha
        have hv' := (LR2 Γ₀).conv vtAA' hv
        have ⟨n', _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HB.defeq W'.fits).2 hBb_sd
        have W2 := cons hp hA1 ha.hasType.1 ((LR2 Γ₀).left hv) W
        have vtBB := toValTy le le' (aty.2 _ hp) iv hmb ((ihB iB iv hmb).1 W2).1
        refine ((LR2 Γ₀).whr beta beta).2 <| (LR2 Γ₀).conv ((LR2 Γ₀).symm_ty vtBB) ?_
        exact ((IH W'.fits).1 (cons hp hA1 ha' hv' W.symm.left)).2
    · have W' := cons hp hA1 ha hv W
      exact ((LR2 Γ₀).whr beta beta).2 <|
        (LR2 _).trans ((IH W'.fits).2 W'.left) ((IH W'.fits).1 W').2
  | @forallEDF Γ A A' u body body' v HA HBody ihA ihBody =>
    cases hmem.unfold with
    | bot hm =>
      cases hm.unfold with
      | forallE => let .sort h := hA; simp [Shape.LE.def] at h
      | _ => cases n <;> constructor <;> intros <;> trivial
    | sort | lam => (try cases n) <;> cases hM; rename_i h _ _ _; simp [Shape.LE.def] at h
    | @forallE k a₂ a₁ r aty
    have hA1 := hM.forallE_inv.1
    have cons := Adequate.cons ihA HA.defeq
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA.defeq W.left.fits).2 hA1
      have HAAσ := HA.defeq.subst W.left.toSubstEq
      have S' := W.toSubstEq.lift HAAσ.hasType.1)
    · have HAσ := HA.defeq.hasType.1.subst W.toSubstEq
      have HA'σ := HA.defeq.hasType.2.subst W.toSubstEq
      constructor
      · refine ⟨A.subst σ, body.subst σ.lift, A.subst σ', body.subst σ'.lift, u, v,
          .rfl, .rfl, HAσ, HBody.defeq.hasType.1.subst S', ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        simp [LR2S.PiEdge2, inst_lift_cons]
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;>
          have hB := hM.forallE_inv'.2 p <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR2 Γ₀).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha.hasType.1 ((LR2 Γ₀).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBody.defeq W'.fits).2 hB
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').1
      · refine ⟨A'.subst σ, body'.subst σ.lift, A'.subst σ', body'.subst σ'.lift, u, v,
          .rfl, .rfl, HA'σ, HAAσ.defeqDF_l (HBody.defeq.hasType.2.subst S'), ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).2
        simp [LR2S.PiEdge2, inst_lift_cons]
        have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W.left)
        refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
          have hv := (LR2 Γ₀).conv ((LR2 Γ₀).symm_ty this) hv
          have ha := HAAσ.symm.defeqDF ha
          have hB := hM.forallE_inv'.2 p) <;> [constructor <;> [
            have W' := cons hp hA1 ha hv W.left;
            ( have := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
              have W' := cons hp hA1 (HAσ.defeqDF ha) ((LR2 Γ₀).conv this hv) W.symm.left )];
            have W' := cons hp hA1 ha ((LR2 Γ₀).left hv) W] <;>
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBody.defeq W'.fits).2 hB
          exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').2
    · refine ⟨A.subst σ, body.subst σ.lift, A'.subst σ, body'.subst σ.lift, u, v,
        .rfl, .rfl, HAAσ, HBody.defeq.subst S', ?_, ?_⟩
      · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W)
      simp [LR2S.PiEdge2, inst_lift_cons]
      refine ⟨fun _ _ p hp ha hv => ?_, fun _ p hp ha hv => ?_⟩ <;> (
        have hB := hM.forallE_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBody.defeq W'.fits).2 hB)
      · exact ⟨toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').1,
               toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 W').2⟩
      · exact toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).2 W')
  | @defeqDF Γ A' B' u' _ _ Hty He ihTy ihE =>
    have tyConv {σ} (W : SubstWF Γ₀ σ σ Γ ρ) :=
      have hA' := (LE_Interp.sound Hty.defeq W.fits).1.2 hA
      have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ := (LE_Interp.sound Hty.defeq W.fits).2 hA'
      toValTy le_n le_a hmem.isType hSort hmem' ((ihTy hA'' hSort hmem').2 W)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have hA' := (LE_Interp.sound Hty.defeq W.left.fits).1.2 hA
    · exact ⟨(LR2 Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).1,
             (LR2 Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).2⟩
    · exact (LR2 Γ₀).conv (tyConv W) ((ihE hM hA' hmem).2 W)
  | beta He Ha Happ Hinst _ihe _iha ihapp ihinst =>
    refine ⟨fun _ _ W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihapp hM hA hmem).1 W).1
    · exact ((ihinst ((LE_Interp.sound (.beta He.defeq Ha.defeq) W.fits).1.1 hM) hA hmem).1 W).2
    · exact ((LR2 _).whr .rfl (subst_inst ▸ .tail .rfl .beta)).1 ((ihapp hM hA hmem).2 W)
  | eta He Hlam ihe ihlam =>
    -- M = .lam A (.app e.lift (.bvar 0)), N = e, type = .forallE A B
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihlam hM hA hmem).1 W).1
    · exact ((ihe ((LE_Interp.sound (.eta He.defeq) W.fits).1.1 hM) hA hmem).1 W).2
    sorry -- eq direction: funext argument
  | proofIrrel Hp =>
    refine .fits fun W => ?_
    have ⟨_, _, s, le_n, le_a, _, hSort, hmem'⟩ := (LE_Interp.sound (Γ₀ := Γ₀) Hp.defeq W).2 hA
    have hS := Shape.HasType.mono_r hSort.le_sort .sort hmem'; simp at hS
    have ha' := hS.mono_r le_a ((Shape.HasType.lift le_n).2 hmem)
    cases (Shape.lift_eq_bot le_n).1 (hS.proofIrrel ha')
    exact .bot hmem.isType
  | extra h1 h2 Hl Hr ihl ihr =>
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihl hM hA hmem).1 W).1
    · exact ((ihr ((LE_Interp.sound (.extra h1 h2) W.fits).1.1 hM) hA hmem).1 W).2
    sorry

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
