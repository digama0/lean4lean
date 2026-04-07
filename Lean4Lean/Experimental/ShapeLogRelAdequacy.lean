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

theorem LR2.Adequate.bvar0
    (ihA : ∀ {ρ n} {m a : Shape n}, LE_Interp ρ m A → LE_Interp ρ a (.sort u) →
      m.HasType a → Adequate Γ₀ Γ ρ A A' (sort u) m a)
    (HA : Γ ⊢ A ≡ A' : .sort u)
    {{k : Nat}} {{a₁ p : Shape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁ A)
    (hx : Γ₀ ⊢ x ≡ x' : A.subst σ) (hv : (LR2 Γ₀).Val2 x x' (A.subst σ) p a₁)
    (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) :
    LR2.Subst1 Γ₀ x x' A.lift (A.subst σ) (A.subst σ') (ρ.push p) := by
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
  refine ⟨hx, fun _ a' ha' => ?_⟩
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
    -- Context manipulation: call body IH with ρ.push p and W.cons h0.
    -- h0 provides DefEq for variable 0 (the new binding), derived from the ValPi2 input.
    have bodyPair {k np : Nat} {p : Shape np} {mb ab : Shape k}
        {t t' : SExpr} {σ σ' : Subst}
        (hMb : LE_Interp (ρ.push p) mb body)
        (hBb : LE_Interp (ρ.push p) ab B)
        (hmb : mb.HasType ab)
        (W : LR2.SubstWF Γ₀ σ σ' Γ ρ)
        (h0 : LR2.Subst1 Γ₀ t t' A.lift (A.subst σ) (A.subst σ') (ρ.push p)) :
        (LR2 Γ₀).Val2 (n := k) (body.subst (σ.cons t)) (body.subst (σ'.cons t'))
          (B.subst (σ.cons t)) mb ab ∧
        (LR2 Γ₀).Val2 (n := k) (body'.subst (σ.cons t)) (body'.subst (σ'.cons t'))
          (B.subst (σ.cons t)) mb ab := (ihBody hMb hBb hmb).1 (W.cons h0)
    have bodyEq {k np : Nat} {p : Shape np} {mb ab : Shape k}
        {t : SExpr} {σ : Subst}
        (hMb : LE_Interp (ρ.push p) mb body)
        (hBb : LE_Interp (ρ.push p) ab B)
        (hmb : mb.HasType ab)
        (W : LR2.SubstWF Γ₀ σ σ Γ ρ)
        (h0 : LR2.Subst1 Γ₀ t t A.lift (A.subst σ) (A.subst σ) (ρ.push p)) :
        (LR2 Γ₀).Val2 (n := k) (body.subst (σ.cons t)) (body'.subst (σ.cons t))
          (B.subst (σ.cons t)) mb ab := (ihBody hMb hBb hmb).2 (W.cons h0)
    -- Domain type validity via ihA
    -- Mirrors DefEq.toType: adjust type-shape from ad to .sort, then extract ValTy2
    have domTyEq {nd : Nat} {md ad : Shape nd} {σ : Subst}
        (hAd : LE_Interp ρ md A) (hSd : LE_Interp (n := nd) ρ ad (.sort u)) (hmd : md.HasType ad)
        (W : LR2.SubstWF Γ₀ σ σ Γ ρ) :
        (LR2 Γ₀).ValTy2 (A.subst σ) (A'.subst σ) md :=
      (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSd.le_sort hmd
        (.mono_r hSd.le_sort .sort hmd) ((LR2 Γ₀).toType (LR2 Γ₀).sort) ((ihA hAd hSd hmd).2 W)
    -- LE_Interp extraction lemmas for lambda/forallE shapes (sorry'd — need shape theory)
    -- From LE_Interp at .forallE: extract domain interpretation
    have forallE_dom_interp {k : Nat} {a₁ : Shape k} {a₂ : ShapeFun k} {X Y : SExpr}
        (hFE : LE_Interp (n := k+1) ρ (.forallE a₁ a₂) (.forallE X Y)) :
        LE_Interp ρ a₁ X := hFE.forallE_inv.1
    -- From LE_Interp at .lam: given p.HasType a₁, extract body interpretation
    have lam_body_interp {k : Nat} {f : ShapeFun k} {a₁ : Shape k} {a₂ : ShapeFun k}
        {p : Shape k} {X Y : SExpr}
        (hLam : LE_Interp (n := k+1) ρ (.lam f) (.lam X Y))
        (htm : Shape.HasTypeLam f a₁ a₂) (hp : p.HasType a₁) :
        LE_Interp (ρ.push p) (ShapeFun.app f p) Y := (hLam.lam_inv htm.2.1).2 _ hp
    -- From LE_Interp at .forallE: given p.HasType a₁, extract codomain interpretation
    have forallE_body_interp {k : Nat} {a₁ : Shape k} {a₂ : ShapeFun k} {p : Shape k}
        (hFE : LE_Interp (n := k+1) ρ (.forallE a₁ a₂) (.forallE A B))
        (hp : p.HasType a₁) :
        LE_Interp (ρ.push p) (ShapeFun.app a₂ p) B := hFE.forallE_inv.2 _ hp
    -- From Val2 input + bvar/lift interpretation: derive DefEq at variable 0
    -- (Agda: transportVal2 — uses downVal2/restrictVal2 to go from (p,a₁) to (m',a'))
    have bvar0 := LR2.Adequate.bvar0 ihA HA.defeq
    -- Mirrors domTyEq but uses ihB (IH for A::Γ ⊢ B : .sort v) with extended SubstWF.
    have codomTyPair {k np : Nat} {mb ab : Shape k} {p : Shape np} {a₁ : Shape np}
        {x x' : SExpr} {σ : Subst}
        (hBb : LE_Interp (ρ.push p) mb B) (hSb : LE_Interp (ρ.push p) ab (.sort v))
        (hmb : mb.HasType ab)
        (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁ A)
        (hx : Γ₀ ⊢ x ≡ x' : A.subst σ)
        (hv : (LR2 Γ₀).Val2 x x' (A.subst σ) p a₁)
        (W : LR2.SubstWF Γ₀ σ σ Γ ρ) :
        (LR2 Γ₀).ValTy2 (B.subst (σ.cons x)) (B.subst (σ.cons x')) mb :=
      (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSb.le_sort hmb
        (.mono_r hSb.le_sort .sort hmb) ((LR2 Γ₀).toType (LR2 Γ₀).sort)
        ((ihB hBb hSb hmb).1 (W.cons (bvar0 hp hA₁ hx hv W)) |>.1)
    have codomTyEq {k np : Nat} {mb ab : Shape k} {p : Shape np} {a₁ : Shape np}
        {x : SExpr} {σ : Subst}
        (hBb : LE_Interp (ρ.push p) mb B) (hSb : LE_Interp (ρ.push p) ab (.sort v))
        (hmb : mb.HasType ab)
        (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁ A)
        (hx : Γ₀ ⊢ x : A.subst σ)
        (hv : (LR2 Γ₀).Val2 x x (A.subst σ) p a₁)
        (W : LR2.SubstWF Γ₀ σ σ Γ ρ) :
        (LR2 Γ₀).ValTy2 (B.subst (σ.cons x)) (B.subst (σ.cons x)) mb :=
      (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSb.le_sort hmb
        (.mono_r hSb.le_sort .sort hmb) ((LR2 Γ₀).toType (LR2 Γ₀).sort)
        ((ihB hBb hSb hmb).2 (W.cons (bvar0 hp hA₁ hx hv W)))
    -- Codomain type validity across substitutions: σ.cons x vs σ'.cons x
    have codomTySubstDir {k np : Nat} {mb ab : Shape k} {p : Shape np} {a₁ : Shape np}
        {x : SExpr} {σ σ' : Subst}
        (hBb : LE_Interp (ρ.push p) mb B) (hSb : LE_Interp (ρ.push p) ab (.sort v))
        (hmb : mb.HasType ab)
        (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁ A)
        (hx : Γ₀ ⊢ x : A.subst σ)
        (hv : (LR2 Γ₀).Val2 x x (A.subst σ) p a₁)
        (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) :
        (LR2 Γ₀).ValTy2 (B.subst (σ.cons x)) (B.subst (σ'.cons x)) mb :=
      (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSb.le_sort hmb
        (.mono_r hSb.le_sort .sort hmb) ((LR2 Γ₀).toType (LR2 Γ₀).sort)
        ((ihB hBb hSb hmb).1 (W.cons (bvar0 hp hA₁ hx hv W)) |>.1)
    -- N interpretation from M interpretation via sound (bidirectional eval)
    have hN (W : ρ.Fits Γ₀ Γ) : LE_Interp ρ m (.lam A' body') :=
      (LE_Interp.sound (.lamDF HA.defeq HBody.defeq) W).1.1 hM
    -- Pair direction: local lemma, used twice (for M and for N)
    -- Produces Val2 (.lam X Y).subst σ (.lam X Y).subst σ' (.forallE A B).subst σ m a
    -- given LE_Interp for the lambda term and the relevant body IH direction.
    have mkPairVal2 {X Y}
        (hTerm : LE_Interp ρ m (.lam X Y))
        (bodyDir : ∀ {k np : Nat} {p : Shape np} {mb ab : Shape k}
          {t t' : SExpr} {σ σ' : Subst},
          LE_Interp (ρ.push p) mb Y → LE_Interp (ρ.push p) ab B → mb.HasType ab →
          LR2.SubstWF Γ₀ σ σ' Γ ρ →
          LR2.Subst1 Γ₀ t t' A.lift (A.subst σ) (A.subst σ') (ρ.push p) →
          (LR2 Γ₀).Val2 (n := k) (Y.subst (σ.cons t)) (Y.subst (σ'.cons t'))
            (B.subst (σ.cons t)) mb ab)
        (σ σ' : Subst) (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) :
        (LR2 Γ₀).Val2 (.subst (.lam X Y) σ) (.subst (.lam X Y) σ')
          (.subst (.forallE A B) σ) m a := by
      suffices ∀ n' b (f : ShapeFun _), n = n' + 1 → a ≍ (.forallE b f : Shape (n'+1)) →
          (LR2 Γ₀).Val2 (.subst (.lam X Y) σ) (.subst (.lam X Y) σ')
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
      -- Syntactic side conditions
      have ⟨v, hBsort⟩ := HBody.defeq.isType
      have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
        HA.defeq.hasType.1.subst W.left.toSubstEq
      have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
        hBsort.subst (W.left.toSubstEq.lift hTypA)
      -- Semantic domain validity: ValTy2 (A.subst σ) (A.subst σ) a₁
      -- Chain: extract LE_Interp ρ a₁ A from hA, use sound to get InterpTyped,
      -- then domTyEq + left_ty + mono_r_2_ty + lift
      have hDomInterp := forallE_dom_interp hA
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA.defeq W.left.fits).2 hDomInterp
      have hDomEq := (LR2 Γ₀).left_ty (domTyEq hA' hSort hmem' W.left)
      have hValTyDom : (LR2 Γ₀).ValTy2 (A.subst σ) (A.subst σ) a₁ :=
        (LR2.ValTy2.lift le_n aty.1.isType).1 <| (LR2 Γ₀).mono_r_2_ty le_a
          (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 aty.1.isType)
          (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType hDomEq
      -- Codomain type validity at each fiber, using ihB
      have hPiEdge : LR2S.PiEdge2 (LR2 Γ₀) (A.subst σ) (B.subst σ.lift) (B.subst σ.lift) a₁ a₂ := by
        constructor
        · intro x x' p hp ha hv
          simp only [inst_lift_cons]
          have W' := W.cons (bvar0 hp (forallE_dom_interp hA) ha hv W)
          have hBb := forallE_body_interp hA hp
          have ⟨n', ab, _, le_n', le_ab, hBb', hSortB, hmemB⟩ :=
            (LE_Interp.sound HB.defeq W'.fits).2 hBb
          have ρ_le : (ρ.push p).LE (ρ.push (n := n') p.lift) :=
            (Valuation.LE.push' le_n' (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ .rfl⟩
          have t := codomTyPair (hBb'.mono_l ρ_le) (hSortB.mono_l ρ_le) hmemB
            ((Shape.HasType.lift le_n').2 hp) ((LE_Interp.lift le_n').2 hDomInterp)
            ha ((Val2.lift le_n' hp).2 hv) W.left
          have hap : (a₂.app p).HasType .type := aty.2 _ hp
          have t' := (LR2.ValTy2.lift le_n' hap).1 <| (LR2 Γ₀).mono_r_2_ty le_ab
            (Shape.lift_type ▸ (Shape.HasType.lift le_n').2 hap)
            (Shape.HasType.mono_r hSortB.le_sort .sort hmemB).toType t
          exact ⟨t', t'⟩
        · intro x p hp ha hv
          simp only [inst_lift_cons]
          have W' := W.cons (bvar0 hp (forallE_dom_interp hA) ha hv W)
          have hBb := forallE_body_interp hA hp
          have ⟨_, ab, _, le_n', le_ab, hBb', hSortB, hmemB⟩ :=
            (LE_Interp.sound HB.defeq W'.fits).2 hBb
          have hap : (a₂.app p).HasType .type := aty.2 _ hp
          exact (LR2.ValTy2.lift le_n' hap).1 <| (LR2 Γ₀).mono_r_2_ty le_ab
            (Shape.lift_type ▸ (Shape.HasType.lift le_n').2 hap)
            (Shape.HasType.mono_r hSortB.le_sort .sort hmemB).toType
            (codomTyEq hBb' hSortB hmemB hp hDomInterp ha hv W.left)
      refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl, hTypA, hValTyDom, hTypB, hPiEdge, ?_⟩
      cases hmem.unfold with | bot => trivial | lam htm
      have betaL t : Γ₀ ⊢ .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
          Y.subst (σ.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
      have betaR t : Γ₀ ⊢ .app (.lam (X.subst σ') (Y.subst σ'.lift)) t ⤳*
          Y.subst (σ'.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
      refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
      -- ValPi2 pair: Val2 x x' (A.subst σ) p a₁ →
      --   Val2 ((.lam X Y).subst σ).app x) .. ∧ Val2 ((.lam X Y).subst σ').app x) ..
      · rw [inst_lift_cons]
        constructor
        -- Conjunct 1: same σ direction
        · exact ((LR2 Γ₀).whr (betaL x) (betaL x')).2
            (bodyDir (lam_body_interp hTerm htm hp) (forallE_body_interp hA hp) (htm.2.2 p hp)
              W.left (bvar0 hp (forallE_dom_interp hA) ha hv W.left))
        -- Conjunct 2: same σ' direction
        · -- Domain type validity across σ→σ' from ihA pair direction
          have vtAA' : (LR2 Γ₀).ValTy2 (A.subst σ) (A.subst σ') a₁ :=
            (LR2.ValTy2.lift le_n aty.1.isType).1 <| (LR2 Γ₀).mono_r_2_ty le_a
              (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 aty.1.isType)
              (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType <|
              (LR2 Γ₀).toType <| (LR2 Γ₀).mono_r_1 hSort.le_sort hmem'
                (.mono_r hSort.le_sort .sort hmem') ((LR2 Γ₀).toType (LR2 Γ₀).sort)
                ((ihA hA' hSort hmem').1 W |>.1)
          -- Convert typing judgment and Val2 from A.subst σ to A.subst σ'
          have ha' : Γ₀ ⊢ x ≡ x' : A.subst σ' :=
            .defeqDF (HA.defeq.hasType.1.subst W.toSubstEq) ha
          have hv' := (LR2 Γ₀).conv vtAA' hv
          -- Codomain type conv: ValTy2 (B.subst (σ'.cons x)) (B.subst (σ.cons x)) (a₂.app p)
          have W_eq := W.cons (bvar0 hp (forallE_dom_interp hA) ha hv W)
          have hBb_sd := forallE_body_interp hA hp
          have ⟨n_sd, ab_sd, _, le_n_sd, le_ab_sd, hBb_sd', hSortB_sd, hmemB_sd⟩ :=
            (LE_Interp.sound HB.defeq W_eq.fits).2 hBb_sd
          have ρ_le_sd : (ρ.push p).LE (ρ.push (n := n_sd) p.lift) :=
            (Valuation.LE.push' le_n_sd (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ .rfl⟩
          have t_sd := codomTySubstDir (hBb_sd'.mono_l ρ_le_sd) (hSortB_sd.mono_l ρ_le_sd)
            hmemB_sd ((Shape.HasType.lift le_n_sd).2 hp)
            ((LE_Interp.lift le_n_sd).2 hDomInterp) (ha.hasType.1)
            ((Val2.lift le_n_sd hp).2 ((LR2 Γ₀).left hv)) W
          have hap_sd : (a₂.app p).HasType .type := aty.2 _ hp
          have vtBconv := (LR2 Γ₀).symm_ty <|
            (LR2.ValTy2.lift le_n_sd hap_sd).1 <| (LR2 Γ₀).mono_r_2_ty le_ab_sd
              (Shape.lift_type ▸ (Shape.HasType.lift le_n_sd).2 hap_sd)
              (Shape.HasType.mono_r (hSortB_sd.mono_l ρ_le_sd).le_sort .sort hmemB_sd).toType
              t_sd
          -- Body Val2 at B.subst (σ'.cons x), then conv to B.subst (σ.cons x)
          exact ((LR2 Γ₀).whr (betaR x) (betaR x')).2 <|
            (LR2 Γ₀).conv vtBconv <|
              bodyDir (lam_body_interp hTerm htm hp) (forallE_body_interp hA hp)
                (htm.2.2 p hp) W.symm.left
                (bvar0 hp (forallE_dom_interp hA) ha' hv' W.symm.left)
      -- ValPi2 eq: Val2 x x (A.subst σ) p a₁ →
      --   Val2 ((.lam X Y).subst σ).app x) ((.lam X Y).subst σ').app x) ..
      · rw [inst_lift_cons]
        exact ((LR2 Γ₀).whr (betaL x) (betaR x)).2
          (bodyDir (lam_body_interp hTerm htm hp) (forallE_body_interp hA hp) (htm.2.2 p hp)
            W (bvar0 hp (forallE_dom_interp hA) ha hv W))
    -- Main result
    refine ⟨fun σ σ' W => ⟨
        mkPairVal2 hM
          (fun hMb hBb hmb W h0 => (ihBody hMb hBb hmb).1 (W.cons h0) |>.1) σ σ' W,
        mkPairVal2 (hN W.fits)
          (fun hMb' hBb hmb W h0 =>
            (ihBody ((LE_Interp.sound HBody.defeq (W.cons h0).fits).1.2 hMb') hBb hmb).1
              (W.cons h0) |>.2) σ σ' W⟩,
      fun σ W => ?_⟩
    -- Val2 (.lam (A.subst σ) (body.subst σ.lift)) (.lam (A'.subst σ) (body'.subst σ.lift))
    --      (.forallE (A.subst σ) (B.subst σ.lift)) m a
    suffices ∀ n' b (f : ShapeFun _), n = n' + 1 → a ≍ (.forallE b f : Shape (n'+1)) →
        (LR2 Γ₀).Val2 (.subst (.lam A body) σ) (.subst (.lam A' body') σ)
          (.subst (.forallE A B) σ) m a by
      cases hmem.unfold with
      | bot hm =>
        cases hm.unfold with
        | forallE => exact this _ _ _ rfl .rfl
        | _ => cases n <;> trivial
      | sort | forallE => (try cases n) <;> cases hM; rename_i h _ _; simp [Shape.LE.def] at h
      | lam => exact this _ _ _ rfl .rfl
    rintro k a₁ a₂ rfl ⟨⟩
    have .forallE aty := hmem.isType.unfold
    -- Syntactic side conditions
    have ⟨v, hBsort⟩ := HBody.defeq.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      HA.defeq.hasType.1.subst W.toSubstEq
    have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      hBsort.subst (W.toSubstEq.lift hTypA)
    -- Semantic domain validity: ValTy2 (A.subst σ) (A.subst σ) a₁
    have hDomInterp := forallE_dom_interp hA
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA.defeq W.fits).2 hDomInterp
    have hDomEq := (LR2 Γ₀).left_ty (domTyEq hA' hSort hmem' W)
    have hValTyDom : (LR2 Γ₀).ValTy2 (A.subst σ) (A.subst σ) a₁ :=
      (LR2.ValTy2.lift le_n aty.1.isType).1 <| (LR2 Γ₀).mono_r_2_ty le_a
        (Shape.lift_type ▸ (Shape.HasType.lift le_n).2 aty.1.isType)
        (Shape.HasType.mono_r hSort.le_sort .sort hmem').toType hDomEq
    -- Codomain type validity at each fiber
    have hPiEdge : LR2S.PiEdge2 (LR2 Γ₀) (A.subst σ) (B.subst σ.lift) (B.subst σ.lift) a₁ a₂ := by
      constructor
      · intro x x' p hp ha hv
        simp only [inst_lift_cons]
        have W' := W.cons (bvar0 hp (forallE_dom_interp hA) ha hv W)
        have hBb := forallE_body_interp hA hp
        have ⟨n', ab, _, le_n', le_ab, hBb', hSortB, hmemB⟩ :=
          (LE_Interp.sound HB.defeq W'.fits).2 hBb
        have ρ_le : (ρ.push p).LE (ρ.push (n := n') p.lift) :=
          (Valuation.LE.push' le_n' (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ .rfl⟩
        have t := codomTyPair (hBb'.mono_l ρ_le) (hSortB.mono_l ρ_le) hmemB
          ((Shape.HasType.lift le_n').2 hp) ((LE_Interp.lift le_n').2 hDomInterp)
          ha ((Val2.lift le_n' hp).2 hv) W
        have hap : (a₂.app p).HasType .type := aty.2 _ hp
        have t' := (LR2.ValTy2.lift le_n' hap).1 <| (LR2 Γ₀).mono_r_2_ty le_ab
          (Shape.lift_type ▸ (Shape.HasType.lift le_n').2 hap)
          (Shape.HasType.mono_r hSortB.le_sort .sort hmemB).toType t
        exact ⟨t', t'⟩
      · intro x p hp ha hv
        simp only [inst_lift_cons]
        have W' := W.cons (bvar0 hp (forallE_dom_interp hA) ha hv W)
        have hBb := forallE_body_interp hA hp
        have ⟨_, ab, _, le_n', le_ab, hBb', hSortB, hmemB⟩ :=
          (LE_Interp.sound HB.defeq W'.fits).2 hBb
        have hap : (a₂.app p).HasType .type := aty.2 _ hp
        exact (LR2.ValTy2.lift le_n' hap).1 <| (LR2 Γ₀).mono_r_2_ty le_ab
          (Shape.lift_type ▸ (Shape.HasType.lift le_n').2 hap)
          (Shape.HasType.mono_r hSortB.le_sort .sort hmemB).toType
          (codomTyEq hBb' hSortB hmemB hp hDomInterp ha hv W)
    refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl, hTypA, hValTyDom, hTypB, hPiEdge, ?_⟩
    cases hmem.unfold with | bot => trivial | lam htm
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    -- ValPi2 pair direction
    · have betaM : Γ₀ ⊢ .app (.lam (A.subst σ) (body.subst σ.lift)) x ⤳*
          body.subst (σ.cons x) := inst_lift_cons (x := x) ▸ .tail .rfl .beta
      have betaM' : Γ₀ ⊢ .app (.lam (A.subst σ) (body.subst σ.lift)) x' ⤳*
          body.subst (σ.cons x') := inst_lift_cons (x := x') ▸ .tail .rfl .beta
      have betaN : Γ₀ ⊢ .app (.lam (A'.subst σ) (body'.subst σ.lift)) x ⤳*
          body'.subst (σ.cons x) := inst_lift_cons (x := x) ▸ .tail .rfl .beta
      have betaN' : Γ₀ ⊢ .app (.lam (A'.subst σ) (body'.subst σ.lift)) x' ⤳*
          body'.subst (σ.cons x') := inst_lift_cons (x := x') ▸ .tail .rfl .beta
      rw [inst_lift_cons]
      have bP := bodyPair
        (lam_body_interp hM htm hp) (forallE_body_interp hA hp) (htm.2.2 p hp)
        W (bvar0 hp (forallE_dom_interp hA) ha hv W)
      exact ⟨((LR2 Γ₀).whr betaM betaM').2 bP.1,
             ((LR2 Γ₀).whr betaN betaN').2 bP.2⟩
    -- ValPi2 eq direction
    · have betaM : Γ₀ ⊢ .app (.lam (A.subst σ) (body.subst σ.lift)) x ⤳*
          body.subst (σ.cons x) := inst_lift_cons (x := x) ▸ .tail .rfl .beta
      have betaN : Γ₀ ⊢ .app (.lam (A'.subst σ) (body'.subst σ.lift)) x ⤳*
          body'.subst (σ.cons x) := inst_lift_cons (x := x) ▸ .tail .rfl .beta
      rw [inst_lift_cons]
      exact ((LR2 Γ₀).whr betaM betaN).2
        (bodyEq (lam_body_interp hM htm hp) (forallE_body_interp hA hp) (htm.2.2 p hp)
          W (bvar0 hp (forallE_dom_interp hA) ha hv W))
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
