import Lean4Lean.Verify.Inductive.Context

/-! # Removing type-annotation wrappers from binder domains

The inductive checker removes `optParam`, `autoParam`, `outParam` and `semiOutParam` from a
binder domain (`Expr.consumeTypeAnnotationsVerified`) only where the environment declares the
wrapper as the prelude's definition (`TypeAnnotationWrappers`, section 1.3 of
the design notes). This file proves that the unannotated domain translates to a
type definitionally equal to the source domain, and discharges the two hypotheses
`ConsumeTypeAnnotationsCompat` and `RecursorConsumeTypeAnnotationsCompat` of `Context.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

/-- The real delta body of a binary annotation wrapper translates to the same
abstract constant as its source head; beta reduction therefore identifies the
translated wrapper application with its first argument. -/
private theorem BinaryTypeAnnotationWrapper.applicationDefEq_closed
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Delta : VLCtx} {name : Name}
    (H : BinaryTypeAnnotationWrapper env name)
    (Hchecking : CheckingEnv safety env venv)
    (hDelta : Delta.WF venv Us.length) (hnoBV : Delta.NoBV)
    {levels : List Level} {first second : Expr} {out : VExpr}
    (htr : TrExprS venv Us Delta
      (.app (.app (.const name levels) first) second) out) :
    exists first', TrExprS venv Us Delta first first' ∧
      venv.IsDefEqU Us.length Delta.toCtx out first' := by
  rcases H.operational with
    ⟨info, value, hlookup, hsafe, hdelta, hreduces⟩
  let .app hfnType hsecondType hfn hsecond := htr
  let .app hheadType hfirstType hhead hfirst := hfn
  let .const habstract hlevels harity := hhead
  have ⟨hname, hsafety, huvars, _htype⟩ :=
    Hchecking.find?_uniq hlookup habstract
  subst name
  have hvalue :=
    (Hchecking.of_value hlookup
      (hsafe ▸ DefinitionSafety.le_safe) hdelta).instL
      Hchecking.wf (by trivial) hlevels (huvars.trans harity.symm)
  have hvalueWeak := hvalue.weakFV Hchecking.wf
    (VLCtx.FVLift.from_nil hnoBV) hDelta
  rw [hvalue.wf.closedN Hchecking.wf trivial |>.liftN_eq
    (Nat.zero_le _)] at hvalueWeak
  simp [VExpr.instL] at hvalueWeak
  rw [VLevel.inst_map_id] at hvalueWeak
  · have happFn :=
      TrExpr.app Hchecking.wf hDelta hheadType hfirstType
        hvalueWeak (hfirst.trExpr Hchecking.wf.orderedStrong hDelta)
    have happ := TrExpr.app Hchecking.wf hDelta hfnType hsecondType happFn
        (hsecond.trExpr Hchecking.wf.orderedStrong hDelta)
    have hfirstClosed : first.Closed := by
      simpa [hnoBV] using hfirst.closed
    have hsecondClosed : second.Closed := by
      simpa [hnoBV] using hsecond.closed
    have hbeta := happ.beta Hchecking.wf hDelta
      (hreduces levels hfirstClosed hsecondClosed)
    exact ⟨_, hfirst,
      hbeta.uniq Hchecking.wf
        (.refl Hchecking.wf hDelta) (hfirst.trExpr Hchecking.wf.orderedStrong hDelta)⟩
  · exact (List.Forall₂.length_eq
      (List.mapM_eq_some.1 hlevels)).symm.trans <|
      harity.trans huvars.symm

/-- Unary output-parameter wrappers are handled by the same real-body
unfolding argument. -/
private theorem UnaryTypeAnnotationWrapper.applicationDefEq_closed
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Delta : VLCtx} {name : Name}
    (H : UnaryTypeAnnotationWrapper env name)
    (Hchecking : CheckingEnv safety env venv)
    (hDelta : Delta.WF venv Us.length) (hnoBV : Delta.NoBV)
    {levels : List Level} {arg : Expr} {out : VExpr}
    (htr : TrExprS venv Us Delta (.app (.const name levels) arg) out) :
    exists arg', TrExprS venv Us Delta arg arg' ∧
      venv.IsDefEqU Us.length Delta.toCtx out arg' := by
  rcases H.operational with
    ⟨info, value, hlookup, hsafe, hdelta, hreduces⟩
  let .app hheadType hargType hhead harg := htr
  let .const habstract hlevels harity := hhead
  have ⟨hname, hsafety, huvars, _htype⟩ :=
    Hchecking.find?_uniq hlookup habstract
  subst name
  have hvalue :=
    (Hchecking.of_value hlookup
      (hsafe ▸ DefinitionSafety.le_safe) hdelta).instL
      Hchecking.wf (by trivial) hlevels (huvars.trans harity.symm)
  have hvalueWeak := hvalue.weakFV Hchecking.wf
    (VLCtx.FVLift.from_nil hnoBV) hDelta
  rw [hvalue.wf.closedN Hchecking.wf trivial |>.liftN_eq
    (Nat.zero_le _)] at hvalueWeak
  simp [VExpr.instL] at hvalueWeak
  rw [VLevel.inst_map_id] at hvalueWeak
  · have happ :=
      TrExpr.app Hchecking.wf hDelta hheadType hargType hvalueWeak
        (harg.trExpr Hchecking.wf.orderedStrong hDelta)
    have hargClosed : arg.Closed := by
      simpa [hnoBV] using harg.closed
    have hbeta :=
      happ.beta Hchecking.wf hDelta (hreduces levels hargClosed)
    exact ⟨_, harg,
      hbeta.uniq Hchecking.wf
        (.refl Hchecking.wf hDelta) (harg.trExpr Hchecking.wf.orderedStrong hDelta)⟩
  · exact (List.Forall₂.length_eq
      (List.mapM_eq_some.1 hlevels)).symm.trans <|
      harity.trans huvars.symm

/-- A named presentation of an abstract context lets closed source placeholders
refer to arbitrary abstract values through local let declarations. -/
private def namedCtx : List VExpr → VLCtx
  | [] => []
  | A :: Γ => (some (⟨.num .anonymous Γ.length⟩, []), .vlam A) :: namedCtx Γ

@[simp] private theorem namedCtx_toCtx (Γ : List VExpr) : (namedCtx Γ).toCtx = Γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp [namedCtx, VLCtx.toCtx, ih]

@[simp] private theorem namedCtx_noBV (Γ : List VExpr) : (namedCtx Γ).NoBV := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => exact ih

private theorem namedCtx_names {Γ : List VExpr} (h : (⟨.num .anonymous n⟩ : FVarId) ∈ (namedCtx Γ).fvars) :
    n < Γ.length := by
  induction Γ with
  | nil => simp [namedCtx, VLCtx.fvars] at h
  | cons A Γ ih =>
    change _ ∈ (⟨.num .anonymous Γ.length⟩ : FVarId) :: (namedCtx Γ).fvars at h
    rcases List.mem_cons.mp h with h | h
    · have := congrArg FVarId.name h
      cases this
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (ih h)

private theorem namedCtx_wf (hΓ : OnCtx Γ (env.IsType U)) : (namedCtx Γ).WF env U := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
    exact ⟨ih hΓ.1, by
      rintro fv deps h
      cases h
      exact ⟨fun h => Nat.lt_irrefl _ (namedCtx_names h), by simp⟩,
      by simpa only [namedCtx_toCtx, VLocalDecl.WF] using hΓ.2⟩

theorem UnaryTypeAnnotationWrapper.applicationDefEq
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx} {name : Name}
    (H : UnaryTypeAnnotationWrapper env name)
    (Hchecking : CheckingEnv safety env venv)
    (hΔ : Δ.WF venv Us.length)
    {levels : List Level} {arg : Expr} {out : VExpr}
    (htr : TrExprS venv Us Δ (.app (.const name levels) arg) out) :
    ∃ arg', TrExprS venv Us Δ arg arg' ∧
      venv.IsDefEqU Us.length Δ.toCtx out arg' := by
  cases htr with
  | @app fn' A B arg' _ _ _ hheadType hargType hhead harg =>
    cases hhead with
    | const hc hl hn =>
      let fresh : FVarId := ⟨.num .anonymous Δ.toCtx.length⟩
      let ctx : VLCtx := (some (fresh, []), .vlet A arg') :: namedCtx Δ.toCtx
      have hctx : ctx.WF venv Us.length := by
        refine ⟨namedCtx_wf hΔ.toCtx, ?_, ?_⟩
        · rintro fv deps h
          cases h
          exact ⟨fun h => Nat.lt_irrefl _ (namedCtx_names h), by simp⟩
        · simpa only [VLocalDecl.WF, namedCtx_toCtx] using hargType
      have hctxEq : ctx.toCtx = Δ.toCtx := by simp [ctx, VLCtx.toCtx]
      have hctxNoBV : ctx.NoBV := namedCtx_noBV _
      have hv : TrExprS venv Us ctx (.fvar fresh) arg' := .fvar (A := A) (by
        simp [ctx, VLCtx.find?, VLCtx.next, VLocalDecl.type, VLocalDecl.value])
      have hsynthetic : TrExprS venv Us ctx
          (.app (.const name levels) (.fvar fresh)) _ :=
        .app (hctxEq.symm ▸ hheadType) (hctxEq.symm ▸ hargType) (.const hc hl hn) hv
      obtain ⟨target, ht, heq⟩ := H.applicationDefEq_closed Hchecking hctx hctxNoBV hsynthetic
      cases ht with
      | fvar hfind =>
        simp only [ctx, VLCtx.find?, VLCtx.next, beq_self_eq_true, ↓reduceIte,
          VLocalDecl.type, VLocalDecl.value, Option.some.injEq, Prod.mk.injEq] at hfind
        rcases hfind with ⟨rfl, _⟩
        exact ⟨arg', harg, hctxEq ▸ heq⟩

theorem BinaryTypeAnnotationWrapper.applicationDefEq
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx} {name : Name}
    (H : BinaryTypeAnnotationWrapper env name)
    (Hchecking : CheckingEnv safety env venv)
    (hΔ : Δ.WF venv Us.length)
    {levels : List Level} {first second : Expr} {out : VExpr}
    (htr : TrExprS venv Us Δ
      (.app (.app (.const name levels) first) second) out) :
    ∃ first', TrExprS venv Us Δ first first' ∧
      venv.IsDefEqU Us.length Δ.toCtx out first' := by
  cases htr with
  | @app fn' B C second' _ _ _ hfnType hsecondType hfn hsecond =>
    cases hfn with
    | @app head' A D first' _ _ _ hheadType hfirstType hhead hfirst =>
      cases hhead with
      | const hc hl hn =>
        let fv1 : FVarId := ⟨.num .anonymous Δ.toCtx.length⟩
        let fv2 : FVarId := ⟨.num .anonymous (Δ.toCtx.length + 1)⟩
        let ctx1 : VLCtx := (some (fv1, []), .vlet A first') :: namedCtx Δ.toCtx
        let ctx : VLCtx := (some (fv2, []), .vlet B second') :: ctx1
        have hne : fv2 ≠ fv1 := by simp [fv1, fv2]
        have hctx1 : ctx1.WF venv Us.length := by
          refine ⟨namedCtx_wf hΔ.toCtx, ?_, ?_⟩
          · rintro fv deps h
            cases h
            exact ⟨fun h => Nat.lt_irrefl _ (namedCtx_names h), by simp⟩
          · simpa only [VLocalDecl.WF, namedCtx_toCtx] using hfirstType
        have hctx1Eq : ctx1.toCtx = Δ.toCtx := by simp [ctx1, VLCtx.toCtx]
        have hctx : ctx.WF venv Us.length := by
          refine ⟨hctx1, ?_, ?_⟩
          · rintro fv deps h
            cases h
            refine ⟨?_, by simp⟩
            intro hm
            change fv2 ∈ fv1 :: (namedCtx Δ.toCtx).fvars at hm
            rcases List.mem_cons.mp hm with hm | hm
            · exact hne hm
            · have := namedCtx_names hm
              omega
          · simpa only [VLocalDecl.WF, hctx1Eq] using hsecondType
        have hctxEq : ctx.toCtx = Δ.toCtx := by simp [ctx, ctx1, VLCtx.toCtx]
        have hctxNoBV : ctx.NoBV := namedCtx_noBV _
        have hv1 : TrExprS venv Us ctx (.fvar fv1) first' := .fvar (A := A) (by
          simp [ctx, ctx1, VLCtx.find?, VLCtx.next, hne,
            VLocalDecl.type, VLocalDecl.value, VLocalDecl.depth])
        have hv2 : TrExprS venv Us ctx (.fvar fv2) second' := .fvar (A := B) (by
          simp [ctx, VLCtx.find?, VLCtx.next, VLocalDecl.type, VLocalDecl.value])
        have hsynthetic : TrExprS venv Us ctx
            (.app (.app (.const name levels) (.fvar fv1)) (.fvar fv2)) _ :=
          .app (hctxEq.symm ▸ hfnType) (hctxEq.symm ▸ hsecondType)
            (.app (hctxEq.symm ▸ hheadType) (hctxEq.symm ▸ hfirstType)
              (.const hc hl hn) hv1) hv2
        obtain ⟨target, ht, heq⟩ := H.applicationDefEq_closed Hchecking hctx hctxNoBV hsynthetic
        cases ht with
        | fvar hfind =>
          simp [ctx, ctx1, VLCtx.find?, VLCtx.next, hne,
            VLocalDecl.type, VLocalDecl.value, VLocalDecl.depth] at hfind
          rcases hfind with ⟨rfl, _⟩
          exact ⟨first', hfirst, hctxEq ▸ heq⟩

/-- Removing type annotations, in any well-formed checking context, including anonymous
bound-variable contexts: given wrappers that are the prelude's definitions, the unannotated
domain translates to a type definitionally equal to the source domain. The statement does
not depend on the inductive checker's contexts, so the ordinary and generated-recursor
hypotheses are both instances of it. -/
theorem consumeTypeAnnotationsSemantic_of_wrappers
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Delta : VLCtx}
    (Hchecking : CheckingEnv safety env venv)
    {annOk : Name → Bool} (Hwrappers : TypeAnnotationWrappers env annOk)
    (hDelta : Delta.WF venv Us.length)
    {dom : Expr} {source' : VExpr}
    (htr : TrExprS venv Us Delta dom source')
    (htype : venv.IsType Us.length Delta.toCtx source') :
    ∃ consumed',
      TrExprS venv Us Delta (dom.consumeTypeAnnotationsVerified annOk) consumed' ∧
      venv.IsType Us.length Delta.toCtx consumed' ∧
      ∃ u, venv.IsDefEq Us.length Delta.toCtx
        source' consumed' (.sort u) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ dom generalizing source'
  case case1 name levels first second hannotation ih =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hannotation
    rcases hannotation with ⟨hopt | hauto, hok⟩
    · subst name
      rcases (Hwrappers.optParam hok).applicationDefEq
          Hchecking hDelta htr with ⟨first', hfirst, hwrap⟩
      rcases htype with ⟨u, hsourceType⟩
      have hwrapAtSort :=
        hwrap.of_l Hchecking.wf hDelta.toCtx hsourceType
      have hfirstType : venv.IsType Us.length Delta.toCtx first' :=
        ⟨u, hwrapAtSort.hasType.2⟩
      rcases ih hfirst hfirstType with
        ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
      have hconsumedAtSort := VEnv.IsDefEqU.of_l
        Hchecking.wf hDelta.toCtx
        (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
          first' consumed') hwrapAtSort.hasType.2
      exact ⟨consumed', hconsumed, hconsumedType, u,
        hwrapAtSort.trans_l Hchecking.wf hDelta.toCtx hconsumedAtSort⟩
    · subst name
      rcases (Hwrappers.autoParam hok).applicationDefEq
          Hchecking hDelta htr with ⟨first', hfirst, hwrap⟩
      rcases htype with ⟨u, hsourceType⟩
      have hwrapAtSort :=
        hwrap.of_l Hchecking.wf hDelta.toCtx hsourceType
      have hfirstType : venv.IsType Us.length Delta.toCtx first' :=
        ⟨u, hwrapAtSort.hasType.2⟩
      rcases ih hfirst hfirstType with
        ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
      have hconsumedAtSort := VEnv.IsDefEqU.of_l
        Hchecking.wf hDelta.toCtx
        (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
          first' consumed') hwrapAtSort.hasType.2
      exact ⟨consumed', hconsumed, hconsumedType, u,
        hwrapAtSort.trans_l Hchecking.wf hDelta.toCtx hconsumedAtSort⟩
  case case2 =>
    rcases htype with ⟨u, hsourceType⟩
    exact ⟨source', htr, ⟨u, hsourceType⟩, u, hsourceType⟩
  case case3 name levels arg hannotation ih =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hannotation
      rcases hannotation with ⟨hout | hsemi, hok⟩
      · subst name
        rcases (Hwrappers.outParam hok).applicationDefEq
            Hchecking hDelta htr with ⟨arg', harg, hwrap⟩
        rcases htype with ⟨u, hsourceType⟩
        have hwrapAtSort :=
          hwrap.of_l Hchecking.wf hDelta.toCtx hsourceType
        have hargType : venv.IsType Us.length Delta.toCtx arg' :=
          ⟨u, hwrapAtSort.hasType.2⟩
        rcases ih harg hargType with
          ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
        have hconsumedAtSort := VEnv.IsDefEqU.of_l
          Hchecking.wf hDelta.toCtx
          (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
            arg' consumed') hwrapAtSort.hasType.2
        exact ⟨consumed', hconsumed, hconsumedType, u,
          hwrapAtSort.trans_l Hchecking.wf hDelta.toCtx hconsumedAtSort⟩
      · subst name
        rcases (Hwrappers.semiOutParam hok).applicationDefEq
            Hchecking hDelta htr with ⟨arg', harg, hwrap⟩
        rcases htype with ⟨u, hsourceType⟩
        have hwrapAtSort :=
          hwrap.of_l Hchecking.wf hDelta.toCtx hsourceType
        have hargType : venv.IsType Us.length Delta.toCtx arg' :=
          ⟨u, hwrapAtSort.hasType.2⟩
        rcases ih harg hargType with
          ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
        have hconsumedAtSort := VEnv.IsDefEqU.of_l
          Hchecking.wf hDelta.toCtx
          (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
            arg' consumed') hwrapAtSort.hasType.2
        exact ⟨consumed', hconsumed, hconsumedType, u,
          hwrapAtSort.trans_l Hchecking.wf hDelta.toCtx hconsumedAtSort⟩
  case case4 | case5 =>
    rcases htype with ⟨u, hsourceType⟩
    exact ⟨source', htr, ⟨u, hsourceType⟩, u, hsourceType⟩
theorem consumeTypeAnnotationsSemantic
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Delta : VLCtx}
    (Hchecking : CheckingEnv.Valid safety env venv)
    (hDelta : Delta.WF venv Us.length)
    {dom : Expr} {source' : VExpr}
    (htr : TrExprS venv Us Delta dom source')
    (htype : venv.IsType Us.length Delta.toCtx source') :
    ∃ consumed',
      TrExprS venv Us Delta (dom.consumeTypeAnnotationsVerified env.isTypeAnnotationWrapper)
        consumed' ∧
      venv.IsType Us.length Delta.toCtx consumed' ∧
      ∃ u, venv.IsDefEq Us.length Delta.toCtx
        source' consumed' (.sort u) :=
  consumeTypeAnnotationsSemantic_of_wrappers Hchecking.tr (.of_env env) hDelta htr htype

/-- The annotation hypothesis of the inductive checker's contexts holds, using the
environment's own wrapper lookup (`TypeAnnotationWrappers.of_env`). -/
theorem consumeTypeAnnotationsCompat : VerifyInductive.ConsumeTypeAnnotationsCompat := by
  intro c Hc dom source' htr htype
  rcases consumeTypeAnnotationsSemantic Hc.checking Hc.mlctx_wf.tr.wf
      htr htype with
    ⟨consumed', hconsumed, hconsumedType, u, hsourceEq⟩
  exact ⟨consumed', {
    source := htr
    unannotated := hconsumed
    isType := hconsumedType
    source_defeq := ⟨u, hsourceEq⟩ }⟩

/-- The annotation hypothesis of the recursor contexts holds: it is the same theorem
at the generated universe list. -/
theorem recursorConsumeTypeAnnotationsCompat :
    VerifyInductive.RecursorConsumeTypeAnnotationsCompat := by
  intro c recLparams R dom source' htr htype
  rcases consumeTypeAnnotationsSemantic R.checking R.mlctx_wf.tr.wf
      htr htype with
    ⟨consumed', hconsumed, hconsumedType, u, hsourceEq⟩
  exact ⟨consumed', {
    source := htr
    unannotated := hconsumed
    isType := hconsumedType
    source_defeq := ⟨u, hsourceEq⟩ }⟩

end Lean4Lean

/-! Exact abstract targets for the executable's removal of type annotations. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- Follow the actual source annotation spine in an already chosen
translation. Source shape matters: metadata is erased by translation but
does not expose an annotation to `Expr.consumeTypeAnnotationsVerified`. -/
def consumeTranslatedTypeAnnotations (ok : Name → Bool) : Expr → VExpr → VExpr
  | .app (.app (.const name _) first) _, target =>
    if (name == ``optParam || name == ``autoParam) && ok name then
      match target with
      | .app (.app (.const _ _) first') _ => consumeTranslatedTypeAnnotations ok first first'
      | _ => target
    else target
  | .app (.const name _) arg, target =>
    if (name == ``outParam || name == ``semiOutParam) && ok name then
      match target with
      | .app (.const _ _) arg' => consumeTranslatedTypeAnnotations ok arg arg'
      | _ => target
    else target
  | _, target => target

/-- Removing annotations reuses subtranslations of the selected source target;
it does not choose a fresh projection representation. -/
theorem TrExprS.consumeTranslatedTypeAnnotations
    (H : TrExprS env Us Δ source target) :
    TrExprS env Us Δ (source.consumeTypeAnnotationsVerified ok)
      (Lean4Lean.consumeTranslatedTypeAnnotations ok source target) := by
  fun_induction Expr.consumeTypeAnnotationsVerified ok source generalizing target
  case case1 name levels first second hannotation ih =>
    cases H with
    | app _ _ hfn _ =>
      cases hfn with
      | app _ _ hhead hfirst =>
        cases hhead
        simpa only [Lean4Lean.consumeTranslatedTypeAnnotations, hannotation, ↓reduceIte] using ih hfirst
  case case3 name levels arg hannotation ih =>
    cases H with
    | app _ _ hhead harg =>
      cases hhead
      simpa only [Lean4Lean.consumeTranslatedTypeAnnotations, hannotation, ↓reduceIte] using ih harg
  all_goals simp [Lean4Lean.consumeTranslatedTypeAnnotations, *]

/-- The fixed unannotated target is a type, definitionally equal to the source domain.
The wrapper definitions supply the equality; translation uniqueness identifies the
translation they produce with the target already fixed by the source traversal. -/
theorem consumeTranslatedTypeAnnotations_semantic_of_wrappers
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx}
    (Hchecking : CheckingEnv safety env venv)
    (Hwrappers : TypeAnnotationWrappers env ok)
    (hΔ : Δ.WF venv Us.length)
    (htr : TrExprS venv Us Δ source target)
    (htype : venv.IsType Us.length Δ.toCtx target) :
    venv.IsType Us.length Δ.toCtx (consumeTranslatedTypeAnnotations ok source target) ∧
    venv.IsDefEqU Us.length Δ.toCtx target (consumeTranslatedTypeAnnotations ok source target) := by
  obtain ⟨consumed, hconsumed, hconsumedType, level, heq⟩ :=
    consumeTypeAnnotationsSemantic_of_wrappers Hchecking Hwrappers hΔ htr htype
  have halign := hconsumed.uniq Hchecking.wf
    (.refl Hchecking.wf hΔ) htr.consumeTranslatedTypeAnnotations
  exact ⟨hconsumedType.defeqU_l Hchecking.wf hΔ.toCtx halign,
    (show venv.IsDefEqU Us.length Δ.toCtx target consumed from ⟨.sort level, heq⟩).trans
      Hchecking.wf hΔ.toCtx halign⟩

end Lean4Lean
