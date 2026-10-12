import Lean4Lean.Verify.Inductive.Recursor.Signature.Constructors
import Lean4Lean.Verify.Inductive.Recursor.Signature.FieldDomains
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The first `n` binders of `consumed` are those of `raw` with each domain unannotated
(`consumeTypeAnnotationsVerified`); the bodies after the `n`-th binder are unrelated. -/
inductive Expr.UnannotatedForallPrefix (ok : Name → Bool) : Nat → Lean.Expr → Lean.Expr → Prop
  | zero (raw consumed : Lean.Expr) : UnannotatedForallPrefix ok 0 raw consumed
  | succ : UnannotatedForallPrefix ok n body body' →
      UnannotatedForallPrefix ok (n + 1) (.forallE name dom body bi)
        (.forallE name' (dom.consumeTypeAnnotationsVerified ok) body' bi')

/-- Removing the type annotations of a telescope's domains (`consumeForallTypes`) and keeping
only its first `n` domains gives an unannotated prefix of the telescope. -/
theorem Expr.ForallTelescope.unannotatedForallPrefix
    (H : Expr.ForallTelescope raw n residual) :
    Expr.UnannotatedForallPrefix ok n raw
      (Expr.forallDomainsOnly n (Lean4Lean.Expr.consumeForallTypes ok raw)) := by
  induction H with
  | nil => exact .zero _ _
  | cons _ ih => exact .succ ih

/-- Binder by binder, a translation of a telescope and a translation of its unannotated prefix
(in definitionally equal contexts) have definitionally equal domains, in either prefix
context, and the unannotated domains are types. -/
theorem TrExprS.unannotatedForallPrefix_defeq
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety} {Us : List Name}
    (Hchecking : CheckingEnv safety env venv)
    (Hwrappers : TypeAnnotationWrappers env ok)
    (Hpre : Expr.UnannotatedForallPrefix ok n raw consumed) :
    ∀ {Δ₁ Δ₂ : VLCtx} {As Cs : List VExpr} {B D : VExpr},
      VLCtx.IsDefEq venv Us.length Δ₁ Δ₂ →
      TrExprS venv Us Δ₁ raw (VExpr.wrapForalls As B) →
      TrExprS venv Us Δ₂ consumed (VExpr.wrapForalls Cs D) →
      (hA : As.length = n) → (hC : Cs.length = n) →
      ∀ i (hi : i < n),
        venv.IsDefEqU Us.length ((Cs.take i).reverse ++ Δ₂.toCtx)
          (Cs[i]'(by omega)) (As[i]'(by omega)) ∧
        venv.IsDefEqU Us.length ((As.take i).reverse ++ Δ₁.toCtx)
          (Cs[i]'(by omega)) (As[i]'(by omega)) ∧
        venv.IsType Us.length ((Cs.take i).reverse ++ Δ₂.toCtx) (Cs[i]'(by omega)) := by
  have henv := Hchecking.wf
  induction Hpre with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ i hi; omega
  | @succ n body body' name dom bi name' bi' _ ih =>
    intro Δ₁ Δ₂ As Cs B D hΔ Hraw Hcons hA hC
    cases As with
    | nil => simp at hA
    | cons A As =>
    cases Cs with
    | nil => simp at hC
    | cons C Cs =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at Hraw Hcons
    cases Hraw with
    | forallE HAtype _ HA Hbody =>
    cases Hcons with
    | forallE HCtype _ HC Hcbody =>
    have hΔ₁ := hΔ.wf
    obtain ⟨_, HAX⟩ := consumeTranslatedTypeAnnotations_semantic_of_wrappers
      Hchecking Hwrappers hΔ₁ HA HAtype
    have HXC := HA.consumeTranslatedTypeAnnotations.uniq henv hΔ HC
    have HAC := HAX.trans henv hΔ₁.toCtx HXC
    have HACt := HAC.of_l henv hΔ₁.toCtx HAtype.choose_spec
    have Hctx : VLCtx.IsDefEq venv Us.length ((none, .vlam A) :: Δ₁) ((none, .vlam C) :: Δ₂) :=
      .cons hΔ nofun (.vlam HACt)
    intro i hi
    cases i with
    | zero =>
      simp only [List.take_zero, List.reverse_nil, List.nil_append, List.getElem_cons_zero]
      exact ⟨HAC.symm.defeqDFC henv.ordered hΔ.defeqCtx, HAC.symm, HCtype⟩
    | succ i =>
      have Hi := ih Hctx Hbody Hcbody (by simpa using hA) (by simpa using hC) i (by omega)
      simpa [VLCtx.toCtx] using Hi

/-- Field by field, the unannotated field domains of a minor (`declFieldDomains`) are
definitionally equal to the field types of the matching source signature constructor, in
either field scope over the parameter scope, in the header environment and universes, and
they are types there. -/
theorem RecursorConstruction.sourceFields_defeq_header
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    let consumed := H.declFieldDomains owner howner localIndex hlocal
    let header := R.sourceSignature.fieldTypes ctor
    consumed.length = header.length ∧
    ∀ i (hi : i < consumed.length) (hh : i < header.length),
      R.headerVEnv.IsDefEqU c.lparams.length
        ((consumed.take i).reverse ++ R.parameterScope.toCtx) consumed[i] header[i] ∧
      R.headerVEnv.IsDefEqU c.lparams.length
        ((header.take i).reverse ++ R.parameterScope.toCtx) consumed[i] header[i] ∧
      R.headerVEnv.IsType c.lparams.length
        ((consumed.take i).reverse ++ R.parameterScope.toCtx) consumed[i] := by
  intro ctor consumed header
  let S := H.origins.minorShapes owner howner localIndex hlocal
  let HS := H.sourceMinorTyping owner howner localIndex hlocal
  have Hraw := H.constructorRawSourceReplay owner howner localIndex hlocal HS
  obtain ⟨rawTraversal, hrawTraversal, _, _, hcount, _⟩ :=
    H.minorSourceReplay owner howner (by rwa [← H.sourceFamilyCount]) localIndex hlocal
      (H.sourceMinorOffsetBound owner howner localIndex hlocal)
  have heqRaw : rawTraversal = HS.semantic.traversal :=
    Option.some.inj (hrawTraversal.symm.trans HS.semantic.traversal_eq)
  rw [heqRaw] at hcount
  change HS.semantic.traversal.fields.size = ctor.fields.length at hcount
  have hheaderLen : header.length = S.fields.size := by
    have h : header.length = HS.semantic.traversal.fields.size := by
      simp only [header, InductiveSignature.fieldTypes, List.length_map, List.length_zipIdx]
      exact hcount.symm
    rw [h, HS.semantic.traversal_fields]
  have hconsumedLen : consumed.length = S.fields.size :=
    H.sourceFields_length owner howner localIndex hlocal
  have Htel := HS.semantic.traversal.fieldTelescope.abstractList H.params.fvars
  rw [HS.semantic.traversal_fields] at Htel
  have Hpre := Htel.unannotatedForallPrefix (ok := ctorEnv.isTypeAnnotationWrapper)
  have Hsrc := (H.sourceFields_headerReplay owner howner localIndex hlocal).1
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  let Hbound := HS.semantic.fieldsRecent.toFVarArrayIn.mono Hext
  have hsrc : (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars =
      Expr.forallDomainsOnly S.fields.size (Lean4Lean.Expr.consumeForallTypes ctorEnv.isTypeAnnotationWrapper
        (HS.semantic.traversal.parameterTail.abstractList H.params.fvars)) := by
    rw [← H.constructorUnannotatedSource owner howner localIndex hlocal HS,
      Expr.forallDomainsOnly_abstractList,
      Hbound.forallDomainsOnly H.localWF HS.semantic.fieldsRecent.nodup]
  rw [hsrc] at Hsrc
  have hΔ := R.headerAnonymousParameterWF
  have henv := R.headerCheckingAnnotations.1.wf
  have Hall := TrExprS.unannotatedForallPrefix_defeq R.headerCheckingAnnotations.1
    R.headerCheckingAnnotations.2 Hpre (.refl henv hΔ) Hraw Hsrc hheaderLen hconsumedLen
  have hctx : (abstractForallContext R.parameterScope.toCtx.reverse []).toCtx =
      R.parameterScope.toCtx := by
    simp [abstractForallContext_toCtx, VLCtx.toCtx]
  rw [hctx] at Hall
  refine ⟨hconsumedLen.trans hheaderLen.symm, fun i hi hh => ?_⟩
  exact Hall i (hconsumedLen ▸ hi)

end Lean4Lean.VerifyInductive
