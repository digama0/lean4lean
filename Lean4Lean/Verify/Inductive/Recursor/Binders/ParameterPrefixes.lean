import Lean4Lean.Verify.Inductive.Recursor.Signature.Counts

/-! Common-parameter prefixes of constructor types: the comparisons of
`checkConstructors.loopCtor` against the cached parameters
(`CheckedConstructorParameterPrefix`), the refinement of a constructor tail to its
abstract shape in the parameter/field scope, and the per-constructor parameter
prefixes (`ConstructorParameterPrefixes`) used by the recursor construction. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

/-- Regard a constructor constant as the root of a header telescope.  The
header telescope invariant (`checkInductiveTypes.loopType.ScopedHeaderTelescope`)
only uses the constant fields of its `target`; the empty constructor list
therefore lets the same invariant serve constructor parameter prefixes
without duplicating it. -/
def constructorTelescopeTarget (ctorVal : VConstVal) :
    VInductiveTypeSkeleton where
  toVConstVal := ctorVal
  ctors := []

/-- Initialize the constructor telescope from the
translated source constant. -/
noncomputable def ConstructorSynthesisState.initial
    (htype : env.IsType Us.length [] ctorVal.type) :
    checkInductiveTypes.loopType.ScopedHeaderTelescope
      env Us (constructorTelescopeTarget ctorVal) [] ctorVal.type 0 0 := by
  let level := Classical.choose htype
  have htyped := Classical.choose_spec htype
  exact checkInductiveTypes.loopType.ScopedHeaderTelescope.empty
    htype htype htyped

/-- The common-parameter comparisons performed
by `checkConstructors.loopCtor`.  Unlike `ParameterPrefix`, this relation
keeps the translated constructor domain and the
definitional equality returned by the executable `isDefEq` call.

The list of `sourceDomains` is in telescope order.  The scope is the cached
common-parameter scope after the same number of steps.  Keeping both sides
is essential for nested restoration: constructor parameter domains need only
be definitionally, not syntactically, equal to the family parameters. -/
inductive CheckedConstructorParameterPrefix
    (env : VEnv) (Us : List Name) (stats : AddInductive.InductiveStats)
    (original : Expr) :
    Nat → Expr → VLCtx → List VExpr → Prop where
  | zero : CheckedConstructorParameterPrefix env Us stats original
      0 original [] []
  | step
      (H : CheckedConstructorParameterPrefix env Us stats original
        i (.forallE name dom body bi) scope sourceDomains)
      (hparam : stats.params[i]? = some param)
      (hparamFVar : param = .fvar fv)
      (hdomain : TrExprS env Us scope dom sourceDomain)
      (hdomainType : env.IsType Us.length scope.toCtx sourceDomain)
      (hcompare : env.IsDefEqU Us.length scope.toCtx
        sourceDomain paramType) :
      CheckedConstructorParameterPrefix env Us stats original
        (i + 1) (body.instantiate1 param)
        ((some (fv, deps), .vlam paramType) :: scope)
        (sourceDomains ++ [sourceDomain])

/-- A successful cached-parameter comparison advances the abstract
constructor telescope directly.  The executable loop performs no
normalization in this branch: after converting the binder context from the
source domain to the cached parameter type, opening the source body with the
cached free variable supplies the next residual verbatim. -/
theorem checkInductiveTypes.loopType.ScopedHeaderTelescope.consumeConstructorParameter
    (henv : env.WF)
    (H : ScopedHeaderTelescope env Us target scope current i 0)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom,
      TrExprS env Us scope dom sourceDom ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom paramType) :
    ∃ next,
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next ∧
      Nonempty (ScopedHeaderTelescope env Us target
        ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0) := by
  cases htype with
  | forallE hdomType _hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom, hsourceDom, hsourceDomEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    rcases hbody.defeqDFC henv hbodyCtx with ⟨next, hnext⟩
    have hopened : TrExprS env Us
        ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next :=
      hnext.inst_fvar henv.ordered hscopeWF
    have hbodyWF : VLCtx.WF env Us.length
        ((none, .vlam paramType) :: scope) :=
      ⟨H.scopeWF, nofun, ⟨_, hdomTyped.hasType.2⟩⟩
    have hnextRefl : env.IsDefEqU Us.length
        (paramType :: scope.toCtx) next next :=
      hnext.wf henv.ordered hbodyWF
    have hindices : H.indices = [] :=
      List.eq_nil_of_length_eq_zero H.indexCount
    have htype' : TrExprS env Us scope
        (.forallE name dom body bi) (.forallE _ _) :=
      .forallE hdomType _hbodyType hdom hbody
    rcases H.consumeParameter (name := name) (bi := bi)
        henv hindices htype' hscopeWF
        ⟨sourceDom, hsourceDom, hsourceDomEq⟩
        ⟨next, next, hnext, hopened, hnextRefl⟩ with
      ⟨next', hopened', Hnext⟩
    exact ⟨next', hopened', Hnext⟩

/-- Traverse the executable constructor's common-parameter prefix while
building its abstract telescope.  The two callbacks isolate the
control-flow boundaries: exact parameter coverage hands the constructed tail
to the field verifier, while an early non-forall is discharged separately by
the invalid-result argument. -/
theorem checkConstructors.loopCtor.parameterTelescopeWF
    {decl : VInductDecl} {ctorVal : VConstVal}
    {original : Expr}
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Q : List Bool → Prop)
    (Hresult : ∀ {source' : Expr}
        {current' fullCurrent' : VExpr} {fuel' : Nat}
        {sourceDomains : List VExpr},
      (Hsynthesis' :
        checkInductiveTypes.loopType.ScopedHeaderTelescope
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          Hsuffix.parameterDecls current' decl.nparams 0) →
      TrExprS Hc.venv c.lparams Hsuffix.parameterDecls source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      ParameterSegment stats 0 decl.nparams original source' →
      CheckedConstructorParameterPrefix Hc.venv c.lparams stats original
        decl.nparams source' Hsuffix.parameterDecls sourceDomains →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' decl.nparams (fuel' + 1) c).WF Q)
    (Hearly : ∀ {source' : Expr} {scope' : VLCtx}
        {current' fullCurrent' : VExpr} {i' fuel' : Nat}
        {sourceDomains : List VExpr},
      i' < decl.nparams →
      (¬ ∃ name dom body bi, source' = .forallE name dom body bi) →
      checkInductiveTypes.loopType.ReusedParameterScope
        Hsuffix i' source' →
      (Hsynthesis' :
        checkInductiveTypes.loopType.ScopedHeaderTelescope
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          scope' current' i' 0) →
      TrExprS Hc.venv c.lparams scope' source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      CheckedConstructorParameterPrefix Hc.venv c.lparams stats original
        i' source' scope' sourceDomains →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' i' (fuel' + 1) c).WF Q)
    (hparams : stats.params.size = decl.nparams)
    (hbound : i ≤ decl.nparams)
    (Hsegment : ParameterSegment stats 0 i original source)
    (Hscope : ∀ _h : i < stats.params.size,
      checkInductiveTypes.loopType.ReusedParameterScope Hsuffix i source)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = decl.nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      source fullCurrent)
    {sourceDomains : List VExpr}
    (Hcomparisons : CheckedConstructorParameterPrefix Hc.venv c.lparams
      stats original i source scope sourceDomains) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i fuel c).WF Q := by
  induction fuel generalizing source scope current fullCurrent i sourceDomains with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hi : i < decl.nparams
    · have histats : i < stats.params.size := by
        simpa [hparams] using hi
      by_cases hforall : ∃ name dom body bi,
          source = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        cases htypeNarrow with
        | @forallE narrowDom narrowBody _ _ _ _ _
            hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
          rcases TrExpr.forallE_source htypeFull with
            ⟨fullDom, fullBody, hdomFull, hbodyFull,
              _hdomFullType, _hbodyFullType, _hfullCurrent⟩
          rcases Hcurrent.typing with
            ⟨paramTy, paramTy', param', hget, hparamTy,
              _hparamTyEq, hparam, hparamType⟩
          obtain ⟨hb₀, hb₁, paramTy₀, hget₀, hparamTy₀, _hparamType₀⟩ :=
            Hcurrent.scopedTyping histats
          have hparamAt : stats.params[i]? = some stats.params[i]! := by
            simp [histats]
          have hj₀ : depth + (stats.params.size - i) ≤ Hc.mlctx.length := by
            rw [Hsuffix.mlctx_length]; omega
          have hj₁ : depth + (stats.params.size - (i + 1)) ≤ Hc.mlctx.length := by
            rw [Hsuffix.mlctx_length]; omega
          have hdomN : TrExprS Hc.venv c.lparams (Hc.mlctx.dropN _ hj₀).vlctx
              dom narrowDom := by
            rw [hb₀]; exact hdomNarrow
          have hparamTyN : TrExprS Hc.venv c.lparams
              (Hc.mlctx.dropN _ hj₀).vlctx paramTy₀ Hcurrent.paramType := by
            rw [hb₀]; exact hparamTy₀
          refine checkConstructors.loopCtor.parameter.sourceWF
            (Q := Q) Hc hparamAt (fun a ha => ⟨hget a ha, hget₀ a ha⟩)
              hdomFull hbodyFull hparamTy hparam hparamType
              _ hj₀ (Hsuffix.bottom i (by omega)).2 hdomN hparamTyN ?_
          intro _heq heq₀ hopenedFull
          have hsourceDomEq : Hc.venv.IsDefEqU c.lparams.length
              Hcurrent.older.toCtx narrowDom Hcurrent.paramType := by
            rw [hb₀] at heq₀; exact heq₀
          have hsourceDom := hdomNarrow
          have hconsumedWF : VLCtx.WF Hc.venv c.lparams.length
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older) :=
            hb₁ ▸ (Hc.mlctx_wf.dropN _ hj₁).tr.wf
          have htypeNarrow' : TrExprS Hc.venv c.lparams Hcurrent.older
              (.forallE name dom body bi) (.forallE narrowDom narrowBody) :=
            .forallE hdomNarrowType hbodyNarrowType
              hdomNarrow hbodyNarrow
          rcases Hsynthesis.consumeConstructorParameter
              (name := name) (bi := bi)
              Hc.checking.tr.wf
              htypeNarrow'
              hconsumedWF
              ⟨narrowDom, hsourceDom, hsourceDomEq⟩ with
            ⟨next, hopenedNarrow, ⟨Hsynthesis'⟩⟩
          have hopenedNarrow' : TrExprS Hc.venv c.lparams
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older)
              (body.instantiate1 stats.params[i]!) next := by
            simpa [Expr.instantiate1_eq, Hcurrent.parameter] using
              hopenedNarrow
          have hsourceDomType := hdomNarrowType
          have Hcomparisons' : CheckedConstructorParameterPrefix
              Hc.venv c.lparams stats original (i + 1)
              (body.instantiate1 stats.params[i]!)
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older)
              (sourceDomains ++ [narrowDom]) :=
            .step Hcomparisons hparamAt Hcurrent.parameter hsourceDom hsourceDomType
              hsourceDomEq
          let Hbody :
              checkInductiveTypes.loopType.ReusedParameterScope
                Hsuffix i body :=
            { Hcurrent with fvars := Hcurrent.fvars.2 }
          exact ih (i := i + 1)
            (scope := (some (Hcurrent.fv, Hcurrent.deps),
              .vlam Hcurrent.paramType) :: Hcurrent.older)
            (current := next) (fullCurrent := fullBody.inst param')
            (hbound := by omega)
            (Hscope := fun hlt => Hbody.next hlt (fun _ _ h => h))
            (hscopeEq := fun hlt =>
              Hbody.nextOlder (Hbody.next hlt (fun _ _ h => h)) hlt)
            (hcompleteScope := fun heq => by
              have hdone : i + 1 = stats.params.size := by
                rw [hparams]
                exact heq
              exact Hbody.scope hdone)
            (Hsegment := Hsegment.push hparamAt)
            Hsynthesis' hopenedNarrow'
            (hopenedFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            Hcomparisons'
      · exact Hearly hi hforall (Hscope histats)
          Hsynthesis htypeNarrow htypeFull Hcomparisons
    · have hieq : i = decl.nparams := by omega
      subst i
      have hscope := hcompleteScope rfl
      subst scope
      exact Hresult Hsynthesis htypeNarrow htypeFull Hsegment Hcomparisons

theorem _root_.Lean4Lean.FVarsIn.getAppArgsList
    (H : FVarsIn P e) (ha : a ∈ e.getAppArgsList) : FVarsIn P a := by
  have H' : FVarsIn P
      (e.getAppFn.mkAppRevList e.getAppArgsRevList) := by
    rw [Expr.mkAppRevList_getAppArgsRevList]
    exact H
  have ha' : a ∈ e.getAppArgsRevList := by
    simpa [← Expr.getAppArgsList_reverse] using ha
  exact (FVarsIn.mkAppRevList.mp H').2 a ha'

/-- Abstracting a free variable removes precisely that variable from the
free-variable obligation. This is the structural lemma needed for nested
parameter replacement, which goes through the opaque executable `Expr.abstract`. -/
theorem _root_.Lean4Lean.FVarsIn.abstract1_of
    (H : FVarsIn (fun fv => fv = selected ∨ P fv) e) :
    FVarsIn P (Expr.abstract1 selected e k) := by
  induction e generalizing k <;>
    simp_all [Lean4Lean.FVarsIn, Expr.abstract1]
  case fvar fv =>
    split
    · trivial
    · rename_i hne
      rcases H with heq | hP
      · subst fv
        simp at hne
      · exact hP

/-- Abstracting a list of selected variables removes the entire selection
from the free-variable obligation. -/
theorem _root_.Lean4Lean.FVarsIn.abstractList_of
    (H : FVarsIn (fun fv => fv ∈ selected ∨ P fv) e) :
    FVarsIn P (e.abstractList selected k) := by
  induction selected generalizing e with
  | nil => simpa [Expr.abstractList] using H
  | cons selected rest ih =>
    simp only [Expr.abstractList]
    apply ih
    apply FVarsIn.abstract1_of
    exact H.mono fun fv hfv => by
      rcases hfv with hmem | hP
      · rcases List.mem_cons.mp hmem with heq | hrest
        · exact Or.inl heq
        · exact Or.inr (Or.inl hrest)
      · exact Or.inr (Or.inr hP)

/-- An index front built in the checking scope closes back to its
base, even when the executable `MLCtx` contains an interleaved ambient
prefix below that front.  `FrontFVLift` records the fact that each
new executable domain depends only on the preceding checking scope, while the
context equality identifies those dependency lists with the executable
declarations selected by `MLCtx.mkForall`. -/
theorem _root_.Lean4Lean.VerifyInductive.checkInductiveTypes.loopType.FrontFVLift.mkForall_fvarsIn_sourceBase
    {sourceDomains expandedDomains : List VExpr}
    {scope expanded : VLCtx} {shift : Lift}
    {m : TypeChecker.MLCtx} {env : VEnv} {Us : List Name}
    (H : Lean4Lean.VerifyInductive.checkInductiveTypes.loopType.FrontFVLift
      sourceDomains expandedDomains scope expanded shift)
    (Hm : MLCtxOnlyLams m) (Hmwf : m.WF env Us)
    (Hctx : VLCtx.IsDefEq env Us.length expanded m.vlctx)
    (hn : sourceDomains.length ≤ m.length) (body : Expr)
    (Hbody : body.FVarsIn (· ∈ scope.fvars)) :
    (m.mkForall sourceDomains.length hn body).FVarsIn
      (· ∈ VLCtx.fvars (scope.drop sourceDomains.length)) := by
  induction H generalizing m body with
  | zero => simpa using Hbody
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    cases m with
    | nil => cases Hctx
    | vlam current name type type' bi tail =>
      cases Hctx with
      | cons Htail _ _ =>
        have hnTail : sourceDomains.length ≤ tail.length := by
          apply Nat.le_of_succ_le_succ
          simpa using hn
        have Hdomain : type.FVarsIn (· ∈ scope.fvars) := by
          apply fvarsIn_iff.mpr
          refine ⟨hdeps, ?_⟩
          exact Hmwf.2.2.1.fvarsIn.mono fun _ _ => trivial
        have Habstract : (body.abstract1 fv).FVarsIn
            (· ∈ scope.fvars) := by
          apply FVarsIn.abstract1_of
          exact Hbody.mono fun current hcurrent => by
            simpa only [VLCtx.fvars_cons_some, List.mem_cons] using hcurrent
        simpa only [List.length_append, List.length_singleton,
          Nat.add_one, TypeChecker.MLCtx.mkForall,
          TypeChecker.MLCtx.dropN, List.drop_succ_cons] using
          ih Hm.tail_vlam Hmwf.1 Htail hnTail
            (.forallE name type (body.abstract1 fv) bi)
            ⟨Hdomain, Habstract⟩
    | vlet current name type value type' value' tail =>
      exact Hm.vlet_false.elim

theorem _root_.Lean4Lean.FVarsIn.abstractN_of {P : FVarId → Prop} {xs : List FVarId} :
    ∀ {e : Expr} {k}, FVarsIn (fun fv => fv ∈ xs ∨ P fv) e → FVarsIn P (e.abstractN xs k)
  | .bvar _, _, _ => trivial
  | .fvar v, k, h => by
    simp only [Expr.abstractN]
    split
    · trivial
    · rename_i hnone
      exact h.resolve_left (Expr.lastRevIdx?_eq_none_iff.1 hnone)
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .lit _, _, h => h
  | .mvar _, _, h => h
  | .mdata _ e, k, h => FVarsIn.abstractN_of (e := e) h
  | .proj _ _ e, k, h => FVarsIn.abstractN_of (e := e) h
  | .app f a, k, h => ⟨FVarsIn.abstractN_of (e := f) h.1, FVarsIn.abstractN_of (e := a) h.2⟩
  | .lam _ t b _, k, h => ⟨FVarsIn.abstractN_of (e := t) h.1, FVarsIn.abstractN_of (e := b) h.2⟩
  | .forallE _ t b _, k, h =>
    ⟨FVarsIn.abstractN_of (e := t) h.1, FVarsIn.abstractN_of (e := b) h.2⟩
  | .letE _ t v b _, k, h =>
    ⟨FVarsIn.abstractN_of (e := t) h.1, FVarsIn.abstractN_of (e := v) h.2.1,
      FVarsIn.abstractN_of (e := b) h.2.2⟩

theorem _root_.Lean4Lean.FVarsIn.abstract_fvarArray_of
    (fvars : List FVarId) (selected : Array Expr)
    (hselected : selected = (fvars.map Expr.fvar).toArray)
    (H : FVarsIn (fun fv => fv ∈ fvars ∨ P fv) e) :
    FVarsIn P (e.abstract selected) := by
  rw [hselected, Expr.abstractN_eq]
  exact H.abstractN_of

/-- `instantiateRev` introduces no free variables beyond those already in
the body and substitution array. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateRev
    (He : FVarsIn P e) (Hsubst : ∀ a ∈ subst, FVarsIn P a) :
    FVarsIn P (e.instantiateRev subst) := by
  rw [Expr.instantiateRev_eq, Expr.instantiate_eq]
  apply He.instantiateList
  intro a ha
  apply Hsubst a
  simpa using ha

/-- Range-restricted reverse instantiation has the same free-variable
discipline as the underlying simultaneous instantiation. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateRevRange
    (He : FVarsIn P e) (Hsubst : ∀ a ∈ subst, FVarsIn P a) :
    FVarsIn P (e.instantiateRevRange start stop subst) := by
  rw [Expr.instantiateRevRange_eq]
  apply He.instantiateRev
  intro a ha
  rcases Array.mem_iff_getElem.mp ha with ⟨i, hi, heq⟩
  have hi' : start + i < subst.size := by
    rw [Array.size_extract] at hi
    have hmin := Nat.min_le_right stop subst.size
    omega
  apply Hsubst a
  rw [← heq, Array.getElem_extract]
  exact Array.getElem_mem hi'

/-- Replacing universe parameters by universe expressions without metavariables
does not introduce a universe metavariable. -/
theorem _root_.Lean.Level.substParams'_hasMVar_false
    (Hu : u.hasMVar' = false)
    (Hs : ∀ name, (s name).hasMVar' = false) :
    (Lean.Level.substParams' s red u).hasMVar' = false := by
  induction u generalizing red with
  | zero | param | mvar => simp_all [Lean.Level.substParams', Lean.Level.hasMVar']
  | succ u ih =>
      simp only [Lean.Level.substParams', Lean.Level.hasMVar'] at Hu ⊢
      exact ih Hu
  | max u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]
  | imax u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelIMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]

/-- Universe-parameter instantiation preserves the expression free-variable
predicate when every supplied universe is metavariable-free. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateLevelParams
    (He : FVarsIn P e)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false) :
    FVarsIn P (e.instantiateLevelParams levelParams levels) := by
  rw [Expr.instantiateLevelParams_eq]
  have Hsubst : ∀ name,
      (((levelParams.idxOf? name).bind fun i => levels[i]?).getD
        (.param name)).hasMVar' = false := by
    intro name
    cases hidx : levelParams.idxOf? name with
    | none => simp [Lean.Level.hasMVar']
    | some i =>
      cases hget : levels[i]? with
      | none => simp [hget, Lean.Level.hasMVar']
      | some level =>
        simp only [Option.bind_some, hget, Option.getD_some]
        have hi : i < levels.length := by
          by_contra hnot
          have hnone := List.getElem?_eq_none (Nat.le_of_not_gt hnot)
          rw [hget] at hnone
          contradiction
        have heq : levels[i]'hi = level := by
          rw [← Option.some.injEq, ← hget]
          exact (List.getElem?_eq_getElem hi).symm
        exact Hlevels level (heq ▸ List.getElem_mem hi)
  induction e <;>
    simp_all [Expr.instantiateLevelParamsCore', Lean4Lean.FVarsIn,
      Lean.Level.substParams'_hasMVar_false]

theorem _root_.Lean4Lean.FVarsIn.mkAppRange_zero
    (hn : n ≤ args.size) (Hfn : FVarsIn P fn)
    (Hargs : ∀ arg ∈ args, FVarsIn P arg) :
    FVarsIn P (mkAppRange fn 0 n args) := by
  rw [Expr.mkAppRange_eq (l₁ := []) (l₂ := args.toList.take n)
    (l₃ := args.toList.drop n)]
  · rw [FVarsIn.mkAppList]
    refine ⟨Hfn, ?_⟩
    intro arg harg
    apply Hargs arg
    apply Array.mem_toList_iff.mp
    exact List.mem_of_mem_take harg
  · simp
  · rfl
  · simp [List.length_take, Nat.min_eq_left (by simpa using hn)]

theorem _root_.Lean4Lean.Expr.eqv_fvar_eq
    (H : (((.fvar fv : Expr) == e)) = true) : e = .fvar fv := by
  cases e <;> simp [(· == ·), Expr.eqv'] at H
  rename_i fv'
  have : fv = fv' := beq_iff_eq.mp H
  cases this
  rfl

/-- A constructor cannot reach its result before consuming every cached
parameter.  A valid result application would contain the current cached free
variable as argument `i`, whereas `ReusedParameterScope` proves that the tail
can mention only the strictly older cached parameters. -/
theorem checkConstructors.loopCtor.earlyParameterResult.WF
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Hscope : checkInductiveTypes.loopType.ReusedParameterScope
      Hsuffix i source)
    (hi : i < stats.params.size)
    (hforall : ¬ ∃ name dom body bi,
      source = .forallE name dom body bi) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i (fuel + 1) c).WF Q := by
  cases hvalid : AddInductive.isValidIndAppIdx stats source targetIdx
  · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
  · have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
    have hiArgs : i < source.getAppArgs.size := by omega
    have hparam : stats.params[i] = .fvar Hscope.fv := by
      have hparam' := Hscope.parameter
      simpa [hi] using hparam'
    have hargEq := checkPositivityStep.isValidIndAppIdx.param hvalid hi
    rw [hparam] at hargEq
    have harg : source.getAppArgs[i] = .fvar Hscope.fv :=
      Expr.eqv_fvar_eq hargEq
    have hsourceArg : source.getAppArgsList[i]? =
        some source.getAppArgs[i] := by
      rw [← Expr.getAppArgs_toList]
      simp [hiArgs]
    have hmem : source.getAppArgs[i] ∈ source.getAppArgsList :=
      List.mem_of_getElem? hsourceArg
    have hargScope := Hscope.fvars.getAppArgsList hmem
    rw [harg] at hargScope
    have hsuffixWF := Hscope.lift.wf Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf
    have hfresh : Hscope.fv ∉ Hscope.older.fvars :=
      (hsuffixWF.2.1 Hscope.fv Hscope.deps rfl).1
    exact False.elim (hfresh hargScope)

/-- Constructor-tail refinement in the parameter/field scope.
The executable traversal runs in the mutual-header context, but
the resulting `CtorTailWF` never mentions those ambient declarations. -/
theorem checkConstructors.loopCtor.tailRefinesScoped
    {decl : VInductDecl} {target : VInductiveType}
    {scope : VLCtx} {depth : Nat} {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) =
      some (VLevel.params decl.uvars))
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun classes => ConstructorTailCertificate Hc.venv decl target
        scope.toCtx depth narrowType classes ∧ ∃ k, Expr.ForallSpine type k) := by
  induction fuel generalizing c type scope narrowType fullType depth i with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases htrFull with ⟨fullForall, hfullForall, hfullTarget⟩
      cases htrNarrow with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hfullForall with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          have henv := Hc.checking.tr.wf
          rcases halign.forallE_align henv hdomNarrow hdomNarrowType hbodyNarrow with
            ⟨dom₀, body₀, hdom₀, hdom₀Type, _hdomU, hbody₀, _⟩
          rcases hconsume _ Hc.atCheckLCtx hdom₀ hdom₀Type with
            ⟨consumedDom₀, Hdom₀⟩
          have hparamNext : stats.params[i + 1]? = none := by
            rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
            omega
          have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
          rcases Hruntime.unannotatedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          cases isUnsafe with
          | false =>
            have Hpos := checkPositivity.refinesScoped
              (ctor := ctor) (idx := i) Hc Hruntime halign Hstats
              hconsume hlit hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            have Huniform := checkPositivity.uniformNormalFormScoped
              (ctor := ctor) (idx := i) Hc Hruntime halign Hstats hlevels
              hconsume hlit hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            have Hboth : (AddInductive.checkPositivity stats dom ctor i c).WF
                (fun recursive => decl.Positive Hc.venv scope.toCtx depth narrowDom ∧
                  ∃ normalized, Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowDom normalized ∧
                    decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) depth recursive
                      normalized) :=
              fun value hrun => ⟨Hpos value hrun, Huniform value hrun⟩
            refine checkConstructors.loopCtor.safeField.sourceWF
              (Q := fun classes => ConstructorTailCertificate Hc.venv decl target
                scope.toCtx depth (.forallE narrowDom narrowBody) classes ∧
                ∃ k, Expr.ForallSpine (.forallE name dom body bi) k)
              Hc hparamAt Hdom hbodyFull Hdom₀ hbody₀ Hboth ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              fieldType₀ hfield₀ htyped₀
              hfieldBound recursive hpositive bodyFull' _hbodyFullEq body₀' _hbody₀Eq
              hopenedFull _hopened₀
            let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
              Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
            let Hruntime' :
                checkInductiveTypes.loopType.FrontScopeEmbedding
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain hdomNarrowType
            have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
              Hdom Hdom₀ hdomNarrow hdomNarrowType hdeps
            have hscopeWF := halign'.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' halign' Hstats'
              (htargetLookup := by
                change Hc.venv.constants target.name = some target.toVConstant
                exact htargetLookup)
              (htargetWF := by
                change target.toVConstant.WF Hc.venv
                exact htargetWF)
              (htargetShape := by
                change decl.TypeShape Hc.venv params target
                exact htargetShape)
              hparamNext hlit hbound hlevels
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun rest htail => by
              rcases htail with ⟨htail, kspine, hspine⟩
              change ConstructorTailCertificate Hc.venv decl target
                (narrowDom :: scope.toCtx) (depth + 1) narrowBody rest at htail
              have hspine' : Expr.ForallSpine
                  (Expr.forallE name dom body bi) (kspine + 1) := by
                rw [Expr.instantiate1_eq] at hspine
                exact .step (Expr.ForallSpine.of_instantiate1'_fvar hspine)
              rcases htail.raw with ⟨doms, result, hwrap, hvalid, hhead⟩
              have hraw : ∃ doms result,
                  VExpr.forallE narrowDom narrowBody =
                    VExpr.wrapForalls doms result ∧
                  decl.ValidIndAppAt (some target.name) (depth + doms.length)
                    result ∧
                  result.getAppFnArgs.1 =
                    .const target.name (VLevel.params decl.uvars) := by
                refine ⟨narrowDom :: doms, result, ?_, ?_, hhead⟩
                · rw [hwrap]
                  rfl
                · have hlen : depth + (narrowDom :: doms).length =
                      depth + 1 + doms.length := by
                    simp
                    omega
                  rw [hlen]
                  exact hvalid
              have hfieldNarrow := VEnv.HasType.alignBack
                Hc.checking.tr.wf halign hdomNarrow hfield₀ htyped₀
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              have this : ConstructorTailCertificate Hc.venv decl target
                  scope.toCtx depth (.forallE narrowDom narrowBody) (recursive :: rest) := {
                shape := .field
                  (by simpa [Hstats.uvars] using hfieldNarrow)
                  (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                  (Or.inr hpositive.1)
                  (by simpa [Hstats.uvars] using hfieldEq)
                  (by simpa [Hstats.uvars] using hbodyTyped)
                  htail.shape
                isType := VEnv.IsType.forallE
                  ⟨_, by simpa [Hstats.uvars] using hfieldNarrow⟩
                  htail.isType
                raw := hraw
                uniform := .field ⟨_, by simpa [Hstats.uvars] using hfieldNarrow⟩
                  (.inr hpositive.2) htail.uniform }
              exact ⟨this, kspine + 1, hspine'⟩
          | true =>
            refine checkConstructors.loopCtor.unsafeField.sourceWF
              (Q := fun classes => ConstructorTailCertificate Hc.venv decl target
                scope.toCtx depth (.forallE narrowDom narrowBody) classes ∧
                ∃ k, Expr.ForallSpine (.forallE name dom body bi) k)
              Hc hparamAt Hdom hbodyFull Hdom₀ hbody₀ ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              fieldType₀ hfield₀ htyped₀
              hfieldBound bodyFull' _hbodyFullEq body₀' _hbody₀Eq
              hopenedFull _hopened₀
            let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
              Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
            let Hruntime' :
                checkInductiveTypes.loopType.FrontScopeEmbedding
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain hdomNarrowType
            have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
              Hdom Hdom₀ hdomNarrow hdomNarrowType hdeps
            have hscopeWF := halign'.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' halign' Hstats'
              (htargetLookup := by
                change Hc.venv.constants target.name = some target.toVConstant
                exact htargetLookup)
              (htargetWF := by
                change target.toVConstant.WF Hc.venv
                exact htargetWF)
              (htargetShape := by
                change decl.TypeShape Hc.venv params target
                exact htargetShape)
              hparamNext hlit hbound hlevels
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun rest htail => by
              rcases htail with ⟨htail, kspine, hspine⟩
              change ConstructorTailCertificate Hc.venv decl target
                (narrowDom :: scope.toCtx) (depth + 1) narrowBody rest at htail
              have hspine' : Expr.ForallSpine
                  (Expr.forallE name dom body bi) (kspine + 1) := by
                rw [Expr.instantiate1_eq] at hspine
                exact .step (Expr.ForallSpine.of_instantiate1'_fvar hspine)
              rcases htail.raw with ⟨doms, result, hwrap, hvalid, hhead⟩
              have hraw : ∃ doms result,
                  VExpr.forallE narrowDom narrowBody =
                    VExpr.wrapForalls doms result ∧
                  decl.ValidIndAppAt (some target.name) (depth + doms.length)
                    result ∧
                  result.getAppFnArgs.1 =
                    .const target.name (VLevel.params decl.uvars) := by
                refine ⟨narrowDom :: doms, result, ?_, ?_, hhead⟩
                · rw [hwrap]
                  rfl
                · have hlen : depth + (narrowDom :: doms).length =
                      depth + 1 + doms.length := by
                    simp
                    omega
                  rw [hlen]
                  exact hvalid
              have hfieldNarrow := VEnv.HasType.alignBack
                Hc.checking.tr.wf halign hdomNarrow hfield₀ htyped₀
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              have this : ConstructorTailCertificate Hc.venv decl target
                  scope.toCtx depth (.forallE narrowDom narrowBody) (false :: rest) := {
                shape := .field
                  (by simpa [Hstats.uvars] using hfieldNarrow)
                  (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                  (Or.inl (hunsafe rfl))
                  (by simpa [Hstats.uvars] using hfieldEq)
                  (by simpa [Hstats.uvars] using hbodyTyped)
                  htail.shape
                isType := VEnv.IsType.forallE
                  ⟨_, by simpa [Hstats.uvars] using hfieldNarrow⟩
                  htail.isType
                raw := hraw
                uniform := .field ⟨_, by simpa [Hstats.uvars] using hfieldNarrow⟩
                  (.inl (hunsafe rfl)) htail.uniform }
              exact ⟨this, kspine + 1, hspine'⟩
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
      · rcases htrNarrow.wf Hc.checking.tr.wf
          halign.wf with ⟨exprType, htype⟩
        have hisType := checkPositivityStep.isValidIndAppIdx.isType
          Hstats hi htrNarrow hvalid (by simpa [htarget] using htargetUvars)
          (by simpa [htarget] using htargetLookup)
          (by simpa [htarget] using htargetWF)
          (by simpa [htarget] using htargetShape)
          Hc.checking.tr.wf halign.wf
        have hvalidAt := checkPositivityStep.isValidIndAppIdx.validIndAppAt
          Hstats hi htrNarrow hvalid (Or.inr rfl) hlit
          (Hruntime.noIndConsts (decl.types.map (·.name)))
        have hshape : decl.CtorTailWF Hc.venv decl.types[targetIdx]
            scope.toCtx depth narrowType :=
          .result hvalidAt (by simpa [Hstats.uvars] using htype)
        have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalid
          (Hstats.indConstAt hi)
        rcases checkPositivityStep.TrExprS.constAppSpine htrNarrow hhead with
          ⟨levels', args', hspine, hlevels', _⟩
        have hlevelsEq : levels' = VLevel.params decl.uvars :=
          Option.some.inj (hlevels'.symm.trans hlevels)
        subst target
        exact checkConstructors.loopCtor.result.WF hforall hvalid
          ⟨⟨hshape, by simpa [Hstats.uvars] using hisType,
            ⟨[], narrowType, by simp [VExpr.wrapForalls],
              by simpa using hvalidAt, by rw [hspine, hlevelsEq]⟩,
            .result hvalidAt (by rw [hspine, hlevelsEq])⟩,
            0, .codomain hhead⟩

/-- Constructor-shape refinement from the cached-parameter
scope.  `tailCtx` is allowed to be definitionally equal to the normalized
constructor parameters, which is the relation supplied by the
header phase. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesScoped
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType narrowType fullType : VExpr}
    {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) =
      some (VLevel.params decl.uvars))
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      ownParams.reverse scope.toCtx)
    (htailEq : narrowType = tail)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type) := by
  have Htail := checkConstructors.loopCtor.tailRefinesScoped
    (params := params) (ctor := ctor) (fuel := fuel) Hc Hruntime halign Hstats hi
    htarget htargetUvars htargetLookup htargetWF htargetShape hparamAt
    hconsume hlit hunsafe hbound hlevels htrNarrow htrFull
  exact Htail.mono fun _ htail => by
    obtain ⟨htail, _⟩ := htail
    subst narrowType
    have hrebuild := (VExpr.takeForalls_rebuild htake).1
    have htailType : Hc.venv.IsType decl.uvars ownParams.reverse tail :=
      htail.isType.defeqDFC Hc.checking.tr.wf.ordered
        (htailCtx.symm Hc.checking.tr.wf.ordered)
    have hnormalizedType : Hc.venv.IsType decl.uvars [] normalized := by
      rw [hrebuild]
      exact VEnv.IsType.wrapForalls
        (by simpa using htailCtx.isType) (by simpa using htailType)
    have hctorType : Hc.venv.IsType decl.uvars [] ctorVal.type :=
      hnormalizedType.defeqU_l Hc.checking.tr.wf (by trivial)
        ⟨exprType, hctor.symm⟩
    exact ⟨⟨normalized, ownParams, tail, exprType, scope.toCtx,
      hctor, htake, hparams, htailCtx, htail.shape⟩, hctorType⟩

/-- Close a constructor-parameter telescope covering all parameters directly
against the verified field tail.  In particular, the normalized constructor
type and its `takeForalls` decomposition are outputs of the
telescope rather than assumptions reconstructed by the caller. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesOfTelescope
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    {source : Expr} {current fullType : VExpr} {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current decl.nparams 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hparamAt : stats.params[decl.nparams]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) =
      some (VLevel.params decl.uvars))
    (hparams : decl.ParamsDefEq Hc.venv params Hsynthesis.params)
    (htrNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source decl.nparams fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type) := by
  have hindices : Hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
  have htake :
      (VExpr.wrapForalls Hsynthesis.params current).takeForalls decl.nparams =
        some (Hsynthesis.params, current) := by
    simpa [Hsynthesis.parameterCount] using
      VExpr.takeForalls_wrapForalls Hsynthesis.params current
  have htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      Hsynthesis.params.reverse scope.toCtx := by
    have hrefl : VEnv.IsDefEqCtx Hc.venv decl.uvars []
        scope.toCtx scope.toCtx :=
      .refl (by simpa [Hstats.uvars] using Hsynthesis.scopeWF.toCtx)
    simpa [Hsynthesis.scopeCtx, hindices] using hrefl
  apply checkConstructors.loopCtor.ctorShapeRefinesScoped
    (ctor := ctor) (fuel := fuel) Hc Hruntime halign Hstats hi htarget
    htargetUvars htargetLookup htargetWF htargetShape
    hparamAt hconsume hlit hunsafe hbound hlevels
    (normalized := VExpr.wrapForalls Hsynthesis.params current)
    (tail := current) (exprType := Hsynthesis.exprType)
    (ownParams := Hsynthesis.params)
  · simpa [constructorTelescopeTarget, hindices, Hstats.uvars] using
      Hsynthesis.header
  · exact htake
  · exact hparams
  · exact htailCtx
  · rfl
  · exact htrNarrow
  · exact htrFull

/-- End-to-end constructor telescope refinement in a single
environment.  The source constructor is translated in the
empty scope; the executable closed-type result supplies its translation in
the executable context.  Cached common parameters are handled by
`parameterTelescopeWF`, and all remaining binders are checked by the
positivity refinement in the checking context. -/
theorem checkConstructors.loopCtor.refinesCtorShape
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hsuffix.parameterDecls Hc.chk.vlctx)
    (hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (Hctor : TrSourceConstRaw Hc.venv c.lparams ctor source ctorVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source checkedType fullType checkedType')
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (htargetUvars : target.uvars = decl.uvars)
    (htargetLookup : Hc.venv.constants target.name =
      some target.toVConstant)
    (htargetWF : target.toVConstant.WF Hc.venv)
    (htargetShape : decl.TypeShape Hc.venv params target)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel ≈ .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) =
      some (VLevel.params decl.uvars)) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source 0 fuel c).WF
      (fun classes => ∃ tail tailTarget,
        ParameterPrefix stats 0 source tail ∧
        ∃ sourceDomains,
        CheckedConstructorParameterPrefix Hc.venv c.lparams stats source
          decl.nparams tail Hsuffix.parameterDecls sourceDomains ∧
        TrExprS Hc.venv c.lparams Hsuffix.parameterDecls tail tailTarget ∧
        ConstructorTailCertificate Hc.venv decl target
          Hsuffix.parameterDecls.toCtx 0 tailTarget classes ∧
        Nonempty
          (checkInductiveTypes.loopType.ScopedHeaderTelescope
            Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
            Hsuffix.parameterDecls tailTarget stats.params.size 0) ∧
        decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type ∧
        ∃ k, Expr.ForallSpine source k) := by
  have hnoFVars : FVarsIn (fun _ => False) source := by
    simpa [VLCtx.fvars] using Hctor.type.fvarsIn
  by_cases hzero : decl.nparams = 0
  ·
    have hscopeLength : Hsuffix.parameterDecls.length = 0 := by
      simpa [Hstats.params_size, hzero] using
        Hsuffix.parameterDecls_length
    have hscope : Hsuffix.parameterDecls = [] :=
      List.eq_nil_of_length_eq_zero hscopeLength
    have hparams : decl.ParamsDefEq Hc.venv params [] := by
      change VEnv.IsDefEqCtx Hc.venv decl.uvars [] params.reverse []
      simpa [hscope, VLCtx.toCtx] using hparamsCtx
    have hctorWF : Hc.venv.IsDefEqU c.lparams.length []
        ctorVal.type ctorVal.type :=
      Hctor.type.wf Hc.checking.tr.wf.ordered (by trivial)
    rcases hctorWF with ⟨exprType, hctorTyped⟩
    cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hparamAt : stats.params[0]? = none := by
        rw [Array.getElem?_eq_none_iff]
        rw [Hstats.params_size, hzero]
        omega
      have Hshape :
          (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor
            targetIdx source 0 (fuel + 1) c).WF
            (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
              Hc.venv.IsType decl.uvars [] ctorVal.type) := by
        exact checkConstructors.loopCtor.ctorShapeRefinesScoped
          (decl := decl) (ctorVal := ctorVal) (params := params)
          (type := source) (i := 0) (ctor := ctor) (fuel := fuel + 1) Hc
          (narrowType := ctorVal.type) (fullType := fullType)
          (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
            Hc Hsuffix) halign
          Hstats hi htarget htargetUvars htargetLookup htargetWF htargetShape
          hparamAt
          hconsume hlit hunsafe hbound hlevels
          (normalized := ctorVal.type) (tail := ctorVal.type)
          (exprType := exprType) (ownParams := [])
          (by simpa [Hstats.uvars] using hctorTyped)
          (by rw [hzero]; rfl) hparams
          (by
            rw [hscope]
            change VEnv.IsDefEqCtx Hc.venv decl.uvars [] [] []
            exact VEnv.IsDefEqCtx.refl (by trivial))
          rfl (by simpa [hscope] using Hctor.type)
          (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      have Htail := checkConstructors.loopCtor.tailRefinesScoped
        (params := params) (type := source) (i := 0) (ctor := ctor)
        (fuel := fuel + 1) Hc
        (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
          Hc Hsuffix) halign
        Hstats hi htarget htargetUvars htargetLookup htargetWF
        htargetShape hparamAt hconsume hlit hunsafe hbound hlevels
        (by simpa [hscope] using Hctor.type)
        (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      intro out hout
      have Hchecked := Hshape out hout
      have Htail' := Htail out hout
      let Hinitial := ConstructorSynthesisState.initial (env := Hc.venv) (Us := c.lparams)
        (ctorVal := ctorVal) (by simpa [Hstats.uvars] using Hchecked.2)
      exact ⟨source, ctorVal.type,
        .done (by rw [Hstats.params_size, hzero]),
        [], by simpa [hzero, hscope] using
          (CheckedConstructorParameterPrefix.zero :
            CheckedConstructorParameterPrefix Hc.venv c.lparams stats source
              0 source [] []),
        by simpa [hscope] using Hctor.type,
        by simpa [hscope] using Htail'.1,
        by simpa [hscope, Hstats.params_size, hzero] using
          (show Nonempty _ from ⟨Hinitial⟩),
        Hchecked.1, Hchecked.2, Htail'.2⟩
  by_cases hforall : ∃ name dom body bi,
      source = .forallE name dom body bi
  · rcases hforall with ⟨name, dom, body, bi, rfl⟩
    have htype : Hc.venv.IsType c.lparams.length [] ctorVal.type := by
      rcases TrExpr.forallE_source
          (Hctor.type.trExpr Hc.checking.tr.wf (by trivial)) with
        ⟨dom', body', _hdom, _hbody, hdomType, hbodyType, heq⟩
      exact (VEnv.IsType.forallE hdomType hbodyType).defeqU_l
        Hc.checking.tr.wf (by trivial) heq
    let Hinitial := ConstructorSynthesisState.initial htype
    apply checkConstructors.loopCtor.parameterTelescopeWF
      (decl := decl) (ctorVal := ctorVal) Hc
      (Q := fun classes => ∃ tail,
        ∃ tailTarget,
        ParameterPrefix stats 0 (.forallE name dom body bi) tail ∧
        ∃ sourceDomains,
        CheckedConstructorParameterPrefix Hc.venv c.lparams stats
          (.forallE name dom body bi) decl.nparams tail
          Hsuffix.parameterDecls sourceDomains ∧
        TrExprS Hc.venv c.lparams Hsuffix.parameterDecls tail tailTarget ∧
        ConstructorTailCertificate Hc.venv decl target
          Hsuffix.parameterDecls.toCtx 0 tailTarget classes ∧
        Nonempty
          (checkInductiveTypes.loopType.ScopedHeaderTelescope
            Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
            Hsuffix.parameterDecls tailTarget stats.params.size 0) ∧
        decl.CtorShape Hc.venv params target ctorVal ∧
        Hc.venv.IsType decl.uvars [] ctorVal.type ∧
        ∃ k, Expr.ForallSpine (.forallE name dom body bi) k)
      (Hresult := by
        intro source' current' fullCurrent' fuel' sourceDomains
          Hsynthesis' htrNarrow htrFull Hsegment' Hcomparisons
        have hindices : Hsynthesis'.indices = [] :=
          List.eq_nil_of_length_eq_zero Hsynthesis'.indexCount
        have hscopeCtx : Hsuffix.parameterDecls.toCtx =
            Hsynthesis'.indices.reverse ++ Hsynthesis'.params.reverse :=
          @checkInductiveTypes.loopType.ScopedHeaderTelescope.scopeCtx
            Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
            Hsuffix.parameterDecls current' decl.nparams 0 Hsynthesis'
        have hparams : decl.ParamsDefEq Hc.venv
            params Hsynthesis'.params := by
          change VEnv.IsDefEqCtx Hc.venv decl.uvars []
            params.reverse Hsynthesis'.params.reverse
          simpa [hscopeCtx, hindices] using hparamsCtx
        have hparamAt : stats.params[decl.nparams]? = none := by
          rw [Array.getElem?_eq_none_iff]
          exact Nat.le_of_eq Hstats.params_size
        have Hshape :
            (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor
              targetIdx source' decl.nparams (fuel' + 1) c).WF
              (fun _ => decl.CtorShape Hc.venv params target ctorVal ∧
                Hc.venv.IsType decl.uvars [] ctorVal.type) := by
          exact checkConstructors.loopCtor.ctorShapeRefinesOfTelescope
            (ctor := ctor) (fuel := fuel' + 1) Hc
            (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
              Hc Hsuffix) halign
            Hstats Hsynthesis' hi htarget htargetUvars htargetLookup
            htargetWF htargetShape hparamAt hconsume hlit hunsafe
            hbound hlevels hparams htrNarrow htrFull
        have Htail := checkConstructors.loopCtor.tailRefinesScoped
          (params := params) (type := source') (i := decl.nparams)
          (ctor := ctor) (fuel := fuel' + 1) Hc
          (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
            Hc Hsuffix) halign
          Hstats hi htarget htargetUvars htargetLookup htargetWF
          htargetShape hparamAt hconsume hlit hunsafe hbound hlevels
          htrNarrow htrFull
        intro out hout
        have Hchecked := Hshape out hout
        have Htail' := Htail out hout
        have HsegmentComplete : ParameterSegment stats 0
            stats.params.size (.forallE name dom body bi) source' := by
          simpa only [Hstats.params_size] using Hsegment'
        have Hprefix := HsegmentComplete.complete rfl
        rcases Htail'.2 with ⟨k, hspine⟩
        exact ⟨source', current', Hprefix,
          sourceDomains, Hcomparisons, htrNarrow, Htail'.1,
          by simpa [Hstats.params_size] using
            (show Nonempty _ from ⟨Hsynthesis'⟩),
          Hchecked.1, Hchecked.2,
          stats.params.size - 0 + k,
          Hprefix.forallSpine Hstats.paramFVars hspine⟩)
      (Hearly := by
        intro source' scope' current' fullCurrent' i' fuel' sourceDomains hi'
          hforall Hscope' _Hsynthesis' _htrNarrow _htrFull _Hcomparisons
        exact checkConstructors.loopCtor.earlyParameterResult.WF
          (fuel := fuel') Hc Hscope'
          (by simpa [Hstats.params_size] using hi') hforall)
      Hstats.params_size (by omega) (.done)
      (fun h =>
        checkInductiveTypes.loopType.ReusedParameterScope.ofNoFVars h hnoFVars)
      (fun h =>
        (checkInductiveTypes.loopType.ReusedParameterScope.ofNoFVars
          h hnoFVars).older_eq_nil h |>.symm)
      (by
        intro hdone
        have hlength := Hsuffix.parameterDecls_length
        have hempty : Hsuffix.parameterDecls = [] :=
          List.eq_nil_of_length_eq_zero (by
            rw [hlength, Hstats.params_size, hdone])
        exact hempty.symm)
      Hinitial Hctor.type
      (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      CheckedConstructorParameterPrefix.zero
  · cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hiStats : 0 < stats.params.size := by
        rw [Hstats.params_size]
        omega
      exact checkConstructors.loopCtor.earlyParameterResult.WF
        (Hsuffix := Hsuffix) (fuel := fuel) Hc
        (checkInductiveTypes.loopType.ReusedParameterScope.ofNoFVars
          (Hsuffix := Hsuffix) hiStats hnoFVars)
        (by omega) hforall

/-- What the constructor loop establishes about the parameter prefix of one executable
constructor: the prefix (`ParameterPrefix`) exists, and the checked type is a pure syntactic
forall spine. -/
def ConstructorParamPrefixAt (stats : AddInductive.InductiveStats) (ctor : Constructor) : Prop :=
  (∃ tail, ParameterPrefix stats 0 ctor.type tail) ∧ ∃ k, Expr.ForallSpine ctor.type k

/-- Parameter prefixes of every constructor, selected by family and
constructor positions. -/
structure ConstructorParameterPrefixes
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) : Prop where
  replay : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    ∃ tail, ParameterPrefix stats 0
      indTypes[familyIdx].ctors[ctorIdx].type tail
  /-- Every executable constructor type is a pure syntactic forall spine,
  as walked by the executable check. -/
  spines : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    ∃ k, Expr.ForallSpine indTypes[familyIdx].ctors[ctorIdx].type k

theorem ConstructorParameterPrefixes.ofAll
    {stats : AddInductive.InductiveStats} {indTypes : Array InductiveType}
    (H : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
      ConstructorParamPrefixAt stats indTypes[familyIdx].ctors[ctorIdx]) :
    ConstructorParameterPrefixes stats indTypes where
  replay familyIdx hfamily ctorIdx hctor := (H familyIdx hfamily ctorIdx hctor).1
  spines familyIdx hfamily ctorIdx hctor := (H familyIdx hfamily ctorIdx hctor).2

/-- The checked parameter prefix and tail of one executable constructor, with the field
classification `classes` its positivity check returned. -/
def CheckedConstructorTailAt
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (source : Constructor) (classes : List Bool) : Prop :=
  ∃ ctorVal tail tailTarget sourceDomains,
    ctorVal ∈ target.ctors ∧
    TrSourceConstRaw env Us source.name source.type ctorVal ∧
    ParameterPrefix stats 0 source.type tail ∧
    CheckedConstructorParameterPrefix env Us stats source.type
      stats.params.size tail scope sourceDomains ∧
    TrExprS env Us scope tail tailTarget ∧
    ConstructorTailCertificate env decl target scope.toCtx 0 tailTarget classes ∧
    Nonempty
      (checkInductiveTypes.loopType.ScopedHeaderTelescope
        env Us (constructorTelescopeTarget ctorVal) scope tailTarget
        stats.params.size 0)

/-- The checked parameter prefixes and tails (`CheckedConstructorTailAt`) of all
constructors `ctors` of one family, with their field classifications `classes`. -/
def FamilyConstructorTails
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (ctors : List Constructor)
    (classes : List (List Bool)) : Prop :=
  classes.length = ctors.length ∧
  ∀ i (hi : i < ctors.length),
    CheckedConstructorTailAt env Us scope stats decl target ctors[i] classes[i]!

/-- The checked tail of every constructor, by family and constructor position, with the
field classifications `classes` returned by the executable constructor check. -/
structure ConstructorTails
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (indTypes : Array InductiveType) (classes : List (List (List Bool))) : Prop where
  size_eq : indTypes.size = decl.types.length
  classes_length : classes.length = indTypes.size
  row_length : ∀ (familyIdx : Nat), familyIdx < indTypes.size →
    classes[familyIdx]!.length = indTypes[familyIdx]!.ctors.length
  replay : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    CheckedConstructorTailAt env Us scope stats decl
      decl.types[familyIdx] indTypes[familyIdx].ctors[ctorIdx] classes[familyIdx]![ctorIdx]!

theorem ConstructorTails.ofAll
    {env : VEnv} {Us : List Name} {scope : VLCtx}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {indTypes : Array InductiveType} {classes : List (List (List Bool))}
    (hsize : indTypes.size = decl.types.length)
    (hclasses : classes.length = indTypes.size)
    (H : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size),
      FamilyConstructorTails env Us scope stats decl
        (decl.types[familyIdx]'(hsize ▸ hfamily)) indTypes[familyIdx].ctors
        classes[familyIdx]!) :
    ConstructorTails env Us scope stats decl indTypes classes where
  size_eq := hsize
  classes_length := hclasses
  row_length familyIdx hfamily := by
    rw [getElem!_pos indTypes familyIdx hfamily]
    exact (H familyIdx hfamily).1
  replay familyIdx hfamily ctorIdx hctor := (H familyIdx hfamily).2 ctorIdx hctor

end VerifyInductive
end Lean4Lean
