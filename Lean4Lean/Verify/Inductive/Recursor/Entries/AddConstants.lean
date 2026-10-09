import Lean4Lean.Verify.Inductive.Recursor.Entries.Targets

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact certificate for a suffix of local declarations introduced by
`withLocalDecl`; its domains are recorded in the same outermost-to-innermost
order used by generated recursor telescopes. -/
inductive MLCtxLamPrefix : TypeChecker.MLCtx → Nat → List VExpr → Prop
  | nil (c : TypeChecker.MLCtx) : MLCtxLamPrefix c 0 []
  | cons : MLCtxLamPrefix c n domains →
      MLCtxLamPrefix (.vlam fv name type type' bi c) (n + 1)
        (domains ++ [type'])

theorem MLCtxLamPrefix.le
    (H : MLCtxLamPrefix c n domains) : n ≤ c.length := by
  induction H with
  | nil => simp
  | cons _ ih => simpa using Nat.succ_le_succ ih

/-- Every bounded prefix of an all-lambda checker context has an exact
`MLCtxLamPrefix` certificate. This packages the structural induction needed
when a later proof walks a recent suffix one declaration at a time. -/
theorem MLCtxOnlyLams.lamPrefix
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    ∃ domains, MLCtxLamPrefix c n domains := by
  induction n generalizing c with
  | zero => exact ⟨[], .nil c⟩
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      rcases ih H.tail_vlam (Nat.le_of_succ_le_succ hn) with
        ⟨domains, Hprefix⟩
      exact ⟨domains ++ [type'], Hprefix.cons⟩
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Extend a `FrontScopeEmbedding` by a recent prefix of lambda declarations that was also
opened in a checker context aligned with the base scope. Each domain is the
checker translation transported along the alignment, so no runtime
translation is restricted, and the resulting scope stays aligned with the
checker context. -/
theorem MLCtxLamPrefix.extendFrontScopeEmbeddingAligned
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF)
    (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.FrontScopeEmbedding env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx)
    {chk : TypeChecker.MLCtx} (hchkWF : chk.WF env Us)
    (hn : n ≤ chk.length) (hagree : MLCtxTopAgree runtime chk n)
    (hbaseAlign : VLCtx.IsDefEq env Us.length baseScope (chk.dropN n hn).vlctx) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FrontScopeEmbedding env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop Hscope.frontSourceDomains.length =
          baseScope.drop Hbase.frontSourceDomains.length ∧
        (∃ newDomains,
          newDomains.length = n ∧
          Hscope.frontSourceDomains =
            Hbase.frontSourceDomains ++ newDomains) ∧
        VLCtx.IsDefEq env Us.length scope chk.vlctx := by
  induction H generalizing chk with
  | nil runtime =>
    exact ⟨baseScope, Hbase,
      by simp [TypeChecker.MLCtx.fvarRevList], rfl, ⟨[], rfl, by simp⟩,
      by simpa using hbaseAlign⟩
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    cases hagree with
    | @vlam _ chkTail _ hagreeTail _ _ _ _ t₂ _ =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, hfresh, Htype, HtypeType⟩
    rcases hchkWF with ⟨hchkTailWF, hfreshC, Htype₀, Htype₀Type⟩
    have hcurrentFresh : fv ∉ tail.vlctx.fvars :=
      HtailWF.tr.find?_eq_none.1 hfresh
    have htailUp : IsFVarUpSet
        (fun fv' =>
          fv' ∈ tail.fvarRevList n Hprefix.le ++ baseScope.fvars)
        tail.vlctx := by
      apply (IsFVarUpSet.congr HtailWF.tr.wf.fvwf ?_).mp hup.1
      intro fv' hfv'
      constructor
      · intro h
        rcases List.mem_cons.mp h with hcurrent | h
        · exact False.elim (hcurrentFresh (hcurrent ▸ hfv'))
        · exact h
      · exact List.mem_cons_of_mem _
    have hnTail : n ≤ chkTail.length := by simpa using hn
    rcases ih HtailWF Hbase htailUp hchkTailWF hnTail hagreeTail
        (by simpa using hbaseAlign) with
      ⟨tailScope, HtailScope, htailScopeFVars, htailBase,
        ⟨tailDomains, htailDomains, htailFront⟩, halignTail⟩
    have hdepsFull : ∀ dep ∈ type.fvarsList,
        dep ∈ fv :: tail.fvarRevList n Hprefix.le ++ baseScope.fvars := by
      exact hup.2 (by simp)
    have hdeps : type.fvarsList ⊆ tailScope.fvars := by
      intro dep hdep
      rw [htailScopeFVars]
      have hselected := hdepsFull dep hdep
      rcases List.mem_cons.mp hselected with hcurrent | hselected
      · exact False.elim (hcurrentFresh (hcurrent ▸ Htype.fvarsList hdep))
      · exact hselected
    have halignTailSymm := halignTail.symm henv.ordered
    obtain ⟨narrowType, HnarrowType⟩ := Htype₀.defeqDFC henv halignTailSymm
    have hNU := Htype₀.uniq henv halignTailSymm HnarrowType
    have HnarrowIsType : env.IsType Us.length tailScope.toCtx narrowType :=
      (Htype₀Type.defeqU_l henv hchkTailWF.tr.wf.toCtx hNU).defeqDFC
        henv.ordered halignTailSymm.defeqCtx
    have Hweak : TrExprS env Us HtailScope.expanded type
        (narrowType.lift' HtailScope.shift) := by
      simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
        HtailScope.context.wf
    have HtargetEq := Hweak.uniq henv HtailScope.context Htype
    have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
        type' :=
      HtypeType.defeqDFC henv.ordered
        (HtailScope.context.symm henv.ordered).defeqCtx
    rcases HtargetType with ⟨u, HtargetType⟩
    have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
        (narrowType.lift' HtailScope.shift) type' (.sort u) :=
      HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
    let Hnext := HtailScope.withIndex
      HruntimeWF
      hdeps name bi type HnarrowType Hdomain HnarrowIsType
    have hfreshScope : fv ∉ tailScope.fvars := by
      rw [halignTail.fvars]
      exact hchkTailWF.tr.find?_eq_none.1 hfreshC
    have hNU' := hNU.symm.defeqDFC henv.ordered halignTailSymm.defeqCtx
    obtain ⟨v, hv⟩ := HnarrowIsType
    refine ⟨_, Hnext, ?_, ?_, ⟨tailDomains ++ [narrowType], ?_, ?_⟩, ?_⟩
    · simp [htailScopeFVars, TypeChecker.MLCtx.fvarRevList]
    · dsimp [Hnext, checkInductiveTypes.loopType.FrontScopeEmbedding.withIndex]
      simpa only [List.length_append, List.length_singleton,
        List.drop_succ_cons] using htailBase
    · simp [htailDomains]
    · dsimp [Hnext, checkInductiveTypes.loopType.FrontScopeEmbedding.withIndex]
      rw [htailFront]
      simp [List.append_assoc]
    · exact halignTail.consAligned hfreshScope hdeps
        (hNU'.of_l henv halignTail.wf.toCtx hv)

/-- A list of executable constants and abstract constants installed in lockstep.
Each translation and typing premise is stated in
the environment at the exact point where that constant is introduced. -/
inductive AddConstants (safety : DefinitionSafety) :
    Environment → VEnv → List (ConstantInfo × VConstVal) →
      Environment → VEnv → Prop
  | nil : AddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none →
    ¬ Kernel.Environment.primitives.contains ci.name →
    TrConstVal safety venv ci ci' →
    ci'.toVConstant.WF venv →
    venv.addConst ci.name ci'.toVConstant = some venv' →
    ci.deltaValue? = none →
    AddConstants safety (env.add ci) venv' rest outEnv outVEnv →
    AddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

theorem AddConstants.append
    (H₁ : AddConstants safety env venv entries middleEnv middleVEnv)
    (H₂ : AddConstants safety middleEnv middleVEnv rest outEnv outVEnv) :
    AddConstants safety env venv (entries ++ rest) outEnv outVEnv := by
  induction H₁ with
  | nil => exact H₂
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact .cons hn hnprim htr hwf hadd hdelta (ih H₂)

/-- Projection metadata commutes with an ordinary lockstep constant batch. -/
theorem AddConstants.addProjections
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    AddConstants safety env (venv.addProjections projections) entries
      outEnv (outVEnv.addProjections projections) := by
  induction H with
  | nil => exact .nil
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact .cons hn hnprim (htr.mono VEnv.addProjections_le)
      (hwf.mono VEnv.addProjections_le)
      (by rw [VEnv.addProjections_addConst, hadd]; rfl) hdelta ih

/-- Registered case eliminators commute with an ordinary lockstep constant batch. -/
theorem AddConstants.addEliminators
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    AddConstants safety env (venv.addEliminators es) entries
      outEnv (outVEnv.addEliminators es) := by
  induction H with
  | nil => exact .nil
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact .cons hn hnprim (htr.mono VEnv.addEliminators_le)
      (hwf.mono VEnv.addEliminators_le)
      (by rw [VEnv.addEliminators_addConst, hadd]; rfl) hdelta ih

theorem AddConstants.hasPrimitives
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (Hprimitives : venv.HasPrimitives) : outVEnv.HasPrimitives := by
  induction H with
  | nil => exact Hprimitives
  | cons _hn hnprim _htr _hwf hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnonprim :
        Kernel.Environment.primitives.contains ci.name = false := by
      cases h : Kernel.Environment.primitives.contains ci.name <;>
        simp_all
    exact ih (Lean4Lean.VEnv.HasPrimitives.addConst Hprimitives
      hnonprim hadd)

/-- A lockstep constant installation also holds over a larger abstract source
environment. The executable environments and the generated constants are unchanged;
translations and typing are weakened monotonically, and the resulting target
extends the given abstract target. -/
theorem AddConstants.rebase
    (H : AddConstants checkSafety prodEnv base entries outProd outBase)
    (Hvalid : CheckingEnv safety prodEnv largerBase)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase) :
    ∃ largerOut,
      AddConstants safety prodEnv largerBase entries outProd largerOut ∧
      outBase ≤ largerOut := by
  induction H generalizing largerBase with
  | nil => exact ⟨largerBase, .nil, hbase⟩
  | cons hn hnprim htr hwf hadd hdelta _Htail ih =>
    rename_i baseHead ci ci' baseNext rest outProd outBase prodHead
    have hexists : ∃ largerNext,
        largerBase.addConst ci.name ci'.toVConstant = some largerNext := by
      unfold VEnv.addConst
      cases hfind : largerBase.constants ci.name with
      | none => simp
      | some existing =>
        exfalso
        rcases Hvalid.find?_iff.mpr ⟨existing, hfind⟩ with
          ⟨source, hsource, _⟩
        rw [hn] at hsource
        contradiction
    rcases hexists with ⟨largerNext, hlargerAdd⟩
    have htrLarger :
        TrConstVal safety largerBase ci ci' :=
      ⟨(htr.1.sf_mono hsafety).mono hbase, htr.2⟩
    have hwfLarger : ci'.toVConstant.WF largerBase := hwf.mono hbase
    have HvalidNext : CheckingEnv safety (prodHead.add ci)
        largerNext :=
      Hvalid.add hn htrLarger.1 hwfLarger hlargerAdd hdelta
    have hnext : baseNext ≤ largerNext :=
      VEnv.addConst_mono hbase hadd hlargerAdd
    rcases ih HvalidNext hnext with ⟨largerOut, Htail, hout⟩
    exact ⟨largerOut,
      .cons hn hnprim htrLarger hwfLarger hlargerAdd hdelta Htail, hout⟩

/-- A lockstep installation checked at a stronger visibility level is also a
valid installation for every weaker observer. The installed abstract
constants and all freshness/typing facts are unchanged. -/
theorem AddConstants.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : AddConstants checkSafety prodEnv venv entries outEnv outVEnv) :
    AddConstants safety prodEnv venv entries outEnv outVEnv := by
  induction H with
  | nil => exact .nil
  | cons hn hnprim htr hwf hadd hdelta _Htail ih =>
    exact .cons hn hnprim ⟨htr.1.sf_mono hsafety, htr.2⟩ hwf hadd
      hdelta ih

theorem AddConstants.quotInit_eq
    (H : AddConstants safety prodEnv venv entries outEnv outVEnv) :
    outEnv.quotInit = prodEnv.quotInit := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => exact ih

/-- Lockstep installation preserves executable/abstract alignment (`Aligned`). This is
the kernel-environment component of `AddInduct`; it follows from the lockstep installation
and need not be supplied by a later compilation proof. -/
theorem AddConstants.aligned
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (Haligned : Aligned safety env.constants venv) :
    Aligned safety outEnv.constants outVEnv := by
  induction H with
  | nil => exact Haligned
  | cons hn _hnprim htr _hwf hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← Haligned.map_wf.find?'_eq_find?]
      exact hn
    exact ih (Haligned.const hnMap htr.1 hadd rfl)

/-- If every newly installed executable constant is hidden from an observer,
the observer's abstract environment is unchanged across the whole lockstep
installation. -/
theorem AddConstants.trEnvIgnore
    (H : AddConstants checkSafety prodEnv venv entries outEnv outVEnv)
    (hhidden : ∀ entry ∈ entries, ¬ observerSafety ≤ entry.1.safety)
    (htr : TrEnv' observerSafety prodEnv.constants quotInit observerEnv) :
    TrEnv' observerSafety outEnv.constants quotInit observerEnv := by
  induction H with
  | nil => exact htr
  | cons hn _hnprim _hentry _hwf _hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← htr.map_wf.find?'_eq_find?]
      exact hn
    have htrHead : TrEnv' observerSafety
        (envHead.constants.insert ci.name ci) quotInit observerEnv :=
      TrEnv'.ignore hnMap (hhidden (ci, ci') (by simp)) htr
    exact ih (fun entry hentry => hhidden entry (by simp [hentry])) htrHead

/-- Constants introduced by a lockstep installation have no delta value,
so every delta-bearing entry in the output constant map was already present
in the source map. -/
theorem AddConstants.deltaConservative
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (Halign : Aligned safety env.constants venv) :
    ∀ {name ci}, outEnv.constants.find? name = some ci →
      ci.deltaValue?.isSome → env.constants.find? name = some ci := by
  induction H with
  | nil => intro name ci hfind _; exact hfind
  | cons hn _hnprim htr _hwf hadd hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    intro name found hfind hfoundDelta
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← Halign.map_wf.find?'_eq_find?]
      exact hn
    have Halign' : Aligned safety
        (envHead.constants.insert ci.name ci) venvNext :=
      Halign.const hnMap htr.1 hadd rfl
    have hnext : (envHead.constants.insert ci.name ci).find? name = some found :=
      ih Halign' hfind hfoundDelta
    rw [Halign.map_wf.find?_insert] at hnext
    split at hnext
    · cases hnext
      simp [hdelta] at hfoundDelta
    · exact hnext

theorem aligned_addDefEqs
    (H : Aligned safety C venv) (rules : List VDefEq) :
    Aligned safety C (venv.addDefEqRules rules) := by
  induction rules generalizing venv with
  | nil => exact H
  | cons rule rules ih =>
    exact ih H.defeq

theorem hasPrimitives_addDefEqs
    {venv : VEnv} (H : venv.HasPrimitives) (rules : List VDefEq) :
    (venv.addDefEqRules rules).HasPrimitives := by
  induction rules generalizing venv with
  | nil => exact H
  | cons rule rules ih => exact ih H.addDefEq

theorem CheckingEnv.exists_addConst
    (H : CheckingEnv safety env venv) (hn : env.find? name = none)
    (ci' : VConstant) :
    ∃ venv', venv.addConst name ci' = some venv' := by
  unfold VEnv.addConst
  cases hfind : venv.constants name with
  | none => simp
  | some ci =>
    exfalso
    rcases H.find?_iff.mpr ⟨ci, hfind⟩ with ⟨source, hsource, _⟩
    rw [hn] at hsource
    contradiction

/-- The inner executable constructor fold installs a translated constructor
list in lockstep with its abstract constants.  Constructor metadata is kept
parametric because only the source name, type, level parameters, and safety
participate in the translation relation. -/
inductive ConstructorListEntries
    (mkInfo : Nat → Constructor → ConstructorVal) :
    Nat → List Constructor → List (ConstantInfo × VConstVal) → Prop
  | nil : ConstructorListEntries mkInfo start [] []
  | cons : ConstructorListEntries mkInfo (start + 1) ctors entries →
      ConstructorListEntries mkInfo start (ctor :: ctors)
        ((.ctorInfo (mkInfo start ctor), value) :: entries)

/-- Family-major source alignment of the complete constructor-entry batch. -/
inductive ConstructorTypeEntries
    (mkInfo : InductiveType → Nat → Constructor → ConstructorVal) :
    List InductiveType → List (ConstantInfo × VConstVal) → Prop
  | nil : ConstructorTypeEntries mkInfo [] []
  | cons : ConstructorListEntries (mkInfo owner) 0 owner.ctors head →
      ConstructorTypeEntries mkInfo owners tail →
      ConstructorTypeEntries mkInfo (owner :: owners) (head ++ tail)

/-- Every source constructor of the families carries a telescope certificate of its type in
`venv`. This is what a successful constructor check establishes (`checkClosedType` runs
`checkType` on each constructor type in the empty context). -/
def SourceCtorsCertified (venv : VEnv) (lparams : List Name) (owners : List InductiveType) :
    Prop :=
  ∀ owner ∈ owners, ∀ ctor ∈ owner.ctors,
    ∃ T, TelTrN venv lparams (AddInductive.constructorArity ctor.type) [] ctor.type T

theorem SourceCtorsCertified.ofTranslated {owners : List InductiveType}
    {targets : List VInductiveType}
    (Htr : List.Forall₂ (fun source target => List.Forall₂
        (fun ctor ctor' => TrSourceConst venv lparams ctor.name ctor.type ctor')
        source.ctors target.ctors) owners targets)
    (h : ∀ owner ∈ owners, ∀ ctor ∈ owner.ctors, ∀ T,
      TrExprS venv lparams [] ctor.type T →
      ∃ T', TelTrN venv lparams (AddInductive.constructorArity ctor.type) [] ctor.type T') :
    SourceCtorsCertified venv lparams owners := by
  intro o ho c hc
  obtain ⟨t, -, ht⟩ := Lean4Lean.List.Forall₂.forall_exists_l Htr o ho
  obtain ⟨c', -, hc'⟩ := Lean4Lean.List.Forall₂.forall_exists_l ht c hc
  exact h o ho c hc _ hc'.type

theorem ConstructorListEntries.ctorTelescopeSteps
    {stats : AddInductive.InductiveStats} {lparams : List Name} {isUnsafe : Bool}
    {owner : InductiveType} {ctors : List Constructor} {initial : Nat}
    {entries : List (ConstantInfo × VConstVal)}
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner) initial ctors entries)
    (hcert : ∀ ctor ∈ ctors,
      ∃ T, TelTrN venv lparams (AddInductive.constructorArity ctor.type) [] ctor.type T) :
    ∀ entry ∈ entries, CtorTelescopeStep safety venv entry.1 := by
  induction H with
  | nil => simp
  | @cons start ctors tailEntries ctor value Htail ih =>
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · intro info e _
      cases e
      obtain ⟨T, hT⟩ := hcert ctor List.mem_cons_self
      exact .of_telTrN hT
    · exact ih (fun c hc => hcert c (List.mem_cons_of_mem _ hc)) entry htail

theorem ConstructorTypeEntries.ctorTelescopeSteps
    {stats : AddInductive.InductiveStats} {lparams : List Name} {isUnsafe : Bool}
    {owners : List InductiveType} {entries : List (ConstantInfo × VConstVal)}
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) owners entries)
    (hcert : SourceCtorsCertified venv lparams owners) :
    ∀ entry ∈ entries, CtorTelescopeStep safety venv entry.1 := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro entry hentry
    rcases List.mem_append.mp hentry with hhead | htail
    · exact Hhead.ctorTelescopeSteps (hcert _ List.mem_cons_self) entry hhead
    · exact ih (fun o ho => hcert o (List.mem_cons_of_mem _ ho)) entry htail

theorem ConstructorListEntries.findSource
    {initial : Nat}
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      initial ctors entries)
    (hctor : ctor ∈ ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.type = ctor.type ∧
      info.levelParams = lparams ∧ info.isUnsafe = isUnsafe := by
  cases H with
  | nil => simp at hctor
  | cons Htail =>
    rename_i tail tailEntries headValue
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact ⟨AddInductive.constructorInfo stats lparams isUnsafe owner
        initial ctor, headValue, by simp,
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo]⟩
    · rcases Htail.findSource htail with
        ⟨info, value, hmem, hname, htype, hlevels, hunsafe⟩
      exact ⟨info, value, by simp [hmem], hname, htype, hlevels, hunsafe⟩

/-- Positional form of constructor-source alignment, retaining the exact
owner-local constructor index used to build the executable metadata. -/
theorem ConstructorListEntries.findAt
    (H : ConstructorListEntries mkInfo initial ctors entries)
    (i : Nat) (hi : i < ctors.length) :
    ∃ value : VConstVal,
      (.ctorInfo (mkInfo (initial + i) ctors[i]), value) ∈ entries := by
  induction H generalizing i with
  | nil => simp at hi
  | @cons initial ctor ctors entries value Htail ih =>
    cases i with
    | zero => exact ⟨value, by simp⟩
    | succ i =>
      rcases ih i (by simpa using hi) with ⟨tailValue, hmem⟩
      refine ⟨tailValue, List.mem_cons_of_mem _ ?_⟩
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.one_add] using hmem

/-- Reverse one owner's constructor-entry alignment. -/
theorem ConstructorListEntries.ownerOfEntry
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      initial ctors entries)
    (hentry : entry ∈ entries) :
    ∃ info : ConstructorVal,
      entry.1 = .ctorInfo info ∧ info.induct = owner.name ∧
      info.name ∈ ctors.map (·.name) ∧ info.isUnsafe = isUnsafe := by
  induction H with
  | nil => simp at hentry
  | @cons start ctor ctors tailEntries value Hrest ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htailEntry
    · exact ⟨_, rfl, by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo], by simp [AddInductive.constructorInfo]⟩
    · rcases ih htailEntry with ⟨info, h1, h2, h3, h4⟩
      exact ⟨info, h1, h2, List.mem_cons_of_mem _ h3, h4⟩

theorem ConstructorTypeEntries.findSource
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) types entries)
    (howner : owner ∈ types) (hctor : ctor ∈ owner.ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.type = ctor.type ∧
      info.levelParams = lparams ∧ info.isUnsafe = isUnsafe := by
  induction H generalizing owner with
  | nil => simp at howner
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at howner
    rcases howner with rfl | htailOwner
    · rcases Hhead.findSource hctor with
        ⟨info, value, hmem, hname, htype, hlevels, hunsafe⟩
      exact ⟨info, value, List.mem_append_left _ hmem, hname, htype,
        hlevels, hunsafe⟩
    · rcases ih htailOwner hctor with
        ⟨info, value, hmem, hname, htype, hlevels, hunsafe⟩
      exact ⟨info, value, List.mem_append_right _ hmem, hname, htype,
        hlevels, hunsafe⟩

theorem ConstructorListEntries.findSourceInduct
    {initial : Nat}
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      initial ctors entries)
    (hctor : ctor ∈ ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.induct = owner.name ∧ info.isUnsafe = isUnsafe := by
  cases H with
  | nil => simp at hctor
  | cons Htail =>
    rename_i tail tailEntries headValue
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact ⟨AddInductive.constructorInfo stats lparams isUnsafe owner
        initial ctor, headValue, by simp,
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo]⟩
    · rcases Htail.findSourceInduct htail with ⟨info, value, hmem, hrest⟩
      exact ⟨info, value, by simp [hmem], hrest⟩

/-- The constructor entry emitted for a source constructor records its source family as
owner. -/
theorem ConstructorTypeEntries.findSourceInduct
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) types entries)
    (howner : owner ∈ types) (hctor : ctor ∈ owner.ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.induct = owner.name ∧ info.isUnsafe = isUnsafe := by
  induction H generalizing owner with
  | nil => simp at howner
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at howner
    rcases howner with rfl | htailOwner
    · rcases Hhead.findSourceInduct hctor with ⟨info, value, hmem, hrest⟩
      exact ⟨info, value, List.mem_append_left _ hmem, hrest⟩
    · rcases ih htailOwner hctor with ⟨info, value, hmem, hrest⟩
      exact ⟨info, value, List.mem_append_right _ hmem, hrest⟩

/-- Family-major positional constructor alignment. -/
theorem ConstructorTypeEntries.findAt
    (H : ConstructorTypeEntries mkInfo types entries)
    (howner : owner ∈ types) (i : Nat) (hi : i < owner.ctors.length) :
    ∃ value : VConstVal,
      (.ctorInfo (mkInfo owner i owner.ctors[i]), value) ∈ entries := by
  induction H generalizing owner with
  | nil => simp at howner
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at howner
    rcases howner with rfl | htailOwner
    · rcases Hhead.findAt i hi with ⟨value, hmem⟩
      exact ⟨value, by simpa using List.mem_append_left _ hmem⟩
    · rcases ih htailOwner hi with ⟨value, hmem⟩
      exact ⟨value, List.mem_append_right _ hmem⟩

/-- Reverse the family-major constructor-entry alignment: every emitted
constructor entry records the name of the source family that owns it. -/
theorem ConstructorTypeEntries.ownerOfEntry
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) owners entries)
    (hentry : entry ∈ entries) :
    ∃ owner ∈ owners, ∃ info : ConstructorVal,
      entry.1 = .ctorInfo info ∧ info.induct = owner.name ∧
      info.name ∈ owner.ctors.map (·.name) ∧ info.isUnsafe = isUnsafe := by
  induction H with
  | nil => simp at hentry
  | cons Hhead Htail ih =>
    rcases List.mem_append.mp hentry with hhead | htail
    · rcases Hhead.ownerOfEntry hhead with ⟨info, heq, hinduct, hmem, hunsafe⟩
      exact ⟨_, by simp, info, heq, hinduct, hmem, hunsafe⟩
    · rcases ih htail with ⟨owner, howner, info, heq, hinduct, hmem, hunsafe⟩
      exact ⟨owner, by simp [howner], info, heq, hinduct, hmem, hunsafe⟩

theorem AddConstants.ofConstructorList
    {env : Environment} {venv sourceEnv : VEnv}
    {ctors : List Constructor} {values : List VConstVal}
    (mkInfo : Nat → Constructor → ConstructorVal)
    (Hvalid : CheckingEnv safety env venv)
    (Hentries : List.Forall₂
      (fun ctor ci' => TrSourceConst sourceEnv lparams ctor.name ctor.type ci')
      ctors values)
    (hle : sourceEnv ≤ venv)
    (hlevelParams : ∀ i ctor, (mkInfo i ctor).levelParams = lparams)
    (hname : ∀ i ctor, (mkInfo i ctor).name = ctor.name)
    (htype : ∀ i ctor, (mkInfo i ctor).type = ctor.type)
    (hvisible : ∀ i ctor, safety ≤
      (if (mkInfo i ctor).isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : allowPrimitive = true → ∀ ctor ∈ ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    (ctors.foldlM (init := (start, env)) fun
        (state : Nat × Environment) (ctor : Constructor) => do
      let (cidx, env) := state
      env.checkName ctor.name allowPrimitive
      pure (cidx + 1, env.add (.ctorInfo (mkInfo cidx ctor)))).WF
      fun result => ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
        entries.map Prod.snd = values ∧
        AddConstants safety env venv entries result.2 outVEnv ∧
        ConstructorListEntries mkInfo start ctors entries ∧
        (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
          ∃ info : ConstructorVal,
            entry.1 = ConstantInfo.ctorInfo info) ∧
        (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
          ∀ (value : InductiveVal),
          entry.1 ≠ ConstantInfo.inductInfo value) := by
  induction Hentries generalizing start env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, [], rfl, .nil, .nil, by simp, by simp⟩
  | @cons ctor ci' ctors values Hentry _ ih =>
    rw [List.foldlM_cons]
    simpa using (checkName.WF Hvalid.map_wf ctor.name allowPrimitive).bind
      fun _ hchecked => by
          have hnprimHead :
              ¬ Kernel.Environment.primitives.contains ctor.name := by
            cases hallow : allowPrimitive with
            | false =>
              intro hp
              have := hchecked.2 hp
              simp [hallow] at this
            | true => exact hnprim hallow ctor (by simp)
          have hnprimTail : allowPrimitive = true → ∀ ctor ∈ ctors,
              ¬ Kernel.Environment.primitives.contains ctor.name := by
            intro hallow ctor hctor
            exact hnprim hallow ctor (by simp [hctor])
          rcases Lean4Lean.VerifyInductive.CheckingEnv.exists_addConst
              Hvalid hchecked.1 ci'.toVConstant with
            ⟨nextVEnv, hnext⟩
          let info := mkInfo start ctor
          have htrSource : TrSourceConst venv lparams ctor.name ctor.type ci' :=
            ⟨Hentry.uvars, Hentry.name, Hentry.type.mono hle,
              Hentry.wf.mono hle⟩
          have htr : TrConstVal safety venv (.ctorInfo info) ci' :=
            Lean4Lean.VerifyInductive.TrSourceConst.ctorInfo htrSource
              (hlevelParams start ctor)
              (hname start ctor) (htype start ctor) (hvisible start ctor)
          have hwf : ci'.toVConstant.WF venv := Hentry.wf.mono hle
          have haddHead :
              venv.addConst info.name ci'.toVConstant = some nextVEnv := by
            simpa [info, hname start ctor, Hentry.name] using hnext
          have hfindInfo : env.find? info.name = none := by
            rw [hname start ctor]
            exact hchecked.1
          have hnprimInfo :
              ¬ Kernel.Environment.primitives.contains info.name := by
            rw [hname start ctor]
            exact hnprimHead
          have HnextValid : CheckingEnv safety
              (env.add (.ctorInfo info)) nextVEnv :=
            Hvalid.add hfindInfo htr.1 hwf haddHead rfl
          have hnextLe : sourceEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddHead)
          exact (ih (start := start + 1) HnextValid hnextLe
            hnprimTail).mono
            fun result Hrest => by
              rcases Hrest with
                ⟨outVEnv, entries, hvalues, Hinstalled, Haligned,
                  hctor, hnind⟩
              have hvalues' :
                  (((.ctorInfo info, ci') :: entries).map Prod.snd) =
                    ci' :: values := by simp [hvalues]
              have Hinstalled' := AddConstants.cons
                (ci := .ctorInfo info) (ci' := ci') hfindInfo hnprimInfo
                htr hwf haddHead rfl Hinstalled
              exact ⟨outVEnv, (.ctorInfo info, ci') :: entries,
                hvalues', Hinstalled', .cons Haligned, by
                  intro entryInfo entryValue hentry
                  simp only [List.mem_cons] at hentry
                  rcases hentry with hhead | htail
                  · exact ⟨info, congrArg Prod.fst hhead⟩
                  · exact hctor (entryInfo, entryValue) htail, by
                  intro entryInfo entryValue hentry value
                  simp only [List.mem_cons, Prod.mk.injEq] at hentry
                  rcases hentry with ⟨rfl, rfl⟩ | htail
                  · simp
                  · exact hnind (entryInfo, entryValue) htail value⟩

/-- The outer mutual-family fold concatenates the per-family
constructor batches in the same family-major order as
`VInductDecl.constructorConstants`. -/
theorem AddConstants.ofConstructorTypes
    {env : Environment} {venv sourceEnv : VEnv}
    {types : List InductiveType} {targets : List VInductiveType}
    (mkInfo : InductiveType → Nat → Constructor → ConstructorVal)
    (Hvalid : CheckingEnv safety env venv)
    (Hentries : List.Forall₂
      (fun source target => List.Forall₂
        (fun ctor ci' =>
          TrSourceConst sourceEnv lparams ctor.name ctor.type ci')
        source.ctors target.ctors)
      types targets)
    (hle : sourceEnv ≤ venv)
    (hlevelParams : ∀ owner i ctor,
      (mkInfo owner i ctor).levelParams = lparams)
    (hname : ∀ owner i ctor, (mkInfo owner i ctor).name = ctor.name)
    (htype : ∀ owner i ctor, (mkInfo owner i ctor).type = ctor.type)
    (hvisible : ∀ owner i ctor, safety ≤
      (if (mkInfo owner i ctor).isUnsafe then
        DefinitionSafety.unsafe else .safe))
    (hnprim : allowPrimitive = true → ∀ owner ∈ types,
      ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    (types.foldlM (init := env) fun
        (env : Environment) (owner : InductiveType) => do
      let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
          (state : Nat × Environment) (ctor : Constructor) => do
        let (cidx, env) := state
        env.checkName ctor.name allowPrimitive
        pure (cidx + 1, env.add (.ctorInfo (mkInfo owner cidx ctor)))
      pure env).WF fun outEnv =>
        ∃ outVEnv : VEnv,
          ∃ entries : List (ConstantInfo × VConstVal),
          entries.map Prod.snd =
            targets.flatMap (fun target : VInductiveType => target.ctors) ∧
          AddConstants safety env venv entries outEnv outVEnv ∧
          ConstructorTypeEntries mkInfo types entries ∧
          (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
            ∃ info : ConstructorVal,
              entry.1 = ConstantInfo.ctorInfo info) ∧
          (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
            ∀ (value : InductiveVal),
            entry.1 ≠ ConstantInfo.inductInfo value) := by
  induction Hentries generalizing env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, [], rfl, .nil, .nil, by simp, by simp⟩
  | @cons owner target types targets Hhead _ ih =>
    have hnprimHead : allowPrimitive = true → ∀ ctor ∈ owner.ctors,
        ¬ Kernel.Environment.primitives.contains ctor.name := by
      intro hallow ctor hctor
      exact hnprim hallow owner (by simp) ctor hctor
    have hnprimTail : allowPrimitive = true → ∀ owner ∈ types,
        ∀ ctor ∈ owner.ctors,
        ¬ Kernel.Environment.primitives.contains ctor.name := by
      intro hallow owner howner ctor hctor
      exact hnprim hallow owner (by simp [howner]) ctor hctor
    rw [List.foldlM_cons]
    let Hinner := AddConstants.ofConstructorList
      (start := 0) (allowPrimitive := allowPrimitive)
      (mkInfo owner) Hvalid Hhead hle
      (hlevelParams owner) (hname owner) (htype owner) (hvisible owner)
      hnprimHead
    simpa using Hinner.bind fun result Hresult => by
      rcases Hresult with
        ⟨middleVEnv, headEntries, hheadValues, HheadInstalled,
          HheadAligned, hheadCtor, hheadNind⟩
      have validInstalled : ∀ {priorEnv nextEnv : Environment}
          {priorVEnv nextVEnv : VEnv} {entries},
          AddConstants safety priorEnv priorVEnv entries nextEnv nextVEnv →
          CheckingEnv safety priorEnv priorVEnv →
          CheckingEnv safety nextEnv nextVEnv := by
        intro priorEnv nextEnv priorVEnv nextVEnv entries Hinstalled Hprior
        induction Hinstalled with
        | nil => exact Hprior
        | cons hn hnprim htr hwf hadd hdelta _ ih =>
          exact ih (Hprior.add hn htr.1 hwf hadd hdelta)
      have HnextValid : CheckingEnv safety result.2 middleVEnv := by
        exact validInstalled HheadInstalled Hvalid
      have installedLe : ∀ {priorEnv nextEnv : Environment}
          {priorVEnv nextVEnv : VEnv} {entries},
          AddConstants safety priorEnv priorVEnv entries nextEnv nextVEnv →
          priorVEnv ≤ nextVEnv := by
        intro priorEnv nextEnv priorVEnv nextVEnv entries Hinstalled
        induction Hinstalled with
        | nil => exact VEnv.LE.rfl
        | cons _ _ _ _ hadd _ _ ih =>
          exact (VEnv.addConst_le hadd).trans ih
      have hnextLe : sourceEnv ≤ middleVEnv :=
        hle.trans (installedLe HheadInstalled)
      exact (ih HnextValid hnextLe hnprimTail).mono
        fun outEnv Htail => by
          rcases Htail with
            ⟨installedVEnv, tailEntries, htailValues, HtailInstalled,
              HtailAligned, htailCtor, htailNind⟩
          have hvalues : (headEntries ++ tailEntries).map Prod.snd =
              (target :: targets).flatMap
                (fun target : VInductiveType => target.ctors) := by
            simp [hheadValues, htailValues]
          exact ⟨installedVEnv, headEntries ++ tailEntries, hvalues,
            HheadInstalled.append HtailInstalled,
            .cons HheadAligned HtailAligned, by
              intro entryInfo entryValue hentry
              rcases List.mem_append.mp hentry with hhead | htail
              · exact hheadCtor (entryInfo, entryValue) hhead
              · exact htailCtor (entryInfo, entryValue) htail, by
              intro entryInfo entryValue hentry value
              rcases List.mem_append.mp hentry with hhead | htail
              · exact hheadNind (entryInfo, entryValue) hhead value
              · exact htailNind (entryInfo, entryValue) htail value⟩

/-- A lockstep installation preserves the checking relation. -/
theorem AddConstants.checking
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hchecking : CheckingEnv safety env venv) :
    CheckingEnv safety outEnv outVEnv := by
  induction H with
  | nil => exact hchecking
  | cons hn _ htr hwf hadd hdelta _ ih =>
    exact ih (hchecking.add hn htr.1 hwf hadd hdelta)

/-- A lockstep installation preserves the constructor telescopes (`CtorTelescopes`), given
the constructor steps of its entries (stated in the environment before the installation). -/
theorem AddConstants.ctorTelescopes
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hchecking : CheckingEnv safety env venv)
    (htels : CtorTelescopes safety env venv)
    (hsteps : ∀ entry ∈ entries, CtorTelescopeStep safety venv entry.1) :
    CtorTelescopes safety outEnv outVEnv := by
  induction H with
  | nil => exact htels
  | cons hn _ htr hwf hadd hdelta _ ih =>
    exact ih (hchecking.add hn htr.1 hwf hadd hdelta)
      (htels.add hchecking.map_wf hn (VEnv.addConst_le hadd) (hsteps _ List.mem_cons_self))
      fun e he => (hsteps e (List.mem_cons_of_mem _ he)).mono (VEnv.addConst_le hadd)

/-- A lockstep installation preserves the local checking invariants. -/
theorem AddConstants.validCore
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.ValidCore safety env venv) :
    CheckingEnv.ValidCore safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta)

theorem AddConstants.abstract
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv.addConstVals (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConstVals]
  | cons _ _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConstVals, ← htr.2, hadd]
    exact ih

theorem AddConstants.existsEntryOfValue
    {entries : List (ConstantInfo × VConstVal)}
    (hvalue : value ∈ entries.map Prod.snd) :
    ∃ info, (info, value) ∈ entries := by
  rcases List.mem_map.mp hvalue with ⟨⟨info, entryValue⟩, hentry, heq⟩
  simp only at heq
  subst entryValue
  exact ⟨info, hentry⟩

/-- Every executable entry in a lockstep batch satisfies the visibility
bound at which the batch was checked. -/
theorem AddConstants.entrySafety
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hentry : (info, value) ∈ entries) :
    safety ≤ info.safety := by
  induction H with
  | nil => simp at hentry
  | cons _ _ htr _ _ _ _ ih =>
    rcases List.mem_cons.mp hentry with hhead | htail
    · cases hhead
      exact htr.1.1
    · exact ih htail

inductive InductiveHeaderEntries :
    List InductiveVal → List (ConstantInfo × VConstVal) → Prop
  | nil : InductiveHeaderEntries [] []
  | cons : InductiveHeaderEntries infos entries →
      InductiveHeaderEntries (info :: infos)
        ((.inductInfo info, value) :: entries)

theorem InductiveHeaderEntries.ofZip
    (hlength : infos.length = values.length) :
    InductiveHeaderEntries infos
      (List.zip (infos.map (fun info => .inductInfo info)) values) := by
  induction infos generalizing values with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons value values => simp at hlength
  | cons info infos ih =>
    cases values with
    | nil => simp at hlength
    | cons value values =>
      simp only [List.length_cons] at hlength
      exact .cons (ih (by omega))

theorem InductiveHeaderEntries.findInfo
    (H : InductiveHeaderEntries infos entries) (hinfo : info ∈ infos) :
    ∃ value, (.inductInfo info, value) ∈ entries := by
  cases H with
  | nil => simp at hinfo
  | cons Htail =>
    rename_i tail entries headValue
    simp only [List.mem_cons] at hinfo
    rcases hinfo with rfl | htail
    · exact ⟨headValue, by simp⟩
    · rcases Htail.findInfo htail with ⟨value, hmem⟩
      exact ⟨value, by simp [hmem]⟩

/-- Reverse the header-entry alignment: every installed entry is the exact
executable metadata for one member of the mutual family. -/
theorem InductiveHeaderEntries.originInfo
    (H : InductiveHeaderEntries infos entries)
    (hentry : entry ∈ entries) :
    ∃ info ∈ infos, entry.1 = .inductInfo info := by
  induction H with
  | nil => simp at hentry
  | cons Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact ⟨_, by simp, rfl⟩
    · rcases ih htail with ⟨info, hinfo, heq⟩
      exact ⟨info, by simp [hinfo], heq⟩

/-- Every emitted header lists exactly the constructor names of its source family. -/
theorem inductiveTypeInfos_ctors
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) {info : InductiveVal}
    (h : info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
        numNested isUnsafe lparams).toList) :
    ∃ owner ∈ indTypes.toList, info.name = owner.name ∧
      info.ctors = owner.ctors.map (·.name) ∧ info.isUnsafe = isUnsafe := by
  simp only [AddInductive.inductiveTypeInfos, Array.toList_zipWith] at h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hi, rfl⟩ := h
  have hi' : i < indTypes.toList.length := by
    simp only [List.length_zipWith] at hi; omega
  simp only [List.getElem_zipWith]
  exact ⟨indTypes.toList[i], List.getElem_mem hi', by simp⟩

/-- Every source family occurs in the executable header array when the
computed index-count array has the checked family cardinality. -/
theorem inductiveTypeInfos_owner
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name)
    (hsize : stats.nindices.size = indTypes.size)
    (howner : owner ∈ indTypes.toList) :
    ∃ info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
        numNested isUnsafe lparams).toList,
      info.name = owner.name ∧ info.ctors = owner.ctors.map (·.name) ∧
      info.isUnsafe = isUnsafe := by
  rcases List.mem_iff_getElem.mp howner with ⟨i, hi, rfl⟩
  have hinfosSize :
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).size = indTypes.size := by
    simp [AddInductive.inductiveTypeInfos, hsize]
  let info := (AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe lparams)[i]'(by simpa [hinfosSize] using hi)
  refine ⟨info, ?_, ?_⟩
  · simp [info]
  · simp [info, AddInductive.inductiveTypeInfos]

theorem AddConstants.le
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv ≤ outVEnv :=
  VEnv.addConstVals_le H.abstract

/-- A lockstep installation preserves lookups from its source kernel
environment. This low-level form is kept with `AddConstants`
so positional entry lookup does not depend on the nested compilation layer. -/
theorem AddConstants.preservesSourceFind
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : env.find? name = some found) :
    outEnv.find? name = some found := by
  induction H with
  | nil => exact hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hne : ci.name ≠ name := by
      intro heq
      subst name
      rw [hfind] at hn
      contradiction
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    apply ih hnextWF
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfind
    change (envHead.constants.insert ci.name ci).find?' name = some found
    rw [(hwf.insert ci.name ci hfreshMap).find?'_eq_find?, hwf.find?_insert]
    split
    · rename_i heq
      exact False.elim (hne (by simpa using heq))
    · exact hfind

theorem AddConstants.targetMapWF
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) : outEnv.constants.WF := by
  induction H with
  | nil => exact hwf
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfresh : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    exact ih (hwf.insert ci.name ci hfresh)

/-- A lockstep installation preserves lookups in the constant map. -/
theorem AddConstants.preservesMapFind
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : env.constants.find? name = some found) :
    outEnv.constants.find? name = some found := by
  have hfind' : env.find? name = some found := by
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    exact hfind
  have hout := H.preservesSourceFind hwf hfind'
  rwa [Lean.Kernel.Environment.find?, (H.targetMapWF hwf).find?'_eq_find?] at hout

/-- A lockstep installation adds no stored equation. -/
theorem AddConstants.defeqs
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ df, outVEnv.defeqs df → venv.defeqs df := by
  induction H with
  | nil => exact fun _ h => h
  | cons _ _ _ _ hadd _ _ ih =>
    intro df hdf
    rw [← VEnv.addConst_defeqs hadd]
    exact ih df hdf

/-- A lockstep installation of constants none of which is a recursor
transports the recursor facts of the checking invariant. -/
theorem AddConstants.recursorEnvCoherent
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hrecs : ∀ entry ∈ entries, ∀ rec : RecursorVal, entry.1 ≠ .recInfo rec)
    (hcoherent : RecursorEnvCoherent safety env.constants venv) :
    RecursorEnvCoherent safety outEnv.constants outVEnv := by
  induction H with
  | nil => exact hcoherent
  | @cons venv ci ci' venv' rest outEnv outVEnv env hn _ _ _ hadd _ _ ih =>
    have hfresh : env.constants.find? ci.name = none := by
      rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
      exact hn
    refine ih (hwf.insert _ _ hfresh) (fun entry hentry => hrecs entry (by simp [hentry])) ?_
    exact hcoherent.insertNonRecursor hwf hfresh (fun rec => hrecs (ci, ci') (by simp) rec)
      (VEnv.addConst_le hadd) fun df hdf => by rwa [VEnv.addConst_defeqs hadd] at hdf

/-- A lockstep installation transports the quotient facts of the checking
invariant, given the equation-head facts at its endpoint. -/
theorem AddConstants.quotEnvCoherent
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hheads : EquationHeadsCoherent outEnv.constants outVEnv)
    (hquot : env.quotInit = true → QuotEnvCoherent env.constants venv) :
    outEnv.quotInit = true → QuotEnvCoherent outEnv.constants outVEnv := by
  intro hq
  rw [H.quotInit_eq] at hq
  exact (hquot hq).extend (H.preservesMapFind hwf) H.le hheads

/-- Every entry of a lockstep fold is fresh in the fold's source
environment. -/
theorem AddConstants.entryFresh
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    env.find? info.name = none := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    simp only [List.mem_cons, Prod.mk.injEq] at hentry
    rcases hentry with ⟨rfl, rfl⟩ | htail
    · exact hn
    · have hfreshMap : envHead.constants.find? ci.name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
      have hnextWF : (envHead.add ci).constants.WF := by
        change (envHead.constants.insert ci.name ci).WF
        exact hwf.insert ci.name ci hfreshMap
      have hnext := ih hnextWF htail
      cases hfind : envHead.find? info.name with
      | none => rfl
      | some found =>
        exfalso
        have hne : ci.name ≠ info.name := by
          intro heq
          rw [← heq, hn] at hfind
          contradiction
        have hpreserved : (envHead.add ci).find? info.name = some found := by
          rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfind
          change (envHead.constants.insert ci.name ci).find?' info.name =
            some found
          rw [(hwf.insert ci.name ci hfreshMap).find?'_eq_find?,
            hwf.find?_insert]
          split
          · rename_i heq
            exact False.elim (hne (by simpa using heq))
          · exact hfind
        rw [hpreserved] at hnext
        contradiction

/-- Every lookup in the output kernel environment either existed before the lockstep fold
or is one of its entries. -/
theorem AddConstants.entryOrigin
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : outEnv.find? name = some found) :
    env.find? name = some found ∨
      ∃ entry ∈ entries, name = entry.1.name ∧ found = entry.1 := by
  induction H with
  | nil => exact Or.inl hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases ih hnextWF hfind with hnext | ⟨entry, hentry, hname, hfound⟩
    · change (envHead.add ci).constants.find?' name = some found at hnext
      rw [hnextWF.find?'_eq_find?] at hnext
      change (envHead.constants.insert ci.name ci).find? name =
        some found at hnext
      rw [hwf.find?_insert] at hnext
      split at hnext
      · rename_i heq
        right
        simp only [Option.some.injEq] at hnext
        have hname : name = ci.name := (LawfulBEq.eq_of_beq heq).symm
        exact ⟨(ci, ci'), by simp, hname, hnext.symm⟩
      · left
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    · exact Or.inr ⟨entry, by simp [hentry], hname, hfound⟩

/-- Constructor-owner presence is preserved by a lockstep batch when every
new constructor entry is accompanied by its owner at the endpoint. -/
theorem AddConstants.constructorOwnersPresent
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hsource : ConstructorOwnersPresent env)
    (hentries : ∀ entry ∈ entries, ∀ info,
      entry.1 = .ctorInfo info →
      ∃ owner, outEnv.find? info.induct = some (.inductInfo owner) ∧
        info.name ∈ owner.ctors ∧ info.isUnsafe = owner.isUnsafe) :
    ConstructorOwnersPresent outEnv := by
  intro name info hfind
  rcases H.entryOrigin hwf hfind with hold |
      ⟨entry, hentry, hname, hfound⟩
  · rcases hsource name info hold with ⟨owner, howner, hmem⟩
    exact ⟨owner, H.preservesSourceFind hwf howner, hmem⟩
  · rcases hentries entry hentry info hfound.symm with ⟨owner, howner, hmem, hunsafe⟩
    refine ⟨owner, howner, ?_, hunsafe⟩
    rw [hname, ← hfound]
    exact hmem

/-- Every executable entry of an `AddConstants` installation is present
with its exact metadata in the output environment. -/
theorem AddConstants.findEntry
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    outEnv.find? info.name = some info := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    simp only [List.mem_cons] at hentry
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases hentry with hhead | htail
    · have hinstalled : outProd.find? ci.name = some ci := by
        apply Htail.preservesSourceFind hnextWF
        change (Lean4Lean.AddInductive.addConstant envHead ci).find? ci.name =
          some ci
        change (envHead.constants.insert ci.name ci).find?' ci.name = some ci
        rw [(hwf.insert ci.name ci hfreshMap).find?'_eq_find?, hwf.find?_insert]
        simp
      have hi : info = ci := congrArg Prod.fst hhead
      simpa [hi] using hinstalled
    · exact ih hnextWF htail

/-- A lockstep installation of constants none of which is a constructor
preserves the full checking invariant: inductive headers and all other
constants carry no projection-registry obligation.  For listed-constructor
coherence, every name a header of the source lists must be present there or
absent from the final environment, and the names the installed headers list
must be absent from the final environment. -/
theorem AddConstants.valid
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv)
    (hkinds : ∀ entry ∈ entries, ∀ info : ConstructorVal,
      entry.1 ≠ .ctorInfo info)
    (hrecs : ∀ entry ∈ entries, ∀ rec : RecursorVal,
      entry.1 ≠ .recInfo rec)
    (hpending : ∀ familyName familyInfo,
      env.find? familyName = some (.inductInfo familyInfo) →
      ∀ name ∈ familyInfo.ctors,
        (∃ found, env.find? name = some found) ∨ outEnv.find? name = none)
    (hheaders : ∀ entry ∈ entries, ∀ familyInfo, entry.1 = .inductInfo familyInfo →
      ∀ name ∈ familyInfo.ctors, outEnv.find? name = none) :
    CheckingEnv.Valid safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | @cons venv ci ci' venv' rest outEnv outVEnv env hn hnprim htr hwf hadd
      hdelta Htail ih =>
    have hmapWF := hvalid.tr.map_wf
    have hnMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hmapWF.find?'_eq_find?] at hn
    have hnextWF : (env.add ci).constants.WF := by
      change (env.constants.insert ci.name ci).WF
      exact hmapWF.insert ci.name ci hnMap
    have hself : (env.add ci).find? ci.name = some ci := by
      change (env.constants.insert ci.name ci).find?' ci.name = some ci
      rw [(hmapWF.insert ci.name ci hnMap).find?'_eq_find?, hmapWF.find?_insert]
      simp
    have hlisted : ListedConstructorsCoherent (env.add ci) := by
      apply hvalid.listedConstructors.add hmapWF hn
      · intro familyName familyInfo hfamily hmem
        rcases hpending familyName familyInfo hfamily ci.name hmem with
          ⟨found, hfound⟩ | habsent
        · rw [hn] at hfound
          cases hfound
        · rw [Htail.preservesSourceFind hnextWF hself] at habsent
          cases habsent
      · intro familyInfo hci name hname
        cases hfind : (env.add ci).find? name with
        | none => rfl
        | some found =>
          have hout := Htail.preservesSourceFind hnextWF hfind
          rw [hheaders (ci, ci') (by simp) familyInfo hci name hname] at hout
          cases hout
    refine ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta
      (fun info => hkinds (ci, ci') (by simp) info)
      (fun rec => hrecs (ci, ci') (by simp) rec) hlisted)
      (fun entry hentry => hkinds entry (by simp [hentry]))
      (fun entry hentry => hrecs entry (by simp [hentry])) ?_
      (fun entry hentry => hheaders entry (by simp [hentry]))
    intro familyName familyInfo hfamily name hname
    rcases findAddFresh_cases hmapWF ci hn hfamily with ⟨-, hheader⟩ | hold
    · exact Or.inr (hheaders (ci, ci') (by simp) familyInfo hheader.symm name hname)
    · rcases hpending familyName familyInfo hold name hname with
        ⟨found, hfound⟩ | habsent
      · exact Or.inl ⟨found, findAddFresh_of_find hmapWF ci hn hfound⟩
      · exact Or.inr habsent

/-- Mutual-header installation preserves the full checking invariant when
every constructor a header of the source lists is present, and the
constructors the installed headers list are absent from the result (the
header environment in which their types are checked). -/
theorem AddConstants.validHeaders {infos : List InductiveVal} {values : List VConstVal}
    (H : AddConstants safety env venv
      (List.zip (infos.map (fun info => .inductInfo info)) values) outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv)
    (hpresent : ListedConstructorsPresent env)
    (habsent : ∀ info ∈ infos, ∀ name ∈ info.ctors, outEnv.find? name = none) :
    CheckingEnv.Valid safety outEnv outVEnv := by
  refine H.valid hvalid ?_ ?_ ?_ ?_
  · intro entry hentry info heq
    rcases List.mem_map.mp (List.of_mem_zip hentry).1 with ⟨_, _, hfst⟩
    rw [← hfst] at heq
    cases heq
  · intro entry hentry info heq
    rcases List.mem_map.mp (List.of_mem_zip hentry).1 with ⟨_, _, hfst⟩
    rw [← hfst] at heq
    cases heq
  · intro familyName familyInfo hfamily name hname
    exact Or.inl (hpresent familyName familyInfo hfamily name hname)
  · intro entry hentry familyInfo heq name hname
    rcases List.mem_map.mp (List.of_mem_zip hentry).1 with ⟨info, hinfo, hfst⟩
    rw [← hfst] at heq
    cases heq
    exact habsent _ hinfo name hname

/-- Installing a batch containing no inductive headers preserves the
constructor-parameter agreement `ConstructorParameterAlignment`. Exact kernel-environment lookups are
transported through the lockstep fold; all abstract judgments use
the larger target environment of the same installation. -/
theorem AddConstants.preservesConstructorTyping
    (H : AddConstants installSafety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (Hsource : ConstructorParameterAlignment
      observer env venv)
    (hnind : ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ inductiveValue,
        info ≠ .inductInfo inductiveValue) :
    ConstructorParameterAlignment observer outEnv outVEnv := by
  intro familyName familyInfo hfamily hvisible i hi
  rcases H.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    exact ⟨C.rebaseKernel (H.preservesSourceFind hwf C.lookup) H.le⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    exact False.elim (hnind entry.1 entry.2 hentry familyInfo hinfo.symm)

/-- Refinement of the executable recursor loop `declareRecursors.loop`. In addition to
the generated entries (`GeneratedRecursorsRange`) and their installation (`AddConstants`),
every recursor entry carries its typed rules (`TypedRecursorRulesRange`): the field
classification and recursive calls of each generated iota rule. -/
theorem AddInductive.declareRecursors.loop.typingWF
    {sourceVEnv currentVEnv envTypes envCtors : VEnv}
    {decl : VInductDecl} {indTypes : Array InductiveType}
    {parameterDecls : VLCtx}
    {recursors : Nat → VConstVal}
    (Hcard : RecursorCounts stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    {recLparams : List Name} {depth : Nat}
    (c : AddInductive.Context) (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      parameterDecls)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ owner (_howner : owner < indTypes.size),
      ∀ ctor, ctor ∈ indTypes[owner]!.ctors →
        ∃ tail tailTarget introTarget,
          ParameterPrefix stats 0 ctor.type tail ∧
          Nonempty
            (ConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS R.venv recLparams R.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
            tailTarget)
    (numMinors numMotives : Nat) (all : List Name)
    (hnumMinors : numMinors = (recInfos.flatMap (·.minors)).size)
    (hnumMotives : numMotives = (recInfos.map (·.motive)).size)
    (k isUnsafe : Bool) (allowPrimitive : Bool)
    (hisUnsafe : isUnsafe = (c.safety != .safe))
    (hall : all = (indTypes.map (·.name)).toList)
    (hk : KEligible stats indTypes k)
    (dIdx : Nat) (hdone : dIdx ≤ indTypes.size)
    (env : Environment)
    (Hvalid : CheckingEnv.ValidCore c.safety env currentVEnv)
    (hle : sourceVEnv ≤ currentVEnv)
    (Htranslate : ∀ owner (_howner : owner < indTypes.size)
      (rules : List RecursorRule),
      TrConstVal c.safety sourceVEnv
          (.recInfo (AddInductive.declareRecursors.recursorInfo stats
            indTypes elimLevel recInfos numMinors numMotives all c.lctx k
            isUnsafe lparams owner rules)) (recursors owner) ∧
        (recursors owner).toVConstant.WF sourceVEnv)
    (hnprim : allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors.loop stats indTypes elimLevel recInfos
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) numMinors
      numMotives all c.lctx k isUnsafe lparams allowPrimitive dIdx env
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          out.2 = recursorMinorOffset indTypes indTypes.size ∧
          Nonempty (GeneratedRecursorsRange c.safety sourceVEnv lparams
            elimLevel c stats indTypes recInfos dIdx entries) ∧
          Nonempty (TypedRecursorRulesRange R decl stats
            indTypes recInfos Horigins elimLevel parameterDecls dIdx entries) ∧
          AddConstants c.safety env currentVEnv entries out.1 outVEnv ∧
          ∀ i (hi : i < entries.length), entries[i].2 = recursors (dIdx + i) := by
  rw [AddInductive.declareRecursors.loop]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have Hrules := AddInductive.mkRecRulesFromTemplates.WF indTypes
      elimLevel stats recInfos dIdx (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors)) c
    have HrulesState :
        ((liftM (AddInductive.mkRecRulesFromTemplates indTypes elimLevel
          stats recInfos dIdx (recInfos.map (·.motive))
          (recInfos.flatMap (·.minors))) :
            StateT Nat AddInductive.M (List RecursorRule))
          (recursorMinorOffset indTypes dIdx) c).WF fun out =>
            (out.1 = recInfos[dIdx]!.ruleTemplates.toList.map fun blueprint =>
              blueprint.instantiate indTypes stats (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors))
                (AddInductive.getRecLevels elimLevel stats.levels) c.lctx) ∧
            out.2 = recursorMinorOffset indTypes dIdx := by
      change (((fun rules => (rules, recursorMinorOffset indTypes dIdx)) <$>
        AddInductive.mkRecRulesFromTemplates indTypes elimLevel stats
          recInfos dIdx (recInfos.map (·.motive))
          (recInfos.flatMap (·.minors)) c).WF _)
      exact Hrules.map fun _ hrules => ⟨hrules, rfl⟩
    simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift, bind,
      StateT.bind, ReaderT.bind, pure, ReaderT.pure,
      _root_.modify, MonadState.modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet]
    exact HrulesState.bind fun generated hrules => by
      have hsize : recInfos.size = indTypes.size := by
        rw [Hcard.records]
        simpa using
          (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl).symm
      have HgeneratedPair := Hblueprints.boundGeneratedRules
        HminorSources elimLevel HblueprintSemantics HminorSemantics Hbindings
        Hparams hnoalias hsize hcounts dIdx hidx
      rw [← hrules.1] at HgeneratedPair
      rcases HgeneratedPair with
        ⟨Hgenerated, ⟨HgeneratedMotive⟩, HgeneratedOrigins⟩
      let info := AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams dIdx generated.1
      have hinfoName : info.name = Lean.mkRecName indTypes[dIdx]!.name := rfl
      have hstateNext : generated.2 + indTypes[dIdx]!.ctors.length =
          recursorMinorOffset indTypes (dIdx + 1) := by
        rw [hrules.2, recursorMinorOffset_step indTypes dIdx hidx]
      have hnormalize :
          ((env.checkName info.name allowPrimitive).bind fun a =>
            Except.pure (a, generated.2 + indTypes[dIdx]!.ctors.length)).bind (fun checked =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info)) checked.2 c) =
          (env.checkName info.name allowPrimitive).bind (fun _ =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info))
                  (recursorMinorOffset indTypes (dIdx + 1)) c) := by
        rw [hstateNext]
        cases env.checkName info.name allowPrimitive <;> rfl
      refine Except.WF.pureBind ?_
      rw [hnormalize]
      have Hname := checkName.WF Hvalid.tr.map_wf info.name allowPrimitive
      exact Hname.bind fun _ Hchecked => by
          let recursor := recursors dIdx
          rcases Htranslate dIdx hidx generated.1 with
            ⟨HtrSource, HwfSource⟩
          rcases CheckingEnv.exists_addConst Hvalid.tr Hchecked.1
              recursor.toVConstant with ⟨nextVEnv, hadd⟩
          have Htr : TrConstVal c.safety currentVEnv (.recInfo info) recursor :=
            HtrSource.mono hle
          have Hwf : recursor.toVConstant.WF currentVEnv :=
            HwfSource.mono hle
          have hname : info.name = recursor.name := Htr.2
          have haddInfo :
              currentVEnv.addConst info.name recursor.toVConstant =
                some nextVEnv := by
            simpa [hname] using hadd
          have hnprimInfo :
              ¬ Kernel.Environment.primitives.contains
                (ConstantInfo.recInfo info).name := by
            change ¬ Kernel.Environment.primitives.contains info.name
            cases hallow : allowPrimitive with
            | false =>
              intro hp
              have := Hchecked.2 hp
              simp [hallow] at this
            | true =>
              simpa [ConstantInfo.name, ConstantInfo.toConstantVal, info,
                AddInductive.declareRecursors.recursorInfo] using
                hnprim hallow dIdx hidx
          have HnextValid : CheckingEnv.ValidCore c.safety
              (env.add (.recInfo info)) nextVEnv :=
            Hvalid.add (ci := .recInfo info) Hchecked.1 hnprimInfo Htr.1 Hwf
              haddInfo rfl
          have hnextLe : sourceVEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddInfo)
          have Htail := AddInductive.declareRecursors.loop.typingWF Hcard
            Hdecl c R Hstats hconsume hlit hctx Hbindings Horigins
            Hblueprints HblueprintSemantics HminorSources HminorSemantics
            Hparams hnoalias hcounts hparameterUp Hseed numMinors numMotives
            all hnumMinors hnumMotives k isUnsafe
            allowPrimitive hisUnsafe hall hk (dIdx + 1) (by omega)
            (env.add (.recInfo info)) HnextValid hnextLe Htranslate hnprim
          exact Htail.mono fun out Hout => by
            rcases Hout with
              ⟨outVEnv, entries, hstate, ⟨Hrange⟩, ⟨HsemRange⟩,
                Hinstalled, Htargets⟩
            let entry : ConstantInfo × VConstVal := (.recInfo info, recursor)
            have Hentry : GeneratedRecursorEntry c.safety sourceVEnv lparams
                elimLevel c stats indTypes recInfos dIdx entry := by
              exact GeneratedRecursorEntry.ofRecursorInfo c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos numMinors
                numMotives all hnumMinors hnumMotives k isUnsafe dIdx
                generated.1 recursor hisUnsafe hall hk
                HtrSource
                Hgenerated.bound hrules.1
            have Hrange' : GeneratedRecursorsRange c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos dIdx
                (entry :: entries) := by
              refine {
                covered := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hrange.covered
                entry := ?_ }
              intro i hi
              cases i with
              | zero => simpa [entry] using Hentry
              | succ i =>
                have hi' : i < entries.length := by simpa using hi
                simpa [Nat.add_assoc, Nat.add_comm 1 i] using Hrange.entry i hi'
            have HsemRange' : TypedRecursorRulesRange R decl
                stats indTypes recInfos Horigins elimLevel parameterDecls dIdx
                (entry :: entries) := by
              refine {
                covered := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    HsemRange.covered
                entry := ?_ }
              intro i hi
              cases i with
              | zero =>
                exact ⟨info, by simp [entry], Hgenerated, ⟨by
                  simpa [info, AddInductive.declareRecursors.recursorInfo]
                    using HgeneratedMotive, by
                  intro localIndex hctor hrule
                  exact HgeneratedOrigins localIndex hctor hrule⟩⟩
              | succ i =>
                have hi' : i < entries.length := by simpa using hi
                have HtailEntry := HsemRange.entry i hi'
                have hownerOffset : dIdx + 1 + i = dIdx + (i + 1) := by
                  omega
                rw [hownerOffset] at HtailEntry
                rcases HtailEntry with
                  ⟨tailInfo, htailInfo, HtailRules, HtailMotive,
                    HtailOrigins⟩
                refine ⟨tailInfo, htailInfo, HtailRules, HtailMotive, ?_⟩
                intro localIndex hctor hrule
                exact HtailOrigins localIndex hctor hrule
            have Hinstalled' : AddConstants c.safety env currentVEnv
                (entry :: entries) out.1 outVEnv := by
              exact AddConstants.cons Hchecked.1
                hnprimInfo Htr Hwf haddInfo rfl Hinstalled
            refine ⟨outVEnv, entry :: entries, hstate, ⟨Hrange'⟩,
              ⟨HsemRange'⟩, Hinstalled', ?_⟩
            intro i hi
            cases i with
            | zero => rfl
            | succ i =>
              simpa [Nat.add_assoc, Nat.add_comm 1 i] using Htargets i (by simpa using hi)
  · rw [dif_neg hidx]
    have heq : dIdx = indTypes.size := by omega
    subst dIdx
    exact Except.WF.pure ⟨currentVEnv, [], rfl, ⟨
      { covered := by simpa [Hcard.records] using
          (show indTypes.size = recInfos.size from by
            have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              Hdecl
            have hsize : indTypes.size = decl.types.length := by
              simpa using htypes
            rw [hsize, ← Hcard.records])
        entry := by intro i hi; simp at hi }⟩, ⟨
      { covered := by simpa [Hcard.records] using
          (show indTypes.size = recInfos.size from by
            have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              Hdecl
            have hsize : indTypes.size = decl.types.length := by
              simpa using htypes
            rw [hsize, ← Hcard.records])
        entry := by intro i hi; simp at hi }⟩,
      .nil, by intro i hi; simp at hi⟩
termination_by indTypes.size - dIdx

/-- Install the chosen generator targets through the executable recursor declaration pass.
The executable's type check supplies their typing; the result records that every entry is
exactly its target, alongside the typed rules. -/
theorem AddInductive.declareRecursors.bindingWFOfTargets
    {envTypes envCtors : VEnv} {decl : VInductDecl}
    {indTypes : Array InductiveType} {parameterDecls : VLCtx}
    {currentVEnv : VEnv} {recLparams : List Name} {depth : Nat}
    (k : Bool)
    (hk : KEligible stats indTypes k)
    (Hvalid : CheckingEnv.Valid c.safety c.env currentVEnv)
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hcard : RecursorCounts stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv c.lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      parameterDecls)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ owner (_howner : owner < indTypes.size),
      ∀ ctor, ctor ∈ indTypes[owner]!.ctors →
        ∃ tail tailTarget introTarget,
          ParameterPrefix stats 0 ctor.type tail ∧
          Nonempty
            (ConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS R.venv recLparams R.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
            tailTarget)
    (targets : TrRecursorTypes currentVEnv c.lparams elimLevel c
      stats indTypes recInfos → Nat → VExpr)
    (Hcanonical : ∀ (T : TrRecursorTypes currentVEnv c.lparams elimLevel c
      stats indTypes recInfos) owner (_howner : owner < indTypes.size),
      TrExprS currentVEnv (AddInductive.getRecLevelParams elimLevel c.lparams) []
        (AddInductive.declareRecursors.recursorType stats recInfos c.lctx owner)
        (targets T owner))
    (hnotPartial : c.safety ≠ .partial)
    (hmode : c.fuel.cacheMode.Sound currentVEnv)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors stats indTypes elimLevel recInfos k
      c.lparams c).WF
      fun outEnv =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          Nonempty (GeneratedRecursors c.safety currentVEnv c.lparams
            elimLevel c stats indTypes recInfos entries) ∧
          Nonempty (TypedRecursorRulesRange R decl stats
            indTypes recInfos Horigins elimLevel parameterDecls 0 entries) ∧
          AddConstants c.safety c.env currentVEnv entries outEnv
            outVEnv ∧
          ∃ T : TrRecursorTypes currentVEnv c.lparams elimLevel c
            stats indTypes recInfos,
          ∀ i (hi : i < entries.length), entries[i].2 = {
            name := Lean.mkRecName indTypes[i]!.name
            uvars := (AddInductive.getRecLevelParams elimLevel c.lparams).length
            type := targets T i } := by
  unfold AddInductive.declareRecursors
  simp only [getLCtx, readThe, read]
  simp only [bind, ReaderT.bind]
  have Hcheck :
        (AddInductive.declareRecursors.checkRecursorTypes stats indTypes
          elimLevel recInfos (recInfos.flatMap (·.minors)).size
          (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList
          c.lctx k (c.safety != .safe) c.lparams 0 c).WF fun _ =>
            TrRecursorTypes currentVEnv c.lparams elimLevel c
              stats indTypes recInfos := by
      simpa using
        (AddInductive.declareRecursors.checkRecursorTypes.trRecursorTypesWF
          Hvalid hmode hnotPartial stats indTypes elimLevel recInfos
          (recInfos.flatMap (·.minors)).size
          (recInfos.map (·.motive)).size
          (indTypes.map (·.name)).toList c.lctx k (c.safety != .safe)
          c.lparams)
  refine Hcheck.bind fun _ Htypes => ?_
  have Hloop := AddInductive.declareRecursors.loop.typingWF
      (elimLevel := elimLevel) Hcard Hdecl c R Hstats hconsume hlit
      hctx Hbindings Horigins Hblueprints HblueprintSemantics
      HminorSources HminorSemantics Hparams hnoalias hcounts hparameterUp Hseed
      (recInfos.flatMap (·.minors)).size
      (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList
      rfl rfl k
      (c.safety != .safe) c.allowPrimitive rfl rfl hk 0 (by omega) c.env
      Hvalid.toValidCore VEnv.LE.rfl
      (fun owner howner rules => Htypes.recursorInfoTranslationOfTarget
        Hvalid.tr.wf k owner howner rules (Hcanonical Htypes owner howner)) hnprim
  change ((Prod.fst <$> AddInductive.declareRecursors.loop stats indTypes
      elimLevel recInfos (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors)) (recInfos.flatMap (·.minors)).size
      (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList c.lctx
      k (c.safety != .safe) c.lparams c.allowPrimitive 0 c.env 0 c).WF _)
  exact Hloop.map fun out Hout => by
    rcases Hout with
      ⟨outVEnv, entries, _hstate, ⟨Hrange⟩, ⟨HsemRange⟩,
        Hinstalled, Htargets⟩
    have hsize : entries.length = recInfos.size := by
      simpa using Hrange.covered
    exact ⟨outVEnv, entries, ⟨Hrange.atZero hsize⟩, ⟨HsemRange⟩,
      Hinstalled, Htypes, by simpa using Htargets⟩

end VerifyInductive
end Lean4Lean
