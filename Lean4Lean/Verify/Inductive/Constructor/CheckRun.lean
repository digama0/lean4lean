import Lean4Lean.Verify.Inductive.Constructor.Checked
import Lean4Lean.Verify.Inductive.Constructor.ParameterSyntacticTranslation
import Lean4Lean.Verify.Inductive.Constructor.RawTranslation
import Lean4Lean.Verify.Inductive.Constructor.OwnerNormalForms
import Lean4Lean.Verify.Inductive.Constructor.LiteralNames
import Lean4Lean.Verify.Inductive.Context.TypeAnnotations

/-! # The constructor check refines its abstract result

`AddInductive.checkConstructors.WF`: run in the header environment, the constructor check
fixes the declaration (its constructor types are the translations of the source ones, read off
the run: `checkConstructors.loopTypes.accumulatesRawTargets`) and establishes, in every header
environment of that declaration, the formation certificates, the checked tails and the owner
normal forms (`ConstructorsChecked`). Source branch: `Install/{Headers,Environments}.lean`
(`declareInductiveTypes.constructorsWF`, `checkConstructors.checkedWF`,
`checkConstructors.ownerNormalFormsWF`), over `Constructor/CheckedConstructors.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace CheckedHeaders

variable {env : VEnv} {Us : List Name} {nparams : Nat} {params : List VExpr}
  {commonLevel : VLevel} {sources : List InductiveType}

/-- The family with a checked header and the given constructors. -/
def familyOf (p : Sigma fun source => CheckedHeader env Us nparams params commonLevel source)
    (row : List VConstVal) : VInductiveType where
  toVConstVal := p.2.target
  numIndices := p.2.numIndices
  resultLevel := p.2.resultLevel
  ctors := row

/-- The declaration with the checked headers and the given constructor rows. -/
def declOf (H : CheckedHeaders env Us nparams params commonLevel sources) (isUnsafe : Bool)
    (rows : List (List VConstVal)) : VInductDecl where
  uvars := Us.length
  nparams := nparams
  isUnsafe := isUnsafe
  recs := []
  types := List.zipWith familyOf H.payloads rows

theorem declOf_describes (H : CheckedHeaders env Us nparams params commonLevel sources)
    (isUnsafe : Bool) {rows : List (List VConstVal)}
    (hrows : List.Forall₂ (fun (s : InductiveType) (row : List VConstVal) =>
      s.ctors.map (·.name) = row.map (·.name)) sources rows) :
    H.Describes (H.declOf isUnsafe rows) := by
  refine ⟨rfl, rfl, ?_⟩
  have go : ∀ {ps : List (Sigma fun source =>
      CheckedHeader env Us nparams params commonLevel source)} {rows : List (List VConstVal)},
      List.Forall₂ (fun (s : InductiveType) (row : List VConstVal) =>
        s.ctors.map (·.name) = row.map (·.name)) (ps.map Sigma.fst) rows →
      List.Forall₂ (fun (p : Sigma fun source =>
          CheckedHeader env Us nparams params commonLevel source) (t : VInductiveType) =>
        t.toVConstVal = p.2.target ∧ t.numIndices = p.2.numIndices ∧
        t.resultLevel = p.2.resultLevel ∧ t.ctors.map (·.name) = p.1.ctors.map (·.name))
        ps (List.zipWith familyOf ps rows) := by
    intro ps rows h
    induction ps generalizing rows with
    | nil => cases h; exact .nil
    | cons p ps ih =>
      cases h with
      | cons h hs => exact .cons ⟨rfl, rfl, rfl, h.symm⟩ (ih hs)
  exact go (by rw [H.sourceOrder]; exact hrows)

/-- Placeholder constructor rows with the source names. -/
def nameRows (sources : List InductiveType) : List (List VConstVal) :=
  sources.map fun s => s.ctors.map fun ct => { name := ct.name, uvars := 0, type := .sort .zero }

theorem nameRows_names : ∀ (sources : List InductiveType),
    List.Forall₂ (fun (s : InductiveType) (row : List VConstVal) =>
      s.ctors.map (·.name) = row.map (·.name)) sources (nameRows sources)
  | [] => .nil
  | s :: ss => .cons (by simp [List.map_map, Function.comp_def]) (nameRows_names ss)

end CheckedHeaders

/-- `checkConstructors` runs the family loop in the header checker context. -/
theorem AddInductive.checkConstructors.ofLoops {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {indTypes : Array InductiveType} {isUnsafe : Bool}
    {Q : List (List (List Bool)) → Prop}
    (h : (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
      (headerCheckContext c stats)).WF Q) :
    (AddInductive.checkConstructors indTypes stats isUnsafe c).WF Q := by
  rw [AddInductive.checkConstructors]
  refine AddInductive.M.WF_bind (P := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
  refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
  subst hL
  rw [AddInductive.withCheckLCtx_apply]
  exact h

/-- A raw source translation determines the abstract constant. -/
theorem TrSourceConstRaw.eq {env : VEnv} {Us : List Name} {name : Name} {type : Expr}
    {a b : VConstVal} (ha : TrSourceConstRaw env Us name type a)
    (hb : TrSourceConstRaw env Us name type b) : a = b := by
  obtain ⟨⟨au, aty⟩, an⟩ := a
  obtain ⟨⟨bu, bty⟩, bn⟩ := b
  have hu : au = bu := ha.uvars.trans hb.uvars.symm
  have hn : an = bn := ha.name.trans hb.name.symm
  have ht : aty = bty := TrExprS.unique ha.type hb.type
  subst hu hn ht; rfl

theorem rawNames {env : VEnv} {Us : List Name} :
    ∀ {ctors : List Constructor} {targets : List VConstVal},
    List.Forall₂ (fun (ctor : Constructor) (target : VConstVal) =>
      TrSourceConstRaw env Us ctor.name ctor.type target) ctors targets →
    ctors.map (·.name) = targets.map (·.name)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [h.name, rawNames hs]

theorem RawBlockCtorTranslations.names {env : VEnv} {Us : List Name} :
    ∀ {sources : List InductiveType} {rows : List (List VConstVal)},
    List.Forall₂ (fun source targets => List.Forall₂
      (fun (ctor : Constructor) (target : VConstVal) =>
        TrSourceConstRaw env Us ctor.name ctor.type target) source.ctors targets) sources rows →
    List.Forall₂ (fun (s : InductiveType) (row : List VConstVal) =>
      s.ctors.map (·.name) = row.map (·.name)) sources rows
  | _, _, .nil => .nil
  | _, _, .cons h hs => by
    exact .cons (rawNames h) (RawBlockCtorTranslations.names hs)

theorem CheckedHeaders.declOf_ctors {env : VEnv} {Us : List Name} {nparams : Nat}
    {params : List VExpr} {commonLevel : VLevel} {sources : List InductiveType}
    (H : CheckedHeaders env Us nparams params commonLevel sources) (isUnsafe : Bool)
    (rows : List (List VConstVal)) (hlen : rows.length = sources.length) :
    (H.declOf isUnsafe rows).types.map (·.ctors) = rows := by
  have hl : H.payloads.length = rows.length := by rw [H.payloads_length, hlen]
  simp only [CheckedHeaders.declOf]
  clear hlen
  generalize H.payloads = ps at hl
  induction ps generalizing rows with
  | nil => cases rows <;> simp_all
  | cons p ps ih =>
    cases rows with
    | nil => simp at hl
    | cons r rs => simp [CheckedHeaders.familyOf, ih rs (by simpa using hl)]

/-- The refinement theorem of the constructor check: run in the installed header environment,
`checkConstructors` fixes the declaration whose constructor types are the translations of
the source ones, and establishes its constructor certificates in every header environment of
it. -/
theorem AddInductive.checkConstructors.WF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    {headerEnv : Environment} (HI : InstalledHeaders P numNested isUnsafe headerEnv)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : ∀ owner ∈ indTypes.toList, ¬ Kernel.Environment.primitives.contains owner.name)
    (hlparams : c'.lparams.Nodup) :
    (AddInductive.checkConstructors indTypes stats isUnsafe { c' with env := headerEnv }).WF
      fun classes => ∃ decl, P.headers.Describes decl ∧ decl.isUnsafe = isUnsafe ∧
        ∀ H : HeaderEnvironment c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes
          headerEnv, ConstructorsChecked H.toData classes := by  -- WAVE 2 install COMPAT
  intro classes hrun
  -- the placeholder declaration gives a header environment to run the first pass in
  let H0 := HI.toHeaderEnvironment hvisible
    (P.headers.declOf_describes isUnsafe (CheckedHeaders.nameRows_names indTypes.toList)) rfl
  let Hc0 := H0.statsWF.parameterSuffix.headerCheck
  have hraw : Nonempty (RawBlockCtorTranslations Hc0.venv c'.lparams indTypes.toList) :=
    AddInductive.checkConstructors.ofLoops
      (checkConstructors.loopTypes.accumulatesRawTargets
        (Q := fun _ => Nonempty (RawBlockCtorTranslations Hc0.venv c'.lparams indTypes.toList))
        Hc0 (RawBlockCtorTranslations.empty _ _)
        (fun _ _ _ _ _ _ R hR => fun out _ => hR out) (fun h _ => ⟨h⟩)) classes hrun
  obtain ⟨R⟩ := hraw
  have hlen : R.targets.length = indTypes.toList.length :=
    (List.Forall₂.length_eq R.translations).symm
  let decl := P.headers.declOf isUnsafe R.targets
  have D : P.headers.Describes decl :=
    P.headers.declOf_describes isUnsafe (RawBlockCtorTranslations.names R.translations)
  refine ⟨decl, D, rfl, fun H => ?_⟩
  -- every header environment of `decl` has the installed abstract header environment
  have hv : H.context.venv = Hc0.venv := by
    have h1 := H.typesAdded
    rw [D.typeConstants] at h1
    have h0 := H0.typesAdded
    rw [(P.headers.declOf_describes isUnsafe
      (CheckedHeaders.nameRows_names indTypes.toList)).typeConstants] at h0
    exact Option.some.inj (h1.symm.trans h0)
  have hctors := P.headers.declOf_ctors isUnsafe R.targets hlen
  have Htypes : List.Forall₂ (TrInductiveTypeHeaders Hc'.venv H.context.venv c'.lparams)
      indTypes.toList decl.types := by
    apply List.forall₂_of_getElem (List.Forall₂.length_eq H.trSources)
    intro i hi hi'
    refine ⟨(List.forall₂_getElem H.trSources i hi hi').1, ?_⟩
    have hr := List.forall₂_getElem R.translations i hi (by rw [hlen]; exact hi)
    have hc : decl.types[i].ctors = R.targets[i]'(by rw [hlen]; exact hi) := by
      have h2 := List.getElem_of_eq hctors (i := i) (by simpa using hi')
      simpa using h2
    rw [hc, hv]
    exact hr
  let Hc := H.statsWF.parameterSuffix.headerCheck
  have hnprimDecl : ∀ T ∈ decl.types, ¬ Kernel.Environment.primitives.contains T.name := by
    intro T hT hp
    have hmem : T.name ∈ indTypes.toList.map (·.name) := by
      rw [← D.names]; exact List.mem_map_of_mem hT
    obtain ⟨o, ho, he⟩ := List.mem_map.mp hmem
    exact hnprim o ho (he ▸ hp)
  have hlit := H.checkedAvailableLiteralDisjoint hnprimDecl
  have Hchecked := AddInductive.checkConstructors.ofLoops
    (checkConstructors.loopTypes.refinesChecked (params := H.headers.params) Hc Htypes
      H.typesAdded H.statsWF H.headerParams
      H.statsWF.parameterSuffix.headerCheck_paramAligned consumeTypeAnnotationsCompat hlit
      (fun h => h) H.statsWF.universeBound hlparams) classes hrun
  have Howners : ConstructorOwnerNormalForms stats indTypes :=
    AddInductive.checkConstructors.ofLoops
      (checkConstructors.loopTypes.ownerNormalFormsWF
        (Q := fun _ => ConstructorOwnerNormalForms stats indTypes) (isUnsafe := isUnsafe)
        Hc Htypes (ConstructorOwnerNormalFormRows.empty stats indTypes)
        H.statsWF.parameterSuffix.toHeaderCheck
        (checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped H.statsWF)
        H.statsWF.parameterSuffix.headerCheck_paramAligned consumeTypeAnnotationsCompat hlit
        (fun Hrows _ => Hrows.complete)) classes hrun
  have hscopeWF := H.statsWF.parameterEmbedding.scopeWF H.context.checking.tr.wf
  have hparamsSize :=
    (checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped H.statsWF).params_size
  have hparamsCtx : H.context.venv.IsDefEqCtx c'.lparams.length [] H.headers.params.reverse
      H.statsWF.parameterScope.toCtx := by
    rw [← H.headerParams]; exact H.statsWF.paramsContext
  have htypesLen : indTypes.size = decl.types.length := by
    simpa using List.Forall₂.length_eq Htypes
  refine {
    ctorTr := ?_
    parameterShapes := Hchecked.parameterShapes H.context.wf Htypes hscopeWF hparamsSize
      H.uvars hparamsCtx
    shapes := Hchecked.checked.formation
    rawShapes := Hchecked.rawShapes H.context.wf Htypes hscopeWF hparamsSize
    types := Hchecked.checked.types
    classes_length := Hchecked.constructorTails.classes_length
    tails := ?_
    parameterPrefixes := Hchecked.parameterPrefixes
    constructorTails := Hchecked.constructorTails
    ownerNormalForms := Howners }
  · refine List.Forall₂.imp (fun s t h => ?_) (Lean4Lean.List.Forall₂.and_mem Htypes)
    obtain ⟨h, _, ht⟩ := h
    refine List.Forall₂.imp (fun ct ct' hc => ?_) (Lean4Lean.List.Forall₂.and_mem h.ctors)
    obtain ⟨hc, _, hct'⟩ := hc
    have hmem : ct' ∈ decl.constructorConstants := List.mem_flatMap.mpr ⟨t, ht, hct'⟩
    have hu : ct'.uvars = decl.uvars := hc.uvars.trans H.uvars.symm
    refine ⟨hc.uvars, hc.name, hc.type, ?_⟩
    have := Hchecked.checked.types ct' hmem
    show H.context.venv.IsType ct'.uvars [] ct'.type
    rw [hu]; exact this
  · intro i hi j hj
    have hs : i < indTypes.size := htypesLen ▸ hi
    have Hi := List.forall₂_getElem Htypes i (by simpa using hs) hi
    have hjs : j < indTypes[i].ctors.length := by
      have := List.Forall₂.length_eq Hi.ctors
      simp only [Array.getElem_toList] at this
      omega
    obtain ⟨ctorVal, tail, tailTarget, sourceDomains, hmem, hraw, -, -, htail, hcert,
      ⟨tele⟩⟩ := Hchecked.constructorTails.replay i hs j hjs
    have hraw' := List.forall₂_getElem Hi.ctors j (by simpa using hjs) hj
    simp only [Array.getElem_toList] at hraw'
    have heq : ctorVal = decl.types[i].ctors[j] := TrSourceConstRaw.eq hraw hraw'
    subst heq
    have hidx : tele.indices = [] := List.eq_nil_of_length_eq_zero tele.indexCount
    have hctx : H.statsWF.parameterScope.toCtx = tele.params.reverse := by
      simpa [hidx] using tele.scopeCtx
    refine ⟨tele.params, tailTarget, ?_, ?_, ?_⟩
    · rw [← hctx, H.uvars]; exact hparamsCtx
    · have := tele.header
      simp only [hidx, List.append_nil] at this
      rw [H.uvars]; exact ⟨_, this⟩
    · rw [← hctx]; exact hcert

end VerifyInductive
end Lean4Lean
