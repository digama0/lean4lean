import Lean4Lean.Verify.Inductive.RecursorInput
import Lean4Lean.Verify.Inductive.Primitive.Shape

/-! # The primitive header installation

`declareInductiveTypes` on a primitive `Bool`/`Nat` declaration installs the family header
before its constructors, so the header-only environment does not satisfy the primitive
invariant `HasPrimitives` and has no valid checker context (`ContextWF`). The header fold still
keeps the translation invariant `CheckingEnv` (`declareInfos_checking`), which is what the
recursor phase's input records of the header environment (`HeaderData`, with its context a
`LocalContextWF`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Move a local context to a larger environment over the same local context. -/
def LocalContextWF.withEnv {c : AddInductive.Context} (H : LocalContextWF c)
    {env' : Environment} {venv' : VEnv} (hchecking : CheckingEnv c.safety env' venv')
    (hle : H.venv ≤ venv') : LocalContextWF { c with env := env' } where
  venv := venv'
  checking := hchecking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf.mono hle
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  check := H.check.mono hle

namespace HeaderInstallation

/-- The header fold keeps the translation invariant, with the translated headers added to the
abstract environment. No primitive invariant is claimed: on the primitive path the header-only
environment violates it. -/
theorem declareInfos_checking {safety : DefinitionSafety} (allow : Bool) (sourceEnv : VEnv) :
    ∀ (infos : List InductiveVal) (values : List VConstVal) (env : Environment) (venv : VEnv),
    List.Forall₂ (fun info v =>
      TrConstVal safety sourceEnv (.inductInfo info) v ∧ v.toVConstant.WF sourceEnv)
      infos values →
    sourceEnv ≤ venv →
    CheckingEnv safety env venv →
    (AddInductive.declareInductiveTypeInfos allow infos env).WF fun out =>
      ∃ outVEnv, venv.addConstVals values = some outVEnv ∧ venv ≤ outVEnv ∧
        CheckingEnv safety out outVEnv
  | [], [], env, venv, .nil, _, hC => Except.WF.pure ⟨venv, rfl, VEnv.LE.rfl, hC⟩
  | info :: infos, v :: values, env, venv, .cons hentry hrest, hle, hC => by
    rw [AddInductive.declareInductiveTypeInfos]
    have hwf := hC.map_wf
    refine (checkName.WF hwf info.name allow).bind fun _ ⟨hn, _⟩ => ?_
    have hn' : env.find? (ConstantInfo.inductInfo info).name = none := hn
    have hname : info.name = v.name := hentry.1.2
    have hvnone : venv.constants info.name = none := by
      cases h : venv.constants info.name with
      | none => rfl
      | some ci =>
        obtain ⟨c, hc, -⟩ := hC.find?_iff.2 ⟨ci, h⟩
        rw [hn] at hc; cases hc
    obtain ⟨venv', hadd⟩ : ∃ venv', venv.addConst info.name v.toVConstant = some venv' := by
      simp [VEnv.addConst, hvnone]
    have hle' : venv ≤ venv' := VEnv.addConst_le hadd
    have hC' := hC.add (ci := .inductInfo info) hn' (hentry.1.1.mono hle) (hentry.2.mono hle)
      hadd rfl
    refine (declareInfos_checking allow sourceEnv infos values (env.add (.inductInfo info)) venv'
      hrest (hle.trans hle') hC').mono
      fun out ⟨outVEnv, hvals, hle'', h1⟩ => ⟨outVEnv, ?_, hle'.trans hle'', h1⟩
    simp only [VEnv.addConstVals, ← hname, hadd, Option.bind_eq_bind, Option.bind_some]
    exact hvals

end HeaderInstallation

/-- The header installation of a declaration the checked headers describe, without the
primitive invariant: `declareInductiveTypes` yields the recursor phase's view of the header
environment (`HeaderData`). Valid for every declaration, primitive or not. -/
theorem AddInductive.declareInductiveTypes.dataWF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested isUnsafe c').WF
      fun headerEnv => headerEnv.constants.WF ∧ ∀ decl : VInductDecl,
        P.headers.Describes decl → decl.isUnsafe = isUnsafe →
        Nonempty (HeaderData c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes
          headerEnv) := by
  have hwf := Hc'.checking.tr.map_wf
  have hsize : stats.nindices.size = indTypes.size := P.nindices_size
  obtain ⟨hlen, hget⟩ := inductiveTypeInfos_getElem stats nparams indTypes numNested isUnsafe
    c'.lparams hsize
  let infos := (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
    c'.lparams).toList
  have hpayloads : P.headers.payloads.length = indTypes.toList.length := P.headers.payloads_length
  have hinfosPayloads : infos.length = P.headers.payloads.length := by
    rw [hpayloads]; exact hlen
  have Hentries : List.Forall₂ (fun info v =>
      TrConstVal c'.safety Hc'.venv (.inductInfo info) v ∧ v.toVConstant.WF Hc'.venv)
      infos P.headers.targets := by
    apply List.forall₂_of_getElem (by simpa [CheckedHeaders.targets] using hinfosPayloads)
    intro i hi hi'
    have hp : i < P.headers.payloads.length := by simpa [CheckedHeaders.targets] using hi'
    have hs : i < indTypes.toList.length := by rw [← hpayloads]; exact hp
    obtain ⟨hname, htype, hlp, -, hunsafe⟩ := hget i hs hi
    have hsrc := P.headers.payloads_getElem_fst i hp hs
    have htr : TrSourceConst Hc'.venv c'.lparams indTypes.toList[i].name indTypes.toList[i].type
        P.headers.payloads[i].2.target := by
      rw [← hsrc]; exact P.headers.payloads[i].2.translation
    simp only [CheckedHeaders.targets, List.getElem_map]
    exact ⟨TrSourceConst.inductInfo htr hlp hname htype (by rw [hunsafe]; exact hvisible),
      htr.wf⟩
  change (AddInductive.declareInductiveTypeInfos c'.allowPrimitive infos c'.env).WF _
  have HS := HeaderInstallation.declareInfos_structural c'.allowPrimitive infos c'.env hwf
  have HC := HeaderInstallation.declareInfos_checking c'.allowPrimitive Hc'.venv infos
    P.headers.targets c'.env Hc'.venv Hentries VEnv.LE.rfl Hc'.checking.tr
  intro out hout
  obtain ⟨hwfOut, hmap, hquot, hfresh, -, -, -⟩ := HS out hout
  obtain ⟨outVEnv, htypes, hle, hC⟩ := HC out hout
  refine ⟨hwfOut, fun decl D hdeclUnsafe => ?_⟩
  have htrHeaders : List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
      TrConstVal c'.safety Hc'.venv (.inductInfo info) t.toVConstVal ∧
      info.ctors = t.ctors.map (·.name)) infos decl.types := by
    have hdlen : decl.types.length = indTypes.toList.length := D.length
    apply List.forall₂_of_getElem (by rw [hdlen]; exact hlen)
    intro i hi hi'
    obtain ⟨hp, ht, -, -, hctors⟩ := D.getElem i hi'
    have hs : i < indTypes.toList.length := by rw [← hdlen]; exact hi'
    obtain ⟨hname, htype, hlp, hictors, hunsafe⟩ := hget i hs hi
    have hsrc := P.headers.payloads_getElem_fst i hp hs
    have htr : TrSourceConst Hc'.venv c'.lparams indTypes.toList[i].name indTypes.toList[i].type
        P.headers.payloads[i].2.target := by
      rw [← hsrc]; exact P.headers.payloads[i].2.translation
    rw [ht]
    refine ⟨TrSourceConst.inductInfo htr hlp hname htype (by rw [hunsafe]; exact hvisible), ?_⟩
    rw [hictors, hctors, hsrc]
  let L := Hc'.toLocal.withEnv (env' := out) hC hle
  let S := P.statsWF D
  exact ⟨{
    numNested := numNested
    infos := infos
    infos_eq := rfl
    map_eq := hmap
    quotInit_eq := hquot
    fresh := hfresh
    uvars := D.1
    nparams := D.2.1
    isUnsafe := hdeclUnsafe
    sourceContext := Hc'
    sourceContextVEnv := rfl
    context := L
    contextMLCtx := rfl
    typesAdded := by rw [D.typeConstants]; exact htypes
    headers := D.headerCertificate
    trHeaders := htrHeaders
    trSources := D.trSources
    sourceParameters := P.parameters
    sourcePresent := hpresent
    sourceStatsWF := S
    sourceHeaderParams := rfl
    statsWF := S.mono hle
    headerParams := rfl
    parameterScopeEq := rfl }⟩

end VerifyInductive
end Lean4Lean
