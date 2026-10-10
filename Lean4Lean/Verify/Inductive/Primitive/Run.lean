import Lean4Lean.Verify.Inductive.Primitive.Shape
import Lean4Lean.Verify.Inductive.Install.Ordinary
import Lean4Lean.Verify.Inductive.Primitive.Install

/-! # The primitive run

The executable runs a recognized `Bool` or `Nat` declaration through the same pipeline with the
primitive-name exception enabled (`allowPrimitive := true`). Its header and constructor phases
are verified separately for the two finite shapes (the ordinary boundary theorems exclude
primitive names); the recursor phase is shared (`RecursorInput.recursorPhasesWF`).

Wave 2 scaffold: owned by the `Install/`+`Primitive/`+`Prelude/` agent (source branch:
`Primitive/{Run,Headers,Constructors,ConstructorCheck,ConstructorParams,BatchInstallation,
Constants,Context}.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The exact checker context selected by the executable's primitive branch. -/
def primitiveAddInductiveContext (env : Environment) (lparams : List Name)
    (isUnsafe : Bool) (fuel : FuelConfig) : AddInductive.Context :=
  { env := env, lparams := lparams,
    safety := if isUnsafe then .unsafe else .safe,
    allowPrimitive := true, fuel := fuel }

/-- Complete primitive run-with-stats result: the same shape as `OrdinaryInstallation`. -/
abbrev PrimitiveInstallation
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (outEnv : Environment) : Prop :=
  OrdinaryInstallation c stats nparams depth indTypes isUnsafe sourceEnv outEnv

/-- The constructor phase of a primitive declaration: the primitive names are installed with
their canonical types (`VEnv.HasPrimitives` is preserved by the resulting checking context). -/
theorem AddInductive.constructorPhase.primitiveWF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hsafety : isUnsafe = (c'.safety != .safe))
    (Hshape : PrimitiveInductiveShape c'.lparams nparams indTypes.toList isUnsafe)
    (hallow : c'.allowPrimitive = true)
    (hclosed : MutualInductivesClosed c'.env)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.constructorPhase stats nparams indTypes numNested isUnsafe c').WF
      fun out => ∃ decl, P.headers.Describes decl ∧
        ∃ R : RecursorInput c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes out.1,
          R.classes = out.2 := by
  have hunsafe : isUnsafe = false := Hshape.2.2.1
  have hlp : c'.lparams = [] := Hshape.1
  have hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe) := by
    rw [hunsafe]; exact DefinitionSafety.le_safe
  let rows := primitiveRows indTypes.toList
  let decl := P.headers.declOf isUnsafe rows
  have D : P.headers.Describes decl := P.headers.declOf_describes isUnsafe (primitiveRows_names _)
  have hrows : decl.types.map (·.ctors) = rows :=
    P.headers.declOf_ctors isUnsafe rows (by simp [rows, primitiveRows])
  have HD := AddInductive.declareInductiveTypes.dataWF P numNested isUnsafe hvisible hpresent
  unfold AddInductive.constructorPhase
  refine Except.WF.bind HD fun headerEnv ⟨hwfH, Hhdr⟩ => ?_
  intro out hout
  change (AddInductive.checkConstructors indTypes stats isUnsafe { c' with env := headerEnv } >>=
    fun positivity => (AddInductive.declareConstructors stats indTypes isUnsafe >>= fun ctorEnv =>
      pure (ctorEnv, positivity)) { c' with env := headerEnv }) = .ok out at hout
  cases hcheck : AddInductive.checkConstructors indTypes stats isUnsafe
      { c' with env := headerEnv } with
  | error e => rw [hcheck] at hout; cases hout
  | ok positivity =>
  rw [hcheck] at hout
  change (AddInductive.declareConstructors stats indTypes isUnsafe { c' with env := headerEnv } >>=
    fun ctorEnv => (pure (ctorEnv, positivity) : Except Exception _)) = .ok out at hout
  cases hdeclare : AddInductive.declareConstructors stats indTypes isUnsafe
      { c' with env := headerEnv } with
  | error e => rw [hdeclare] at hout; cases hout
  | ok ctorEnv =>
  rw [hdeclare] at hout
  cases hout
  obtain ⟨hmap, hquot, hfr, hnd⟩ := AddInductive.declareConstructors.WF
    (c := { c' with env := headerEnv }) stats indTypes isUnsafe hwfH ctorEnv hdeclare
  obtain ⟨H⟩ := Hhdr decl D rfl
  let PE : PrimitiveHeaderEnvironment c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes
      headerEnv := { H with translation := H.primitiveTranslation Hshape hrows }
  have hclasses : positivity = primitiveFieldClasses indTypes := PE.checkedClasses Hshape _ hcheck
  subst hclasses
  have hnindices : ∀ i (hi : i < decl.types.length) (hn : i < stats.nindices.size),
      stats.nindices[i] = decl.types[i].numIndices := by
    intro i hi hn
    have h1 := congrArg (·[i]?) P.nindices
    have h2 := congrArg (·[i]?) D.numIndices
    simp only [Array.getElem?_toList] at h1
    rw [← h2] at h1
    simpa [hi, hn] using h1
  -- the new constants of a primitive declaration are safe and universe-monomorphic
  have hsafe : ∀ {n ci}, ctorEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci h hp
    have hwfC : headerEnv.constants.WF := hwfH
    have hfrC : ∀ ci ∈ (ctorInfos stats c'.lparams isUnsafe indTypes.toList).map
        ConstantInfo.ctorInfo, headerEnv.find? ci.name = none := by
      intro ci hci
      obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
      exact (hfr cval hcval).1
    have hndC : (((ctorInfos stats c'.lparams isUnsafe indTypes.toList).map
        ConstantInfo.ctorInfo).map (·.name)).Nodup := by rw [List.map_map]; exact hnd
    rcases insertConsts_env_cases hmap hwfC hfrC hndC h with h | ⟨hmem, -⟩
    · have hfrH : ∀ ci ∈ H.infos.map ConstantInfo.inductInfo, c'.env.find? ci.name = none := by
        intro ci hci
        obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hci
        exact H.fresh info hinfo
      have hndH : ((H.infos.map ConstantInfo.inductInfo).map (·.name)).Nodup := by
        have := VEnv.addConstVals_names_nodup H.typesAdded
        rcases H.primitiveTranslation Hshape hrows with ⟨-, -, -, -, htr⟩
        have hn : (H.infos.map ConstantInfo.inductInfo).map (·.name) =
            decl.typeConstants.map (·.name) := by
          have go : ∀ {infos : List InductiveVal} {types : List VInductiveType},
              List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
                TrConstVal c'.safety Hc'.venv (.inductInfo info) t.toVConstVal ∧
                info.ctors = t.ctors.map (·.name)) infos types →
              (infos.map ConstantInfo.inductInfo).map (·.name) =
                types.map (·.toVConstVal.name) := by
            intro infos types h
            induction h with
            | nil => rfl
            | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h.1.2
          simpa [VInductDecl.typeConstants, List.map_map, Function.comp_def] using go H.trHeaders
        rw [hn]; exact this
      rcases insertConsts_env_cases H.map_eq Hc'.map_wf hfrH hndH h with h | ⟨hmem, -⟩
      · exact Hc'.checking.safePrimitives h hp
      · obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hmem
        rw [H.infos_eq] at hinfo
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hinfo
        obtain ⟨hlen, hget⟩ := inductiveTypeInfos_getElem stats nparams indTypes H.numNested
          isUnsafe c'.lparams P.nindices_size
        obtain ⟨-, -, hlpI, -, huI⟩ := hget i (by rw [← hlen]; exact hi) hi
        have huI' := huI.trans hunsafe
        have hlpI' := hlpI.trans hlp
        refine ⟨?_, ?_⟩
        · simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, huI']
          rfl
        · simp only [ConstantInfo.levelParams, ConstantInfo.toConstantVal]; exact hlpI'
    · obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨tp, -, j, ctor, -, rfl⟩ := mem_ctorInfos hcval
      refine ⟨?_, ?_⟩
      · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial,
          AddInductive.constructorInfo, hunsafe]
      · simp [ConstantInfo.levelParams, ConstantInfo.toConstantVal, AddInductive.constructorInfo,
          hlp]
  let I : CtorInstall c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes headerEnv ctorEnv
      (primitiveFieldClasses indTypes) := {
    H := PE.toHeaderData
    K := PE.constructorsChecked Hshape hrows
    map_eq := hmap
    quotInit_eq := hquot
    fresh := fun cval hcval => (hfr cval hcval).1
    nodup := hnd
    hasPrimitives := PE.hasPrimitives Hshape hrows
    safePrimitives := hsafe
    literalDisjoint := fun _ _ => (H.primitiveLiteralDisjoint Hshape).available
    nindices_size := P.nindices_size
    nindices := hnindices
    params_size := P.params_size
    visible := hvisible }
  exact ⟨decl, D, I.toRecursorInput hclosed, rfl⟩

/-- Source-aligned primitive result, retaining the exact abstract model from
which the executable header traversal began. -/
def PrimitiveRunResult
    (source : AddInductive.Context) (Hsource : ContextWF source) (nparams : Nat)
    (types : List InductiveType) (outEnv : Environment) : Prop :=
  ∃ c' stats, ∃ Hc' : ContextWF c',
    ∃ P : HeaderPhase Hsource nparams types.toArray c' Hc' stats,
      PrimitiveInductiveShape c'.lparams nparams types.toArray.toList (source.safety != .safe) ∧
      PrimitiveInstallation c' stats nparams P.depth Hc'.venv types.toArray
        (source.safety != .safe) outEnv

/-- The complete executable primitive checker. -/
theorem AddInductive.run.primitiveSourceAlignedWF
    {c : AddInductive.Context} {types : List InductiveType}
    (nparams numNested : Nat) (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (Hshape : PrimitiveInductiveShape c.lparams nparams types.toArray.toList (c.safety != .safe))
    (hallow : c.allowPrimitive = true)
    (hctx : Hc.mlctx.vlctx = [])
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF (PrimitiveRunResult c Hc nparams types) := by
  have hnonempty : 0 < types.toArray.size := by
    have := Hshape.types_nonempty
    cases h : types with
    | nil => rw [h] at this; exact absurd rfl this
    | cons _ _ => simp
  show (Kernel.Environment.checkDuplicatedUnivParams c.lparams >>= fun _ =>
      AddInductive.checkInductiveTypes nparams types.toArray (fun stats =>
        AddInductive.runWithStats stats nparams types.toArray numNested (c.safety != .safe))
        c).WF _
  refine Except.WF.bind (Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams)
    fun _ hnodup => ?_
  refine AddInductive.checkInductiveTypes.WF _ _ Hc hctx hnonempty fun {c' stats} Hc' P => ?_
  have hsafety : (c.safety != .safe) = (c'.safety != .safe) := by rw [P.safety_eq]
  have Hshape' : PrimitiveInductiveShape c'.lparams nparams types.toArray.toList
      (c.safety != .safe) := by
    rw [P.lparams_eq]; exact Hshape
  unfold AddInductive.runWithStats
  refine AddInductive.M.WF_bind
    (AddInductive.constructorPhase.primitiveWF P numNested _ hsafety Hshape'
      (P.allowPrimitive_eq.trans hallow) (P.env_eq ▸ Hclosed) (P.env_eq ▸ Hpresent))
    fun out Hout => ?_
  obtain ⟨ctorEnv, positivity⟩ := out
  obtain ⟨decl, -, R, hclasses⟩ := Hout
  refine (R.recursorPhasesWF (by rw [P.lparams_eq]; exact hnodup) hsafety
    (by rw [P.safety_eq]; exact HnotPartial)
    (fun _ => by simpa using Hshape'.recursorsNonprimitive) hclasses.symm).mono
    fun outEnv Hrec => ⟨c', stats, Hc', P, Hshape', decl, ctorEnv, R, Hrec⟩

end VerifyInductive
end Lean4Lean
