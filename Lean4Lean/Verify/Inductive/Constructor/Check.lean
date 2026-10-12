import Lean4Lean.Verify.Inductive.ConstructorCheck

/-! # The constructor phase: `constructorPhase`

`AddInductive.constructorPhase` installs the headers (`declareInductiveTypes`), checks the
constructors against them (`checkConstructors`) and installs them (`declareConstructors`). Its
output is the constructor environment, the input of the recursor phase. `ConstructorCheck` is the
interface of that environment; `AddInductive.constructorPhase.WF` is the boundary theorem,
composing `declareInductiveTypes.WF` with the `checkConstructors` and `declareConstructors`
refinements. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The boundary theorem of the constructor phase: in the context of a completed header phase,
`constructorPhase` yields a constructor check for a declaration the checked headers describe,
whose classification is the one returned. The postcondition is `∃ R, R.classes = out.2`: the
form `Nonempty … ∧ ∀ R, R.classes = out.2` is unprovable, since nothing pins an arbitrary `R`'s
classes. -/
theorem AddInductive.constructorPhase.WF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c'.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe c'.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hnprimCtors : c'.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hlparams : c'.lparams.Nodup)
    (hclosed : MutualInductivesClosed c'.env)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.constructorPhase stats nparams indTypes numNested isUnsafe c').WF
      fun out => ∃ decl, P.headers.Describes decl ∧
        ∃ R : ConstructorCheck c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes out.1,
          R.classes = out.2 := by
  have HD := AddInductive.declareInductiveTypes.installedWF P numNested isUnsafe hvisible
    hnprimTypes hpresent
  have HP := AddInductive.declareInductiveTypes.allowsPrimitives (c := c') stats nparams indTypes
    numNested isUnsafe Hc'.checking.tr.map_wf
  unfold AddInductive.constructorPhase
  refine Except.WF.bind (fun r h => And.intro (HD r h) (HP r h))
    fun headerEnv ⟨⟨hwfH, Hhdr⟩, hprimH⟩ => ?_
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
  have habsent := AddInductive.declareConstructors.namesAbsent (c := { c' with env := headerEnv })
    (stats := stats) (indTypes := indTypes) (isUnsafe := isUnsafe) hwfH ctorEnv hdeclare
  obtain ⟨hmap, hquot, hfr, hnd⟩ := AddInductive.declareConstructors.WF
    (c := { c' with env := headerEnv }) stats indTypes isUnsafe hwfH ctorEnv hdeclare
  obtain ⟨HI⟩ := Hhdr habsent
  have hnprimOwner : ∀ owner ∈ indTypes.toList,
      ¬ Kernel.Environment.primitives.contains owner.name := by
    intro owner howner hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp howner
    obtain ⟨hlen, hget⟩ := inductiveTypeInfos_getElem stats nparams indTypes numNested isUnsafe
      c'.lparams P.nindices_size
    have hi' : i < (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
        c'.lparams).toList.length := by rw [hlen]; exact hi
    obtain ⟨hname, -⟩ := hget i hi hi'
    have hmem := List.getElem_mem hi'
    rw [← hname] at hp
    exact hnprimTypes (hprimH _ hmem hp) _ hmem hp
  obtain ⟨decl, hD, hU, hK⟩ := AddInductive.checkConstructors.WF P numNested isUnsafe HI
    hvisible hnprimOwner hlparams positivity hcheck
  let H := HI.toHeaderEnvironment hvisible hD hU
  have hnindices : ∀ i (hi : i < decl.types.length) (hn : i < stats.nindices.size),
      stats.nindices[i] = decl.types[i].numIndices := by
    intro i hi hn
    have h1 := congrArg (·[i]?) P.nindices
    have h2 := congrArg (·[i]?) hD.numIndices
    simp only [Array.getElem?_toList] at h1
    rw [← h2] at h1
    simpa [hi, hn] using h1
  have hnprim : ∀ cval ∈ ctorInfos stats c'.lparams isUnsafe indTypes.toList,
      ¬ Kernel.Environment.primitives.contains cval.name := fun cval hcval hp => by
    have hallow := (hfr cval hcval).2 hp
    obtain ⟨t, ht, j, ctor, hctor, rfl⟩ := mem_ctorInfos hcval
    exact hnprimCtors hallow t ht ctor hctor hp
  -- `CtorInstall` over the header data, with its primitive fields
  have hnprimFam : ∀ T ∈ decl.types, ¬ Kernel.Environment.primitives.contains T.name := by
    intro T hT hp
    obtain ⟨src, hsrc, htr⟩ := List.Forall₂.forall_exists_r H.trSources T hT
    exact hnprimOwner src hsrc (htr.1.name ▸ hp)
  have hprims := CtorInstall.ordinaryPrimitives H (hK H) hmap (fun cval hcval => (hfr cval hcval).1)
    hnd hnprim hnprimFam
  let I : CtorInstall c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes headerEnv ctorEnv
      positivity := {
    H := H.toHeaderData
    K := hK H
    map_eq := hmap
    quotInit_eq := hquot
    fresh := fun cval hcval => (hfr cval hcval).1
    nodup := hnd
    hasPrimitives := hprims.1
    safePrimitives := hprims.2.1
    literalDisjoint := hprims.2.2
    nindices_size := P.nindices_size
    nindices := hnindices
    params_size := P.params_size
    visible := hvisible }
  refine ⟨decl, hD, I.toConstructorCheck hclosed fun _ => ?_, rfl⟩
  intro T hT
  refine ⟨hnprimFam T hT, fun ctor hctor hp => ?_⟩
  have hmem : ctor ∈ decl.constructorConstants := List.mem_flatMap.mpr ⟨T, hT, hctor⟩
  obtain ⟨ci, hci, ⟨-, hname⟩, -, -⟩ :=
    List.Forall₂.forall_exists_r I.ctorEntries ctor hmem
  obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
  exact hnprim cval hcval (by rw [show cval.name = ctor.name from hname]; exact hp)

end VerifyInductive
end Lean4Lean
