import Lean4Lean.Verify.Inductive.Primitive.Constants
import Lean4Lean.Verify.Inductive.Install.Environments

/-!
# Atomic installation of a primitive batch

Between installing the `Bool` or `Nat` family and its constructors the invariant
`HasPrimitives` is false, so the primitive path cannot use the ordinary `AddConstants` with
`ContextWF` after each step. This file provides the weaker objects used instead:
`LocalContextWF` (the local-context part of `ContextWF`), `AtomicAddConstants` (constants
added in lockstep to the kernel and abstract environments, with validity checked only once
the batch is complete), its preservation lemmas, the executable header and constructor folds
as atomic batches, and the primitive header and constructor environments
(`PrimitiveHeaderEnvironment`, `PrimitiveConstructorEnvironment`).  The primitive
constructor check built on them is `PrimitiveConstructorCheck`
(`Primitive/ConstructorParams.lean`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The part of `ContextWF` that remains meaningful while a primitive
inductive declaration is only partly installed.  In particular this record
does not assert `HasPrimitives`: that invariant is false between installing
the `Bool`/`Nat` family header and its constructors. -/
structure LocalContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv c.safety c.env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  typeCheckerLParams_eq : c.typeCheckerLParams = none
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : forall fv, fv ∈ mlctx.vlctx.fvars -> c.ngen.Reserves fv
  kernelFresh : forall fv, fv ∈ mlctx.vlctx.fvars ->
    ({} : TypeChecker.State).ngen.Reserves fv
  /-- The cache mode of the embedded checker runs is sound for the environment. -/
  cacheSound : c.fuel.cacheMode.Sound venv
  /-- The semantic checker context, embedded in the main one. -/
  check : CheckBase venv c.lparams mlctx c.lctx c.checkLCtx
  /-- The constructor telescope certificates, carried to the restored checker context. -/
  ctorTelescopes : CtorTelescopes c.safety c.env venv

def ContextWF.toLocal (H : ContextWF c) : LocalContextWF c where
  venv := H.venv
  checking := H.checking.tr
  ctorTelescopes := H.checking.ctorTelescopes
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  cacheSound := H.cacheSound
  check := H.check

/-- Move a local-context invariant across an extension of the kernel and
abstract environments.  Unlike `ContextWF.withEnv`, this operation intentionally needs no
primitive invariant. -/
def LocalContextWF.withEnv (H : LocalContextWF c)
    (hchecking : CheckingEnv c.safety env' venv')
    (hle : H.venv <= venv')
    (htels : CtorTelescopes c.safety env' venv') :
    LocalContextWF { c with env := env' } where
  venv := venv'
  checking := hchecking
  ctorTelescopes := htels
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf.mono hle
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  cacheSound := H.cacheSound.mono hle
  check := H.check.mono hle

/-- Restore the ordinary checker context exactly at an atomic completion point, given the
checking invariant there. -/
def LocalContextWF.toContextWF (H : LocalContextWF c)
    (hvalid : CheckingEnv.Valid c.safety c.env H.venv) :
    ContextWF c where
  venv := H.venv
  checking := hvalid
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  cacheSound := H.cacheSound
  check := H.check

/-- Kernel-environment and abstract constants installed in lockstep without
requiring their names to be nonprimitive.  This relation describes the batch
only: unlike
`AddConstants`, it has no theorem claiming preservation of `HasPrimitives`
or `CheckingEnv.Valid` after each step. -/
inductive AtomicAddConstants (safety : DefinitionSafety) :
    Environment -> VEnv -> List (ConstantInfo × VConstVal) ->
      Environment -> VEnv -> Prop
  | nil : AtomicAddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none ->
    TrConstVal safety venv ci ci' ->
    ci'.toVConstant.WF venv ->
    venv.addConst ci.name ci'.toVConstant = some venv' ->
    ci.deltaValue? = none ->
    AtomicAddConstants safety (env.add ci) venv' rest outEnv outVEnv ->
    AtomicAddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

theorem AtomicAddConstants.ofAddConstants
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    AtomicAddConstants safety env venv entries outEnv outVEnv := by
  induction H with
  | nil => exact .nil
  | cons hn _hnprim htr hwf hadd hdelta _ ih =>
    exact .cons hn htr hwf hadd hdelta ih

/-- Projection metadata commutes with a lockstep constant batch. -/
theorem AtomicAddConstants.addProjections
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv) :
    AtomicAddConstants safety env (venv.addProjections projections) entries
      outEnv (outVEnv.addProjections projections) := by
  induction H with
  | nil => exact .nil
  | cons hn htr hwf hadd hdelta _ ih =>
    exact .cons hn (htr.mono VEnv.addProjections_le)
      (hwf.mono VEnv.addProjections_le)
      (by rw [VEnv.addProjections_addConst, hadd]; rfl) hdelta ih

theorem AtomicAddConstants.addEliminators
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv) :
    AtomicAddConstants safety env (venv.addEliminators es) entries
      outEnv (outVEnv.addEliminators es) := by
  induction H with
  | nil => exact .nil
  | cons hn htr hwf hadd hdelta _ ih =>
    exact .cons hn (htr.mono VEnv.addEliminators_le)
      (hwf.mono VEnv.addEliminators_le)
      (by rw [VEnv.addEliminators_addConst, hadd]; rfl) hdelta ih

theorem AtomicAddConstants.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : AtomicAddConstants checkSafety env venv entries outEnv outVEnv) :
    AtomicAddConstants safety env venv entries outEnv outVEnv := by
  induction H with
  | nil => exact .nil
  | cons hn htr hwf hadd hdelta _ ih =>
      exact .cons hn ⟨htr.1.sf_mono hsafety, htr.2⟩ hwf hadd hdelta ih

theorem AtomicAddConstants.append
    (H1 : AtomicAddConstants safety env venv entries middleEnv middleVEnv)
    (H2 : AtomicAddConstants safety middleEnv middleVEnv rest outEnv outVEnv) :
    AtomicAddConstants safety env venv (entries ++ rest) outEnv outVEnv := by
  induction H1 with
  | nil => exact H2
  | cons hn htr hwf hadd hdelta _ ih =>
    exact .cons hn htr hwf hadd hdelta (ih H2)

theorem AtomicAddConstants.le
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv) :
    venv <= outVEnv := by
  induction H with
  | nil => exact VEnv.LE.rfl
  | cons _ _ _ hadd _ _ ih => exact (VEnv.addConst_le hadd).trans ih

/-- Replay an atomic constant batch in a larger abstract source environment.
Unlike `AddConstants.rebase`, this theorem deliberately assumes and preserves
only `CheckingEnv`: a canonical primitive header prefix need not satisfy the
global primitive invariant until its constructors have also been installed. -/
theorem AtomicAddConstants.rebase
    (H : AtomicAddConstants checkSafety prodEnv base entries outProd outBase)
    (Hchecking : CheckingEnv safety prodEnv largerBase)
    (hsafety : safety <= checkSafety)
    (hbase : base <= largerBase) :
    exists largerOut,
      AtomicAddConstants safety prodEnv largerBase entries outProd largerOut /\
      outBase <= largerOut := by
  induction H generalizing largerBase with
  | nil => exact ⟨largerBase, .nil, hbase⟩
  | cons hn htr hwf hadd hdelta _Htail ih =>
    rename_i baseHead ci ci' baseNext rest outProd outBase prodHead
    rcases CheckingEnv.exists_addConst Hchecking hn ci'.toVConstant with
      ⟨largerNext, hlargerAdd⟩
    have htrLarger : TrConstVal safety largerBase ci ci' :=
      ⟨(htr.1.sf_mono hsafety).mono hbase, htr.2⟩
    have hwfLarger : ci'.toVConstant.WF largerBase := hwf.mono hbase
    have HcheckingNext : CheckingEnv safety (prodHead.add ci) largerNext :=
      Hchecking.add hn htrLarger.1 hwfLarger hlargerAdd hdelta
    have hnext : baseNext <= largerNext :=
      VEnv.addConst_mono hbase hadd hlargerAdd
    rcases ih HcheckingNext hnext with ⟨largerOut, Htail, hout⟩
    exact ⟨largerOut,
      .cons hn htrLarger hwfLarger hlargerAdd hdelta Htail, hout⟩

/-- Every member of an atomic batch satisfies the same visibility
bound as an ordinary lockstep installation. -/
theorem AtomicAddConstants.entrySafety
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hentry : (info, value) ∈ entries) :
    safety ≤ info.safety := by
  induction H with
  | nil => simp at hentry
  | cons _ htr _ _ _ _ ih =>
    rcases List.mem_cons.mp hentry with hhead | htail
    · cases hhead
      exact htr.1.1
    · exact ih htail

/-- Kernel-environment and abstract entries in an atomic batch retain the same
constant name. -/
theorem AtomicAddConstants.entryNames
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hentry : entry ∈ entries) : entry.1.name = entry.2.name := by
  induction H with
  | nil => simp at hentry
  | cons _ htr _ _ _ _ ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact htr.2
    · exact ih htail

theorem AtomicAddConstants.checking
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hchecking : CheckingEnv safety env venv) :
    CheckingEnv safety outEnv outVEnv := by
  induction H with
  | nil => exact hchecking
  | cons hn htr hwf hadd hdelta _ ih =>
    exact ih (hchecking.add hn htr.1 hwf hadd hdelta)

theorem AtomicAddConstants.abstract
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv) :
    venv.addConstVals (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConstVals]
  | cons _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConstVals, ← htr.2, hadd]
    exact ih

theorem AtomicAddConstants.targetMapWF
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) : outEnv.constants.WF := by
  induction H with
  | nil => exact hwf
  | cons hn _htr _hciwf _hadd _hdelta _Htail ih =>
    rename_i _venvHead ci _ci' _venvNext _rest _outProd _outAbs envHead
    have hfresh : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    exact ih (hwf.insert ci.name ci hfresh)

/-- A lockstep batch adds no stored equation. -/
theorem AtomicAddConstants.defeqs
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv) :
    ∀ df, outVEnv.defeqs df → venv.defeqs df := by
  induction H with
  | nil => exact fun _ h => h
  | cons _ _ _ hadd _ _ ih =>
    intro df hdf
    rw [← VEnv.addConst_defeqs hadd]
    exact ih df hdf

/-- A lockstep batch of constants none of which is a recursor transports the
recursor facts of the checking invariant. -/
theorem AtomicAddConstants.recursorEnvCoherent
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hrecs : ∀ entry ∈ entries, ∀ rec : RecursorVal, entry.1 ≠ .recInfo rec)
    (hcoherent : RecursorEnvCoherent safety env.constants venv) :
    RecursorEnvCoherent safety outEnv.constants outVEnv := by
  induction H with
  | nil => exact hcoherent
  | @cons venv ci ci' venv' rest outEnv outVEnv env hn _ _ hadd _ _ ih =>
    have hfresh : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    refine ih (hwf.insert _ _ hfresh)
      (fun entry hentry => hrecs entry (by simp [hentry])) ?_
    exact hcoherent.insertNonRecursor hwf hfresh
      (fun rec => hrecs (ci, ci') (by simp) rec) (VEnv.addConst_le hadd)
      fun df hdf => by rwa [VEnv.addConst_defeqs hadd] at hdf

theorem AtomicAddConstants.quotInit_eq
    (H : AtomicAddConstants safety prodEnv venv entries outEnv outVEnv) :
    outEnv.quotInit = prodEnv.quotInit := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => exact ih

theorem AtomicAddConstants.aligned
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (Haligned : Aligned safety env.constants venv) :
    Aligned safety outEnv.constants outVEnv := by
  induction H with
  | nil => exact Haligned
  | cons hn htr _hwf hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← Haligned.map_wf.find?'_eq_find?]
      exact hn
    exact ih (Haligned.const hnMap htr.1 hadd rfl)

/-- Constants introduced by an atomic inductive batch have no delta value,
so any delta-bearing kernel-environment entry after the batch is inherited from the source. -/
theorem AtomicAddConstants.deltaConservative
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (Haligned : Aligned safety env.constants venv) :
    forall {name ci}, outEnv.constants.find? name = some ci ->
      ci.deltaValue?.isSome -> env.constants.find? name = some ci := by
  induction H with
  | nil => intro name ci hfind _; exact hfind
  | cons hn htr _hwf hadd hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    intro name found hfind hfoundDelta
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← Haligned.map_wf.find?'_eq_find?]
      exact hn
    have Haligned' : Aligned safety
        (envHead.constants.insert ci.name ci) venvNext :=
      Haligned.const hnMap htr.1 hadd rfl
    have hnext : (envHead.constants.insert ci.name ci).find? name =
        some found := ih Haligned' hfind hfoundDelta
    rw [Haligned.map_wf.find?_insert] at hnext
    split at hnext
    · cases hnext
      simp [hdelta] at hfoundDelta
    · exact hnext

/-- An atomic batch containing no inductive headers preserves closure of all
existing mutual families.  This requires only freshness in the kernel environment's constant map; it
does not require a valid abstract environment at an intermediate prefix. -/
theorem AtomicAddConstants.closesMutuals
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (hclosed : MutualInductivesClosed env)
    (hnind : ∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
      ∀ (value : InductiveVal),
      entry.1 ≠ ConstantInfo.inductInfo value) :
    MutualInductivesClosed outEnv := by
  induction H with
  | nil => exact hclosed
  | cons hn _htr _hciwf _hadd _hdelta _Htail ih =>
    rename_i _venvHead ci ci' _venvNext _rest _outProd _outAbs envHead
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    have hclosedNext : MutualInductivesClosed (envHead.add ci) := by
      change MutualInductivesClosed
        (Lean4Lean.AddInductive.addConstant envHead ci)
      exact hclosed.addNonInductive hwf hn
        (fun value => hnind (ci, ci') (by simp) value)
    exact ih hnextWF hclosedNext fun entry hentry value =>
      hnind entry (by simp [hentry]) value

/-- Every final lookup after an atomic batch is either inherited from the
source environment or is one of the exact batch entries. -/
theorem AtomicAddConstants.entryOrigin
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : outEnv.find? name = some found) :
    env.find? name = some found ∨
      ∃ entry ∈ entries, name = entry.1.name ∧ found = entry.1 := by
  induction H with
  | nil => exact Or.inl hfind
  | cons hn _htr _hciwf _hadd _hdelta _Htail ih =>
    rename_i _venvHead ci ci' _venvNext rest _outProd _outAbs envHead
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases ih hnextWF hfind with hnext |
        ⟨entry, hentry, hname, hfound⟩
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

/-- An atomic installation preserves the constructor telescope certificates
(`CtorTelescopes`), given the certificate step (`CtorTelescopeStep`) of each of
its entries (stated in the environment before the installation). -/
theorem AtomicAddConstants.ctorTelescopes
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hchecking : CheckingEnv safety env venv)
    (htels : CtorTelescopes safety env venv)
    (hsteps : ∀ entry ∈ entries, CtorTelescopeStep safety venv entry.1) :
    CtorTelescopes safety outEnv outVEnv := by
  induction H with
  | nil => exact htels
  | cons hn htr hwf hadd hdelta _ ih =>
    exact ih (hchecking.add hn htr.1 hwf hadd hdelta)
      (htels.add hchecking.map_wf hn (VEnv.addConst_le hadd) (hsteps _ List.mem_cons_self))
      fun e he => (hsteps e (List.mem_cons_of_mem _ he)).mono (VEnv.addConst_le hadd)

/-- An installation of no constructor adds no constructor lookup. -/
theorem AtomicAddConstants.ctors_of_noCtor
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hkinds : ∀ entry ∈ entries, ∀ info : ConstructorVal, entry.1 ≠ .ctorInfo info) :
    ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      env.find? name = some (.ctorInfo ci) := by
  intro name ci hfind
  rcases H.entryOrigin hwf hfind with h | ⟨entry, hentry, -, hci⟩
  · exact h
  · exact absurd hci.symm (hkinds entry hentry ci)

theorem _root_.Lean4Lean.inductInfo_zip_noCtor {infos : List InductiveVal}
    {values : List VConstVal} :
    ∀ entry ∈ List.zip (infos.map (fun info => ConstantInfo.inductInfo info)) values,
      ∀ info : ConstructorVal, entry.1 ≠ .ctorInfo info := by
  intro entry hentry info heq
  rcases List.mem_map.mp (List.of_mem_zip hentry).1 with ⟨_, _, hfst⟩
  rw [← hfst] at heq
  cases heq

/-- Every entry of an atomic batch is fresh with respect to the batch's
starting environment. -/
theorem AtomicAddConstants.entryFresh
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    env.find? info.name = none := by
  induction H with
  | nil => simp at hentry
  | cons hn _htr _hciwf _hadd _hdelta _Htail ih =>
    rename_i _venvHead ci ci' _venvNext rest _outProd _outAbs envHead
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

/-- Atomic installation preserves every kernel-environment lookup already present at
the start of the batch. -/
theorem AtomicAddConstants.preservesSourceFind
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : env.find? name = some found) :
    outEnv.find? name = some found := by
  induction H with
  | nil => exact hfind
  | cons hn _htr _hciwf _hadd _hdelta _Htail ih =>
    rename_i _venvHead ci _ci' _venvNext _rest _outProd _outAbs envHead
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

/-- A lockstep batch transports the quotient facts of the checking invariant,
given the equation-head facts at its endpoint. -/
theorem AtomicAddConstants.quotEnvCoherent
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hheads : EquationHeadsCoherent outEnv.constants outVEnv)
    (hquot : env.quotInit = true → QuotEnvCoherent env.constants venv) :
    outEnv.quotInit = true → QuotEnvCoherent outEnv.constants outVEnv := by
  intro hq
  rw [H.quotInit_eq] at hq
  refine (hquot hq).extend ?_ H.le hheads
  intro n ci hfind
  have hfind' : env.find? n = some ci := by
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    exact hfind
  have hout := H.preservesSourceFind hwf hfind'
  rwa [Lean.Kernel.Environment.find?, (H.targetMapWF hwf).find?'_eq_find?] at hout

/-- Constructor-owner presence is preserved by an exact atomic batch once
each constructor entry in that batch is accompanied by its installed owner.
This is the generic argument about the kernel environment's constant map;
inductive installation supplies the owner of each constructor from its header
and constructor folds. -/
theorem AtomicAddConstants.constructorOwnersPresent
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
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

/-- Every source-aligned entry of an atomic batch is present with its exact
kernel metadata at the endpoint of the batch. -/
theorem AtomicAddConstants.findEntry
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    outEnv.find? info.name = some info := by
  induction H with
  | nil => simp at hentry
  | cons hn _htr _hciwf _hadd _hdelta Htail ih =>
    rename_i _venvHead ci ci' _venvNext rest outProd outAbs envHead
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
        rw [(hwf.insert ci.name ci hfreshMap).find?'_eq_find?,
          hwf.find?_insert]
        simp
      have hi : info = ci := congrArg Prod.fst hhead
      simpa [hi] using hinstalled
    · exact ih hnextWF htail

/-- Constants hidden from an observer can be installed without changing that
observer's translated environment. -/
theorem AtomicAddConstants.trEnvIgnore
    (H : AtomicAddConstants checkSafety prodEnv venv entries outEnv outVEnv)
    (hhidden : ∀ entry ∈ entries, ¬ observerSafety ≤ entry.1.safety)
    (htr : TrEnv' observerSafety prodEnv.constants quotInit observerEnv) :
    TrEnv' observerSafety outEnv.constants quotInit observerEnv := by
  induction H with
  | nil => exact htr
  | cons hn _hentry _hwf _hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← htr.map_wf.find?'_eq_find?]
      exact hn
    have htrHead : TrEnv' observerSafety
        (envHead.constants.insert ci.name ci) quotInit observerEnv :=
      TrEnv'.ignore hnMap (hhidden (ci, ci') (by simp)) htr
    exact ih (fun entry hentry => hhidden entry (by simp [hentry])) htrHead

/-- Global primitive metadata can be restored once every primitive member of
the complete atomic batch is known to carry canonical safe metadata. -/
theorem AtomicAddConstants.safePrimitives
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hsource : ∀ {n ci}, env.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hentries : ∀ entry ∈ entries,
      Kernel.Environment.primitives.contains entry.1.name →
      entry.1.safety = .safe ∧ entry.1.levelParams = []) :
    ∀ {n ci}, outEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro n ci hfind hprimitive
  rcases H.entryOrigin hwf hfind with hold |
      ⟨entry, hentry, hname, hinfo⟩
  · exact hsource hold hprimitive
  · subst n
    subst ci
    exact hentries entry hentry hprimitive

/-- The executable mutual-header fold is an atomic batch (`AtomicAddConstants`) even when
`allowPrimitive` permits the canonical reserved family name.  The theorem
uses only `CheckingEnv`; no validity assertion is made for the resulting
header-only environment. -/
theorem AtomicAddConstants.ofDeclareInductiveTypeInfos
    (Hchecking : CheckingEnv safety env venv)
    (Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal safety sourceEnv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF sourceEnv)
      infos values)
    (hle : sourceEnv <= venv)
    (hadd : venv.addConstVals values = some outVEnv) :
    (AddInductive.declareInductiveTypeInfos allowPrimitive infos env).WF
      fun outEnv =>
        AtomicAddConstants safety env venv
          (List.zip (infos.map (fun info => .inductInfo info)) values)
          outEnv outVEnv := by
  induction Hentries generalizing env venv with
  | nil =>
    simp [AddInductive.declareInductiveTypeInfos, VEnv.addConstVals] at hadd ⊢
    subst outVEnv
    exact Except.WF.pure .nil
  | @cons info ci' infos values Hentry _ ih =>
    have hname : info.name = ci'.name := Hentry.1.2
    cases hnext : venv.addConst ci'.name ci'.toVConstant with
    | none => simp [VEnv.addConstVals, hnext] at hadd
    | some nextVEnv =>
      have hrest : nextVEnv.addConstVals values = some outVEnv := by
        simpa [VEnv.addConstVals, hnext] using hadd
      rw [AddInductive.declareInductiveTypeInfos]
      exact (checkName.WF Hchecking.map_wf info.name allowPrimitive).bind
        fun _ hchecked => by
          have hn : env.find? info.name = none := hchecked.1
          have htr : TrConstVal safety venv (.inductInfo info) ci' :=
            Hentry.1.mono hle
          have hwf : ci'.toVConstant.WF venv := Hentry.2.mono hle
          have haddHead :
              venv.addConst info.name ci'.toVConstant = some nextVEnv := by
            simpa [hname] using hnext
          have HnextChecking : CheckingEnv safety
              (env.add (.inductInfo info)) nextVEnv :=
            Hchecking.add hn htr.1 hwf haddHead rfl
          have hnextLe : sourceEnv <= nextVEnv :=
            hle.trans (VEnv.addConst_le haddHead)
          exact (ih HnextChecking hnextLe hrest).mono fun outEnv Hrest => by
            simpa using AtomicAddConstants.cons (ci := .inductInfo info)
              (ci' := ci') hn htr hwf haddHead rfl Hrest

/-- Atomic counterpart of the inner executable constructor fold.  Reserved
constructor names are admitted by the executable `allowPrimitive` flag, while
no validity is claimed for the abstract environment until the complete batch
is available. -/
theorem AtomicAddConstants.ofConstructorList
    {env : Environment} {venv sourceEnv : VEnv}
    {ctors : List Constructor} {values : List VConstVal}
    (mkInfo : Nat -> Constructor -> ConstructorVal)
    (Hchecking : CheckingEnv safety env venv)
    (Hentries : List.Forall₂
      (fun ctor ci' => TrSourceConst sourceEnv lparams ctor.name ctor.type ci')
      ctors values)
    (hle : sourceEnv <= venv)
    (hlevelParams : forall i ctor, (mkInfo i ctor).levelParams = lparams)
    (hname : forall i ctor, (mkInfo i ctor).name = ctor.name)
    (htype : forall i ctor, (mkInfo i ctor).type = ctor.type)
    (hvisible : forall i ctor, safety <=
      (if (mkInfo i ctor).isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (ctors.foldlM (init := (start, env)) fun
        (state : Nat × Environment) (ctor : Constructor) => do
      let (cidx, env) := state
      env.checkName ctor.name allowPrimitive
      pure (cidx + 1, env.add (.ctorInfo (mkInfo cidx ctor)))).WF
      fun result => exists outVEnv : VEnv,
        exists entries : List (ConstantInfo × VConstVal),
        entries.map Prod.snd = values ∧
        AtomicAddConstants safety env venv entries result.2 outVEnv ∧
        ConstructorListEntries mkInfo start ctors entries ∧
        (forall entry : ConstantInfo × VConstVal, entry ∈ entries ->
          exists info : ConstructorVal,
            entry.1 = ConstantInfo.ctorInfo info) ∧
        (forall entry : ConstantInfo × VConstVal, entry ∈ entries ->
          forall value : InductiveVal,
            entry.1 ≠ ConstantInfo.inductInfo value) := by
  induction Hentries generalizing start env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, [], rfl, .nil, .nil, by simp, by simp⟩
  | @cons ctor ci' ctors values Hentry _ ih =>
    rw [List.foldlM_cons]
    simpa using (checkName.WF Hchecking.map_wf ctor.name allowPrimitive).bind
      fun _ hchecked => by
        rcases Lean4Lean.VerifyInductive.CheckingEnv.exists_addConst
            Hchecking hchecked.1 ci'.toVConstant with
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
        have HnextChecking : CheckingEnv safety
            (env.add (.ctorInfo info)) nextVEnv :=
          Hchecking.add hfindInfo htr.1 hwf haddHead rfl
        have hnextLe : sourceEnv <= nextVEnv :=
          hle.trans (VEnv.addConst_le haddHead)
        exact (ih (start := start + 1) HnextChecking hnextLe).mono
          fun result Hrest => by
            rcases Hrest with
              ⟨outVEnv, entries, hvalues, Hinstalled, Haligned,
                hctor, hnind⟩
            have hvalues' :
                (((.ctorInfo info, ci') :: entries).map Prod.snd) =
                  ci' :: values := by simp [hvalues]
            have Hinstalled' := AtomicAddConstants.cons
              (ci := .ctorInfo info) (ci' := ci') hfindInfo
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

/-- Atomic counterpart of the outer mutual-family constructor fold. -/
theorem AtomicAddConstants.ofConstructorTypes
    {env : Environment} {venv sourceEnv : VEnv}
    {types : List InductiveType} {targets : List VInductiveType}
    (mkInfo : InductiveType -> Nat -> Constructor -> ConstructorVal)
    (Hchecking : CheckingEnv safety env venv)
    (Hentries : List.Forall₂
      (fun source target => List.Forall₂
        (fun ctor ci' =>
          TrSourceConst sourceEnv lparams ctor.name ctor.type ci')
        source.ctors target.ctors)
      types targets)
    (hle : sourceEnv <= venv)
    (hlevelParams : forall owner i ctor,
      (mkInfo owner i ctor).levelParams = lparams)
    (hname : forall owner i ctor, (mkInfo owner i ctor).name = ctor.name)
    (htype : forall owner i ctor, (mkInfo owner i ctor).type = ctor.type)
    (hvisible : forall owner i ctor, safety <=
      (if (mkInfo owner i ctor).isUnsafe then
        DefinitionSafety.unsafe else .safe)) :
    (types.foldlM (init := env) fun
        (env : Environment) (owner : InductiveType) => do
      let (_, env) <- owner.ctors.foldlM (init := (0, env)) fun
          (state : Nat × Environment) (ctor : Constructor) => do
        let (cidx, env) := state
        env.checkName ctor.name allowPrimitive
        pure (cidx + 1, env.add (.ctorInfo (mkInfo owner cidx ctor)))
      pure env).WF fun outEnv =>
        exists outVEnv : VEnv,
          exists entries : List (ConstantInfo × VConstVal),
          entries.map Prod.snd =
            targets.flatMap (fun target : VInductiveType => target.ctors) ∧
          AtomicAddConstants safety env venv entries outEnv outVEnv ∧
          ConstructorTypeEntries mkInfo types entries ∧
          (forall entry : ConstantInfo × VConstVal, entry ∈ entries ->
            exists info : ConstructorVal,
              entry.1 = ConstantInfo.ctorInfo info) ∧
          (forall entry : ConstantInfo × VConstVal, entry ∈ entries ->
            forall value : InductiveVal,
              entry.1 ≠ ConstantInfo.inductInfo value) := by
  induction Hentries generalizing env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, [], rfl, .nil, .nil, by simp, by simp⟩
  | @cons owner target types targets Hhead _ ih =>
    rw [List.foldlM_cons]
    let Hinner := AtomicAddConstants.ofConstructorList
      (start := 0) (allowPrimitive := allowPrimitive)
      (mkInfo owner) Hchecking Hhead hle
      (hlevelParams owner) (hname owner) (htype owner) (hvisible owner)
    simpa using Hinner.bind fun result Hresult => by
      rcases Hresult with
        ⟨middleVEnv, headEntries, hheadValues, HheadInstalled,
          HheadAligned, hheadCtor, hheadNind⟩
      have HnextChecking : CheckingEnv safety result.2 middleVEnv :=
        HheadInstalled.checking Hchecking
      have hnextLe : sourceEnv <= middleVEnv :=
        hle.trans HheadInstalled.le
      exact (ih HnextChecking hnextLe).mono fun outEnv Htail => by
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

/-- Forget the per-step details only after the complete abstract batch has
been identified.  This certificate still makes no validity claim. -/
theorem AtomicAddConstants.toConstantsInstallation
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hvalues : entries.map Prod.snd = constants) :
    PrimitiveConstantsInstallation venv outVEnv constants where
  installed := by simpa [hvalues] using H.abstract

/-- Atomic form of `AddConstants.listedConstructorsOfDeclaration`: after the headers and
then the constructors of a declaration are installed on an environment whose listed
constructors are present and coherent, every listed constructor is coherent. -/
theorem AtomicAddConstants.listedConstructorsOfDeclaration
    (Hheaders : AtomicAddConstants safety env venv headerEntries headerEnv headerVEnv)
    (Hctors : AtomicAddConstants safety' headerEnv venv' ctorEntries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hlisted : ListedConstructorsCoherent env) (hpresent : ListedConstructorsPresent env)
    (hinfos : ∀ entry ∈ headerEntries, ∃ numNested, ∃ info ∈ (AddInductive.inductiveTypeInfos
      stats nparams indTypes numNested isUnsafe lparams).toList, entry.1 = .inductInfo info)
    (hentries : ConstructorTypeEntries (AddInductive.constructorInfo stats lparams isUnsafe)
      indTypes.toList ctorEntries) :
    ListedConstructorsCoherent outEnv := by
  have hheaderWF := Hheaders.targetMapWF hwf
  intro familyName familyInfo hfamily name hname found hfound
  rcases Hctors.entryOrigin hheaderWF hfamily with hfamilyHeader | ⟨entry, hentry, -, hentryEq⟩
  · rcases Hheaders.entryOrigin hwf hfamilyHeader with hold | ⟨entry, hentry, hentryName, hentryEq⟩
    · rcases hpresent familyName familyInfo hold name hname with ⟨old, hold'⟩
      have hout := Hctors.preservesSourceFind hheaderWF (Hheaders.preservesSourceFind hwf hold')
      rw [hfound] at hout
      cases hout
      exact hlisted familyName familyInfo hold name hname _ hold'
    · rcases hinfos entry hentry with ⟨numNested, info, hinfo, hfst⟩
      rw [hfst] at hentryEq hentryName
      cases hentryEq
      rcases inductiveTypeInfos_ctors stats nparams indTypes numNested isUnsafe lparams hinfo
        with ⟨owner, howner, hownerName, hctors, hunsafe⟩
      rw [hctors] at hname
      obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hname
      rcases hentries.findSourceInduct howner hctor with
        ⟨ctorInfo, value, hmem, hctorName, hinduct, hctorUnsafe⟩
      have hctorFind : outEnv.find? ctorInfo.name = some (.ctorInfo ctorInfo) :=
        Hctors.findEntry hheaderWF hmem
      rw [hctorName, hfound] at hctorFind
      cases hctorFind
      refine ⟨ctorInfo, rfl, ?_, hctorUnsafe.trans hunsafe.symm⟩
      rw [hinduct, hentryName, ← hownerName]
      rfl
  · rcases hentries.ownerOfEntry hentry with ⟨_, _, _, hctorEq, -⟩
    rw [hctorEq] at hentryEq
    cases hentryEq

/-- Header result for the primitive branch.  It mirrors the ordinary
`HeaderEnvironment`, except that its checking context (`LocalContextWF`) and installation
(`AtomicAddConstants`) do not claim `HasPrimitives`. -/
structure PrimitiveHeaderEnvironment (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool)
    (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  entries : List (ConstantInfo × VConstVal)
  infos : exists numNested,
    entries.map Prod.fst =
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList.map (fun info => .inductInfo info)
  sourceAligned : exists numNested,
    InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList entries
  values : entries.map Prod.snd = decl.typeConstants
  context : LocalContextWF { c with env := outEnv }
  headers : HeaderCertificate sourceEnv decl
  translation : TrInductDeclHeaders sourceEnv c.lparams nparams
    indTypes.toList isUnsafe decl context.venv
  installed : AtomicAddConstants c.safety c.env sourceEnv entries
    outEnv context.venv
  sourceContext : ContextWF c
  /-- Every constructor a header of the source environment lists is present there. -/
  sourcePresent : ListedConstructorsPresent c.env
  sourceContextVEnv : sourceContext.venv = sourceEnv
  sourceStatsWF : checkInductiveTypes.loopInd.HeaderStatsWF
    sourceContext.venv c.lparams sourceContext.mlctx.vlctx stats decl depth
  sourceHeaderParams : sourceStatsWF.headers.params = headers.params
  statsWF : checkInductiveTypes.loopInd.HeaderStatsWF
    context.venv c.lparams context.mlctx.vlctx stats decl depth
  headerParams : statsWF.headers.params = headers.params
  parameterScopeEq : statsWF.parameterScope = sourceStatsWF.parameterScope

/-- Constructor installation completes the primitive batch and is the first
point at which the ordinary valid checking context is restored. -/
structure PrimitiveConstructorEnvironment
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (outEnv : Environment) where
  venvCtors : VEnv
  entries : List (ConstantInfo × VConstVal)
  values : entries.map Prod.snd = decl.constructorConstants
  installed : AtomicAddConstants c.safety headerEnv H.context.venv entries
    outEnv venvCtors
  sourceAligned : ConstructorTypeEntries
    (AddInductive.constructorInfo stats c.lparams isUnsafe)
    indTypes.toList entries
  infos : forall (entry : ConstantInfo × VConstVal), entry ∈ entries ->
    exists info : ConstructorVal, entry.1 = ConstantInfo.ctorInfo info
  nonInductive : forall (entry : ConstantInfo × VConstVal), entry ∈ entries ->
    forall value : InductiveVal,
    entry.1 ≠ ConstantInfo.inductInfo value
  translation : TrInductDeclConstructors H.context.venv c.lparams
    indTypes.toList decl venvCtors
  /-- The complete header/constructor batch is the canonical Bool or Nat batch. -/
  primitiveConstants :
    decl.typeConstants ++ decl.constructorConstants = primitiveBoolConstants ∨
      decl.typeConstants ++ decl.constructorConstants = primitiveNatConstants
  /-- Every installed entry with a reserved primitive name is safe and
  universe-monomorphic. -/
  safeEntries : ∀ entry ∈ H.entries ++ entries,
    Kernel.Environment.primitives.contains entry.1.name →
    entry.1.safety = .safe ∧ entry.1.levelParams = []
  /-- The checking context over the constructor environment.  The full checking invariant
  is only restored once the declaration's case eliminators and projections are registered
  (`PrimitiveConstructorCheck.projectedChecking`). -/
  context : LocalContextWF { c with env := outEnv }
  contextVEnv : context.venv = venvCtors
  contextMLCtx : context.mlctx = H.context.mlctx
  validCore : CheckingEnv.ValidCore c.safety outEnv venvCtors
  owners : ConstructorOwnersPresent outEnv
  equationHeads : EquationHeadsCoherent outEnv.constants venvCtors
  quot : outEnv.quotInit = true → QuotEnvCoherent outEnv.constants venvCtors

end VerifyInductive
end Lean4Lean
