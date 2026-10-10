import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Environment.QuotCoherence
import Lean4Lean.Verify.Typing.PrimSpec

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

private theorem find?_add_of_ne
    {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hne : ci.name ≠ name) :
    (env.add ci).find? name = env.find? name := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change SMap.find?' (env.constants.insert ci.name ci) name = env.find? name
  rw [(hwf.insert ci.name ci hfresh).find?'_eq_find?,
    hwf.find?_insert, if_neg (by simpa using hne)]
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]

private theorem find?_add_cases
    {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hfind : (env.add ci).find? name = some found) :
    (name = ci.name ∧ found = ci) ∨ env.find? name = some found := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change SMap.find?' (env.constants.insert ci.name ci) name = some found at hfind
  rw [(hwf.insert ci.name ci hfresh).find?'_eq_find?,
    hwf.find?_insert] at hfind
  split at hfind
  · left
    exact ⟨(LawfulBEq.eq_of_beq (by assumption)).symm,
      (Option.some.inj hfind).symm⟩
  · right
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    exact hfind

/-- Adding a fresh non-constructor constant preserves constructor-owner
presence. -/
theorem ConstructorOwnersPresent.addNonConstructor
    {ci : ConstantInfo}
    (H : ConstructorOwnersPresent env)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnctor : ∀ info, ci ≠ .ctorInfo info) :
    ConstructorOwnersPresent (env.add ci) := by
  intro name info hfind
  rcases find?_add_cases hwf ci hfresh hfind with
    ⟨_, hnew⟩ | hold
  · exact False.elim (hnctor info hnew.symm)
  · rcases H name info hold with ⟨owner, howner, hmem⟩
    have hne : ci.name ≠ info.induct := by
      intro heq
      rw [← heq, hfresh] at howner
      contradiction
    exact ⟨owner, (find?_add_of_ne hwf ci hfresh hne).trans howner, hmem⟩

/-- Lookup classification for one fresh addition (public form of `find?_add_cases`). -/
theorem findAddFresh_cases {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hfind : (env.add ci).find? name = some found) :
    (name = ci.name ∧ found = ci) ∨ env.find? name = some found :=
  find?_add_cases hwf ci hfresh hfind

/-- An old lookup survives one fresh addition. -/
theorem findAddFresh_of_find {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hfind : env.find? name = some found) :
    (env.add ci).find? name = some found := by
  have hne : ci.name ≠ name := by
    intro heq
    subst name
    rw [hfind] at hfresh
    cases hfresh
  rw [find?_add_of_ne hwf ci hfresh hne]
  exact hfind

/-- Adding a fresh constant preserves listed-constructor coherence when every present header
that lists its name is coherent with it, and, for a header, when the names it lists are absent
afterwards. -/
theorem ListedConstructorsCoherent.add
    {ci : ConstantInfo}
    (H : ListedConstructorsCoherent env)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hold : ∀ familyName familyInfo,
      env.find? familyName = some (.inductInfo familyInfo) → ci.name ∈ familyInfo.ctors →
      ∃ info, ci = .ctorInfo info ∧ info.induct = familyName ∧
        info.isUnsafe = familyInfo.isUnsafe)
    (hnew : ∀ familyInfo, ci = .inductInfo familyInfo →
      ∀ name ∈ familyInfo.ctors, (env.add ci).find? name = none) :
    ListedConstructorsCoherent (env.add ci) := by
  intro familyName familyInfo hfamily name hname found hfound
  rcases find?_add_cases hwf ci hfresh hfamily with ⟨-, hheader⟩ | hfamilyOld
  · rw [hnew familyInfo hheader.symm name hname] at hfound
    cases hfound
  · rcases find?_add_cases hwf ci hfresh hfound with ⟨hnameEq, hfoundEq⟩ | hfoundOld
    · subst hnameEq hfoundEq
      exact hold familyName familyInfo hfamilyOld hname
    · exact H familyName familyInfo hfamilyOld name hname found hfoundOld

/-- Listed-constructor coherence passes to an environment whose lookups are all lookups of a
coherent one. -/
theorem ListedConstructorsCoherent.ofSub {env env' : Environment}
    (H : ListedConstructorsCoherent env')
    (hsub : ∀ {name found}, env.find? name = some found → env'.find? name = some found) :
    ListedConstructorsCoherent env :=
  fun familyName familyInfo hfamily name hname found hfound =>
    H familyName familyInfo (hsub hfamily) name hname found (hsub hfound)

/-- After a declaration's families are installed with their constructors, every listed
constructor is coherent: an old header lists only old constants, and each header of the
declaration is aligned with its installed constructors. -/
theorem ListedConstructorsCoherent.ofInductInfosFromDecl {source target : Environment}
    (hsourceWF : source.constants.WF) (htargetWF : target.constants.WF)
    (hlisted : ListedConstructorsCoherent source) (hpresent : ListedConstructorsPresent source)
    (hsub : ∀ {name found}, source.find? name = some found → target.find? name = some found)
    (H : InductInfosFromDecl source.constants target.constants decl) :
    ListedConstructorsCoherent target := by
  intro familyName familyInfo hfamily name hname found hfound
  have hfamilyMap : target.constants.find? familyName = some (.inductInfo familyInfo) := by
    rwa [Lean.Kernel.Environment.find?, htargetWF.find?'_eq_find?] at hfamily
  rcases H familyName familyInfo hfamilyMap with hold | ⟨familyIdx, hfamilyName, ⟨A⟩⟩
  · have hold' : source.find? familyName = some (.inductInfo familyInfo) := by
      rw [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
      exact hold
    rcases hpresent familyName familyInfo hold' name hname with ⟨old, hold''⟩
    rw [hsub hold''] at hfound
    cases hfound
    exact hlisted familyName familyInfo hold' name hname _ hold''
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hname
    have hctor : i < (decl.types[familyIdx]'A.familyIdx_lt).ctors.length := by
      rw [← A.constructors]; exact hi
    rcases A.constructor i hctor with ⟨C⟩
    have hlookup : target.find? familyInfo.ctors[i] = some (.ctorInfo C.info) := by
      rw [Lean.Kernel.Environment.find?, htargetWF.find?'_eq_find?]
      exact C.lookup
    rw [hlookup] at hfound
    cases hfound
    exact ⟨C.info, rfl, C.induct.trans hfamilyName.symm, C.isUnsafe.trans A.isUnsafe.symm⟩

theorem InductiveMemberInfos.addConstant
    {ci : ConstantInfo}
    (H : InductiveMemberInfos env names)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    InductiveMemberInfos (env.add ci) names := by
  induction H with
  | nil => exact .nil
  | @cons name value names hlookup Htail ih =>
    have hne : ci.name ≠ name := by
      intro heq
      subst name
      rw [hlookup] at hfresh
      contradiction
    exact .cons ((find?_add_of_ne hwf ci hfresh hne).trans hlookup) ih

theorem MutualInductiveClosure.addConstant
    {ci : ConstantInfo}
    (H : MutualInductiveClosure env targetName value)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    MutualInductiveClosure (env.add ci) targetName value := by
  refine ⟨H.members.addConstant hwf hfresh, H.target, H.names, ?_⟩
  intro member info hmember hfind
  rcases H.members.find hmember with ⟨oldInfo, hold⟩
  have hne : ci.name ≠ member := by
    intro heq
    subst member
    rw [hold] at hfresh
    contradiction
  have hfind' := hfind
  rw [find?_add_of_ne hwf ci hfresh hne] at hfind'
  have hinfo : info = oldInfo := by
    rw [hold] at hfind'
    exact ConstantInfo.inductInfo.inj (Option.some.inj hfind'.symm)
  subst info
  exact H.parameters member oldInfo hmember hold

/-- A fresh non-inductive kernel constant preserves complete mutual-block
metadata. -/
theorem MutualInductivesClosed.addNonInductive
    {ci : ConstantInfo}
    (H : MutualInductivesClosed env)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnind : ∀ value, ci ≠ .inductInfo value) :
    MutualInductivesClosed (env.add ci) := by
  intro targetName value hfind
  rcases find?_add_cases hwf ci hfresh hfind with
    ⟨_, hvalue⟩ | hold
  · exact False.elim (hnind value hvalue.symm)
  · exact (H targetName value hold).addConstant hwf hfresh

def ConstructorParameterAlignmentAt.mono
    (H : ConstructorParameterAlignmentAt
      env venv familyName familyInfo i hi)
    (hle : venv ≤ venv') :
    ConstructorParameterAlignmentAt
      env venv' familyName familyInfo i hi :=
  { H with
    familyLookup := hle.constants H.familyLookup
    constructorLookup := hle.constants H.constructorLookup
    familyDefEq := H.familyDefEq.mono hle
    constructorDefEq := H.constructorDefEq.mono hle
    parameterDomains := H.parameterDomains.mono hle }

/-- Transport `ConstructorParameterAlignmentAt` across an arbitrary
kernel-environment extension once the exact constructor lookup has been
shown to survive.  All semantic fields only require monotonicity of the
abstract environment. -/
def ConstructorParameterAlignmentAt.rebaseKernel
    (H : ConstructorParameterAlignmentAt
      env venv familyName familyInfo i hi)
    (hlookup : env'.find? familyInfo.ctors[i] = some (.ctorInfo H.info))
    (hle : venv ≤ venv') :
    ConstructorParameterAlignmentAt
      env' venv' familyName familyInfo i hi :=
  { H.mono hle with
    toCtorInfoCoherentAt :=
      { H.toCtorInfoCoherentAt with lookup := hlookup } }

theorem ConstructorParameterAlignment.mono
    (H : ConstructorParameterAlignment safety env venv)
    (hle : venv ≤ venv') :
    ConstructorParameterAlignment safety env venv' := by
  intro familyName familyInfo hfamily hvisible i hi
  rcases H familyName familyInfo hfamily hvisible i hi with ⟨C⟩
  exact ⟨C.mono hle⟩

end VerifyInductive

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  /-- The empty constant map, in either stage. -/
  | empty {s : Bool} : Aligned { stage₁ := s } .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)
  /-- Registering a pattern-reduction rule (an ι rule) changes neither the constant
  map nor the model's constants. -/
  | pat : Aligned C venv → Aligned C (venv.addPat p r)
  /-- An inductive block, inserted as a whole: the map gets the block's constants `cis`
  (fresh, with distinct names, in the order the kernel inserts them), the model the
  matching constants `l`, and each constant translates in the model environment holding
  the whole block — the types of a block's recursors mention all of its type formers and
  constructors, so a nested mutual block, which the kernel inserts type by type, cannot
  be aligned one constant at a time. The block's projection entries `es` (which add no
  constant) are registered with it, since the recursor types are translated where the
  block's structures already have their projections. -/
  | block {cis : List ConstantInfo} {l : List (Name × VConstant)} {es : List VProjectionEntry} :
    Aligned C venv →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup →
    List.Forall₂ (fun ci b => TrConstant safety (venv'.addProjections es) ci b.2 ∧ ci.name = b.1)
      cis l →
    l.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) venv = some venv' →
    Aligned (insertConsts C cis) (venv'.addProjections es)
  /-- Registering projection entries adds no constant. -/
  | projections : Aligned C venv → Aligned C (venv.addProjections entries)
  /-- Kernel constant maps are implementation maps rather than ordered declaration lists:
  exact lookup equivalence, together with well-formedness of the target representation,
  permits transport between insertion histories without changing their semantics. -/
  | mapExt : Aligned C venv → C'.WF →
      (∀ name, C.find? name = C'.find? name) → Aligned C' venv

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty_stage _
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih | pat _ ih | projections _ ih => exact ih
  | block _ hfr hnd _ _ ih => exact insertConsts_wf ih hfr hnd
  | mapExt _ htarget _ _ => exact htarget

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih | pat _ ih => exact ih
  | block H hfr hnd hblk hfold ih =>
    simp only [VEnv.addProjections_constants]
    constructor
    · rintro ⟨ci, hci, hs⟩
      rcases insertConsts_find? H.map_wf hfr hnd hci with h | ⟨hmem, hn⟩
      · obtain ⟨ci', hci'⟩ := ih.1 ⟨ci, h, hs⟩
        exact ⟨ci', (VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold).constants hci'⟩
      · obtain ⟨b, hb, -, hbn⟩ := hblk.forall_exists_l ci hmem
        refine ⟨b.2, ?_⟩
        rw [← hn, hbn]
        exact VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb
    · rintro ⟨ci', hci'⟩
      rcases VEnv.addConst_foldlM_constants_inv (nm := Prod.fst) (ci := Prod.snd) hfold hci'
        with h | ⟨b, hb, hbn, -⟩
      · obtain ⟨ci, hci, hs⟩ := ih.2 ⟨ci', h⟩
        refine ⟨ci, insertConsts_find?_mono H.map_wf.map₂ (fun d hd e => ?_) hci, hs⟩
        have := hfr d hd; rw [e, hci] at this; cases this
      · obtain ⟨ci, hci, htr, hcn⟩ := hblk.forall_exists_r b hb
        refine ⟨ci, ?_, htr.1⟩
        rw [← hbn, ← hcn]; exact insertConsts_find?_self H.map_wf hfr hnd ci hci
  | projections _ ih => simpa only [VEnv.addProjections_constants] using ih
  | mapExt _ _ heq ih => simpa only [← heq] using ih

/-- Every constant of an aligned constant map is stored under its own name. -/
theorem Aligned.find?_name (H : Aligned safety C venv)
    (h : C.find? name = some ci) : ci.name = name := by
  induction H with
  | empty => simp at h
  | ignoreConst H _ _ hname ih =>
    rw [H.map_wf.find?_insert] at h
    split at h
    · rename_i heq
      cases h
      rw [hname]
      exact LawfulBEq.eq_of_beq heq
    · exact ih h
  | const H _ _ _ hname ih =>
    rw [H.map_wf.find?_insert] at h
    split at h
    · rename_i heq
      cases h
      rw [hname]
      exact LawfulBEq.eq_of_beq heq
    · exact ih h
  | defeq _ ih => exact ih h
  | projections _ ih => exact ih h
  | pat _ ih => exact ih h
  | block H hfr hnd _ _ ih =>
    rcases insertConsts_find? H.map_wf hfr hnd h with h | ⟨-, hn⟩
    · exact ih h
    · exact hn
  | mapExt _ _ heq ih =>
    rw [← heq] at h
    exact ih h

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

/-- Registering the ι rules of a declaration keeps `Aligned`: every step is an `addPat`. -/
theorem Aligned.addRules {decl : VInductDecl} (h : Aligned safety C venv)
    (hP : decl.addRules venv = some venv') : Aligned safety C venv' := by
  unfold VInductDecl.addRules at hP
  refine VEnv.foldlM_inv (P := Aligned safety C) (fun r _ _ _ hA hfold => ?_) h hP
  refine VEnv.foldlM_inv (P := Aligned safety C) (fun ru _ _ _ hA' hstep => ?_) hA hfold
  unfold VEnv.addRecRule at hstep; split at hstep
  · cases hstep; exact hA'.pat
  · cases hstep

/-- Adding an inductive block keeps `Aligned`: the constant stages form one `Aligned.block`
step — the kernel inserts the block's constants in `H.order`, the model in stage order
(`VInductDecl.consts`, which `addTypesCtorsProjsRecs` folds over before the projection stage), and an `addConst` fold does
not depend on its order (`VEnv.addConst_foldlM_perm`); each constant translates in the
environment holding the whole block (`H.envR`). The ι-rule stage is `Aligned.addRules`. -/
theorem Aligned.addInduct (H : AddInduct safety C₁ venv₁ decl C₂ venv₂)
    (h : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  have leT : H.envT ≤ H.envR :=
    (VEnv.addCtors_le H.stC).trans (VEnv.addProjs_le.trans (VEnv.addRecs_le H.stR))
  -- the block's constants, kernel side and model side, matched by kind
  have hpair : List.Forall₂ (fun ci (b : Name × VConstant) =>
      TrConstant safety H.envR ci b.2 ∧ ci.name = b.1)
      (AddInduct.consts H.ivals H.rvals) decl.consts := by
    unfold AddInduct.consts VInductDecl.consts
    refine List.Forall₂.append (List.Forall₂.append ?_ ?_) ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact H.types.imp fun _ _ ht =>
        ⟨ht.tr.1.mono ((VEnv.addTypes_le H.stT).trans leT), ht.tr.2⟩
    · rw [← List.map_flatMap, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact (List.Forall₂.flatMap (fun _ _ ht => ht.ctors) H.types).imp fun _ _ hc =>
        ⟨hc.1.1.mono leT, hc.1.2⟩
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact H.recs.imp fun _ _ hr =>
        ⟨hr.tr.1.mono (VEnv.addRecs_le H.stR), hr.tr.2⟩  -- WAVE 2 rec COMPAT
  -- the constant stages are one fold, followed by the projection stage
  have hR := H.addTypesCtorsProjsRecs
  rw [VInductDecl.addTypesCtorsProjsRecs_eq] at hR
  obtain ⟨envF, hF, hFR⟩ := Option.map_eq_some_iff.1 hR
  -- the same matching, in the kernel's insertion order
  obtain ⟨l', hl', hpair'⟩ := List.Forall₂.perm_left H.order_perm hpair
  have hfold : l'.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) venv₁ = some envF :=
    VEnv.addConst_foldlM_perm (nm := Prod.fst) (ci := Prod.snd) hl'.symm hF
  rw [H.map_eq]
  have hpair'' : List.Forall₂ (fun ci (b : Name × VConstant) =>
      TrConstant safety (envF.addProjections decl.projectionEntries) ci b.2 ∧ ci.name = b.1)
      H.order l' := by
    have : envF.addProjections decl.projectionEntries = H.envR := hFR
    rw [this]; exact hpair'
  have hA := h.block H.order_fresh H.order_nodup hpair'' hfold
  have : envF.addProjections decl.projectionEntries = H.envR := hFR
  rw [this] at hA
  exact hA.addRules H.stP

theorem Aligned.addDefEqs {C : ConstMap} : ∀ {cis' : List VDefVal} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqs cis')
  | [], _, H => H
  | ci :: cis, venv, H => by
    show Aligned safety C (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis)
    exact Aligned.addDefEqs H.defeq

theorem Aligned.insertDefs : ∀ {cis : List DefinitionVal} {cis' : List VDefVal} {C venv venv'},
    Aligned safety C venv → (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    List.Forall₂ (fun ci ci' => TrConstVal safety venv (.defnInfo ci) ci'.toVConstVal) cis cis' →
    venv.addConsts cis' = some venv' → Aligned safety (insertDefs C cis) venv'
  | [], _, _, _, _, H, _, _, hblk, e => by
    cases hblk; simp [VEnv.addConsts] at e; cases e; exact H
  | ci :: cis, _, C, venv, _, H, hnd, hfr, hblk, e => by
    cases hblk with | @cons _ ci' _ _ htr hblk => ?_
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    have hname := htr.2
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1' : venv.addConst ci.name ci'.toVConstant = some venv₁ := by rw [hname]; exact h1
    show Aligned safety
      (_root_.Lean4Lean.insertDefs (SMap.insert C ci.name (.defnInfo ci)) cis) _
    refine Aligned.insertDefs (H.const (hfr _ (.head _)) htr.1 h1' rfl) hnd.2
      (fun c hc => ?_) (Lean4Lean.List.Forall₂.imp
        (fun _ _ h => h.mono (VEnv.addConst_le h1')) hblk) h2
    rw [H.map_wf.find?_insert]
    have : ¬ (ci.name == c.name) = true := by
      simp only [beq_iff_eq]; intro h
      exact hnd.1 ⟨c, hc, h.symm⟩
    simp [this]
    exact hfr c (.tail _ hc)

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | inductProjections _ _ ih => exact ih.projections
  | ignore h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | thm h1 h2 _ _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | mutualDef hblk hnd hfr _ hadd _ _ ih =>
    exact Aligned.addDefEqs <| ih.insertDefs hnd hfr
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) hblk) hadd
  | quot _ h _ ih => exact ih.addQuot h
  | induct _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

/-! ### Recursor lookup across the quotient constants

`pats_iota'` (below) pulls a `recInfo` lookup back across a `quot` step: `addQuot`
registers only `quotInfo` constants. -/

/-- Pull a `recInfo` lookup back across one fresh non-`recInfo` insertion: since
the inserted value is not a `recInfo`, a `recInfo` resolved in the extended map
was already resolved before the insertion. -/
theorem pull_recInfo {m : ConstMap} {name recName : Name} {q : ConstantInfo}
    {rval : RecursorVal} (wf : m.WF) (hq : ∀ v, q ≠ .recInfo v)
    (h : (m.insert name q).find? recName = some (.recInfo rval)) :
    m.find? recName = some (.recInfo rval) := by
  rw [wf.find?_insert] at h; split at h
  · exact absurd (Option.some.inj h) (hq rval)
  · exact h

/-- Pull-back combinator for one `AddQuot1` step: the inserted quotient constant
is a `quotInfo`, so a `recInfo` lookup passes through it. -/
theorem AddQuot1.pull {P : ConstMap → VEnv → Prop} {name kind ci' recName rval}
    (H1 : ∀ m env, m.WF → P m env → m.find? recName = some (.recInfo rval))
    (m env) (wf : m.WF) (H2 : AddQuot1 name kind ci' P m env) :
    m.find? recName = some (.recInfo rval) := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact pull_recInfo wf (fun _ => by nofun) (H1 _ _ (wf.insert _ _ h2) h4)

/-- A `recInfo` resolvable after adding the quotient constants was already
resolvable before: `addQuot` only registers `quotInfo` constants. -/
theorem AddQuot.pull {recName rval} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (hfind : C₂.find? recName = some (.recInfo rval)) :
    C₁.find? recName = some (.recInfo rval) := by
  dsimp [AddQuot] at H
  refine (AddQuot1.pull <| AddQuot1.pull <| AddQuot1.pull <| AddQuot1.pull ?_) _ _ wf H
  rintro m env hwf ⟨rfl, _⟩; exact hfind

/-- A constant other than a `quotInfo` resolvable after adding the quotient constants was
already resolvable before. -/
theorem AddQuot.pull_of {x ci} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (hq : ∀ v, ci ≠ .quotInfo v) (hfind : C₂.find? x = some ci) : C₁.find? x = some ci := by
  have step {P : ConstMap → VEnv → Prop} {name kind ci'}
      (H1 : ∀ m env, m.WF → P m env → m.find? x = some ci) (m env) (wf : m.WF)
      (H2 : AddQuot1 name kind ci' P m env) : m.find? x = some ci := by
    let ⟨_, _, _, _, h2, _, h4⟩ := H2
    have h := H1 _ _ (wf.insert _ _ h2) h4
    rw [wf.find?_insert] at h; split at h
    · exact absurd (Option.some.inj h).symm (hq _)
    · exact h
  dsimp [AddQuot] at H
  refine (step <| step <| step <| step ?_) _ _ wf H
  rintro m env _ ⟨rfl, _⟩; exact hfind

/-- Inserting a whole block of definitions preserves constant-map well-formedness,
provided every name is fresh and the block has no duplicate names. -/
theorem insertDefs_wf : ∀ {cis : List DefinitionVal} {C : ConstMap}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup → (insertDefs C cis).WF
  | [], _, hC, _, _ => hC
  | d :: ds, C, hC, hfr, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine insertDefs_wf (cis := ds) (hC.insert _ _ (hfr _ (.head _))) (fun e he => ?_) hnd.2
    rw [hC.find?_insert, if_neg]; · exact hfr e (.tail _ he)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (List.mem_map.2 ⟨e, he, hh.symm⟩)

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩
  | pat h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addPat_le⟩
  | block H hfr hnd hblk hfold ih =>
    rcases insertConsts_find? H.map_wf hfr hnd h with h' | ⟨hmem, hn⟩
    · exact mono ((VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold).trans
        VEnv.addProjections_le) (ih h')
    · obtain ⟨b, hb, htr, hbn⟩ := hblk.forall_exists_l ci hmem
      refine ⟨b.2, ?_, htr⟩
      rw [← hn, hbn, VEnv.addProjections_constants]
      exact VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb
  | projections _ ih =>
    rcases ih h with ⟨ci', hci', htr⟩
    exact ⟨ci', by simpa only [VEnv.addProjections_constants] using hci',
      htr.mono VEnv.addProjections_le⟩
  | mapExt _ _ heq ih => rw [← heq] at h; exact ih h

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩
  | pat h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addPat_le⟩
  | block H hfr hnd hblk hfold ih =>
    rw [VEnv.addProjections_constants] at hs
    rcases insertConsts_find? H.map_wf hfr hnd h with h' | ⟨hmem, hn⟩
    · rcases VEnv.addConst_foldlM_constants_inv (nm := Prod.fst) (ci := Prod.snd) hfold hs
        with hs' | ⟨b, hb, hbn, -⟩
      · obtain ⟨h1, h2⟩ := ih h' hs'
        exact ⟨h1, h2.mono ((VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold).trans
          VEnv.addProjections_le)⟩
      · exfalso
        obtain ⟨d, hd, -, hdn⟩ := hblk.forall_exists_r b hb
        have := hfr d hd; rw [hdn, hbn, h'] at this; cases this
    · obtain ⟨b, hb, htr, hbn⟩ := hblk.forall_exists_l ci hmem
      have := VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb
      rw [← hbn, hn, hs] at this
      cases this
      exact ⟨hn, htr⟩
  | projections _ ih =>
    rcases ih h (by simpa only [VEnv.addProjections_constants] using hs) with ⟨hname, htr⟩
    exact ⟨hname, htr.mono VEnv.addProjections_le⟩
  | mapExt _ _ heq ih => rw [← heq] at h; exact ih h hs

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem VEnv.addDefEqs_self : ∀ {cis' : List VDefVal} {venv : VEnv} {ci'}, ci' ∈ cis' →
    (venv.addDefEqs cis').defeqs ci'.toDefEq
  | ci :: cis, venv, _, hc => by
    show (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis).defeqs _
    cases hc with
    | head => exact VEnv.addDefEqs_le.defeqs VEnv.addDefEq_self
    | tail _ hc => exact VEnv.addDefEqs_self hc

theorem insertDefs_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertDefs C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ ConstantInfo.defnInfo d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    have h : (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci := h
    rcases insertDefs_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with h | ⟨e, he, h1, h2⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨d, .head _, by simpa using hb, rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, h1, h2⟩

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp at h
  | inductProjections _ _ ih => exact (ih h).mono VEnv.addProjections_le
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    have' le := (VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, rfl, rfl⟩
    · exact (ih h).mono le
    · obtain ⟨d', hd', htr, hval⟩ := Lean4Lean.List.Forall₂.forall_exists_l hblk _ hd
      cases hv
      have hdefeq := VEnv.IsDefEq.extra0 (VEnv.addDefEqs_self hd')
        ((H.mutualDef hblk hnd hfr ‹_› hadd ‹_›).wf.ordered.defEqWF (VEnv.addDefEqs_self hd'))
      let ⟨⟨b1, b2, b3⟩, b4⟩ := htr
      exact ⟨_, hval.mono VEnv.addDefEqs_le, b2.symm ▸ b4.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | thm h2 h3 h4 h5 h1 H ih =>
    have' le := VEnv.addConst_le h1
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      dsimp only [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal] at b2 b4 ⊢
      have hp := h5.mono le
      have hb := h4.mono le
      have hc := VEnv.HasType.const0 (VEnv.addConst_self h1) ⟨_, hp⟩
      rw [b4] at hc
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ?_⟩
      exact ⟨_, .proofIrrel hp hb hc⟩
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | induct _ hadd H ih =>
    -- The registered constants carry no delta-value, so `hv` forces `name` to have
    -- been present already in `C` (`AddInduct.value_find`); then `ih` applies.
    exact (ih (hadd.value_find H.map_wf h hv)).mono hadd.le

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv

/-- The fragment of `TrEnv` needed by the executable type checker. Unlike
`TrEnv`, this invariant does not assert that the current kernel environment
was assembled from complete declarations, so it can also describe the
header and constructor environments used while checking an inductive block. -/
structure CheckingEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop where
  aligned : Aligned safety env.constants venv
  wf : venv.WF
  of_value : env.find? name = some ci → safety ≤ ci.safety → ci.deltaValue? = some v →
    TrExpr venv ci.levelParams [] v
      (.const ci.name (VLevel.params ci.levelParams.length))

theorem TrEnv.toChecking (H : TrEnv safety env venv) : CheckingEnv safety env venv where
  aligned := H.aligned
  wf := H.wf
  of_value := H.of_value

theorem CheckingEnv.map_wf (H : CheckingEnv safety env venv) : env.constants.WF :=
  H.aligned.map_wf

theorem CheckingEnv.find?_iff (H : CheckingEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔
      ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

theorem CheckingEnv.find? (H : CheckingEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

/-- Every constant of a checking environment is stored under its own name. -/
theorem CheckingEnv.find?_name (H : CheckingEnv safety env venv)
    (h : env.find? name = some ci) : ci.name = name :=
  H.aligned.find?_name (H.map_wf.find?'_eq_find? _ ▸ h)

theorem CheckingEnv.find?_uniq (H : CheckingEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

open private Lean.Kernel.Environment.add from Lean.Environment

/-- Extend a checking environment by a typed, non-delta constant. This is the
operation used for temporary inductive headers, constructors, and recursors. -/
theorem CheckingEnv.add (H : CheckingEnv safety env venv)
    (hn : env.find? ci.name = none)
    (htr : TrConstant safety venv ci ci')
    (hci : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv')
    (hdelta : ci.deltaValue? = none) :
    CheckingEnv safety (env.add ci) venv' := by
  have hn' : env.constants.find? ci.name = none := by
    rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?] at hn
    exact hn
  refine {
    aligned := H.aligned.const hn' htr hadd rfl
    wf := ?_
    of_value := ?_ }
  · obtain ⟨ds, hds⟩ := H.wf
    let vi : VConstVal := { ci' with name := ci.name }
    exact ⟨_, hds.decl (.axiom (ci := vi) hci hadd)⟩
  · intro name ci₀ value hfind hs hvalue
    change (env.constants.insert ci.name ci).find?' name = some ci₀ at hfind
    rw [(H.map_wf.insert _ _ hn').find?'_eq_find?, H.map_wf.find?_insert] at hfind
    split at hfind
    · cases hfind
      rw [hdelta] at hvalue
      contradiction
    · have hold : env.find? name = some ci₀ := by
        rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?]
        exact hfind
      exact (H.of_value hold hs hvalue).mono (VEnv.addConst_le hadd)

/-- Adding a nonprimitive constant cannot change the metadata of any primitive
looked up by the executable type checker. -/
theorem CheckingEnv.safePrimitives_add (H : CheckingEnv safety env venv)
    (hn : env.find? ci.name = none)
    (hnprim : ¬ Kernel.Environment.primitives.contains ci.name)
    (hsafe : ∀ {n ci}, env.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []) :
    ∀ {n ci₀}, (env.add ci).find? n = some ci₀ →
      Kernel.Environment.primitives.contains n →
      ci₀.safety = .safe ∧ ci₀.levelParams = [] := by
  have hn' : env.constants.find? ci.name = none := by
    rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?] at hn
    exact hn
  intro n ci₀ hfind hprim
  change (env.constants.insert ci.name ci).find?' n = some ci₀ at hfind
  rw [(H.map_wf.insert _ _ hn').find?'_eq_find?, H.map_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    have hname : ci.name = n := by simpa using heq
    subst n
    exact False.elim (hnprim hprim)
  · apply hsafe (n := n) (ci := ci₀) _ hprim
    rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?]
    exact hfind

/-! ## Recursor rules and quotient facts along the declaration history -/

theorem insertDefs_find?_of_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    C.find? name = some ci → (insertDefs C cis).find? name = some ci
  | [], _, _, _, _, _, _, h => h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    show (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci
    refine insertDefs_find?_of_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 ?_
    rw [hC.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; rw [← hb, hfr d (.head _)] at h; cases h
    · exact h

theorem insertDefs_find?_self : ∀ {cis : List DefinitionVal} {C : ConstMap} {d}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    d ∈ cis → (insertDefs C cis).find? d.name = some (.defnInfo d)
  | [], _, _, _, _, _, h => by cases h
  | e :: ds, C, d, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ f ∈ ds, (SMap.insert C e.name (.defnInfo e)).find? f.name = none := by
      intro f hf
      rw [hC.find?_insert]
      have : ¬ (e.name == f.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨f, hf, hh.symm⟩
      simp [this]; exact hfr f (.tail _ hf)
    show (insertDefs (SMap.insert C e.name (.defnInfo e)) ds).find? d.name = some _
    cases h with
    | head =>
      refine insertDefs_find?_of_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 ?_
      rw [hC.find?_insert]; simp
    | tail _ h =>
      exact insertDefs_find?_self (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h

/-- Lookup of a constant through the four quotient insertions. -/
theorem AddQuot.find? (H : AddQuot C₁ C₂ venv₁ venv₂) (hwf : C₁.WF) :
    C₁.find? ``Quot = none ∧
    (∀ {n ci}, C₁.find? n = some ci → C₂.find? n = some ci) ∧
    (∃ q : QuotVal, C₂.find? ``Quot = some (.quotInfo q) ∧ q.kind = .type) ∧
    (∃ q : QuotVal, C₂.find? ``Quot.lift = some (.quotInfo q) ∧ q.kind = .lift) ∧
    (∀ {n ci}, C₂.find? n = some ci → C₁.find? n = some ci ∨ ∃ q, ci = .quotInfo q) := by
  obtain ⟨l1, t1, e1, -, f1, -, l2, t2, e2, -, f2, -, l3, t3, e3, -, f3, -, l4, t4, e4, -, f4, -,
    hm, -⟩ := H
  subst hm
  have w1 := hwf.insert _ (.quotInfo ⟨⟨``Quot, l1, t1⟩, .type⟩) f1
  have w2 := w1.insert _ (.quotInfo ⟨⟨``Quot.mk, l2, t2⟩, .ctor⟩) f2
  have w3 := w2.insert _ (.quotInfo ⟨⟨``Quot.lift, l3, t3⟩, .lift⟩) f3
  -- the intermediate freshness facts on the base map
  have g2 : C₁.find? ``Quot.mk = none := by
    rw [hwf.find?_insert] at f2; simpa using f2
  have g3 : C₁.find? ``Quot.lift = none := by
    rw [w1.find?_insert, hwf.find?_insert] at f3; simpa using f3
  have g4 : C₁.find? ``Quot.ind = none := by
    rw [w2.find?_insert, w1.find?_insert, hwf.find?_insert] at f4; simpa using f4
  have look : ∀ n, ((((C₁.insert ``Quot (.quotInfo ⟨⟨``Quot, l1, t1⟩, .type⟩)).insert ``Quot.mk
      (.quotInfo ⟨⟨``Quot.mk, l2, t2⟩, .ctor⟩)).insert ``Quot.lift
      (.quotInfo ⟨⟨``Quot.lift, l3, t3⟩, .lift⟩)).insert ``Quot.ind
      (.quotInfo ⟨⟨``Quot.ind, l4, t4⟩, .ind⟩)).find? n =
      if ``Quot.ind = n then some (.quotInfo ⟨⟨``Quot.ind, l4, t4⟩, .ind⟩)
      else if ``Quot.lift = n then some (.quotInfo ⟨⟨``Quot.lift, l3, t3⟩, .lift⟩)
      else if ``Quot.mk = n then some (.quotInfo ⟨⟨``Quot.mk, l2, t2⟩, .ctor⟩)
      else if ``Quot = n then some (.quotInfo ⟨⟨``Quot, l1, t1⟩, .type⟩)
      else C₁.find? n := by
    intro n
    rw [w3.find?_insert, w2.find?_insert, w1.find?_insert, hwf.find?_insert]
    simp only [beq_iff_eq]
  refine ⟨f1, ?_, ?_, ?_, ?_⟩
  · intro n ci h
    rw [look]
    split
    · rename_i hb; subst hb; rw [g4] at h; cases h
    split
    · rename_i hb; subst hb; rw [g3] at h; cases h
    split
    · rename_i hb; subst hb; rw [g2] at h; cases h
    split
    · rename_i hb; subst hb; rw [f1] at h; cases h
    exact h
  · exact ⟨_, by rw [look, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl],
      rfl⟩
  · exact ⟨_, by rw [look, if_neg (by decide), if_pos rfl], rfl⟩
  · intro n ci h
    rw [look] at h
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    exact .inl h

/-- The stored equations after quotient initialization. -/
theorem AddQuot.defeqs (H : AddQuot C₁ C₂ venv₁ venv₂) :
    ∀ df, venv₂.defeqs df → venv₁.defeqs df ∨ df = quotDefEq := by
  obtain ⟨_, _, e1, -, -, h1, _, _, e2, -, -, h2, _, _, e3, -, -, h3, _, _, e4, -, -, h4, -, rfl⟩ :=
    H
  intro df hdf
  rcases hdf with rfl | hdf
  · exact .inr rfl
  · rw [VEnv.addConst_defeqs h4, VEnv.addConst_defeqs h3, VEnv.addConst_defeqs h2,
      VEnv.addConst_defeqs h1] at hdf
    exact .inl hdf

/-- The heads of the reduction rules along the translation: every stored equation is headed by
a definition or by `Quot.lift`, and every registered pattern by a recursor of the map. -/
theorem TrEnv'.equationHeads (H : TrEnv' safety C Q venv) : EquationHeadsCoherent C venv := by
  induction H with
  | empty => exact ⟨fun _ h => h.elim, fun _ _ h => h.elim⟩
  | inductProjections _ _ ih => exact ih.addProjections _
  | ignore h1 _ h3 ih => exact ih.insert h3.map_wf h1 (fun _ h => h) (fun _ _ h => h)
  | «axiom» _ h2 _ h4 h5 ih =>
    exact ih.insert h5.map_wf h2 (fun _ h => by rwa [VEnv.addConst_defeqs h4] at h)
      (fun _ _ h => by rwa [VEnv.addConst_pats h4] at h)
  | thm _ h2 _ _ h4 h5 ih =>
    exact ih.insert h5.map_wf h2 (fun _ h => by rwa [VEnv.addConst_defeqs h4] at h)
      (fun _ _ h => by rwa [VEnv.addConst_pats h4] at h)
  | «opaque» _ h2 _ h4 h5 ih =>
    exact ih.insert h5.map_wf h2 (fun _ h => by rwa [VEnv.addConst_defeqs h4] at h)
      (fun _ _ h => by rwa [VEnv.addConst_pats h4] at h)
  | @defn _ ci _ C _ ci' h1 h2 _ h4 h5 ih =>
    have hname := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal, VDefVal.toVConstVal] at hname
    refine (ih.insert h5.map_wf h2 (fun _ h => by rwa [VEnv.addConst_defeqs h4] at h)
      (fun _ _ h => by rwa [VEnv.addConst_pats h4] at h)).addDefEq ?_
    have hfind : (SMap.insert C ci.name (ConstantInfo.defnInfo ci)).find? ci'.name =
        some (ConstantInfo.defnInfo ci) := by
      rw [← hname, h5.map_wf.find?_insert, if_pos (beq_self_eq_true _)]
    exact EquationHeadOf.ofDefn ⟨_, _, _, VDefVal.toDefEq_head _, hfind⟩
  | @mutualDef _ _ C _ cis cis' hblk hnd hfr _ hadd _ htr ih =>
    refine ih.extend (insertDefs_find?_of_find? htr.map_wf hfr hnd) ?_ ?_
    · intro df hdf
      rcases VEnv.addDefEqs_defeqs_iff.1 hdf with hdf | ⟨ci', hci', rfl⟩
      · rw [VEnv.addConsts_defeqs hadd] at hdf; exact .inl hdf
      · obtain ⟨ci, hci, htrc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hblk ci' hci'
        have hname := htrc.1.2
        dsimp [ConstantInfo.name, ConstantInfo.toConstantVal, VDefVal.toVConstVal] at hname
        have hfind : (insertDefs C cis).find? ci'.name = some (ConstantInfo.defnInfo ci) := by
          rw [← hname]
          exact insertDefs_find?_self htr.map_wf hfr hnd hci
        exact .inr (EquationHeadOf.ofDefn ⟨_, _, _, VDefVal.toDefEq_head _, hfind⟩)
    · intro p r hp
      rw [VEnv.addDefEqs_pats, VEnv.addConsts_pats hadd] at hp
      exact .inl hp
  | quot _ hq htr ih =>
    obtain ⟨-, hpres, -, ⟨q, hlift, hkind⟩, -⟩ := hq.find? htr.map_wf
    refine ih.extend hpres ?_ ?_
    · intro df hdf
      rcases hq.defeqs df hdf with h | rfl
      · exact .inl h
      · exact .inr ⟨``Quot.lift, _, _, rfl, hlift, nofun, fun q' hq' => by
          cases hq'; exact hkind⟩
    · intro p r hp
      rw [VEnv.addQuot_pats hq.to_addQuot] at hp
      exact .inl hp
  | induct hwf hadd htr ih =>
    have wf := htr.map_wf
    refine ih.extend (hadd.find?_mono wf) ?_ ?_
    · intro df hdf
      rw [VEnv.addInduct_defeqs hadd.env_eq] at hdf
      exact .inl hdf
    · intro p r hp
      rcases VEnv.addInduct_pats_origin hadd.env_eq hp with h | ⟨rec, hrec, ru, hru, rfl⟩
      · exact .inl h
      · obtain ⟨rval, hrfind, -⟩ := hadd.rec_reg wf hwf hrec
        exact .inr ⟨rval, by rw [SimplePattern.iota_headConst]; exact hrfind⟩

theorem TrEnv.equationHeads (H : TrEnv safety env venv) :
    EquationHeadsCoherent env.constants venv :=
  TrEnv'.equationHeads H

/-- Once quotients are initialized, the quotient constants and the `Quot.lift` equation are
present and `Quot` is rigid. -/
theorem TrEnv'.quotEnvCoherent (H : TrEnv' safety C Q venv) (hQ : Q = true) :
    QuotEnvCoherent C venv := by
  have pres_insert {C : ConstMap} {n ci} (hwf : C.WF) (hfresh : C.find? n = none) :
      ∀ {m ci'}, C.find? m = some ci' → (C.insert n ci).find? m = some ci' :=
    fun h => SMap.find?_insert_of_fresh hwf.map₂ hfresh h
  induction H with
  | empty => cases hQ
  | inductProjections h1 h2 ih =>
    exact (ih hQ).extend id VEnv.addProjections_le (TrEnv'.inductProjections h1 h2).equationHeads
  | ignore h1 h2 h3 ih =>
    exact (ih hQ).extend (pres_insert h3.map_wf h1) VEnv.LE.rfl
      (TrEnv'.ignore h1 h2 h3).equationHeads
  | «axiom» h1 h2 h3 h4 h5 ih =>
    exact (ih hQ).extend (pres_insert h5.map_wf h2) (VEnv.addConst_le h4)
      (TrEnv'.axiom h1 h2 h3 h4 h5).equationHeads
  | thm h1 h2 h3 h3' h4 h5 ih =>
    exact (ih hQ).extend (pres_insert h5.map_wf h2) (VEnv.addConst_le h4)
      (TrEnv'.thm h1 h2 h3 h3' h4 h5).equationHeads
  | «opaque» h1 h2 h3 h4 h5 ih =>
    exact (ih hQ).extend (pres_insert h5.map_wf h2) (VEnv.addConst_le h4)
      (TrEnv'.opaque h1 h2 h3 h4 h5).equationHeads
  | defn h1 h2 h3 h4 h5 ih =>
    exact (ih hQ).extend (pres_insert h5.map_wf h2) ((VEnv.addConst_le h4).trans VEnv.addDefEq_le)
      (TrEnv'.defn h1 h2 h3 h4 h5).equationHeads
  | mutualDef hblk hnd hfr hwf hadd hci htr ih =>
    exact (ih hQ).extend (insertDefs_find?_of_find? htr.map_wf hfr hnd)
      ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le)
      (TrEnv'.mutualDef hblk hnd hfr hwf hadd hci htr).equationHeads
  | quot h0 hq htr _ =>
    obtain ⟨-, -, ⟨q, hq', hk⟩, -, -⟩ := hq.find? htr.map_wf
    exact ⟨AddQuot.quotCoherent hq
      ((TrEnv'.quot h0 hq htr).equationHeads.rigid_quot hq' hk), q, hq', hk⟩
  | induct hwf hadd htr ih =>
    exact (ih hQ).extend (hadd.find?_mono htr.map_wf) hadd.le
      (TrEnv'.induct hwf hadd htr).equationHeads

theorem TrEnv.quotEnvCoherent (H : TrEnv safety env venv) (hQ : env.quotInit = true) :
    QuotEnvCoherent env.constants venv :=
  TrEnv'.quotEnvCoherent H hQ

structure CheckingEnv.ValidCore (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv) : Prop where
  tr : CheckingEnv safety env venv
  hasPrimitives : venv.HasPrimitives
  safePrimitives : ∀ {n ci}, env.find? n = some ci →
    Kernel.Environment.primitives.contains n →
    ci.safety = .safe ∧ ci.levelParams = []

theorem CheckingEnv.ValidCore.add (H : CheckingEnv.ValidCore safety env venv)
    (hn : env.find? ci.name = none)
    (hnprim : ¬ Kernel.Environment.primitives.contains ci.name)
    (htr : TrConstant safety venv ci ci')
    (hci : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv')
    (hdelta : ci.deltaValue? = none) :
    CheckingEnv.ValidCore safety (env.add ci) venv' where
  tr := H.tr.add hn htr hci hadd hdelta
  hasPrimitives := H.hasPrimitives.addConst_of_not_primitive hadd hnprim
  safePrimitives := H.tr.safePrimitives_add hn hnprim H.safePrimitives

theorem CheckingEnv.addProjections
    (H : CheckingEnv safety env venv)
    (hwf : (venv.addProjections entries).WF) :
    CheckingEnv safety env (venv.addProjections entries) where
  aligned := .projections H.aligned
  wf := hwf
  of_value := fun hfind hvisible hvalue =>
    (H.of_value hfind hvisible hvalue).mono VEnv.addProjections_le


theorem CheckingEnv.ValidCore.addProjections
    (H : CheckingEnv.ValidCore safety env venv)
    (hwf : (venv.addProjections entries).WF) :
    CheckingEnv.ValidCore safety env (venv.addProjections entries) where
  tr := H.tr.addProjections hwf
  hasPrimitives := H.hasPrimitives.addProjections
  safePrimitives := H.safePrimitives

/-! ### Forward `find?` transport across fresh insertions

A constant already resolvable stays resolvable, to the same value, across insertions of
names it does not carry (`SMap.find?_insert_of_fresh`, `SMap.insertList_find?_mono`,
`AddInduct.find?_mono` in `Basic.lean`); here for `insertDefs` and `AddQuot`. -/

theorem insertDefs_find?_mono {cis : List DefinitionVal} {C : ConstMap} {x v} (wf : C.WF)
    (hfr : ∀ d ∈ cis, C.find? d.name = none) (h : C.find? x = some v) :
    (insertDefs C cis).find? x = some v := by
  unfold insertDefs
  refine SMap.insertList_find?_mono (nm := (·.name)) (val := (.defnInfo ·)) wf.map₂
    (fun d hd hx => ?_) h
  have := hfr d hd; rw [hx, h] at this; cases this

theorem AddQuot1.find?_mono {P : ConstMap → VEnv → Prop} {Q : Prop} {name kind ci' x v}
    (H1 : ∀ m env, m.WF → m.find? x = some v → P m env → Q)
    (m env) (wf : m.WF) (h : m.find? x = some v) (H2 : AddQuot1 name kind ci' P m env) : Q := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact H1 _ _ (wf.insert _ _ h2) (SMap.find?_insert_of_fresh wf.map₂ h2 h) h4

/-- A constant resolvable before adding the quotient constants is still resolvable, to
the same value, afterwards. -/
theorem AddQuot.find?_mono {x v} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (h : C₁.find? x = some v) : C₂.find? x = some v := by
  dsimp [AddQuot] at H
  refine (AddQuot1.find?_mono <| AddQuot1.find?_mono <| AddQuot1.find?_mono <|
    AddQuot1.find?_mono ?_) _ _ wf h H
  rintro m env _ h ⟨rfl, _⟩; exact h

/-! ### The ι-reduction interface -/

/-- `TrEnv'`-level ι-rule lookup with the registered witness named: the reduct is
`iotaRHS` at the recursor's telescope split and the constructor's parameter count
(`cval.numParams`, read off the constructor's own `ctorInfo`), over a template `rhs`
translating the kernel rule's reduct; the check is trivial (so `iota_defeq` runs with
`chk := []`). -/
theorem TrEnv'.pats_iota' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv' safety C Q venv)
    (hrec : C.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      C.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true) := by
  induction H with
  | empty => simp at hrec
  | inductProjections _ _ ih =>
    obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
    exact ⟨cval, rhs, hc, hct, htr.mono VEnv.addProjections_le, by rwa [VEnv.addProjections_pats]⟩
  | ignore h1 h2 h3 ih =>
    rw [h3.map_wf.find?_insert] at hrec; split at hrec
    · injection hrec with hrec; subst hrec; exact absurd hsafe h2
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h3.map_wf.map₂ h1 hct, htr, hp⟩
  | thm _ h2 _ _ h5 h6 ih =>
    rw [h6.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h5
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h6.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | mutualDef _ hnd hfr _ hadd _ h7 ih =>
    rcases insertDefs_find? h7.map_wf hfr hnd hrec with hrec' | ⟨d, _, _, hd⟩
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec'
      exact ⟨cval, rhs, hc, insertDefs_find?_mono h7.map_wf hfr hct,
        htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le),
        ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le).pats hp⟩
    · exact absurd hd (by nofun)
  | «axiom» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | defn _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le),
        ((VEnv.addConst_le h4).trans VEnv.addDefEq_le).pats hp⟩
  | «opaque» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | quot _ h2 h3 ih =>
    obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih (h2.pull h3.map_wf hrec)
    exact ⟨cval, rhs, hc, h2.find?_mono h3.map_wf hct, htr.mono h2.le, h2.le.pats hp⟩
  | induct _ hadd h3 ih =>
    rcases hadd.rec_find h3.map_wf hrec with
      hC | ⟨r, hr, hname, _, hpar, hmot, hmin, hind, hrules⟩
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hC
      exact ⟨cval, rhs, hc, hadd.find?_mono h3.map_wf hct, htr.mono hadd.le,
        hadd.le.pats hp⟩
    · obtain ⟨hctor, hmem⟩ : rule.ctor = cName ∧ rule ∈ rval.rules :=
        ⟨by simpa using List.find?_some hrule, List.mem_of_find?_eq_some hrule⟩
      obtain ⟨ru, hru, hructor, hrunf, ⟨cval, hcfind, hcnp⟩, hclosed, hrutr⟩ := hrules rule hmem
      refine ⟨cval, ru.rhs, hclosed, by rw [← hctor]; exact hcfind, hrutr, ?_⟩
      rw [← hname, ← hpar, ← hmot, ← hmin, ← hind, ← hrunf, ← hctor, ← hructor, ← hcnp]
      exact VEnv.addInduct_pat hr hru hclosed hadd.env_eq

/-- `TrEnv'.pats_iota'` against the environment's own `find?`: the ι rule of a recursor
rule resolvable in `env` is registered in the translated environment's `pats`. -/
theorem TrEnv.pats_iota' {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      env.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true) := by
  have h : env.constants.find?' recName = some (.recInfo rval) := hrec
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := TrEnv'.pats_iota' H h hrule hsafe
  refine ⟨cval, rhs, hc, ?_, htr, hp⟩
  show env.constants.find?' cName = _
  rw [(TrEnv'.map_wf H).find?'_eq_find?]; exact hct

/-- Inverse of `pats_iota'`, at the `TrEnv'` level: every registered ι pattern
`SimplePattern.iota recName M cName N` comes from a kernel recursor `rval` (resolvable in
`C` under `recName`) and its rule for `cName` (found by constructor, uniquely by
`VInductDecl.WF.rules_nodup`), whose constructor `cval` is resolvable in `C`; `M` and `N`
are the kernel telescope split and `cval.numParams + rule.nfields`, and the registered
entry is `iotaRHS` at those counts over a translation of the kernel reduct, with the
trivial check. The reduct component is stated with `HEq` because its type mentions `M`
and `N`. -/
theorem TrEnv'.pats_iota_inv' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv' safety C Q venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed),
      C.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      C.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true := by
  induction H with
  | empty => exact (hp : False).elim
  | inductProjections _ _ ih =>
    rw [VEnv.addProjections_pats] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    exact ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr.mono VEnv.addProjections_le,
      hh1, hh2⟩
  | ignore h1 _ Hprev ih =>
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h1 hrec, hru,
      SMap.find?_insert_of_fresh wf h1 hct, hM, hN, htr, hh1, hh2⟩
  | «axiom» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h4), hh1, hh2⟩
  | defn _ h2 _ h4 Hprev ih =>
    rw [VEnv.addDefEq_pats, VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN,
      htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le), hh1, hh2⟩
  | mutualDef _ hnd hfr _ hadd _ Hprev ih =>
    rw [VEnv.addDefEqs_pats, VEnv.addConsts_pats hadd] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf
    exact ⟨rval, rule, cval, rhs, hc, insertDefs_find?_mono wf hfr hrec, hru,
      insertDefs_find?_mono wf hfr hct, hM, hN,
      htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le), hh1, hh2⟩
  | thm _ h2 _ _ h5 Hprev ih =>
    rw [VEnv.addConst_pats h5] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h5), hh1, hh2⟩
  | «opaque» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h4), hh1, hh2⟩
  | quot _ h2 Hprev ih =>
    rw [VEnv.addQuot_pats h2.to_addQuot] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf
    exact ⟨rval, rule, cval, rhs, hc, h2.find?_mono wf hrec, hru, h2.find?_mono wf hct, hM, hN,
      htr.mono h2.le, hh1, hh2⟩
  | induct hwf hadd Hprev ih =>
    have wf := Hprev.map_wf
    rcases VEnv.addInduct_pats_origin' hadd.env_eq hp with
      hold | ⟨rec, hrec, ru, hru, hc, e, he⟩
    · obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hold
      exact ⟨rval, rule, cval, rhs, hc, hadd.find?_mono wf hrec, hru, hadd.find?_mono wf hct,
        hM, hN, htr.mono hadd.le, hh1, hh2⟩
    · obtain ⟨hrn, hm, hcn, hkk⟩ := VEnv.iota_toPattern_inj e
      subst hrn hm hcn hkk
      cases e
      obtain ⟨rval, hrfind, hmaj, hpar, hmot, hmin, hind, hrules⟩ := hadd.rec_reg wf hwf hrec
      obtain ⟨rule, hfind, hnf, ⟨cval, hcfind, hcnp⟩, htr⟩ := hrules ru hru
      refine ⟨rval, rule, cval, ru.rhs, hc, hrfind, hfind, hcfind, ?_, by rw [← hcnp, ← hnf],
        htr, ?_, ?_⟩
      · rw [hmaj]; rfl
      · rw [← hpar, ← hmot, ← hmin, ← hind, ← hcnp, ← hnf]
        exact heq_of_eq (congrArg Prod.fst he)
      · exact congrArg Prod.snd he

/-- Inverse of `pats_iota'`; see `TrEnv'.pats_iota_inv'`. From a registered ι pattern,
recover the kernel recursor and its rule for the constructor, the constructor itself, the
full kernel telescope split behind `M`, the split of `N` into the constructor's parameter
and field counts, and the registered reduct. -/
theorem TrEnv.pats_iota_inv' {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv safety env venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed),
      env.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      env.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true := by
  obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ :=
    TrEnv'.pats_iota_inv' H hp
  have wf := TrEnv'.map_wf H
  refine ⟨rval, rule, cval, rhs, hc, ?_, hru, ?_, hM, hN, htr, hh1, hh2⟩
  · show env.constants.find?' recName = _; rw [wf.find?'_eq_find?]; exact hrec
  · show env.constants.find?' cName = _; rw [wf.find?'_eq_find?]; exact hct

/-! ### The block behind a kernel type former or constructor -/

/-- A type former or constructor resolvable in `C` and visible at `safety` was inserted by an
`induct` step: it is one of the kernel constants of an `AddInduct` block `decl`, well-formed
over the environment `env₀` it extends, whose result `env₁` lies below `venv`. Every other
step inserts only definitions, axioms, theorems, opaques, quotient constants, or (`ignore`)
constants invisible at `safety`. -/
theorem TrEnv'.find?_induct {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {x : Name} {ci : ConstantInfo}
    (H : TrEnv' safety C Q venv) (h : C.find? x = some ci) (hsafe : safety ≤ ci.safety)
    (hk : ci.isInductive ∨ ci.isCtor) :
    ∃ (C₀ C₁ : ConstMap) (env₀ env₁ : VEnv) (decl : VInductDecl),
      decl.WF env₀ ∧ env₁ ≤ venv ∧
      ∃ A : AddInduct safety C₀ env₀ decl C₁ env₁,
        ci ∈ AddInduct.consts A.ivals A.rvals ∧ ci.name = x := by
  induction H with
  | empty => simp at h
  | inductProjections _ _ ih =>
    obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
    exact ⟨_, _, _, _, _, hwf, hle.trans VEnv.addProjections_le, A, hA⟩
  | ignore _ h2 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; exact absurd hsafe h2
    · exact ih h
  | «axiom» _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans (VEnv.addConst_le h4), A, hA⟩
  | defn _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf,
        hle.trans ((VEnv.addConst_le h4).trans VEnv.addDefEq_le), A, hA⟩
  | mutualDef _ hnd hfr _ hadd _ Hprev ih =>
    rcases insertDefs_find? Hprev.map_wf hfr hnd h with h | ⟨_, _, _, rfl⟩
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf,
        hle.trans ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le), A, hA⟩
    · simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
  | thm _ _ _ _ h5 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans (VEnv.addConst_le h5), A, hA⟩
  | «opaque» _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans (VEnv.addConst_le h4), A, hA⟩
  | quot _ h2 Hprev ih =>
    have hq : ∀ v, ci ≠ .quotInfo v := by
      rintro v rfl; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih (h2.pull_of Hprev.map_wf hq h)
    exact ⟨_, _, _, _, _, hwf, hle.trans h2.le, A, hA⟩
  | induct hwf hadd Hprev ih =>
    rcases hadd.find? Hprev.map_wf h with h | hA
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans hadd.le, A, hA⟩
    · exact ⟨_, _, _, _, _, hwf, .rfl, hadd, hA⟩

/-- The block that declared a kernel type former `ival` as the model type former `t`: `decl`
is well-formed over `env₀`, its type formers extend `env₀` to `envT` and the whole block to
`env₁ ≤ venv`, and `t ∈ decl.types` translates `ival` with the constructors `cvals`
(`TrIndType`: `ival` translating to `t` in `env₀`, `ival.ctors` the names of `cvals`, each
constructor translating in `envT` with its Π-arity). -/
structure TrEnv'.InductOrigin (safety : DefinitionSafety) (venv : VEnv) (ival : InductiveVal)
    (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
    (cvals : List ConstructorVal) : Prop where
  wf : decl.WF env₀
  addTypes : decl.addTypes env₀ = some envT
  addInduct : env₀.addInduct decl = some env₁
  le : env₁ ≤ venv
  mem : t ∈ decl.types
  tr : TrIndType safety env₀ envT ival cvals t

/-- The type former and block behind an `inductInfo` of `C`: the inverse of `TrEnv'`'s
`induct` clause for type formers. Visibility at `safety` is needed, as for `pats_iota'`: an
`ignore` step inserts a type former of no block. -/
theorem TrEnv'.inductInfo_inv {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {I : Name} {ival : InductiveVal}
    (H : TrEnv' safety C Q venv) (hI : C.find? I = some (.inductInfo ival))
    (hsafe : safety ≤ (Lean.ConstantInfo.inductInfo ival).safety) :
    ∃ (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      t.name = I ∧ InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  obtain ⟨_, _, env₀, env₁, decl, hwf, hle, A, hmem, hn⟩ :=
    H.find?_induct hI hsafe (.inl rfl)
  rcases AddInduct.mem_consts.1 hmem with ⟨iv, hiv, he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, he⟩ <;>
    cases he
  obtain ⟨t, ht, htr⟩ := A.types.forall_exists_l iv hiv
  exact ⟨decl, env₀, A.envT, env₁, t, iv.2, htr.tr.2.symm.trans hn,
    ⟨hwf, A.stT, A.env_eq, hle, ht, htr⟩⟩

/-- The type former and block behind a `ctorInfo` of `C`: `cval` is among the constructors
`cvals` of a type former `t` of a block `decl`, with the data of `InductOrigin`; its model
constructor and translation are the matching entry of `tr.ctors`. -/
theorem TrEnv'.ctorInfo_inv {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {x : Name} {cval : ConstructorVal}
    (H : TrEnv' safety C Q venv) (hc : C.find? x = some (.ctorInfo cval))
    (hsafe : safety ≤ (Lean.ConstantInfo.ctorInfo cval).safety) :
    ∃ (ival : InductiveVal) (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      cval ∈ cvals ∧ cval.name = x ∧ InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  obtain ⟨_, _, env₀, env₁, decl, hwf, hle, A, hmem, hn⟩ :=
    H.find?_induct hc hsafe (.inr rfl)
  rcases AddInduct.mem_consts.1 hmem with ⟨_, _, he⟩ | ⟨iv, hiv, _, hcv, he⟩ | ⟨_, _, he⟩ <;>
    cases he
  obtain ⟨t, ht, htr⟩ := A.types.forall_exists_l iv hiv
  exact ⟨iv.1, decl, env₀, A.envT, env₁, t, iv.2, hcv, hn, ⟨hwf, A.stT, A.env_eq, hle, ht, htr⟩⟩

/-- `TrEnv'.inductInfo_inv` against the environment's own `find?`. -/
theorem TrEnv.inductInfo_inv {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {I : Name} {ival : InductiveVal}
    (H : TrEnv safety env venv) (hI : env.find? I = some (.inductInfo ival))
    (hsafe : safety ≤ (Lean.ConstantInfo.inductInfo ival).safety) :
    ∃ (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      t.name = I ∧ TrEnv'.InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  have h : env.constants.find?' I = some (.inductInfo ival) := hI
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  exact TrEnv'.inductInfo_inv H h hsafe

/-- `TrEnv'.ctorInfo_inv` against the environment's own `find?`. -/
theorem TrEnv.ctorInfo_inv {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {x : Name} {cval : ConstructorVal}
    (H : TrEnv safety env venv) (hc : env.find? x = some (.ctorInfo cval))
    (hsafe : safety ≤ (Lean.ConstantInfo.ctorInfo cval).safety) :
    ∃ (ival : InductiveVal) (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      cval ∈ cvals ∧ cval.name = x ∧
      TrEnv'.InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  have h : env.constants.find?' x = some (.ctorInfo cval) := hc
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  exact TrEnv'.ctorInfo_inv H h hsafe

/-- A registered ι rule, matched against a well-typed redex with its `Realizes` side
conditions discharged, gives a definitional equality between redex and reduct. Thin
wrapper over `VEnv.IsDefEq.pat`. -/
theorem TrEnv.iota_defeq {venv : VEnv} {U : Nat} {Γ : List VExpr}
    {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 m2 chk}
    (hpat : venv.pats p r) (hm : p.Matches e m1 m2)
    (hty : venv.HasType U Γ e A) (hR : r.2.Realizes m1 m2 chk)
    (hall : ∀ t ∈ chk, venv.IsDefEq U Γ t.1 t.2.1 t.2.2) :
    venv.IsDefEqU U Γ e (r.1.apply m1 m2) :=
  ⟨A, VEnv.IsDefEq.pat hpat hm hty hR hall⟩

/-- The ι reduction step of a translated environment, as `reduceRecursor.WF` needs it: a
well-typed redex matching a recursor's ι pattern (over the constructor `cval` resolved in
`env`) is definitionally equal to the `iotaRHS` reduct, over a template `rhs` translating
the kernel rule's reduct. Composes `pats_iota'` with `iota_defeq` at the trivial check. -/
theorem TrEnv.iota_rec {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule} {cval : ConstructorVal}
    {U : Nat} {Γ : List VExpr} {e A : VExpr} {m1 m2}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety)
    (hctor : env.find? cName = some (.ctorInfo cval))
    (hm : (SimplePattern.iota recName
        (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
        (cval.numParams + rule.nfields)).toPattern.Matches e m1 m2)
    (hty : venv.HasType U Γ e A) :
    ∃ (rhs : VExpr) (hc : rhs.Closed),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.IsDefEqU U Γ e ((SimplePattern.iotaRHS recName cName rval.numParams
        rval.numMotives rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc).apply
          m1 m2) := by
  obtain ⟨cval', rhs, hc, hct, htr, hp⟩ := H.pats_iota' hrec hrule hsafe
  rw [hctor] at hct; cases hct
  exact ⟨rhs, hc, htr, TrEnv.iota_defeq hp hm hty (chk := []) trivial nofun⟩

/-- The head of a well-typed application spine is well-typed. -/
theorem VEnv.HasType.mkApps_inv_head {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {as : List VExpr} {f V : VExpr}, env.HasType U Γ (f.mkApps as) V → ∃ W, env.HasType U Γ f W
  | [], _, V, H => ⟨V, H⟩
  | a :: as, f, _, H => by
    rw [VExpr.mkApps_cons] at H
    obtain ⟨_, H'⟩ := mkApps_inv_head henv hΓ (as := as) (f := f.app a) H
    obtain ⟨_, _, hf, -⟩ := H'.app_inv henv hΓ
    exact ⟨_, hf⟩

/-! ### Rebuilding an application spine in the translation

A head and arguments that translate assemble into a translation of the spine, provided the
model spine is well-typed: each application node needs the typing of its function and
argument, which `HasType.mkApps_inv_head` and `HasType.app_inv` read off the whole spine. -/

theorem TrExpr.mkAppList {env : VEnv} {Us : List Name} {Δ : VLCtx}
    (henv : env.WF) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length))
    {as : List Expr} {as' : List VExpr} (has : List.Forall₂ (TrExpr env Us Δ) as as') :
    ∀ {f f' V}, TrExpr env Us Δ f f' → env.HasType Us.length Δ.toCtx (f'.mkApps as') V →
      TrExpr env Us Δ (f.mkAppList as) (f'.mkApps as') := by
  induction has with
  | nil => exact fun hf _ => hf
  | cons ha _ ih =>
    intro f f' V hf hty
    rw [VExpr.mkApps_cons] at hty ⊢
    obtain ⟨_, hty'⟩ := hty.mkApps_inv_head henv hΔ
    obtain ⟨_, _, h1, h2⟩ := hty'.app_inv henv hΔ
    exact ih (.app henv hΔ h1 h2 hf ha) hty
