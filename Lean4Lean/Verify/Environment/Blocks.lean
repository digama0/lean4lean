import Lean4Lean.Verify.Environment.Lemmas

/-!
# Installed inductive blocks

One descriptor per installed inductive declaration (`InstalledBlock`), and the environment
invariant stating that every inductive header, constructor and recursor of the kernel
environment belongs to a well-formed descriptor, and that every projection-registry entry
of the abstract environment was registered by one (`InstalledBlocks`).

A descriptor records, for one declaration, the kernel headers, constructors and recursors it
installed, the abstract declaration together with the abstract constant of each kernel
header and constructor, the case eliminators and projections it registered, the constructor
telescope certificates, and how far the installation has progressed (`InstallStage`).  An
inductive declaration is checked in staged environments: the headers are installed first and
the constructor types are checked against them, then the constructors (with the
declaration's case eliminators and projections in the abstract environment), and finally the
recursors.  A staged environment carries a partial descriptor: at `.headers` the
constructor names the headers list are still absent, at `.constructors` the constructors are
present and the registrations made, and at `.complete` the whole abstract block is installed
(`VEnv.InstalledBelow`).

Every lookup fact the checker consumes is a projection of this invariant: constructor owners
(`InstalledBlocks.constructorOwnersPresent`), listed constructors
(`InstalledBlocks.listedConstructorsCoherent`), closure of mutual blocks
(`InstalledBlocks.mutualInductivesClosed`), the projection registry in both directions
(`InstalledBlocks.projectionRegistryCoherent`, `InstalledBlocks.projectionHeader`), recursor
alignment (`InstalledBlocks.recursorEnvCoherent`) and constructor telescopes
(`InstalledBlocks.ctorTelescopes`).
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- How far the installation of an inductive block has progressed. -/
inductive InstallStage where
  /-- The headers are installed; the constructors they list are not yet present. -/
  | headers
  /-- The constructors are installed, and the block's case eliminators and projections are
  registered in the abstract environment. -/
  | constructors
  /-- The whole abstract block is installed. -/
  | complete
  deriving DecidableEq

namespace InstallStage

def rank : InstallStage → Nat
  | headers => 0
  | constructors => 1
  | complete => 2

instance : LE InstallStage := ⟨fun a b => a.rank ≤ b.rank⟩

instance (a b : InstallStage) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.rank ≤ b.rank))

theorem le_refl (a : InstallStage) : a ≤ a := Nat.le_refl _

theorem le_trans {a b c : InstallStage} : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans

theorem headers_le (a : InstallStage) : headers ≤ a := Nat.zero_le _

theorem le_complete (a : InstallStage) : a ≤ complete := by
  cases a <;> decide

theorem eq_complete {a : InstallStage} (h : complete ≤ a) : a = complete := by
  cases a <;> first | rfl | exact absurd h (by decide)

theorem ne_headers {a b : InstallStage} (h : constructors ≤ a) (hb : a ≤ b) : b ≠ headers := by
  rintro rfl; cases a <;> exact absurd (le_trans h hb) (by decide)

end InstallStage

/-- One family of an installed block: its kernel header, its kernel constructors (in the
order the header lists them; meaningful from `InstallStage.constructors` on), and the abstract
family that the header and constructors translate. -/
structure InstalledFamily where
  header : InductiveVal
  ctors : List ConstructorVal
  type : VInductiveType

/-- The descriptor of one installed inductive declaration. -/
structure InstalledBlock where
  stage : InstallStage
  numParams : Nat
  isUnsafe : Bool
  /-- The families, in the order of `InductiveVal.all`. -/
  families : List InstalledFamily
  /-- The recursors installed so far, with their rules. -/
  recursors : List RecursorVal
  /-- The case eliminators the declaration registers. -/
  eliminators : List (Name × InductiveSignature.CaseSchema)
  /-- The abstract declaration; its families are `families.map (·.type)`. Its projections
  are `decl.projectionEntries`. -/
  decl : VInductDecl

namespace InstalledBlock

/-- The names of the block's headers. -/
def names (B : InstalledBlock) : List Name := B.families.map (·.header.name)

/-- The safety level of the block's constants. -/
def defSafety (B : InstalledBlock) : DefinitionSafety := if B.isUnsafe then .unsafe else .safe

/-- The block's constants are visible to an observer at `safety`. -/
def Visible (safety : DefinitionSafety) (B : InstalledBlock) : Prop := safety ≤ B.defSafety

end InstalledBlock

/-- Kernel metadata of the `i`th constructor `c` of family `F` of block `B`. -/
structure InstalledFamily.CtorAt (env : Environment) (B : InstalledBlock)
    (F : InstalledFamily) (i : Nat) (c : ConstructorVal) : Prop where
  find : env.find? c.name = some (.ctorInfo c)
  induct : c.induct = F.header.name
  cidx : c.cidx = i
  numParams : c.numParams = B.numParams
  levelParams : c.levelParams = F.header.levelParams
  isUnsafe : c.isUnsafe = B.isUnsafe
  /-- The field count is the syntactic arity of the stored type beyond the parameters. -/
  numFields : c.numFields = AddInductive.constructorArity c.type - B.numParams

/-- The kernel side of a descriptor, which does not depend on the observer. -/
structure InstalledBlock.Concrete (env : Environment) (B : InstalledBlock) : Prop where
  header : ∀ F ∈ B.families, env.find? F.header.name = some (.inductInfo F.header)
  /-- Once the constructors are installed every header of the block is present, and the
  headers list exactly the block's families. -/
  all : B.stage ≠ .headers → ∀ F ∈ B.families, F.header.all = B.names
  nodup : B.stage ≠ .headers → B.names.Nodup
  numParams : ∀ F ∈ B.families, F.header.numParams = B.numParams
  isUnsafe : ∀ F ∈ B.families, F.header.isUnsafe = B.isUnsafe
  /-- While only the headers are installed, the constructors they list are absent. -/
  pending : B.stage = .headers → ∀ F ∈ B.families, ∀ n ∈ F.header.ctors, env.find? n = none
  ctorNames : B.stage ≠ .headers → ∀ F ∈ B.families, F.ctors.map (·.name) = F.header.ctors
  ctor : B.stage ≠ .headers → ∀ F ∈ B.families, ∀ i (h : i < F.ctors.length),
    F.CtorAt env B i F.ctors[i]
  recursor : ∀ r ∈ B.recursors, env.find? r.name = some (.recInfo r) ∧ B.stage ≠ .headers
  /-- The major inductive of every recursor is a header whose constructors are present. -/
  recursorMajor : ∀ r ∈ B.recursors, ∃ info,
    env.find? r.getMajorInduct = some (.inductInfo info) ∧
      ∀ n ∈ info.ctors, ∃ ci, env.find? n = some ci

/-- Common-parameter agreement of a constructor with its family: the two types normalize, in
the abstract environment, to telescopes whose first `nparams` domains are definitionally
equal. -/
def CtorParamsDefEq (venv : VEnv) (uvars nparams : Nat) (familyType ctorType : VExpr) : Prop :=
  ∃ familyNormalized ctorNormalized familyDomains ctorDomains familyTail ctorTail
    familySort ctorSort,
    venv.IsDefEq uvars [] familyType familyNormalized familySort ∧
    venv.IsDefEq uvars [] ctorType ctorNormalized ctorSort ∧
    familyNormalized.takeForalls nparams = some (familyDomains, familyTail) ∧
    ctorNormalized.takeForalls nparams = some (ctorDomains, ctorTail) ∧
    venv.IsDefEqCtx uvars [] familyDomains.reverse ctorDomains.reverse

theorem CtorParamsDefEq.mono (henv : venv ≤ venv')
    (H : CtorParamsDefEq venv uvars nparams familyType ctorType) :
    CtorParamsDefEq venv' uvars nparams familyType ctorType :=
  let ⟨a, b, c, d, e, f, g, h, h1, h2, h3, h4, h5⟩ := H
  ⟨a, b, c, d, e, f, g, h, h1.mono henv, h2.mono henv, h3, h4, h5.mono henv⟩

/-- The abstract counterpart `T` of the kernel constructor `c`. -/
structure InstalledFamily.CtorAbstract (venv : VEnv) (B : InstalledBlock)
    (c : ConstructorVal) (T : VConstVal) : Prop where
  name : c.name = T.name
  uvars : T.uvars = B.decl.uvars
  lookup : venv.constants T.name = some T.toVConstant
  /-- The kernel field count is the forall arity of the abstract type beyond the
  parameters. -/
  numFields : c.numFields = T.type.forallArity - B.numParams
  telescope : CtorTelescopeAt venv c

/-- The abstract side of one family. -/
structure InstalledFamily.Abstract (venv : VEnv) (B : InstalledBlock)
    (F : InstalledFamily) : Prop where
  name : F.header.name = F.type.name
  numIndices : F.header.numIndices = F.type.numIndices
  uvars : F.type.uvars = B.decl.uvars
  lookup : venv.constants F.type.name = some F.type.toVConstant
  ctorsLength : B.stage ≠ .headers → F.ctors.length = F.type.ctors.length
  ctor : B.stage ≠ .headers → ∀ i (h₁ : i < F.ctors.length) (h₂ : i < F.type.ctors.length),
    InstalledFamily.CtorAbstract venv B F.ctors[i] F.type.ctors[i]
  params : B.stage = .complete → ∀ i (h : i < F.type.ctors.length),
    CtorParamsDefEq venv B.decl.uvars B.numParams F.type.type F.type.ctors[i].type

/-- The abstract side of a descriptor, for an observer that sees the block. -/
structure InstalledBlock.Abstract (env : Environment) (venv : VEnv) (B : InstalledBlock) :
    Prop where
  uvars : ∀ F ∈ B.families, F.header.levelParams.length = B.decl.uvars
  nparams : B.decl.nparams = B.numParams
  isUnsafe : B.decl.isUnsafe = B.isUnsafe
  types : B.decl.types = B.families.map (·.type)
  family : ∀ F ∈ B.families, F.Abstract venv B
  projections : B.stage ≠ .headers →
    ∀ e ∈ B.decl.projectionEntries, venv.projections e.typeName e.info
  eliminators : B.stage ≠ .headers → ∀ e ∈ B.eliminators, venv.eliminators e.1 e.2
  installed : B.stage = .complete → VEnv.InstalledBelow venv B.decl

/-- A well-formed descriptor: its kernel side, and its abstract side if the observer sees
it.  A block with only its headers installed has no abstract side yet: the abstract
declaration is fixed by the constructor check. -/
structure InstalledBlock.WF (safety : DefinitionSafety) (env : Environment) (venv : VEnv)
    (B : InstalledBlock) : Prop where
  concrete : B.Concrete env
  abstract : B.Visible safety → B.stage ≠ .headers → B.Abstract env venv
  /-- Every recursor the observer sees is aligned with the stored iota equations. -/
  recursor : ∀ r ∈ B.recursors, safety ≤ (ConstantInfo.recInfo r).safety →
    RecursorAlignmentCore venv r ∧ KLikeRecursor env.constants venv r

/-- The environment invariant: every inductive header, constructor and recursor of `env`
belongs to a well-formed descriptor that has reached at least `stage`, and every projection
registered in `venv` was registered by a visible one. -/
structure InstalledBlocks (safety : DefinitionSafety) (env : Environment) (venv : VEnv)
    (stage : InstallStage) : Prop where
  header : env.find? n = some (.inductInfo v) → n = v.name ∧
    ∃ B : InstalledBlock, stage ≤ B.stage ∧ B.WF safety env venv ∧
      ∃ F ∈ B.families, F.header = v
  ctor : env.find? n = some (.ctorInfo v) → n = v.name ∧
    ∃ B : InstalledBlock, stage ≤ B.stage ∧ B.stage ≠ .headers ∧ B.WF safety env venv ∧
      ∃ F ∈ B.families, v ∈ F.ctors
  recursor : env.find? n = some (.recInfo v) → n = v.name ∧
    ∃ B : InstalledBlock, stage ≤ B.stage ∧ B.WF safety env venv ∧ v ∈ B.recursors
  projection : venv.projections S info →
    ∃ B : InstalledBlock, stage ≤ B.stage ∧ B.stage ≠ .headers ∧ B.Visible safety ∧
      B.WF safety env venv ∧ ⟨S, info⟩ ∈ B.decl.projectionEntries

/-! ## Basic facts -/

namespace InstalledBlock

theorem safety_inductInfo {B : InstalledBlock} {v : InductiveVal} (h : v.isUnsafe = B.isUnsafe) :
    (ConstantInfo.inductInfo v).safety = B.defSafety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h,
    InstalledBlock.defSafety]

theorem safety_ctorInfo {B : InstalledBlock} {v : ConstructorVal} (h : v.isUnsafe = B.isUnsafe) :
    (ConstantInfo.ctorInfo v).safety = B.defSafety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h,
    InstalledBlock.defSafety]

theorem Visible.mono {B : InstalledBlock} (h : safety ≤ safety') (H : B.Visible safety') :
    B.Visible safety := DefinitionSafety.le_trans h H

theorem mem_names {B : InstalledBlock} {F : InstalledFamily} (h : F ∈ B.families) :
    F.header.name ∈ B.names := List.mem_map_of_mem h

/-- The header names of a block are found as its families' headers. -/
theorem Concrete.memberInfos {env : Environment} {B : InstalledBlock} (H : B.Concrete env) :
    VerifyInductive.InductiveMemberInfos env B.names := by
  have : ∀ L : List InstalledFamily, (∀ F ∈ L, F ∈ B.families) →
      VerifyInductive.InductiveMemberInfos env (L.map (·.header.name)) := by
    intro L hL
    induction L with
    | nil => exact .nil
    | cons F L ih =>
      exact .cons (H.header F (hL F (by simp)))
        (ih fun G hG => hL G (by simp [hG]))
  exact this B.families fun _ h => h

/-- The `i`th constructor of a family of a block at the constructor stage. -/
theorem Concrete.ctor_getElem {env : Environment} {B : InstalledBlock} (H : B.Concrete env)
    (hst : B.stage ≠ .headers) {F : InstalledFamily} (hF : F ∈ B.families) {i : Nat}
    (hi : i < F.header.ctors.length) :
    ∃ h : i < F.ctors.length, F.header.ctors[i] = F.ctors[i].name := by
  have hnames := H.ctorNames hst F hF
  have hlen : F.ctors.length = F.header.ctors.length := by
    rw [← hnames, List.length_map]
  refine ⟨hlen ▸ hi, ?_⟩
  simp only [← hnames, List.getElem_map]

end InstalledBlock

/-! ## Transport -/

/-- A descriptor stays well formed when the kernel environment grows without adding the
constructor names it awaits, and the abstract environment grows. -/
theorem InstalledBlock.WF.mono {B : InstalledBlock} (H : B.WF safety env venv)
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci)
    (hmap : ∀ {n ci}, env.constants.find? n = some ci → env'.constants.find? n = some ci)
    (hpending : B.stage = .headers → ∀ F ∈ B.families, ∀ n ∈ F.header.ctors,
      env'.find? n = none)
    (hle : venv ≤ venv') : B.WF safety env' venv' where
  concrete := by
    have C := H.concrete
    exact {
      header := fun F hF => hpres (C.header F hF)
      all := C.all
      nodup := C.nodup
      numParams := C.numParams
      isUnsafe := C.isUnsafe
      pending := hpending
      ctorNames := C.ctorNames
      ctor := fun hst F hF i hi =>
        let D := C.ctor hst F hF i hi
        { D with find := hpres D.find }
      recursor := fun r hr => ⟨hpres (C.recursor r hr).1, (C.recursor r hr).2⟩
      recursorMajor := fun r hr =>
        let ⟨info, hinfo, hctors⟩ := C.recursorMajor r hr
        ⟨info, hpres hinfo, fun n hn =>
          let ⟨ci, hci⟩ := hctors n hn
          ⟨ci, hpres hci⟩⟩ }
  abstract hvis hst := by
    have A := H.abstract hvis hst
    exact {
      uvars := A.uvars
      nparams := A.nparams
      isUnsafe := A.isUnsafe
      types := A.types
      family := fun F hF =>
        let FA := A.family F hF
        { name := FA.name
          numIndices := FA.numIndices
          uvars := FA.uvars
          lookup := hle.constants FA.lookup
          ctorsLength := FA.ctorsLength
          ctor := fun hst i h₁ h₂ =>
            let D := FA.ctor hst i h₁ h₂
            { D with
              lookup := hle.constants D.lookup
              telescope := D.telescope.mono hle }
          params := fun hst i h => (FA.params hst i h).mono hle }
      projections := fun hst e he => hle.projections (A.projections hst e he)
      eliminators := fun hst e he => hle.eliminators (A.eliminators hst e he)
      installed := fun hst => (A.installed hst).mono hle }
  recursor r hr hvis :=
    ⟨(H.recursor r hr hvis).1.mono hle, (H.recursor r hr hvis).2.mono hle hmap⟩

/-- Lower the stage the invariant promises. -/
theorem InstalledBlocks.weaken (H : InstalledBlocks safety env venv st) (h : st' ≤ st) :
    InstalledBlocks safety env venv st' where
  header hf :=
    let ⟨hn, B, hst, hB, rest⟩ := H.header hf
    ⟨hn, B, InstallStage.le_trans h hst, hB, rest⟩
  ctor hf :=
    let ⟨hn, B, hst, hne, hB, rest⟩ := H.ctor hf
    ⟨hn, B, InstallStage.le_trans h hst, hne, hB, rest⟩
  recursor hf :=
    let ⟨hn, B, hst, hB, rest⟩ := H.recursor hf
    ⟨hn, B, InstallStage.le_trans h hst, hB, rest⟩
  projection hp :=
    let ⟨B, hst, hne, hvis, hB, rest⟩ := H.projection hp
    ⟨B, InstallStage.le_trans h hst, hne, hvis, hB, rest⟩

/-- The general extension step.  Old constants keep their descriptors, which survive because
no constructor name an old header lists becomes present; every new header, constructor and
recursor, and every new projection entry, comes with a descriptor of the extended
environments. -/
theorem InstalledBlocks.extend (H : InstalledBlocks safety env venv st)
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci)
    (hmap : ∀ {n ci}, env.constants.find? n = some ci → env'.constants.find? n = some ci)
    (hunlisted : ∀ {fn fi n}, env.find? fn = some (.inductInfo fi) → n ∈ fi.ctors →
      env.find? n = none → env'.find? n = none)
    (hle : venv ≤ venv') (hst : st' ≤ st)
    (hheader : ∀ {n v}, env'.find? n = some (.inductInfo v) → env.find? n = none →
      n = v.name ∧ ∃ B : InstalledBlock, st' ≤ B.stage ∧ B.WF safety env' venv' ∧
        ∃ F ∈ B.families, F.header = v)
    (hctor : ∀ {n v}, env'.find? n = some (.ctorInfo v) → env.find? n = none →
      n = v.name ∧ ∃ B : InstalledBlock, st' ≤ B.stage ∧ B.stage ≠ .headers ∧
        B.WF safety env' venv' ∧ ∃ F ∈ B.families, v ∈ F.ctors)
    (hrecursor : ∀ {n v}, env'.find? n = some (.recInfo v) → env.find? n = none →
      n = v.name ∧ ∃ B : InstalledBlock, st' ≤ B.stage ∧ B.WF safety env' venv' ∧
        v ∈ B.recursors)
    (hproj : ∀ {S info}, venv'.projections S info → venv.projections S info ∨
      ∃ B : InstalledBlock, st' ≤ B.stage ∧ B.stage ≠ .headers ∧ B.Visible safety ∧
        B.WF safety env' venv' ∧ ⟨S, info⟩ ∈ B.decl.projectionEntries) :
    InstalledBlocks safety env' venv' st' := by
  have transport : ∀ {B : InstalledBlock}, B.WF safety env venv → B.WF safety env' venv' :=
    fun {B} hB => hB.mono hpres hmap (fun hst F hF n hn =>
      hunlisted (hB.concrete.header F hF) hn (hB.concrete.pending hst F hF n hn)) hle
  have old : ∀ {n ci}, env'.find? n = some ci → env.find? n = none ∨ env.find? n = some ci := by
    intro n ci h
    cases h' : env.find? n with
    | none => exact .inl rfl
    | some ci' =>
      rw [hpres h'] at h
      exact .inr (by rw [Option.some.inj h])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n v hf
    rcases old hf with hnone | hold
    · exact hheader hf hnone
    · obtain ⟨hn, B, hstB, hB, rest⟩ := H.header hold
      exact ⟨hn, B, InstallStage.le_trans hst hstB, transport hB, rest⟩
  · intro n v hf
    rcases old hf with hnone | hold
    · exact hctor hf hnone
    · obtain ⟨hn, B, hstB, hne, hB, rest⟩ := H.ctor hold
      exact ⟨hn, B, InstallStage.le_trans hst hstB, hne, transport hB, rest⟩
  · intro n v hf
    rcases old hf with hnone | hold
    · exact hrecursor hf hnone
    · obtain ⟨hn, B, hstB, hB, rest⟩ := H.recursor hold
      exact ⟨hn, B, InstallStage.le_trans hst hstB, transport hB, rest⟩
  · intro S info hp
    rcases hproj hp with hold | hnew
    · obtain ⟨B, hstB, hne, hvis, hB, rest⟩ := H.projection hold
      exact ⟨B, InstallStage.le_trans hst hstB, hne, hvis, transport hB, rest⟩
    · exact hnew

/-- The empty environment has no blocks. -/
theorem InstalledBlocks.empty {env : Environment} (h : ∀ n, env.find? n = none) :
    InstalledBlocks safety env .empty st where
  header hf := by rw [h] at hf; cases hf
  ctor hf := by rw [h] at hf; cases hf
  recursor hf := by rw [h] at hf; cases hf
  projection hp := hp.elim

/-! ## Projections of the invariant -/

namespace InstalledBlocks

variable {safety : DefinitionSafety} {env : Environment} {venv : VEnv} {st : InstallStage}

/-- Every kernel inductive header has complete mutual-family metadata. -/
theorem mutualInductivesClosed (H : InstalledBlocks safety env venv st)
    (hst : .constructors ≤ st) : VerifyInductive.MutualInductivesClosed env := by
  intro targetName value hfind
  obtain ⟨hn, B, hstB, hB, F, hF, rfl⟩ := H.header hfind
  have C := hB.concrete
  have hne := InstallStage.ne_headers hst hstB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [C.all hne F hF]; exact C.memberInfos
  · rw [C.all hne F hF, hn]; exact InstalledBlock.mem_names hF
  · rw [C.all hne F hF]; exact C.nodup hne
  · intro member info hmember hfind'
    rw [C.all hne F hF] at hmember
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hmember
    rw [C.header G hG] at hfind'
    cases Option.some.inj hfind'
    rw [C.numParams G hG, C.numParams F hF]

/-- Every present constructor is listed by its present owner, with the owner's `isUnsafe`. -/
theorem constructorOwnersPresent (H : InstalledBlocks safety env venv st) :
    VerifyInductive.ConstructorOwnersPresent env := by
  intro name info hfind
  obtain ⟨hn, B, -, hne, hB, F, hF, hmem⟩ := H.ctor hfind
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  have D := hB.concrete.ctor hne F hF i hi
  refine ⟨F.header, by rw [D.induct]; exact hB.concrete.header F hF, ?_, ?_⟩
  · rw [hn, ← hB.concrete.ctorNames hne F hF]
    exact List.mem_map_of_mem (List.getElem_mem hi)
  · rw [D.isUnsafe, hB.concrete.isUnsafe F hF]

/-- Every name a present header lists is, if present, a constructor of that header. -/
theorem listedConstructorsCoherent (H : InstalledBlocks safety env venv st) :
    VerifyInductive.ListedConstructorsCoherent env := by
  intro familyName familyInfo hfamily name hname ci hci
  obtain ⟨hn, B, -, hB, F, hF, rfl⟩ := H.header hfamily
  by_cases hst : B.stage = .headers
  · rw [hB.concrete.pending hst F hF name hname] at hci
    cases hci
  · rw [← hB.concrete.ctorNames hst F hF] at hname
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hname
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    have D := hB.concrete.ctor hst F hF i hi
    rw [D.find] at hci
    cases hci
    exact ⟨_, rfl, D.induct.trans hn.symm,
      D.isUnsafe.trans (hB.concrete.isUnsafe F hF).symm⟩

/-- Once every block has its constructors, every listed constructor is present. -/
theorem listedConstructorsPresent (H : InstalledBlocks safety env venv st)
    (hst : .constructors ≤ st) : VerifyInductive.ListedConstructorsPresent env := by
  intro familyName familyInfo hfamily name hname
  obtain ⟨-, B, hstB, hB, F, hF, rfl⟩ := H.header hfamily
  have hne := InstallStage.ne_headers hst hstB
  rw [← hB.concrete.ctorNames hne F hF] at hname
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hname
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  exact ⟨_, (hB.concrete.ctor hne F hF i hi).find⟩

/-- Once every block has its constructors, every listed constructor resolves to coherent
kernel metadata. -/
theorem inductiveConstructorsCoherent (H : InstalledBlocks safety env venv st)
    (hst : .constructors ≤ st) : VerifyInductive.InductiveConstructorsCoherent env := by
  intro familyName familyInfo hfamily i hi
  obtain ⟨hn, B, hstB, hB, F, hF, rfl⟩ := H.header hfamily
  have hne := InstallStage.ne_headers hst hstB
  obtain ⟨hi', hname⟩ := hB.concrete.ctor_getElem hne hF hi
  have D := hB.concrete.ctor hne F hF i hi'
  exact ⟨{
    info := F.ctors[i]
    lookup := hname ▸ D.find
    induct := D.induct.trans hn.symm
    cidx := D.cidx
    numParams := D.numParams.trans (hB.concrete.numParams F hF).symm
    levelParams := D.levelParams
    isUnsafe := D.isUnsafe.trans (hB.concrete.isUnsafe F hF).symm }⟩

/-- Every visible constructor carries its telescope certificate. -/
theorem ctorTelescopes (H : InstalledBlocks safety env venv st) :
    CtorTelescopes safety env venv := by
  intro name ci hfind hvis
  obtain ⟨-, B, -, hne, hB, F, hF, hmem⟩ := H.ctor hfind
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  have D := hB.concrete.ctor hne F hF i hi
  have hvis' : B.Visible safety := by
    rw [InstalledBlock.safety_ctorInfo D.isUnsafe] at hvis
    exact hvis
  have FA := (hB.abstract hvis' hne).family F hF
  exact (FA.ctor hne i hi (FA.ctorsLength hne ▸ hi)).telescope

/-- A family of a visible block at the constructor stage with a single constructor `c`
registers the projection entry of that constructor. -/
private theorem singleton_entry {B : InstalledBlock} {F : InstalledFamily}
    (A : B.Abstract env venv) (hst : B.stage ≠ .headers) (hF : F ∈ B.families)
    {T : VConstVal} (hT : F.type.ctors = [T]) :
    venv.projections F.type.name {
      uvars := B.decl.uvars
      nparams := B.decl.nparams
      nindices := F.type.numIndices
      resultLevel := F.type.resultLevel
      ctorName := T.name
      ctorType := T.type } := by
  refine A.projections hst ⟨F.type.name, _⟩ ?_
  rw [VInductDecl.projectionEntries, List.mem_filterMap]
  refine ⟨F.type, ?_, by simp [hT]⟩
  rw [A.types]
  exact List.mem_map_of_mem hF

/-- Every visible singleton family whose constructor is present aligns with the abstract
projection registry. -/
theorem projectionRegistryCoherent (H : InstalledBlocks safety env venv st)
    (hwf : env.constants.WF) : ProjectionRegistryCoherent safety env.constants venv := by
  have hfind : ∀ {n ci}, env.constants.find? n = some ci → env.find? n = some ci := by
    intro n ci h
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  intro familyName familyInfo constructorName constructorInfo hfamily hvisible hsingle
    hconstructor hinduct
  obtain ⟨hn, B, -, hB, F, hF, rfl⟩ := H.header (hfind hfamily)
  have C := hB.concrete
  have hst : B.stage ≠ .headers := by
    intro hst
    have := C.pending hst F hF constructorName (by rw [hsingle]; simp)
    rw [hfind hconstructor] at this
    cases this
  have hvis : B.Visible safety := by
    rw [InstalledBlock.safety_inductInfo (C.isUnsafe F hF)] at hvisible
    exact hvisible
  have A := hB.abstract hvis hst
  have FA := A.family F hF
  have hnames := C.ctorNames hst F hF
  rw [hsingle] at hnames
  obtain ⟨c, hc, hcname⟩ : ∃ c, F.ctors = [c] ∧ c.name = constructorName := by
    match h : F.ctors, hnames with
    | [c], hnames => exact ⟨c, rfl, by simpa using hnames⟩
  have hlen := FA.ctorsLength hst
  obtain ⟨T, hT⟩ : ∃ T, F.type.ctors = [T] := by
    rw [hc] at hlen
    match h : F.type.ctors, hlen with
    | [T], _ => exact ⟨T, rfl⟩
  have D := C.ctor hst F hF 0 (by simp [hc])
  have DA := FA.ctor hst 0 (by simp [hc]) (by simp [hT])
  simp only [hc, hT, List.getElem_cons_zero] at D DA
  have hceq : c = constructorInfo := by
    have := D.find
    rw [hcname, hfind hconstructor] at this
    exact (ConstantInfo.ctorInfo.inj (Option.some.inj this)).symm
  subst hceq
  have hname : F.header.name = F.type.name := FA.name
  exact ⟨{
    info := {
      uvars := B.decl.uvars
      nparams := B.decl.nparams
      nindices := F.type.numIndices
      resultLevel := F.type.resultLevel
      ctorName := T.name
      ctorType := T.type }
    projection := by
      rw [hn, hname]
      exact singleton_entry A hst hF hT
    ctorName := DA.name.symm.trans hcname
    uvars := A.uvars F hF
    nparams := by rw [C.numParams F hF, A.nparams]
    nindices := FA.numIndices
    constructorInfo := c
    constructor_lookup := hconstructor
    constructor_induct := hinduct
    constructor_levelParams := D.levelParams
    constructor_numParams := D.numParams.trans (C.numParams F hF).symm
    constructor_isUnsafe := D.isUnsafe.trans (C.isUnsafe F hF).symm
    constructor_numFields := by
      rw [DA.numFields, VProjectionInfo.numFields, A.nparams]
    constructor_arity := by rw [D.numFields, D.numParams]
    familyType := F.type.type
    family_lookup := by
      rw [hn, hname, FA.lookup, ← FA.uvars]
    constructor_abstract := by
      rw [← hcname, DA.name, DA.lookup, ← DA.uvars] }⟩

/-- The reverse direction of the projection registry: a structure with an abstract registry
entry is a visible kernel header listing exactly the registered constructor, which is
present with that header as its owner. -/
theorem projectionHeader (H : InstalledBlocks safety env venv st)
    (hproj : venv.projections S info) :
    ∃ v : InductiveVal, env.find? S = some (.inductInfo v) ∧ v.ctors = [info.ctorName] ∧
      safety ≤ (ConstantInfo.inductInfo v).safety ∧
      ∃ c : ConstructorVal, env.find? info.ctorName = some (.ctorInfo c) ∧ c.induct = S := by
  obtain ⟨B, -, hst, hvis, hB, hentry⟩ := H.projection hproj
  have A := hB.abstract hvis hst
  have C := hB.concrete
  rw [VInductDecl.projectionEntries, List.mem_filterMap] at hentry
  obtain ⟨T, hT, hentry⟩ := hentry
  rw [A.types] at hT
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hT
  have FA := A.family F hF
  match hc : F.type.ctors, hentry with
  | [Tc], hentry =>
    simp only [Option.some.injEq, VProjectionEntry.mk.injEq] at hentry
    obtain ⟨rfl, rfl⟩ := hentry
    have hlen := FA.ctorsLength hst
    rw [hc] at hlen
    obtain ⟨c, hcs⟩ : ∃ c, F.ctors = [c] := by
      match h : F.ctors, hlen with
      | [c], _ => exact ⟨c, rfl⟩
    have D := C.ctor hst F hF 0 (by simp [hcs])
    have DA := FA.ctor hst 0 (by simp [hcs]) (by simp [hc])
    simp only [hcs, hc, List.getElem_cons_zero] at D DA
    refine ⟨F.header, ?_, ?_, ?_, c, ?_, ?_⟩
    · rw [← FA.name]; exact C.header F hF
    · rw [← C.ctorNames hst F hF, hcs]; simp [DA.name]
    · rw [InstalledBlock.safety_inductInfo (C.isUnsafe F hF)]; exact hvis
    · rw [← DA.name]; exact D.find
    · rw [D.induct, FA.name]

/-- Recursor coherence, with the rigidity of each major inductive read off the heads of the
stored equations. -/
theorem recursorEnvCoherent (H : InstalledBlocks safety env venv st)
    (hwf : env.constants.WF) (hheads : EquationHeadsCoherent env.constants venv) :
    RecursorEnvCoherent safety env.constants venv := by
  have hfind : ∀ {n ci}, env.constants.find? n = some ci → env.find? n = some ci := by
    intro n ci h
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  have hmap : ∀ {n ci}, env.find? n = some ci → env.constants.find? n = some ci := by
    intro n ci h
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h
  refine ⟨?_, ?_, hheads⟩
  · intro name r hrec hvisible
    obtain ⟨-, B, -, hB, hmem⟩ := H.recursor (hfind hrec)
    obtain ⟨hcore, hk⟩ := hB.recursor r hmem hvisible
    obtain ⟨info, hmajor, -⟩ := hB.concrete.recursorMajor r hmem
    exact ⟨hcore.toAlignment (hheads.rigid (hmap hmajor)), hk⟩
  · intro name r hrec _
    obtain ⟨-, B, -, hB, hmem⟩ := H.recursor (hfind hrec)
    obtain ⟨info, hmajor, -⟩ := hB.concrete.recursorMajor r hmem
    exact ⟨info, hmap hmajor⟩

/-- The major inductive of every present recursor is a header whose constructors are all
present. -/
theorem recursorMajorCtors (H : InstalledBlocks safety env venv st)
    (hrec : env.find? name = some (.recInfo r)) :
    ∃ info, env.find? r.getMajorInduct = some (.inductInfo info) ∧
      ∀ n ∈ info.ctors, ∃ ci, env.find? n = some ci := by
  obtain ⟨-, B, -, hB, hmem⟩ := H.recursor hrec
  exact hB.concrete.recursorMajor r hmem

/-- Constructor parameter agreement of every visible constructor, once every block is
complete. -/
theorem constructorParameterAlignment (H : InstalledBlocks safety env venv .complete) :
    VerifyInductive.ConstructorParameterAlignment safety env venv := by
  intro familyName familyInfo hfamily hvisible i hi
  obtain ⟨hn, B, hst, hB, F, hF, rfl⟩ := H.header hfamily
  have hcomplete : B.stage = .complete := InstallStage.eq_complete hst
  have hne : B.stage ≠ .headers := by rw [hcomplete]; decide
  have C := hB.concrete
  have hvis : B.Visible safety := by
    unfold InstalledBlock.Visible InstalledBlock.defSafety
    rw [← C.isUnsafe F hF]
    exact hvisible
  have A := hB.abstract hvis hne
  have FA := A.family F hF
  obtain ⟨hi', hname⟩ := C.ctor_getElem hne hF hi
  have D := C.ctor hne F hF i hi'
  have hi'' : i < F.type.ctors.length := FA.ctorsLength hne ▸ hi'
  have DA := FA.ctor hne i hi' hi''
  obtain ⟨fN, cN, fD, cD, fT, cT, fS, cS, h1, h2, h3, h4, h5⟩ := FA.params hcomplete i hi''
  have huv : F.header.levelParams.length = B.decl.uvars := A.uvars F hF
  have hnp : F.header.numParams = B.numParams := C.numParams F hF
  exact ⟨{
    info := F.ctors[i]
    lookup := hname ▸ D.find
    induct := D.induct.trans hn.symm
    cidx := D.cidx
    numParams := D.numParams.trans hnp.symm
    levelParams := D.levelParams
    isUnsafe := D.isUnsafe.trans (C.isUnsafe F hF).symm
    familyTarget := F.type.toVConstant
    constructorTarget := F.type.ctors[i].toVConstant
    familyLookup := by rw [hn, FA.name]; exact FA.lookup
    constructorLookup := by rw [hname, DA.name]; exact DA.lookup
    familyUvars := FA.uvars.trans huv.symm
    constructorUvars := DA.uvars.trans huv.symm
    familyNormalized := fN
    constructorNormalized := cN
    familyDomains := fD
    constructorDomains := cD
    familyTail := fT
    constructorTail := cT
    familyType := fS
    constructorType := cS
    familyDefEq := by rw [huv]; exact h1
    constructorDefEq := by rw [huv]; exact h2
    familyParams := by rw [hnp]; exact h3
    constructorParams := by rw [hnp]; exact h4
    parameterDomains := by rw [huv]; exact h5 }⟩

end InstalledBlocks

/-! ## Installing a complete block -/

namespace InstalledBlocks

/-- The header stored under `n`, if `env` stores one there. -/
noncomputable def headerAt (env : Environment) (n : Name) : InductiveVal :=
  match env.find? n with
  | some (.inductInfo v) => v
  | _ => default

theorem headerAt_eq {env : Environment} (h : env.find? n = some (.inductInfo v)) :
    headerAt env n = v := by
  simp [headerAt, h]

/-- The constructor stored under `n`, if `env` stores one there. -/
noncomputable def ctorAt (env : Environment) (n : Name) : ConstructorVal :=
  match env.find? n with
  | some (.ctorInfo v) => v
  | _ => default

theorem ctorAt_eq {env : Environment} (h : env.find? n = some (.ctorInfo v)) :
    ctorAt env n = v := by
  simp [ctorAt, h]

/-- The family of `env` that installs the abstract family `T`: the header stored under its
name and the constructors that header lists. -/
noncomputable def familyAt (env : Environment) (T : VInductiveType) : InstalledFamily where
  header := headerAt env T.name
  ctors := (headerAt env T.name).ctors.map (ctorAt env)
  type := T

/-- The recursors of `env'` absent from `env`. -/
noncomputable def newRecursors (env env' : Environment) : List RecursorVal :=
  env'.constants.toList'.filterMap fun p =>
    match env'.find? p.1, env.find? p.1 with
    | some (.recInfo r), none => some r
    | _, _ => none

theorem mem_newRecursors {env env' : Environment} (hwf : env'.constants.WF) :
    r ∈ newRecursors env env' ↔
      ∃ n, env'.find? n = some (.recInfo r) ∧ env.find? n = none := by
  constructor
  · intro h
    obtain ⟨⟨n, ci⟩, -, hp⟩ := List.mem_filterMap.mp h
    revert hp
    dsimp only
    split
    · rename_i r' h1 h2
      intro hp
      cases hp
      exact ⟨n, h1, h2⟩
    · intro hp; cases hp
  · rintro ⟨n, h1, h2⟩
    have hlookup : env'.constants.toList'.lookup n = some (.recInfo r) := by
      rw [← hwf.find?_eq, ← hwf.find?'_eq_find?]
      exact h1
    obtain ⟨l₁, l₂, heq, -⟩ := List.lookup_eq_some_iff.mp hlookup
    refine List.mem_filterMap.mpr ⟨(n, .recInfo r), by rw [heq]; simp, ?_⟩
    simp [h1, h2]

variable {safety : DefinitionSafety} {env env' : Environment} {venv venv' : VEnv}

/-- The abstract registrations of a declaration at a stage at least `.constructors`: its
family and constructor constants, its projection entries and its case eliminators. -/
structure DeclRegistered (venv : VEnv) (decl : VInductDecl)
    (es : List (Name × InductiveSignature.CaseSchema)) : Prop where
  typeUvars : ∀ T ∈ decl.types, T.uvars = decl.uvars
  constructorUvars : ∀ c ∈ decl.constructorConstants, c.uvars = decl.uvars
  family : ∀ i (hi : i < decl.types.length),
    venv.constants decl.types[i].name = some decl.types[i].toVConstant
  ctor : ∀ i k (hi : i < decl.types.length) (hk : k < decl.types[i].ctors.length),
    venv.constants decl.types[i].ctors[k].name = some decl.types[i].ctors[k].toVConstant
  projections : ∀ e ∈ decl.projectionEntries, venv.projections e.typeName e.info
  eliminators : ∀ e ∈ es, venv.eliminators e.1 e.2

/-- Installing an inductive declaration up to `stage` (`.constructors` or `.complete`)
extends the invariant by one descriptor, read off the installation: its families are the
declaration's (each a new kernel header aligned with it), its constructors those the headers
list, and its recursors the given new kernel recursors.  The abstract side is supplied at
observers that see the declaration. -/
theorem addBlock {decl : VInductDecl} (stage : InstallStage) (hstage : stage ≠ .headers)
    (H : InstalledBlocks safety env venv st) (hst' : st' ≤ st) (hstage' : st' ≤ stage)
    (hpresent : VerifyInductive.ListedConstructorsPresent env)
    (hwf : env.constants.WF) (hchk' : CheckingEnv safety env' venv')
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci)
    (hle : venv ≤ venv')
    (horigins : InductInfosFromDecl env.constants env'.constants decl)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, env'.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none)
    (hnodup : (decl.types.map (·.name)).Nodup)
    (howners : VerifyInductive.ConstructorOwnersPresent env')
    (recs : List RecursorVal)
    (hrecs : ∀ {n r}, env'.find? n = some (.recInfo r) → env.find? n = none → r ∈ recs)
    (hrecFind : ∀ r ∈ recs, env'.find? r.name = some (.recInfo r) ∧ env.find? r.name = none)
    (hrecMajor : ∀ r ∈ recs, ∃ info, env'.find? r.getMajorInduct = some (.inductInfo info))
    (es : List (Name × InductiveSignature.CaseSchema))
    (hreg : safety ≤ (if decl.isUnsafe then .unsafe else .safe) → DeclRegistered venv' decl es)
    (hrecAlign : ∀ r ∈ recs, safety ≤ (ConstantInfo.recInfo r).safety →
      RecursorAlignmentCore venv' r ∧ KLikeRecursor env'.constants venv' r)
    (hcomplete : safety ≤ (if decl.isUnsafe then .unsafe else .safe) → stage = .complete →
      VEnv.InstalledBelow venv' decl ∧
        VerifyInductive.ConstructorParameterAlignment safety env' venv')
    (hproj : ∀ {S info}, venv'.projections S info → venv.projections S info ∨
      (safety ≤ (if decl.isUnsafe then .unsafe else .safe) ∧
        ⟨S, info⟩ ∈ decl.projectionEntries))
    (htels : ∀ {n c}, env'.find? n = some (.ctorInfo c) → env.find? n = none →
      safety ≤ (ConstantInfo.ctorInfo c).safety → CtorTelescopeAt venv' c) :
    InstalledBlocks safety env' venv' st' := by
  have hwf' : env'.constants.WF := hchk'.map_wf
  have toEnv' : ∀ {n ci}, env'.constants.find? n = some ci → env'.find? n = some ci := by
    intro n ci h; rwa [Lean.Kernel.Environment.find?, hwf'.find?'_eq_find?]
  have toMap' : ∀ {n ci}, env'.find? n = some ci → env'.constants.find? n = some ci := by
    intro n ci h; rwa [Lean.Kernel.Environment.find?, hwf'.find?'_eq_find?] at h
  have toEnv : ∀ {n ci}, env.constants.find? n = some ci → env.find? n = some ci := by
    intro n ci h; rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  have toMap : ∀ {n ci}, env.find? n = some ci → env.constants.find? n = some ci := by
    intro n ci h; rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h
  have hmap : ∀ {n ci}, env.constants.find? n = some ci → env'.constants.find? n = some ci :=
    fun h => toMap' (hpres (toEnv h))
  -- the declaration's families are exactly aligned new headers
  have hfam : ∀ j (hj : j < decl.types.length),
      env'.find? decl.types[j].name =
          some (.inductInfo (headerAt env' decl.types[j].name)) ∧
        env.find? decl.types[j].name = none ∧
        (headerAt env' decl.types[j].name).name = decl.types[j].name ∧
        InductInfoAlignment env'.constants decl j (headerAt env' decl.types[j].name) := by
    intro j hj
    obtain ⟨v, hv, hfresh⟩ := hcover decl.types[j] (List.getElem_mem hj)
    rw [headerAt_eq hv]
    have hvname : v.name = decl.types[j].name := hchk'.find?_name hv
    refine ⟨hv, hfresh, hvname, ?_⟩
    rcases horigins _ v (toMap' hv) with hold | ⟨i, hname, ⟨A⟩⟩
    · rw [toEnv hold] at hfresh; cases hfresh
    · have hi : i = j := by
        have heq : (decl.types.map (·.name))[i]'(by simpa using A.familyIdx_lt) =
            (decl.types.map (·.name))[j]'(by simpa using hj) := by
          simp only [List.getElem_map]
          rw [← A.name, hvname]
        exact (List.getElem_inj hnodup).mp heq
      subst hi
      exact A
  -- the members of the block
  have hmemFam : ∀ {F}, F ∈ decl.types.map (familyAt env') →
      ∃ j, ∃ hj : j < decl.types.length, F = familyAt env' decl.types[j] := by
    intro F hF
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hF
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hT
    exact ⟨j, hj, rfl⟩
  have hfamMem : ∀ j (hj : j < decl.types.length),
      familyAt env' decl.types[j] ∈ decl.types.map (familyAt env') :=
    fun j hj => List.mem_map_of_mem (List.getElem_mem hj)
  have hnames : (decl.types.map (familyAt env')).map (·.header.name) =
      decl.types.map (·.name) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro T hT
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hT
    exact (hfam j hj).2.2.1
  -- the constructors of the `j`th family
  have hctor : ∀ j (hj : j < decl.types.length) k
      (hk : k < (headerAt env' decl.types[j].name).ctors.length),
      ∃ C : CtorInfoAlignment env'.constants decl j k (headerAt env' decl.types[j].name),
        ctorAt env' (headerAt env' decl.types[j].name).ctors[k] = C.info ∧
        C.info.name = (headerAt env' decl.types[j].name).ctors[k] := by
    intro j hj k hk
    have A := (hfam j hj).2.2.2
    have hk' : k < decl.types[j].ctors.length := A.constructors ▸ hk
    obtain ⟨C⟩ := A.constructor k hk'
    refine ⟨C, ctorAt_eq (toEnv' C.lookup), hchk'.find?_name (toEnv' C.lookup)⟩
  have hctorNames : ∀ j (hj : j < decl.types.length),
      (familyAt env' decl.types[j]).ctors.map (·.name) =
        (familyAt env' decl.types[j]).header.ctors := by
    intro j hj
    simp only [familyAt, List.map_map]
    apply List.ext_getElem (by simp)
    intro k hk _
    simp only [List.getElem_map, Function.comp]
    obtain ⟨C, h1, h2⟩ := hctor j hj k (by simpa using hk)
    rw [h1, h2]
  let B : InstalledBlock := {
    stage := stage
    numParams := decl.nparams
    isUnsafe := decl.isUnsafe
    families := decl.types.map (familyAt env')
    recursors := recs
    eliminators := es
    decl := decl }
  have hBnames : B.names = decl.types.map (·.name) := hnames
  have hBvis : ∀ {safety'}, B.Visible safety' ↔
      safety' ≤ (if decl.isUnsafe then .unsafe else .safe) := Iff.rfl
  have hBC : B.Concrete env' := {
    header := by
      intro F hF
      obtain ⟨j, hj, rfl⟩ := hmemFam hF
      obtain ⟨hv, -, hname, -⟩ := hfam j hj
      show env'.find? (headerAt env' decl.types[j].name).name = _
      rw [hname]; exact hv
    all := by
      intro _ F hF
      obtain ⟨j, hj, rfl⟩ := hmemFam hF
      rw [hBnames]
      exact (hfam j hj).2.2.2.all
    nodup := fun _ => by rw [hBnames]; exact hnodup
    numParams := by
      intro F hF
      obtain ⟨j, hj, rfl⟩ := hmemFam hF
      exact (hfam j hj).2.2.2.numParams
    isUnsafe := by
      intro F hF
      obtain ⟨j, hj, rfl⟩ := hmemFam hF
      exact (hfam j hj).2.2.2.isUnsafe
    pending := fun h => absurd h hstage
    ctorNames := by
      intro _ F hF
      obtain ⟨j, hj, rfl⟩ := hmemFam hF
      exact hctorNames j hj
    ctor := by
      intro _ F hF k hk
      obtain ⟨j, hj, rfl⟩ := hmemFam hF
      have hk' : k < (headerAt env' decl.types[j].name).ctors.length := by
        simpa [familyAt] using hk
      obtain ⟨C, h1, h2⟩ := hctor j hj k hk'
      have hget : (familyAt env' decl.types[j]).ctors[k] = C.info := by
        simp only [familyAt, List.getElem_map]; exact h1
      rw [hget]
      have A := (hfam j hj).2.2.2
      exact {
        find := by rw [h2]; exact toEnv' C.lookup
        induct := C.induct
        cidx := C.cidx
        numParams := C.numParams
        levelParams := C.levelParamsExact
        isUnsafe := C.isUnsafe
        numFields := C.numFields }
    recursor := fun r hr => ⟨(hrecFind r hr).1, hstage⟩
    recursorMajor := by
      intro r hr
      obtain ⟨info, hinfo⟩ := hrecMajor r hr
      refine ⟨info, hinfo, fun m hm => ?_⟩
      cases hold : env.find? r.getMajorInduct with
      | some ci =>
        have := hpres hold
        rw [hinfo] at this
        cases this
        obtain ⟨ci', hci'⟩ := hpresent _ info hold m hm
        exact ⟨ci', hpres hci'⟩
      | none =>
        rcases horigins _ info (toMap' hinfo) with hold' | ⟨i, -, ⟨A⟩⟩
        · rw [toEnv hold'] at hold; cases hold
        · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hm
          obtain ⟨C⟩ := A.constructor k (A.constructors ▸ hk)
          exact ⟨_, toEnv' C.lookup⟩ }
  have hBA : B.Visible safety → B.Abstract env' venv' := by
    intro hvis
    have hinst := hreg hvis
    exact {
      uvars := by
        intro F hF
        obtain ⟨j, hj, rfl⟩ := hmemFam hF
        exact (hfam j hj).2.2.2.levelParams
      nparams := rfl
      isUnsafe := rfl
      types := by
        show decl.types = (decl.types.map (familyAt env')).map (·.type)
        rw [List.map_map]
        exact (List.map_id' decl.types).symm.trans (List.map_congr_left fun _ _ => rfl)
      family := by
        intro F hF
        obtain ⟨j, hj, rfl⟩ := hmemFam hF
        obtain ⟨hv, -, hname, A⟩ := hfam j hj
        have hTmem : decl.types[j] ∈ decl.types := List.getElem_mem hj
        exact {
          name := hname
          numIndices := A.numIndices
          uvars := hinst.typeUvars _ hTmem
          lookup := hinst.family j hj
          ctorsLength := fun _ => by simpa [familyAt] using A.constructors
          ctor := by
            intro _ k h₁ h₂
            have hk' : k < (headerAt env' decl.types[j].name).ctors.length := by
              simpa [familyAt] using h₁
            obtain ⟨C, h1, h2⟩ := hctor j hj k hk'
            have hget : (familyAt env' decl.types[j]).ctors[k] = C.info := by
              simp only [familyAt, List.getElem_map]; exact h1
            rw [hget]
            have hCmem : decl.types[j].ctors[k] ∈ decl.constructorConstants := by
              simp only [VInductDecl.constructorConstants, List.mem_flatMap]
              exact ⟨_, hTmem, List.getElem_mem h₂⟩
            have hfresh : env.find? C.info.name = none := by
              cases hold : env.find? C.info.name with
              | none => rfl
              | some ci =>
                exfalso
                have h' := hpres hold
                rw [h2, toEnv' C.lookup] at h'
                cases h'
                obtain ⟨owner, howner, -⟩ := H.constructorOwnersPresent _ _ hold
                rw [C.induct] at howner
                have hf := (hfam j hj).2.1
                rw [← hname, howner] at hf
                cases hf
            exact {
              name := h2.trans C.name
              uvars := hinst.constructorUvars _ hCmem
              lookup := hinst.ctor j k hj h₂
              numFields := by rw [C.numFields_forallArity]; rfl
              telescope := htels (by rw [h2]; exact toEnv' C.lookup) hfresh (by
                simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial,
                  C.isUnsafe]
                exact hvis) }
          params := by
            intro hc k hk
            obtain ⟨-, hparamsAll⟩ := hcomplete hvis hc
            have hk' : k < (headerAt env' decl.types[j].name).ctors.length := by
              rw [A.constructors]; exact hk
            obtain ⟨P⟩ := hparamsAll _ _ hv (by rw [A.isUnsafe]; exact hvis) k hk'
            have hft : P.familyTarget = decl.types[j].toVConstant := by
              exact Option.some.inj (P.familyLookup.symm.trans
                (hinst.family j hj))
            have hct : P.constructorTarget = decl.types[j].ctors[k].toVConstant := by
              have h1 := P.constructorLookup
              obtain ⟨C, -, -⟩ := hctor j hj k hk'
              rw [C.name] at h1
              exact Option.some.inj (h1.symm.trans
                (hinst.ctor j k hj hk))
            have huv : (headerAt env' decl.types[j].name).levelParams.length = decl.uvars :=
              A.levelParams
            have hnp : (headerAt env' decl.types[j].name).numParams = decl.nparams :=
              A.numParams
            refine ⟨P.familyNormalized, P.constructorNormalized, P.familyDomains,
              P.constructorDomains, P.familyTail, P.constructorTail, P.familyType,
              P.constructorType, ?_, ?_, ?_, ?_, ?_⟩
            · have := P.familyDefEq; rw [hft, huv] at this; exact this
            · have := P.constructorDefEq; rw [hct, huv] at this; exact this
            · have := P.familyParams; rw [hnp] at this; exact this
            · have := P.constructorParams; rw [hnp] at this; exact this
            · have := P.parameterDomains; rw [huv] at this; exact this }
      projections := fun _ e he => hinst.projections e he
      eliminators := fun _ => hinst.eliminators
      installed := fun hc => (hcomplete hvis hc).1 }
  have hB : B.WF safety env' venv' := ⟨hBC, fun h _ => hBA h, hrecAlign⟩
  have hBmem : ∀ j (hj : j < decl.types.length),
      ∃ F ∈ B.families, F.header = headerAt env' decl.types[j].name :=
    fun j hj => ⟨_, hfamMem j hj, rfl⟩
  refine H.extend hpres hmap ?_ hle hst' ?_ ?_ ?_ ?_
  · intro fn fi n hfi hn hnone
    obtain ⟨ci, hci⟩ := hpresent fn fi hfi n hn
    rw [hci] at hnone; cases hnone
  · intro n v hf hnone
    have hn : n = v.name := (hchk'.find?_name hf).symm
    refine ⟨hn, B, hstage', hB, ?_⟩
    rcases horigins n v (toMap' hf) with hold | ⟨j, -, ⟨A⟩⟩
    · rw [toEnv hold] at hnone; cases hnone
    · obtain ⟨F, hF, hFh⟩ := hBmem j A.familyIdx_lt
      exact ⟨F, hF, hFh.trans (headerAt_eq (by rw [← A.name, ← hn]; exact hf))⟩
  · intro n v hf hnone
    have hn : n = v.name := (hchk'.find?_name hf).symm
    refine ⟨hn, B, hstage', hstage, hB, ?_⟩
    obtain ⟨owner, howner, hmem, -⟩ := howners n v hf
    have hownerNew : env.find? v.induct = none := by
      cases hold : env.find? v.induct with
      | none => rfl
      | some ci =>
        have := hpres hold
        rw [howner] at this
        cases this
        obtain ⟨ci', hci'⟩ := hpresent _ owner hold n hmem
        rw [hci'] at hnone; cases hnone
    rcases horigins _ owner (toMap' howner) with hold | ⟨j, -, ⟨A⟩⟩
    · rw [toEnv hold] at hownerNew; cases hownerNew
    · have hj := A.familyIdx_lt
      have hhead : headerAt env' decl.types[j].name = owner := by
        apply headerAt_eq
        have hname : owner.name = v.induct := hchk'.find?_name howner
        rw [← A.name, hname]; exact howner
      refine ⟨familyAt env' decl.types[j], hfamMem j hj, ?_⟩
      show v ∈ (headerAt env' decl.types[j].name).ctors.map (ctorAt env')
      rw [hhead]
      exact List.mem_map.mpr ⟨n, hmem, ctorAt_eq hf⟩
  · intro n v hf hnone
    have hn : n = v.name := (hchk'.find?_name hf).symm
    exact ⟨hn, B, hstage', hB, hrecs hf hnone⟩
  · intro S info hp
    rcases hproj hp with hold | ⟨hvis, hentry⟩
    · exact .inl hold
    · exact .inr ⟨B, hstage', hstage, hvis, hB, hentry⟩

/-- Installing a complete inductive declaration extends the invariant by one complete
descriptor (`addBlock`), whose recursors are the new kernel recursors and whose abstract side
is the installation `AddInduct`, at observers that see the declaration; observers that do
not see it keep their abstract environment. -/
theorem addInduct {decl : VInductDecl}
    (H : InstalledBlocks safety env venv .complete)
    (hwf : env.constants.WF) (hchk' : CheckingEnv safety env' venv')
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci)
    (hle : venv ≤ venv')
    (horigins : InductInfosFromDecl env.constants env'.constants decl)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, env'.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none)
    (hclosed : VerifyInductive.MutualInductivesClosed env')
    (howners : VerifyInductive.ConstructorOwnersPresent env')
    (hrecMajor : ∀ {n r}, env'.find? n = some (.recInfo r) → env.find? n = none →
      ∃ info, env'.find? r.getMajorInduct = some (.inductInfo info))
    (hadd : safety ≤ (if decl.isUnsafe then .unsafe else .safe) →
      AddInduct safety env.constants venv decl env'.constants venv')
    (hhidden : ¬ safety ≤ (if decl.isUnsafe then .unsafe else .safe) → venv' = venv)
    (hparams : safety ≤ (if decl.isUnsafe then .unsafe else .safe) →
      VerifyInductive.ConstructorParameterAlignment safety env' venv')
    (htels : safety ≤ (if decl.isUnsafe then .unsafe else .safe) →
      ∀ {n c}, env'.find? n = some (.ctorInfo c) → env.find? n = none →
        CtorTelescopeAt venv' c)
    (hrecAlign : ∀ {n r}, env'.find? n = some (.recInfo r) → env.find? n = none →
      safety ≤ (ConstantInfo.recInfo r).safety →
      RecursorAlignmentCore venv' r ∧ KLikeRecursor env'.constants venv' r) :
    InstalledBlocks safety env' venv' .complete := by
  have hwf' : env'.constants.WF := hchk'.map_wf
  have toMap' : ∀ {n ci}, env'.find? n = some ci → env'.constants.find? n = some ci := by
    intro n ci h; rwa [Lean.Kernel.Environment.find?, hwf'.find?'_eq_find?] at h
  have toEnv : ∀ {n ci}, env.constants.find? n = some ci → env.find? n = some ci := by
    intro n ci h; rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  have hnodup : (decl.types.map (·.name)).Nodup := by
    cases hts : decl.types with
    | nil => simp
    | cons T ts =>
      obtain ⟨v, hv, hfresh⟩ := hcover T (by simp [hts])
      rcases horigins _ v (toMap' hv) with hold | ⟨i, -, ⟨A⟩⟩
      · rw [toEnv hold] at hfresh; cases hfresh
      · rw [← hts, ← A.all]
        exact (hclosed _ v hv).names
  obtain ⟨es, hes, hproj⟩ : ∃ es : List (Name × InductiveSignature.CaseSchema),
      (safety ≤ (if decl.isUnsafe then .unsafe else .safe) →
        ∀ e ∈ es, venv'.eliminators e.1 e.2) ∧
      ∀ {S info}, venv'.projections S info → venv.projections S info ∨
        (safety ≤ (if decl.isUnsafe then .unsafe else .safe) ∧
          ⟨S, info⟩ ∈ decl.projectionEntries) := by
    by_cases hv : safety ≤ (if decl.isUnsafe then .unsafe else .safe)
    · have := (hadd hv).toVEnv
      cases this with
      | @intro block _ hdecl hcompile hblock helim hinstall =>
        refine ⟨block.eliminators, fun _ e he =>
          (VInductBlock.install_eliminators_iff hinstall).mpr (.inl he), ?_⟩
        intro S info hp
        rcases (VInductBlock.install_projections_iff hinstall).mp hp with
          ⟨entry, hentry, rfl, rfl⟩ | hold
        · right
          refine ⟨hv, ?_⟩
          rw [← hcompile.projections]
          exact hentry
        · exact .inl hold
    · refine ⟨[], fun h => absurd h hv, ?_⟩
      intro S info hp
      rw [hhidden hv] at hp
      exact .inl hp
  refine H.addBlock .complete (by decide) (InstallStage.le_refl _) (InstallStage.le_refl _)
    (H.listedConstructorsPresent (by decide)) hwf hchk' hpres hle horigins hcover hnodup
    howners (newRecursors env env') (fun hf hnone => (mem_newRecursors hwf').mpr ⟨_, hf, hnone⟩)
    ?_ ?_ es ?_ ?_ (fun hvis _ => ⟨(hadd hvis).installedCertificate, hparams hvis⟩) hproj ?_
  · intro r hr
    obtain ⟨n, h1, h2⟩ := (mem_newRecursors hwf').mp hr
    have hn : r.name = n := hchk'.find?_name h1
    rw [hn]; exact ⟨h1, h2⟩
  · intro r hr
    obtain ⟨n, h1, h2⟩ := (mem_newRecursors hwf').mp hr
    exact hrecMajor h1 h2
  · intro hvis
    have hinst := (hadd hvis).installedCertificate
    exact {
      typeUvars := hinst.typeUvars
      constructorUvars := hinst.constructorUvars
      family := hinst.familyConstant
      ctor := hinst.constructorConstant
      projections := fun _ he => hinst.projection he
      eliminators := hes hvis }
  · intro r hr hrvis
    obtain ⟨n, h1, h2⟩ := (mem_newRecursors hwf').mp hr
    exact hrecAlign h1 h2 hrvis
  · intro n c hf hnone hcvis
    refine htels ?_ hf hnone
    obtain ⟨owner, howner, hmem, hunsafe⟩ := howners n c hf
    have hpresent := H.listedConstructorsPresent (by decide)
    have hownerNew : env.find? c.induct = none := by
      cases hold : env.find? c.induct with
      | none => rfl
      | some ci =>
        have := hpres hold
        rw [howner] at this
        cases this
        obtain ⟨ci', hci'⟩ := hpresent _ owner hold n hmem
        rw [hci'] at hnone; cases hnone
    rcases horigins _ owner (toMap' howner) with hold | ⟨j, -, ⟨A⟩⟩
    · rw [toEnv hold] at hownerNew; cases hownerNew
    · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hunsafe,
        A.isUnsafe] using hcvis

/-- Installing the headers and constructors of an inductive declaration, with its case
eliminators and projections registered, extends the invariant by a descriptor at stage
`.constructors`. -/
theorem addCtorStage {decl : VInductDecl}
    (H : InstalledBlocks safety env venv st)
    (hpresent : VerifyInductive.ListedConstructorsPresent env)
    (hwf : env.constants.WF) (hchk' : CheckingEnv safety env' venv')
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci)
    (hle : venv ≤ venv')
    (horigins : InductInfosFromDecl env.constants env'.constants decl)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, env'.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none)
    (hnodup : (decl.types.map (·.name)).Nodup)
    (howners : VerifyInductive.ConstructorOwnersPresent env')
    (recs : List RecursorVal)
    (hrecs : ∀ {n r}, env'.find? n = some (.recInfo r) → env.find? n = none → r ∈ recs)
    (hrecFind : ∀ r ∈ recs, env'.find? r.name = some (.recInfo r) ∧ env.find? r.name = none)
    (hrecMajor : ∀ r ∈ recs, ∃ info, env'.find? r.getMajorInduct = some (.inductInfo info))
    (hrecAlign : ∀ r ∈ recs, safety ≤ (ConstantInfo.recInfo r).safety →
      RecursorAlignmentCore venv' r ∧ KLikeRecursor env'.constants venv' r)
    (es : List (Name × InductiveSignature.CaseSchema))
    (hreg : DeclRegistered venv' decl es)
    (hproj : ∀ {S info}, venv'.projections S info → venv.projections S info ∨
      ⟨S, info⟩ ∈ decl.projectionEntries)
    (htels : CtorTelescopes safety env' venv') :
    InstalledBlocks safety env' venv' .headers := by
  have hwf' : env'.constants.WF := hchk'.map_wf
  refine H.addBlock .constructors (by decide) (InstallStage.headers_le _)
    (InstallStage.headers_le _) hpresent hwf hchk' hpres hle horigins hcover hnodup howners recs
    hrecs hrecFind hrecMajor es (fun _ => hreg)
    hrecAlign (fun _ h => absurd h (by decide)) ?_ (fun hf _ hvis => htels hf hvis)
  intro S info hp
  rcases hproj hp with hold | hentry
  · exact .inl hold
  · right
    refine ⟨?_, hentry⟩
    rw [VInductDecl.projectionEntries, List.mem_filterMap] at hentry
    obtain ⟨T, hT, -⟩ := hentry
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
    obtain ⟨ci, hci, hvis⟩ := hchk'.find?_iff.mpr ⟨_, hreg.family i hi⟩
    obtain ⟨v, hv, hnone⟩ := hcover _ hT
    rw [hv] at hci
    cases hci
    have hvMap : env'.constants.find? decl.types[i].name = some (.inductInfo v) := by
      rwa [Lean.Kernel.Environment.find?, hwf'.find?'_eq_find?] at hv
    rcases horigins _ v hvMap with hold | ⟨j, -, ⟨A⟩⟩
    · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
    · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, A.isUnsafe]
        using hvis

/-- Adding constants that are neither inductive headers, constructors nor recursors, and
growing the abstract environment without registering projections, keeps every descriptor. -/
theorem addNonInductive (H : InstalledBlocks safety env venv .complete)
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci)
    (hmap : ∀ {n ci}, env.constants.find? n = some ci → env'.constants.find? n = some ci)
    (hle : venv ≤ venv')
    (hnew : ∀ {n ci}, env'.find? n = some ci → env.find? n = none →
      (∀ v, ci ≠ .inductInfo v) ∧ (∀ v, ci ≠ .ctorInfo v) ∧ (∀ v, ci ≠ .recInfo v))
    (hproj : ∀ {S info}, venv'.projections S info → venv.projections S info) :
    InstalledBlocks safety env' venv' .complete := by
  have hpresent := H.listedConstructorsPresent (by decide)
  refine H.extend hpres hmap ?_ hle (InstallStage.le_refl _) ?_ ?_ ?_ ?_
  · intro fn fi n hfi hn hnone
    obtain ⟨ci, hci⟩ := hpresent fn fi hfi n hn
    rw [hci] at hnone; cases hnone
  · intro n v hf hnone; exact absurd rfl ((hnew hf hnone).1 v)
  · intro n v hf hnone; exact absurd rfl ((hnew hf hnone).2.1 v)
  · intro n v hf hnone; exact absurd rfl ((hnew hf hnone).2.2 v)
  · intro S info hp; exact .inl (hproj hp)

/-- The invariant depends on the kernel environment only through its lookups. -/
theorem mapEnvironmentEq (H : InstalledBlocks safety env venv st)
    (heq : ∀ n, env.find? n = env'.find? n)
    (hmapEq : ∀ n, env.constants.find? n = env'.constants.find? n) :
    InstalledBlocks safety env' venv st := by
  refine H.extend (fun h => (heq _).symm.trans h) (fun h => (hmapEq _).symm.trans h) ?_
    VEnv.LE.rfl (InstallStage.le_refl _) ?_ ?_ ?_ ?_
  · intro fn fi n _ _ hnone; rw [← heq]; exact hnone
  · intro n v hf hnone; rw [heq, hf] at hnone; cases hnone
  · intro n v hf hnone; rw [heq, hf] at hnone; cases hnone
  · intro n v hf hnone; rw [heq, hf] at hnone; cases hnone
  · intro S info hp; exact .inl hp

open private Lean.Kernel.Environment.add from Lean.Environment in
/-- Adding one fresh constant that is neither an inductive header, a constructor nor a
recursor. -/
theorem addFresh (H : InstalledBlocks safety env venv .complete) (hwf : env.constants.WF)
    {ci : ConstantInfo} (hn : env.find? ci.name = none)
    (hnind : ∀ v, ci ≠ .inductInfo v) (hnctor : ∀ v, ci ≠ .ctorInfo v)
    (hnrec : ∀ v, ci ≠ .recInfo v)
    (hle : venv ≤ venv') (hproj : ∀ {S info}, venv'.projections S info → venv.projections S info) :
    InstalledBlocks safety (env.add ci) venv' .complete := by
  have hnMap : env.constants.find? ci.name = none := by
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
  refine H.addNonInductive (fun h => VerifyInductive.findAddFresh_of_find hwf ci hn h) ?_ hle
    ?_ hproj
  · intro n c h
    change (env.constants.insert ci.name ci).find? n = some c
    rw [hwf.find?_insert]
    split
    · rename_i heq
      rw [← LawfulBEq.eq_of_beq heq, hnMap] at h
      cases h
    · exact h
  · intro n c h hnone
    rcases VerifyInductive.findAddFresh_cases hwf ci hn h with ⟨-, rfl⟩ | hold
    · exact ⟨hnind, hnctor, hnrec⟩
    · rw [hold] at hnone; cases hnone

open private Lean.Kernel.Environment.add from Lean.Environment in
/-- Adding a block of fresh definitions. -/
theorem addDefinitions (vs : List DefinitionVal) (H : InstalledBlocks safety env venv .complete)
    (hwf : env.constants.WF) (hle : venv ≤ venv')
    (hproj : ∀ {S info}, venv'.projections S info → venv.projections S info)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none) (hnodup : (vs.map (·.name)).Nodup) :
    InstalledBlocks safety (vs.foldl (fun e v => e.add (.defnInfo v)) env) venv' .complete := by
  induction vs generalizing env venv with
  | nil =>
    refine H.addNonInductive id id hle ?_ hproj
    intro n c h hnone
    simp only [List.foldl_nil] at h
    rw [h] at hnone; cases hnone
  | cons v vs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    have hvfresh := hfresh v (by simp)
    have hvfreshMap : env.constants.find? v.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hvfresh
    have hwf' : (env.add (.defnInfo v)).constants.WF := by
      change (env.constants.insert v.name (.defnInfo v)).WF
      exact hwf.insert v.name (.defnInfo v) hvfreshMap
    have H' := H.addFresh hwf (ci := .defnInfo v) hvfresh nofun nofun nofun hle hproj
    refine ih H' hwf' VEnv.LE.rfl id ?_ hnodup.2
    intro w hw
    have hne : v.name ≠ w.name := fun heq =>
      hnodup.1 (List.mem_map.mpr ⟨w, hw, heq.symm⟩)
    cases h : (env.add (.defnInfo v)).find? w.name with
    | none => rfl
    | some c =>
      rcases VerifyInductive.findAddFresh_cases hwf (.defnInfo v) hvfresh h with
        ⟨heq, -⟩ | hold
      · exact absurd heq.symm hne
      · rw [hfresh w (by simp [hw])] at hold; cases hold

open private Lean.Kernel.Environment.add from Lean.Environment in
/-- Adding one fresh constant that is neither a constructor nor a recursor, while every
name a header lists stays a constructor of that header if present.  A new header is its own
descriptor at stage `.headers`: the constructors it lists are absent. -/
theorem addFreshListed (H : InstalledBlocks safety env venv st) (hwf : env.constants.WF)
    {ci : ConstantInfo} (hn : env.find? ci.name = none)
    (hnctor : ∀ v, ci ≠ .ctorInfo v) (hnrec : ∀ v, ci ≠ .recInfo v)
    (howners : VerifyInductive.ConstructorOwnersPresent env)
    (hlisted : VerifyInductive.ListedConstructorsCoherent (env.add ci))
    (hle : venv ≤ venv')
    (hproj : ∀ {S info}, venv'.projections S info → venv.projections S info) :
    InstalledBlocks safety (env.add ci) venv' .headers := by
  have hnMap : env.constants.find? ci.name = none := by
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
  have hwf' : (env.add ci).constants.WF := hwf.insert ci.name ci hnMap
  have hpres : ∀ {n c}, env.find? n = some c → (env.add ci).find? n = some c :=
    fun h => VerifyInductive.findAddFresh_of_find hwf ci hn h
  have hself : (env.add ci).find? ci.name = some ci := by
    change (env.constants.insert ci.name ci).find?' ci.name = some ci
    rw [(hwf.insert ci.name ci hnMap).find?'_eq_find?, hwf.find?_insert]
    simp
  -- a name listed by a present header is not the new constant
  have hnotListed : ∀ {fn fi n}, (env.add ci).find? fn = some (.inductInfo fi) →
      n ∈ fi.ctors → n ≠ ci.name := by
    intro fn fi n hfi hmem heq
    subst heq
    obtain ⟨info, hinfo, -⟩ := hlisted fn fi hfi _ hmem ci hself
    exact hnctor info hinfo
  refine H.extend hpres ?_ ?_ hle (InstallStage.headers_le _) ?_ ?_ ?_ ?_
  · intro n c h
    change (env.constants.insert ci.name ci).find? n = some c
    rw [hwf.find?_insert]
    split
    · rename_i heq
      rw [← LawfulBEq.eq_of_beq heq, hnMap] at h
      cases h
    · exact h
  · intro fn fi n hfi hmem hnone
    cases h : (env.add ci).find? n with
    | none => rfl
    | some c =>
      rcases VerifyInductive.findAddFresh_cases hwf ci hn h with ⟨heq, -⟩ | hold
      · exact absurd heq (hnotListed (hpres hfi) hmem)
      · rw [hold] at hnone; cases hnone
  · intro n v hf hnone
    rcases VerifyInductive.findAddFresh_cases hwf ci hn hf with ⟨rfl, hci⟩ | hold
    · subst hci
      have hvname : (ConstantInfo.inductInfo v).name = v.name := rfl
      let T : VInductiveType := {
        name := v.name
        uvars := v.levelParams.length
        type := VExpr.sort .zero
        numIndices := v.numIndices
        resultLevel := VLevel.zero
        ctors := [] }
      let D : VInductDecl := {
        uvars := v.levelParams.length
        nparams := v.numParams
        types := [T]
        isUnsafe := v.isUnsafe }
      refine ⟨hvname, ⟨.headers, v.numParams, v.isUnsafe, [⟨v, [], T⟩], [], [], D⟩,
        InstallStage.le_refl _, ⟨?_, fun _ h => absurd rfl h, by simp⟩, ⟨v, [], T⟩, by simp, rfl⟩
      exact {
        header := by
          intro F hF
          simp only [List.mem_singleton] at hF
          subst hF
          exact hself
        all := fun h => absurd rfl h
        nodup := fun h => absurd rfl h
        numParams := by intro F hF; simp only [List.mem_singleton] at hF; subst hF; rfl
        isUnsafe := by intro F hF; simp only [List.mem_singleton] at hF; subst hF; rfl
        pending := by
          intro _ F hF m hm
          simp only [List.mem_singleton] at hF
          subst hF
          cases h : (env.add (.inductInfo v)).find? m with
          | none => rfl
          | some c =>
            obtain ⟨info, rfl, hinduct, -⟩ := hlisted _ v hself m hm c h
            rcases VerifyInductive.findAddFresh_cases hwf _ hn h with ⟨-, hc⟩ | hold
            · cases hc
            · obtain ⟨owner, howner, -⟩ := howners m info hold
              rw [hinduct] at howner
              rw [howner] at hn
              cases hn
        ctorNames := fun h => absurd rfl h
        ctor := fun h => absurd rfl h
        recursor := by simp
        recursorMajor := by simp }
    · rw [hold] at hnone; cases hnone
  · intro n v hf hnone
    rcases VerifyInductive.findAddFresh_cases hwf ci hn hf with ⟨-, rfl⟩ | hold
    · exact absurd rfl (hnctor v)
    · rw [hold] at hnone; cases hnone
  · intro n v hf hnone
    rcases VerifyInductive.findAddFresh_cases hwf ci hn hf with ⟨-, rfl⟩ | hold
    · exact absurd rfl (hnrec v)
    · rw [hold] at hnone; cases hnone
  · intro S info hp; exact .inl (hproj hp)

end InstalledBlocks

/-- The declaration of an inductive installation has the `isUnsafe` of its new headers. -/
theorem InductInfosFromDecl.declUnsafe {env env' : Environment} {decl : VInductDecl}
    (hwf : env.constants.WF) (hwf' : env'.constants.WF)
    (horigins : InductInfosFromDecl env.constants env'.constants decl)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, env'.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none)
    (hnonempty : decl.types ≠ [])
    (hnew : ∀ {n v}, env'.find? n = some (.inductInfo v) → env.find? n = none →
      v.isUnsafe = b) : decl.isUnsafe = b := by
  obtain ⟨T, hT⟩ := List.exists_mem_of_ne_nil _ hnonempty
  obtain ⟨v, hv, hnone⟩ := hcover T hT
  have hvMap : env'.constants.find? T.name = some (.inductInfo v) := by
    rwa [Lean.Kernel.Environment.find?, hwf'.find?'_eq_find?] at hv
  rcases horigins _ v hvMap with hold | ⟨i, -, ⟨A⟩⟩
  · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
  · rw [← A.isUnsafe]; exact hnew hv hnone

/-- Every family of an installed declaration is a new kernel header, read off the abstract
side: the family constant is registered, so some visible kernel constant carries its name; it
is new because the name was fresh in the source model, and it is a header because the only new
constants are headers and constructors, and a constructor name is not a family name. -/
theorem InductInfosFromDecl.cover {env env' : Environment} {venv venv' : VEnv}
    {decl : VInductDecl}
    (hchk : CheckingEnv safety env venv) (hchk' : CheckingEnv safety env' venv')
    (hpresent : VerifyInductive.ListedConstructorsPresent env)
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci)
    (horigins : InductInfosFromDecl env.constants env'.constants decl)
    (howners : VerifyInductive.ConstructorOwnersPresent env')
    (hfresh : ∀ T ∈ decl.types, venv.constants T.name = none)
    (hfamily : ∀ T ∈ decl.types, ∃ c, venv'.constants T.name = some c)
    (hnodup : decl.sourceNames.Nodup)
    (hkinds : ∀ {n ci}, env'.find? n = some ci → env.find? n = none →
      (∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v)) :
    ∀ T ∈ decl.types, ∃ v, env'.find? T.name = some (.inductInfo v) ∧
      env.find? T.name = none := by
  have hwf' := hchk'.map_wf
  intro T hT
  obtain ⟨c, hc⟩ := hfamily T hT
  obtain ⟨ci, hci, hvis⟩ := hchk'.find?_iff.mpr ⟨c, hc⟩
  have hnone : env.find? T.name = none := by
    cases h : env.find? T.name with
    | none => rfl
    | some c0 =>
      have := hpres h
      rw [hci] at this
      cases this
      obtain ⟨c', hc'⟩ := hchk.find?_iff.mp ⟨ci, h, hvis⟩
      rw [hfresh T hT] at hc'
      cases hc'
  have hind : ∃ v, ci = .inductInfo v := by
    rcases hkinds hci hnone with h | ⟨v, rfl⟩
    · exact h
    · exfalso
      obtain ⟨o, ho, hmem, -⟩ := howners _ v hci
      have hoNew : env.find? v.induct = none := by
        cases h : env.find? v.induct with
        | none => rfl
        | some c0 =>
          have := hpres h
          rw [ho] at this
          cases this
          obtain ⟨c1, hc1⟩ := hpresent _ o h _ hmem
          rw [hc1] at hnone; cases hnone
      have hoMap : env'.constants.find? v.induct = some (.inductInfo o) := by
        rwa [Lean.Kernel.Environment.find?, hwf'.find?'_eq_find?] at ho
      rcases horigins _ o hoMap with hold | ⟨j, -, ⟨A⟩⟩
      · rw [Lean.Kernel.Environment.find?, hchk.map_wf.find?'_eq_find?, hold] at hoNew
        cases hoNew
      · obtain ⟨k, hk, hkEq⟩ := List.mem_iff_getElem.mp hmem
        obtain ⟨C⟩ := A.constructor k (A.constructors ▸ hk)
        have hctorName : T.name ∈ decl.constructorConstants.map VConstVal.name := by
          rw [← hkEq, C.name]
          apply List.mem_map_of_mem
          simp only [VInductDecl.constructorConstants, List.mem_flatMap]
          exact ⟨_, List.getElem_mem A.familyIdx_lt, List.getElem_mem _⟩
        have htypeName : T.name ∈ decl.typeConstants.map VConstVal.name := by
          simp only [VInductDecl.typeConstants, List.map_map]
          exact List.mem_map_of_mem hT
        exact (List.nodup_append.mp hnodup).2.2 _ htypeName _ hctorName rfl
  obtain ⟨v, rfl⟩ := hind
  exact ⟨v, hci, hnone⟩

/-- Declaration alignment transfers to a constant map with the same headers and
constructors. -/
theorem InductInfosFromDecl.transfer {C₀ C C' : ConstMap} {decl : VInductDecl}
    (H : InductInfosFromDecl C₀ C decl)
    (hind : ∀ {n v}, C'.find? n = some (.inductInfo v) → C.find? n = some (.inductInfo v))
    (hfam : ∀ {n v}, C.find? n = some (.inductInfo v) → C'.find? n = some (.inductInfo v))
    (hctor : ∀ {n v}, C.find? n = some (.ctorInfo v) → C'.find? n = some (.ctorInfo v)) :
    InductInfosFromDecl C₀ C' decl := by
  intro familyName familyInfo hfind
  rcases H familyName familyInfo (hind hfind) with hold | ⟨i, hname, ⟨A⟩⟩
  · exact .inl hold
  · refine .inr ⟨i, hname, ⟨{ A with
      lookup := hfam A.lookup
      constructor := fun k hk => ?_ }⟩⟩
    obtain ⟨Ck⟩ := A.constructor k hk
    exact ⟨{ Ck with lookup := hctor Ck.lookup }⟩

/-! ## Installed families -/

/-- A visible kernel family is a family of a complete installed declaration: the
declaration, the family's position in it, the abstract installation, and the agreement of
the kernel header with the abstract family. -/
structure InductFamilyInstalledAt (venv : VEnv) (familyInfo : InductiveVal) where
  decl : VInductDecl
  familyIdx : Nat
  familyIdx_lt : familyIdx < decl.types.length
  installed : VEnv.InstalledBelow venv decl
  name : familyInfo.name = decl.types[familyIdx].name
  numParams : familyInfo.numParams = decl.nparams
  levelParams : familyInfo.levelParams.length = decl.uvars
  numIndices : familyInfo.numIndices = decl.types[familyIdx].numIndices
  constructors : familyInfo.ctors.length = decl.types[familyIdx].ctors.length
  constructorName : ∀ i (hi : i < familyInfo.ctors.length),
    familyInfo.ctors[i] = (decl.types[familyIdx].ctors[i]'(constructors ▸ hi)).name
  isUnsafe : familyInfo.isUnsafe = decl.isUnsafe

/-- Every visible kernel family of an environment whose blocks are complete is a family of
an installed declaration. -/
theorem InstalledBlocks.familyInstalled (H : InstalledBlocks safety env venv .complete)
    (hfind : env.find? familyName = some (.inductInfo familyInfo))
    (hvisible : safety ≤ (ConstantInfo.inductInfo familyInfo).safety) :
    familyName = familyInfo.name ∧ Nonempty (InductFamilyInstalledAt venv familyInfo) := by
  obtain ⟨hn, B, hst, hB, F, hF, rfl⟩ := H.header hfind
  refine ⟨hn, ?_⟩
  have hcomplete : B.stage = .complete := InstallStage.eq_complete hst
  have hne : B.stage ≠ .headers := by rw [hcomplete]; decide
  have C := hB.concrete
  have hvis : B.Visible safety := by
    rw [InstalledBlock.safety_inductInfo (C.isUnsafe F hF)] at hvisible
    exact hvisible
  have A := hB.abstract hvis hne
  have FA := A.family F hF
  obtain ⟨j, hj, hFj⟩ := List.mem_iff_getElem.mp hF
  have hj' : j < B.decl.types.length := by rw [A.types]; simpa using hj
  have hT : B.decl.types[j] = F.type := by
    simp only [A.types, List.getElem_map, hFj]
  have hlen : F.header.ctors.length = F.type.ctors.length := by
    rw [← C.ctorNames hne F hF, List.length_map]; exact FA.ctorsLength hne
  exact ⟨{
    decl := B.decl
    familyIdx := j
    familyIdx_lt := hj'
    installed := A.installed hcomplete
    name := by rw [hT]; exact FA.name
    numParams := (C.numParams F hF).trans A.nparams.symm
    levelParams := A.uvars F hF
    numIndices := by rw [hT]; exact FA.numIndices
    constructors := by rw [hT]; exact hlen
    constructorName := by
      intro i hi
      obtain ⟨hi', hname⟩ := C.ctor_getElem hne hF hi
      rw [hname]
      have DA := FA.ctor hne i hi' (FA.ctorsLength hne ▸ hi')
      rw [DA.name]
      simp only [hT]
    isUnsafe := (C.isUnsafe F hF).trans A.isUnsafe.symm }⟩

/-! ## The checking invariant -/

/-- Stored-equation heads survive an extension that preserves lookups and adds no
equation. -/
theorem EquationHeadsCoherent.mono {C C' : ConstMap} {venv venv' : VEnv}
    (H : EquationHeadsCoherent C venv)
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df) : EquationHeadsCoherent C' venv' := by
  intro df hdf
  obtain ⟨head, ls, ci, hhead, hci, hne, hq⟩ := H df (hdefeq df hdf)
  exact ⟨head, ls, ci, hhead, hpres hci, hne, hq⟩

/-- Everything the verified type checker needs of its environment, which may be one an
inductive declaration builds while it is checked: the local invariants (`ValidCore`), the
installed blocks of every inductive constant (`InstalledBlocks`, at any stage, so that a
block may still await its constructors), the heads of the stored equations, and the quotient
facts.  Every lookup fact the checker reads is a projection of these. -/
structure CheckingEnv.Valid (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv) : Prop extends
    CheckingEnv.ValidCore safety env venv where
  blocks : InstalledBlocks safety env venv .headers
  /-- Every stored equation is headed by a non-inductive constant of the environment, which
  keeps every inductive type constant rigid. -/
  equationHeads : EquationHeadsCoherent env.constants venv
  /-- Once quotients are initialized, the quotient constants and the `Quot.lift` equation are
  present. This is what quotient reduction reads. -/
  quot : env.quotInit = true → QuotEnvCoherent env.constants venv

namespace CheckingEnv.Valid
variable {safety : DefinitionSafety} {env : Environment} {venv : VEnv}

/-- Every present constructor is listed by its present owner, with its `isUnsafe`. -/
theorem constructorOwners (H : Valid safety env venv) :
    VerifyInductive.ConstructorOwnersPresent env := H.blocks.constructorOwnersPresent

/-- Every constructor name a present header lists is, if present, a constructor of that
header. -/
theorem listedConstructors (H : Valid safety env venv) :
    VerifyInductive.ListedConstructorsCoherent env := H.blocks.listedConstructorsCoherent

/-- Every visible singleton family whose constructor is present aligns with the abstract
projection registry. -/
theorem projectionRegistry (H : Valid safety env venv) :
    ProjectionRegistryCoherent safety env.constants venv :=
  H.blocks.projectionRegistryCoherent H.tr.map_wf

/-- A structure with an abstract registry entry is a visible header listing exactly the
registered constructor. -/
theorem projectionHeader (H : Valid safety env venv) (hproj : venv.projections S info) :
    ∃ v : InductiveVal, env.find? S = some (.inductInfo v) ∧ v.ctors = [info.ctorName] ∧
      safety ≤ (ConstantInfo.inductInfo v).safety ∧
      ∃ c : ConstructorVal, env.find? info.ctorName = some (.ctorInfo c) ∧ c.induct = S :=
  H.blocks.projectionHeader hproj

/-- Every visible recursor is aligned with the stored iota equations. -/
theorem recursors (H : Valid safety env venv) :
    RecursorEnvCoherent safety env.constants venv :=
  H.blocks.recursorEnvCoherent H.tr.map_wf H.equationHeads

/-- Every visible constructor carries its telescope certificate. -/
theorem ctorTelescopes (H : Valid safety env venv) : CtorTelescopes safety env venv :=
  H.blocks.ctorTelescopes

end CheckingEnv.Valid

theorem TrEnv.toCheckingValid (H : TrEnv safety env venv)
    (hprims : venv.HasPrimitives)
    (hsafe : ∀ {n ci}, env.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hblocks : InstalledBlocks safety env venv st) :
    CheckingEnv.Valid safety env venv :=
  ⟨⟨H.toChecking, hprims, hsafe⟩, hblocks.weaken (InstallStage.headers_le _),
    H.recursorEnvCoherent.heads, H.quotEnvCoherent⟩

/-- Promote the local invariants to the full checking invariant. -/
theorem CheckingEnv.ValidCore.toValid
    (H : CheckingEnv.ValidCore safety env venv)
    (hblocks : InstalledBlocks safety env venv st)
    (hheads : EquationHeadsCoherent env.constants venv)
    (hquot : env.quotInit = true → QuotEnvCoherent env.constants venv) :
    CheckingEnv.Valid safety env venv :=
  { H with
    blocks := hblocks.weaken (InstallStage.headers_le _)
    equationHeads := hheads
    quot := hquot }

open private Lean.Kernel.Environment.add from Lean.Environment in
/-- Extend a valid environment by a fresh, typed, non-delta, nonprimitive constant that is
neither a constructor nor a recursor (an inductive header is its own descriptor awaiting its
constructors), given the listed-constructor coherence of the extended environment. -/
theorem CheckingEnv.Valid.add (H : CheckingEnv.Valid safety env venv)
    (hn : env.find? ci.name = none)
    (hnprim : ¬ Kernel.Environment.primitives.contains ci.name)
    (htr : TrConstant safety venv ci ci')
    (hci : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv')
    (hdelta : ci.deltaValue? = none)
    (hnctor : ∀ info, ci ≠ .ctorInfo info) (hnrec : ∀ rec, ci ≠ .recInfo rec)
    (hlisted : VerifyInductive.ListedConstructorsCoherent (env.add ci)) :
    CheckingEnv.Valid safety (env.add ci) venv' := by
  have hcore := H.toValidCore.add hn hnprim htr hci hadd hdelta
  have hfresh : env.constants.find? ci.name = none := by
    rw [Lean.Kernel.Environment.find?, H.tr.map_wf.find?'_eq_find?] at hn
    exact hn
  have hle : venv ≤ venv' := VEnv.addConst_le hadd
  have hpres : ∀ {n c}, env.constants.find? n = some c → (env.add ci).constants.find? n = some c := by
    intro n c h
    show (env.constants.insert ci.name ci).find? n = some c
    rw [H.tr.map_wf.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; subst hb; rw [hfresh] at h; cases h
    · exact h
  have hheads : EquationHeadsCoherent (env.add ci).constants venv' :=
    H.equationHeads.mono hpres fun df hdf => by rwa [VEnv.addConst_defeqs hadd] at hdf
  refine hcore.toValid (H.blocks.addFreshListed H.tr.map_wf hn hnctor hnrec
    H.constructorOwners hlisted hle fun hp => by rwa [VEnv.addConst_projections hadd] at hp)
    hheads fun hq => (H.quot hq).extend hpres hle hheads

/-- Adding well-formed case eliminators to the abstract environment keeps the
checking invariant; the kernel environment is unchanged. -/
theorem CheckingEnv.Valid.addEliminators
    (H : CheckingEnv.Valid safety env venv)
    (hwf : (venv.addEliminators es).WF) :
    CheckingEnv.Valid safety env (venv.addEliminators es) := by
  have hheads : EquationHeadsCoherent env.constants (venv.addEliminators es) :=
    H.equationHeads.mono id fun df hdf => by simpa using hdf
  refine (H.toValidCore.addEliminators hwf).toValid (st := .headers) ?_ hheads
    fun hq => (H.quot hq).extend id VEnv.addEliminators_le hheads
  refine H.blocks.extend id id (fun _ _ h => h) VEnv.addEliminators_le (InstallStage.le_refl _)
    ?_ ?_ ?_ ?_
  · intro n v hf hnone; rw [hf] at hnone; cases hnone
  · intro n v hf hnone; rw [hf] at hnone; cases hnone
  · intro n v hf hnone; rw [hf] at hnone; cases hnone
  · intro S info hp; exact .inl (by simpa using hp)

end Lean4Lean
