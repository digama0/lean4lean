import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructors

/-! # The constructor shape of a container constructor

`NestedRun.containerConstructorShape`: a constructor `c` of the container family of a
specialization has, in the source constructor stage, the constructor shape at the number of
specialization arguments plus the field count of the generated constructor it specializes.
With `NestedRun.loweredConstructorShape` (moved here from `RuleConstructors.lean`, which
imports this file). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Telescope arity under substitution, level instantiation and expansion -/

/-- The Π-body of a term is headed by a constant. -/
def ConstTail (e : VExpr) : Prop := ∃ c ls, e.piBody.getAppFn = .const c ls

private theorem getAppFn_subst_const {σ : VExpr.Subst} :
    ∀ {e : VExpr} {c : Name} {ls : List VLevel}, e.getAppFn = .const c ls →
      (e.subst σ).getAppFn = .const c ls
  | .const _ _, _, _, h => by simpa [VExpr.getAppFn] using h
  | .app f _, _, _, h => by
    simp only [VExpr.getAppFn] at h
    simp only [VExpr.subst, VExpr.getAppFn]
    exact getAppFn_subst_const h
  | .bvar _, _, _, h | .sort _, _, _, h | .lam .., _, _, h | .forallE .., _, _, h
  | .proj .., _, _, h => by simp [VExpr.getAppFn] at h

theorem ConstTail.subst : ∀ {e : VExpr} (σ : VExpr.Subst), ConstTail e →
    (e.subst σ).piArity = e.piArity ∧ ConstTail (e.subst σ)
  | .forallE d b, σ, h => by
    obtain ⟨ih1, ih2⟩ := ConstTail.subst (e := b) σ.lift h
    exact ⟨by simp [VExpr.subst, VExpr.piArity, ih1], by simpa [VExpr.subst, ConstTail,
      VExpr.piBody] using ih2⟩
  | .const c ls, σ, _ => ⟨rfl, c, ls, rfl⟩
  | .app f a, σ, h => by
    obtain ⟨c, ls, h⟩ := h
    have h' := getAppFn_subst_const (σ := σ) (e := f) (by simpa [VExpr.piBody,
      VExpr.getAppFn] using h)
    exact ⟨rfl, c, ls, by simpa [VExpr.subst, VExpr.piBody, VExpr.getAppFn] using h'⟩
  | .bvar _, _, h | .sort _, _, h | .lam .., _, h | .proj .., _, h => by
    obtain ⟨c, ls, h⟩ := h
    simp [VExpr.piBody, VExpr.getAppFn] at h

private theorem getAppFn_instL_const {us : List VLevel} :
    ∀ {e : VExpr} {c : Name} {ls : List VLevel}, e.getAppFn = .const c ls →
      (e.instL us).getAppFn = .const c (ls.map (VLevel.inst us))
  | .const _ _, _, _, h => by
    simp only [VExpr.getAppFn, VExpr.const.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | .app f _, _, _, h => by
    simp only [VExpr.getAppFn] at h
    simp only [VExpr.instL, VExpr.getAppFn]
    exact getAppFn_instL_const h
  | .bvar _, _, _, h | .sort _, _, _, h | .lam .., _, _, h | .forallE .., _, _, h
  | .proj .., _, _, h => by simp [VExpr.getAppFn] at h

theorem ConstTail.instL : ∀ {e : VExpr} (us : List VLevel), ConstTail e →
    (e.instL us).piArity = e.piArity ∧ ConstTail (e.instL us)
  | .forallE d b, us, h => by
    obtain ⟨ih1, ih2⟩ := ConstTail.instL (e := b) us h
    exact ⟨by simp [VExpr.instL, VExpr.piArity, ih1], by simpa [VExpr.instL, ConstTail,
      VExpr.piBody] using ih2⟩
  | .const c ls, us, _ => ⟨rfl, c, _, rfl⟩
  | .app f a, us, h => by
    obtain ⟨c, ls, h⟩ := h
    have h' := getAppFn_instL_const (us := us) (e := f) (by simpa [VExpr.piBody,
      VExpr.getAppFn] using h)
    exact ⟨rfl, c, _, by simpa [VExpr.instL, VExpr.piBody, VExpr.getAppFn] using h'⟩
  | .bvar _, _, h | .sort _, _, h | .lam .., _, h | .proj .., _, h => by
    obtain ⟨c, ls, h⟩ := h
    simp [VExpr.piBody, VExpr.getAppFn] at h

private theorem LEquiv.getAppFn_const {U : Nat} {e e' : VExpr} (H : VExpr.LEquiv U e e') :
    (∃ c ls, e.getAppFn = .const c ls) ↔ (∃ c ls, e'.getAppFn = .const c ls) := by
  induction H with
  | refl => rfl
  | const => simp [VExpr.getAppFn]
  | app _ _ ih _ => simpa [VExpr.getAppFn] using ih
  | sort | proj | lam | forallE => simp [VExpr.getAppFn]

theorem LEquiv.constTail {U : Nat} {e e' : VExpr} (H : VExpr.LEquiv U e e') :
    e.piArity = e'.piArity ∧ (ConstTail e ↔ ConstTail e') := by
  induction H with
  | refl => exact ⟨rfl, Iff.rfl⟩
  | forallE _ _ _ ih => exact ⟨by simp [VExpr.piArity, ih.1], by simpa [ConstTail,
      VExpr.piBody] using ih.2⟩
  | @app f f' a a' hf _ _ _ =>
    exact ⟨rfl, by simpa [ConstTail, VExpr.piBody, VExpr.getAppFn] using
      LEquiv.getAppFn_const hf⟩
  | const => exact ⟨rfl, by simp [ConstTail, VExpr.piBody, VExpr.getAppFn]⟩
  | sort | proj | lam => exact ⟨rfl, by simp [ConstTail, VExpr.piBody, VExpr.getAppFn]⟩

theorem ConstTail.instantiateForallPrefix : ∀ {T : VExpr} (args : List VExpr), ConstTail T →
    args.length ≤ T.piArity →
    (VExpr.instantiateForallPrefix T args).piArity = T.piArity - args.length ∧
      ConstTail (VExpr.instantiateForallPrefix T args)
  | T, [], h, _ => by simp [VExpr.instantiateForallPrefix, h]
  | .forallE d b, a :: as, h, hlen => by
    have hb : ConstTail b := by simpa [ConstTail, VExpr.piBody] using h
    obtain ⟨h1, h2⟩ := hb.subst (VExpr.Subst.one a)
    rw [← VExpr.inst_eq] at h1 h2
    have hlen' : as.length ≤ (b.inst a).piArity := by
      rw [h1]; simp [VExpr.piArity] at hlen; omega
    obtain ⟨ih1, ih2⟩ := ConstTail.instantiateForallPrefix as h2 hlen'
    refine ⟨?_, ih2⟩
    simp only [VExpr.instantiateForallPrefix, ih1, h1, VExpr.piArity, List.length_cons]
    omega
  | .bvar _, _ :: _, _, hlen | .sort _, _ :: _, _, hlen | .const .., _ :: _, _, hlen
  | .app .., _ :: _, _, hlen | .lam .., _ :: _, _, hlen | .proj .., _ :: _, _, hlen => by
    simp [VExpr.piArity] at hlen

private theorem piArity_eq_forallArity' : ∀ e : VExpr, e.piArity = e.forallArity
  | .forallE _ b => by simp [VExpr.piArity, VExpr.forallArity, piArity_eq_forallArity' b]
  | .bvar _ | .sort _ | .const .. | .app .. | .proj .. | .lam .. => rfl

/-- Nested expansion with application leaves keeps the Π-arity. -/
theorem NestedExprExpansion.piArity_eq {leaf : Nat → VExpr → VExpr → Prop}
    (hleaf : ∀ {depth input output}, leaf depth input output →
      input.piArity = 0 ∧ output.piArity = 0) {depth : Nat} {source target : VExpr}
    (H : VExpr.NestedExprExpansion leaf depth source target) :
    source.piArity = target.piArity := by
  induction H with
  | occurrence h => rw [(hleaf h).1, (hleaf h).2]
  | forallE _ _ _ ih => simp [VExpr.piArity, ih]
  | _ => rfl

theorem const_mkApps_piArity (c : Name) (ls : List VLevel) (args : List VExpr) :
    ((VExpr.const c ls).mkApps args).piArity = 0 := by
  rw [piArity_eq_forallArity']
  exact VExpr.forallArity_eq_zero_of_getAppFnArgs (VExpr.getAppFnArgs_mkApps_const _ _ _)

/-- The leaves of the abstract nested replacement are applications on both sides. -/
theorem NestedOccurrenceReplacementAbs.piArity {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {depth : Nat} {input output : VExpr}
    (H : VInductDecl.NestedOccurrenceReplacementAbs env source generated depth input output) :
    input.piArity = 0 ∧ output.piArity = 0 := by
  rcases H with ⟨relativeDepth, _, H⟩
  cases H with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hin hout =>
    rw [hin, hout]; exact ⟨const_mkApps_piArity _ _ _, const_mkApps_piArity _ _ _⟩

theorem piBody_of_piArity_zero : ∀ {e : VExpr}, e.piArity = 0 → e.piBody = e
  | .forallE _ _, h => by simp [VExpr.piArity] at h
  | .bvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .proj .., _ | .lam .., _ => rfl

/-- A term whose application head is a constant has a constant-headed Π-body and Π-arity zero. -/
theorem constTail_of_getAppFnArgs {e : VExpr} {n : Name} {ls : List VLevel}
    (h : e.getAppFnArgs.1 = .const n ls) : e.piArity = 0 ∧ ConstTail e := by
  have he : e = (VExpr.const n ls).mkApps e.getAppFnArgs.2 := by
    have := VExpr.mkApps_getAppFnArgs_eq e
    rw [show VExpr.getAppFnArgs.go e [] = e.getAppFnArgs from rfl, h] at this
    exact this.symm
  have h0 : e.piArity = 0 := by rw [he]; exact const_mkApps_piArity _ _ _
  refine ⟨h0, n, ls, ?_⟩
  rw [piBody_of_piArity_zero h0, he]; simp [VExpr.getAppFn]

/-- The lowered constructor of a generated constructor has the constructor shape at the lowered
parameter count plus the generated field count. -/
theorem NestedRun.loweredConstructorShape
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {venv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes venv sourceDecl lparams nparams isUnsafe
      safety outEnv L)
    (index : Fin E.lowered.signature.constructors.size) :
    ∃ ci, E.lowered.constructors.ctorVEnv.constants
        E.lowered.signature.constructors[index].name = some ci ∧
      ci.type.CtorShape (E.lowered.loweredDecl.nparams +
        E.lowered.signature.constructors[index].fields.length) := by
  let H := E.lowered.recursors
  let owner : Fin H.generationSignature.families.size :=
    E.lowered.signature.constructors[index].owner
  have hmem : index ∈ H.generationSignature.ownedConstructors owner := by
    unfold InductiveSignature.ownedConstructors
    exact List.mem_filter.mpr ⟨List.mem_finRange _, beq_self_eq_true _⟩
  obtain ⟨l, hl, hidx⟩ := List.mem_iff_getElem.mp hmem
  have hcov := H.rulesCoverage owner
  obtain ⟨hl', Htr⟩ := List.forall₂_getElem_exists hcov l hl
  replace Htr := hidx ▸ Htr
  have hru : H.modelRule index ((H.rvalAt owner).rules[l]) ∈ (H.modelRecursor owner).rules := by
    simp only [RecursorInstallation.modelRecursor]
    have hlz : l < (List.zipWith H.modelRule (H.generationSignature.ownedConstructors owner)
        (H.rvalAt owner).rules).length := by
      simp only [List.length_zipWith]; exact Nat.lt_min.mpr ⟨hl, hl'⟩
    have := List.getElem_mem hlz
    rw [List.getElem_zipWith] at this
    exact hidx ▸ this
  obtain ⟨ci, hci, hshape⟩ := H.rulesCtor owner _ hru
  refine ⟨ci, ?_, ?_⟩
  · have h : (H.modelRule index ((H.rvalAt owner).rules[l])).ctor =
        E.lowered.signature.constructors[index].name := Htr.ctor
    rw [← h]; exact hci
  · have h : (H.modelRule index ((H.rvalAt owner).rules[l])).nfields =
        E.lowered.signature.constructors[index].fields.length := Htr.nfields
    rw [← h]; exact hshape

/-- The constructor shape of a container constructor at the specialization
arguments plus the field count of the generated constructor it specializes.

The proof: the generated constructor is the container constructor instantiated at the
specialization arguments under the common parameters
(`SpecializationGenerates.constructorShapes`), the lowered constructor is its nested expansion
(`NestedTypeExpansion.constructors`, which keeps the forall arity), and the lowered constructor
has the lowered parameter count plus the generated field count
(`NestedRun.loweredConstructorShape`). -/
theorem NestedRun.containerConstructorShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    {envTypes : VEnv} {ctx : List VExpr} {generated : List VInductiveType}
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes ctx sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (index : Fin E.lowered.signature.constructors.size)
    (hge : sourceDecl.types.length ≤ E.lowered.signature.constructors[index].owner.val)
    (hidx : E.lowered.signature.constructors[index].owner.val - sourceDecl.types.length <
      auxiliaries.length)
    {c : VConstVal}
    (hc : c ∈ (auxiliaries[E.lowered.signature.constructors[index].owner.val -
      sourceDecl.types.length]'hidx).source.ctors)
    (hname : E.lowered.signature.constructors[index].name =
      (auxiliaries[E.lowered.signature.constructors[index].owner.val -
        sourceDecl.types.length]'hidx).constructorName c) :
    ∃ ci, E.sourceCore.envCtors.constants c.name = some ci ∧
      ci.type.CtorShape ((auxiliaries[E.lowered.signature.constructors[index].owner.val -
        sourceDecl.types.length]'hidx).arguments.length +
        E.lowered.signature.constructors[index].fields.length) := by
  -- the specialization and its generated family
  have hgo : E.lowered.signature.constructors[index].owner.val - sourceDecl.types.length <
      generated.length := (Lean4Lean.List.Forall₂.length_eq Haux) ▸ hidx
  have SG := List.forall₂_getElem Haux _ hidx hgo
  have hlo : E.lowered.signature.constructors[index].owner.val - sourceDecl.types.length <
      (E.lowered.loweredDecl.types.drop sourceDecl.types.length).length :=
    (Lean4Lean.List.Forall₂.length_eq Hexpansion) ▸ hgo
  have NTE := List.forall₂_getElem Hexpansion _ hgo hlo
  generalize (auxiliaries[E.lowered.signature.constructors[index].owner.val -
    sourceDecl.types.length]'hidx) = a at SG hc hname ⊢
  generalize (generated[E.lowered.signature.constructors[index].owner.val -
    sourceDecl.types.length]'hgo) = gen at SG NTE
  generalize hlt : (E.lowered.loweredDecl.types.drop sourceDecl.types.length)[
    E.lowered.signature.constructors[index].owner.val - sourceDecl.types.length]'hlo = lt
    at NTE
  have hltMem : lt ∈ E.lowered.loweredDecl.types :=
    hlt ▸ List.mem_of_mem_drop (List.getElem_mem hlo)
  -- the position of `c`
  obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨sp, hsp, HC⟩ := SG.constructorShapes
  have hj' : j < gen.ctors.length := (Lean4Lean.List.Forall₂.length_eq HC) ▸ hj
  obtain ⟨instT, hLE, htarget⟩ := List.forall₂_getElem HC j hj hj'
  obtain ⟨sp2, _, _, _, _, _, HA⟩ := SG.application
  have hgenName := (List.forall₂_getElem HA j hj hj').name
  have hj'' : j < lt.ctors.length := (Lean4Lean.List.Forall₂.length_eq NTE.constructors) ▸ hj'
  have NCE := List.forall₂_getElem NTE.constructors j hj' hj''
  rw [hcj] at hLE hgenName
  -- the lowered constructor and its shape
  obtain ⟨ci', hci', hshape'⟩ := E.loweredConstructorShape index
  have hlcMem : lt.ctors[j] ∈ E.lowered.loweredDecl.constructorConstants :=
    List.mem_flatMap.mpr ⟨lt, hltMem, List.getElem_mem hj''⟩
  have hlcGet := VEnv.addConstVals_get E.lowered.constructors.core.ctorsAdded hlcMem
  have hlcName : lt.ctors[j].name = E.lowered.signature.constructors[index].name := by
    rw [NCE.name, hgenName, hname, ContainerSpecialization.constructorName, SG.auxiliary]
  rw [hlcName, hci'] at hlcGet
  cases hlcGet
  have hlArity : lt.ctors[j].type.piArity =
      E.lowered.loweredDecl.nparams + E.lowered.signature.constructors[index].fields.length :=
    hshape'.1
  have hexp : (gen.ctors[j]).type.piArity = lt.ctors[j].type.piArity :=
    NestedExprExpansion.piArity_eq (fun h => NestedOccurrenceReplacementAbs.piArity h)
      NCE.type
  -- the container constructor's raw shape
  obtain ⟨base, hparams⟩ := SG.installed.sourceParameterWF
  have haSrc : a.source ∈ a.container.types := List.getElem_mem _
  obtain ⟨doms, result, hct, hnp, -, hhead⟩ := hparams.rawCtorShape a.source haSrc c hc
  obtain ⟨hr0, hrTail⟩ := constTail_of_getAppFnArgs hhead
  have hcTail : ConstTail c.type := by
    rw [hct]; simpa [ConstTail, VExpr.piBody_wrapForalls] using hrTail
  have hcArity : c.type.piArity = doms.length := by
    rw [hct, VExpr.piArity_wrapForalls, hr0]; rfl
  obtain ⟨hlA, hlT⟩ := hcTail.instL a.levels
  obtain ⟨hEA, hET⟩ := LEquiv.constTail hLE
  have hTtail : ConstTail instT := hET.mpr hlT
  have hargs : a.arguments.length = a.container.nparams := SG.argumentsLength
  have hle : a.arguments.length ≤ instT.piArity := by
    rw [hEA, hlA, hcArity, hargs]; exact hnp
  obtain ⟨hIA, -⟩ := hTtail.instantiateForallPrefix a.arguments hle
  have htA : (gen.ctors[j]).type.piArity =
      sp.length + (instT.piArity - a.arguments.length) := by
    rw [htarget, VExpr.piArity_wrapForalls, hIA]
  have hnpL : E.lowered.loweredDecl.nparams = sourceDecl.nparams := Hdata.nparams
  -- the constant in the source constructor stage
  have hconst : (ves.venv (if isUnsafe then .unsafe else .safe)).constants c.name =
      some c.toVConstant := by
    have h := SG.installed.constructorConstant a.family.val j a.family.isLt
      (by simpa [ContainerSpecialization.source] using hj)
    rw [← hcj]
    simp only [ContainerSpecialization.source, Fin.getElem_fin] at h ⊢
    exact h
  have hle' : (ves.venv (if isUnsafe then .unsafe else .safe)) ≤ E.sourceCore.envCtors :=
    (VEnv.addConstVals_le E.sourceCore.core.typesAdded).trans
      (VEnv.addConstVals_le E.sourceCore.core.ctorsAdded)
  refine ⟨c.toVConstant, hle'.constants hconst, ?_, ?_⟩
  · show c.type.piArity = _
    rw [hcArity]
    have : doms.length = instT.piArity := by rw [hEA, hlA, hcArity]
    omega
  · obtain ⟨n, ls, h⟩ := hcTail
    exact ⟨n, ls, h⟩


end VerifyInductive
end Lean4Lean
