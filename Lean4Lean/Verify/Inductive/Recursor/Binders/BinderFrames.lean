import Lean4Lean.Verify.Inductive.Recursor.Binders.MotiveTelescopes

/-! Binder frames of the recursor construction: the binder groups (parameters,
motives, minors, indices, major) that one generated recursor type is built from,
their order in the executable local context (`RecInfoOuterOrder`), the motive
shapes `MotiveTypes`, and the row counts of the motive and minor passes of
`mkRecInfos`. Part of the recursor phase (section 3.2 of the design notes). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

theorem MotiveTypes.empty (c : AddInductive.Context)
    (elimLevel : Level) :
    MotiveTypes c #[] #[] elimLevel where
  size_eq := rfl
  shape i hi := by simp at hi

/-- Row-wise inverse image of one declaration in the executable's flattened
minor array.  It records the mutual-family owner, the constructor-local
position, and the exact type used when that minor premise was introduced. -/
structure RecInfoBinderTypes.FlatMinorBinderType
    (H : RecInfoBinderTypes c recInfos)
    (D : FVarDeclAt c (recInfos.flatMap (·.minors)) i) where
  owner : Nat
  owner_lt : owner < recInfos.size
  localIndex : Nat
  local_lt : localIndex < recInfos[owner].minors.size
  declaration : FVarDeclAt c recInfos[owner].minors localIndex
  expression_eq : recInfos[owner].minors[localIndex]'local_lt =
    (recInfos.flatMap (·.minors))[i]'D.inBounds
  originType_eq : D.type = H.minorTypes[owner]![localIndex]!

/-- Every flattened minor declaration comes from an actual owner row.  The
proof follows the executable `Array.flatMap` membership, then uses local
declaration uniqueness to connect the row's binder type to the flattened
declaration. -/
theorem RecInfoBinderTypes.flatMinorBinderType
    (H : RecInfoBinderTypes c recInfos)
    (D : FVarDeclAt c (recInfos.flatMap (·.minors)) i) :
    Nonempty (H.FlatMinorBinderType D) := by
  have hmember : Expr.fvar D.fvar ∈ recInfos.flatMap (·.minors) := by
    rw [← D.expression]
    exact Array.getElem_mem D.inBounds
  rcases Array.mem_flatMap.mp hmember with ⟨info, hinfo, hminor⟩
  rcases Array.mem_iff_getElem.mp hinfo with ⟨owner, howner, hinfoEq⟩
  rcases Array.mem_iff_getElem.mp hminor with
    ⟨localIndex, hlocal, hlocalEq⟩
  subst info
  have hinfoBang : recInfos[owner]! = recInfos[owner] := by
    simp [howner]
  have Hrow : FVarArrayBinderTypes c recInfos[owner].minors
      H.minorTypes[owner]! := by
    simpa only [hinfoBang] using H.minors owner howner
  rcases Hrow.declaration localIndex hlocal with
    ⟨E, htype⟩
  have hexpression : recInfos[owner].minors[localIndex]'hlocal =
      (recInfos.flatMap (·.minors))[i]'D.inBounds :=
    hlocalEq.trans D.expression.symm
  exact ⟨{
    owner := owner
    owner_lt := howner
    localIndex := localIndex
    local_lt := hlocal
    declaration := E
    expression_eq := hexpression
    originType_eq := (D.type_eq_of_expression E hexpression.symm).trans htype }⟩

def RecInfoBindings.flatMinors
    (H : RecInfoBindings c recInfos) :
    FVarArrayIn c (recInfos.flatMap (·.minors)) where
  fvars := (List.ofFn fun i : Fin recInfos.size =>
    (H.minors i i.isLt).fvars).flatten
  expressions := by
    rw [← Array.toList_inj]
    simp only [Array.toList_flatMap, List.map_flatten]
    rw [← List.ofFn_getElem (xs := recInfos.toList)]
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      simpa [Array.getElem!_eq_getD, Array.getD, hn] using
        congrArg Array.toList (H.minors n hn).expressions
  members := by
    intro fv hfv
    simp only [List.mem_flatten, List.mem_ofFn] at hfv
    rcases hfv with ⟨fvs, ⟨i, rfl⟩, hfv⟩
    exact (H.minors i i.isLt).members fv hfv

def RecInfoBindings.flatIndices
    (H : RecInfoBindings c recInfos) :
    FVarArrayIn c (recInfos.flatMap (·.indices)) where
  fvars := (List.ofFn fun i : Fin recInfos.size =>
    (H.indices i i.isLt).fvars).flatten
  expressions := by
    rw [← Array.toList_inj]
    simp only [Array.toList_flatMap, List.map_flatten]
    rw [← List.ofFn_getElem (xs := recInfos.toList)]
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      simpa [Array.getElem!_eq_getD, Array.getD, hn] using
        congrArg Array.toList (H.indices n hn).expressions
  members := by
    intro fv hfv
    simp only [List.mem_flatten, List.mem_ofFn] at hfv
    rcases hfv with ⟨fvs, ⟨i, rfl⟩, hfv⟩
    exact (H.indices i i.isLt).members fv hfv

/-- All binder identities recorded for recursor generation, in the category
order used by the generated telescope. Keeping this global list distinct is
stronger than the per-owner fact needed by any one recursor.
The selection depends only on the executable arrays. -/
def RecInfoBindings.allFvars (params : Array Expr)
    (recInfos : Array AddInductive.RecInfo) : List FVarId :=
  ExprArrayFVarIds params ++
    (ExprArrayFVarIds (recInfos.map (·.motive)) ++
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
        (ExprArrayFVarIds (recInfos.flatMap (·.indices)) ++
          ExprArrayFVarIds (recInfos.map (·.major)))))

theorem RecInfoBindings.allFvars_eq
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params) :
    RecInfoBindings.allFvars stats.params recInfos =
      Hparams.fvars ++
        (H.motives.fvars ++
          (H.flatMinors.fvars ++ (H.flatIndices.fvars ++ H.majors.fvars))) := by
  unfold RecInfoBindings.allFvars
  rw [Hparams.exprArrayFVarIds, H.motives.exprArrayFVarIds,
    H.flatMinors.exprArrayFVarIds, H.flatIndices.exprArrayFVarIds,
    H.majors.exprArrayFVarIds]

def RecInfoBindings.NoAlias (params : Array Expr)
    (recInfos : Array AddInductive.RecInfo) : Prop :=
  (RecInfoBindings.allFvars params recInfos).Nodup

theorem RecInfoBindings.allFvars_members
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params) :
    ∀ fv ∈ RecInfoBindings.allFvars stats.params recInfos, fv ∈ c.lctx.fvars := by
  intro fv hfv
  rw [H.allFvars_eq Hparams] at hfv
  simp only [List.mem_append] at hfv
  rcases hfv with hp | hm | hmi | hi | hma
  · exact Hparams.members fv hp
  · exact H.motives.members fv hm
  · exact H.flatMinors.members fv hmi
  · exact H.flatIndices.members fv hi
  · exact H.majors.members fv hma

theorem RecInfoBindings.outerNodup
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos) :
    ((Hparams.fvars ++ H.motives.fvars) ++
      H.flatMinors.fvars).Nodup := by
  have hsub : ((Hparams.fvars ++ H.motives.fvars) ++
      H.flatMinors.fvars) <+ RecInfoBindings.allFvars stats.params recInfos := by
    rw [H.allFvars_eq Hparams]
    simp [List.append_assoc]
  exact hnoalias.sublist hsub

/-- The outer binders selected by the generated recursor telescope occur in
their category order inside the executable local context.  Local contexts
store newest declarations first, hence the reversal.  This fact
is separate from `NoAlias`: membership and distinctness alone
do not determine binder order when indices and majors are interleaved. -/
def RecInfoOuterOrder
    {stats : AddInductive.InductiveStats}
    (R : RecursorContextWF c recLparams)
    (Hparams : FVarArrayIn c stats.params)
    (Hbindings : RecInfoBindings c recInfos) : Prop :=
  (Hparams.fvars ++ Hbindings.motives.fvars ++
    Hbindings.flatMinors.fvars).reverse <+ R.mlctx.vlctx.fvars

def RecInfoBindings.major
    (H : RecInfoBindings c recInfos) (i : Nat) (hi : i < recInfos.size) :
    FVarArrayIn c #[recInfos[i]!.major] := by
  have hsize : H.majors.fvars.length = recInfos.size := by
    have h := congrArg Array.size H.majors.expressions
    simpa using h.symm
  let fv := H.majors.fvars[i]'(by simpa [hsize] using hi)
  refine {
    fvars := [fv]
    expressions := ?_
    members := ?_
  }
  · apply congrArg (fun e => #[e])
    have hget := congrArg (fun xs => xs[i]!) H.majors.expressions
    simpa [fv, Array.getElem!_eq_getD, Array.getD, hi, hsize] using hget
  · intro fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact H.majors.members fv (List.getElem_mem (by simpa [hsize] using hi))

/-- Motive telescope shapes are stable under verified local-context
extension because all selected index and major declarations keep their
declaration data. -/
theorem MotiveTypes.mono
    (H : MotiveTypes c recInfos motiveTypes elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (hle : BindingContextLE c c') :
    MotiveTypes c' recInfos motiveTypes elimLevel where
  size_eq := H.size_eq
  shape i hi := by
    let Hindices := Hbindings.indices i hi
    let Hmajor := Hbindings.major i hi
    calc
      motiveTypes[i]! =
          c.lctx.mkForall recInfos[i]!.indices
            (c.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel)) :=
        H.shape i hi
      _ = c'.lctx.mkForall recInfos[i]!.indices
            (c.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel)) :=
        (Hindices.mkForall_mono hle _).symm
      _ = c'.lctx.mkForall recInfos[i]!.indices
            (c'.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel)) := by
        rw [Hmajor.mkForall_mono hle]

/-- Append one newly constructed motive telescope while weakening every
earlier family shape into the final frame context. -/
theorem MotiveTypes.push
    (H : MotiveTypes c recInfos motiveTypes elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (hle : BindingContextLE c c')
    (info : AddInductive.RecInfo) (motiveType : Expr)
    (hnew : motiveType =
      c'.lctx.mkForall info.indices
        (c'.lctx.mkForall #[info.major] (.sort elimLevel))) :
    MotiveTypes c' (recInfos.push info)
      (motiveTypes.push motiveType) elimLevel where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    by_cases hold : i < recInfos.size
    · have hmotives : i < motiveTypes.size := by
        rw [H.size_eq]
        exact hold
      have hmotivesPush : (motiveTypes.push motiveType)[i]! =
          motiveTypes[i]! := by
        have hmotivesPushBounds : i < (motiveTypes.push motiveType).size := by
          simp only [Array.size_push]
          omega
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hmotivesPushBounds, dif_pos hmotives]
        exact Array.getElem_push_lt hmotives
      have hinfoPush : (recInfos.push info)[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hmotivesPush, hinfoPush]
      exact (H.mono Hbindings hle).shape i hold
    · have hieq : i = recInfos.size := by
        simp only [Array.size_push] at hi
        omega
      subst i
      have hmotivesPush :
          (motiveTypes.push motiveType)[recInfos.size]! = motiveType := by
        rw [show recInfos.size = motiveTypes.size from H.size_eq.symm]
        simp
      have hinfoPush : (recInfos.push info)[recInfos.size]! = info := by
        simp
      rw [hmotivesPush, hinfoPush]
      exact hnew

/-- The five executable binder groups used to build one executable recursor
type, all selected from the same local context. -/
structure RecursorBinderGroups (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat) where
  params : CDeclArray c.lctx stats.params
  motives : CDeclArray c.lctx (recInfos.map (·.motive))
  minors : CDeclArray c.lctx (recInfos.flatMap (·.minors))
  indices : CDeclArray c.lctx recInfos[ownerIdx]!.indices
  major : CDeclArray c.lctx #[recInfos[ownerIdx]!.major]

def RecursorBinderGroups.allFvars
    (H : RecursorBinderGroups c stats recInfos ownerIdx) : List FVarId :=
  H.params.fvars ++
    (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))

def RecursorBinderGroups.NoAlias
    (H : RecursorBinderGroups c stats recInfos ownerIdx) : Prop :=
  H.allFvars.Nodup

structure RecursorBinderGroups.NoAliasParts
    (H : RecursorBinderGroups c stats recInfos ownerIdx) : Prop where
  params : H.params.fvars.Nodup
  motives : H.motives.fvars.Nodup
  minors : H.minors.fvars.Nodup
  indices : H.indices.fvars.Nodup
  major : H.major.fvars.Nodup
  params_later : ∀ fv ∈ H.params.fvars,
    ∀ fv' ∈ H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)), fv ≠ fv'
  motives_later : ∀ fv ∈ H.motives.fvars,
    ∀ fv' ∈ H.minors.fvars ++
      (H.indices.fvars ++ H.major.fvars), fv ≠ fv'
  minors_later : ∀ fv ∈ H.minors.fvars,
    ∀ fv' ∈ H.indices.fvars ++ H.major.fvars, fv ≠ fv'
  indices_major : ∀ fv ∈ H.indices.fvars,
    ∀ fv' ∈ H.major.fvars, fv ≠ fv'

theorem RecursorBinderGroups.NoAlias.parts
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (h : H.NoAlias) : H.NoAliasParts := by
  unfold RecursorBinderGroups.NoAlias
    RecursorBinderGroups.allFvars at h
  rcases List.nodup_append.mp h with ⟨hp, hrest, hpLater⟩
  rcases List.nodup_append.mp hrest with ⟨hm, hrest, hmLater⟩
  rcases List.nodup_append.mp hrest with ⟨hmi, hrest, hmiLater⟩
  rcases List.nodup_append.mp hrest with ⟨hi, hma, hiMajor⟩
  exact ⟨hp, hm, hmi, hi, hma, hpLater, hmLater, hmiLater, hiMajor⟩

def RecInfoBindings.toRecursorBinderGroups
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (Hparams : FVarArrayIn c stats.params)
    (ownerIdx : Nat) (howner : ownerIdx < recInfos.size) :
    RecursorBinderGroups c stats recInfos ownerIdx where
  params := Hparams.toCDeclArray Hc
  motives := H.motives.toCDeclArray Hc
  minors := H.flatMinors.toCDeclArray Hc
  indices := (H.indices ownerIdx howner).toCDeclArray Hc
  major := (H.major ownerIdx howner).toCDeclArray Hc

theorem RecInfoBindings.selectionNoAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (ownerIdx : Nat) (howner : ownerIdx < recInfos.size) :
    (H.toRecursorBinderGroups Hc Hparams ownerIdx howner).NoAlias := by
  let rows := List.ofFn fun i : Fin recInfos.size =>
    (H.indices i i.isLt).fvars
  have hrowMem : (H.indices ownerIdx howner).fvars ∈ rows := by
    simp only [rows, List.mem_ofFn]
    exact ⟨⟨ownerIdx, howner⟩, rfl⟩
  have hindices : (H.indices ownerIdx howner).fvars <+
      H.flatIndices.fvars := by
    exact List.sublist_flatten_of_mem hrowMem
  have hmajor : (H.major ownerIdx howner).fvars <+ H.majors.fvars := by
    have himap : ownerIdx < (recInfos.map (·.major)).size := by
      simpa using howner
    let Hget := H.majors.get ownerIdx himap
    have heq : #[recInfos[ownerIdx]!.major] =
        #[(recInfos.map (·.major))[ownerIdx]] := by
      simp [howner]
    rw [FVarArrayIn.fvars_eq (H.major ownerIdx howner) Hget heq]
    exact FVarArrayIn.get_fvars_sublist _ _ _
  have hsub :
      Hparams.fvars ++
        (H.motives.fvars ++
          (H.flatMinors.fvars ++
            ((H.indices ownerIdx howner).fvars ++
              (H.major ownerIdx howner).fvars))) <+
      RecInfoBindings.allFvars stats.params recInfos :=
    H.allFvars_eq Hparams ▸
      ((List.Sublist.refl Hparams.fvars).append <|
        (List.Sublist.refl H.motives.fvars).append <|
          (List.Sublist.refl H.flatMinors.fvars).append <|
            hindices.append hmajor)
  apply hnoalias.sublist hsub

/-- The opened index telescope of every recursor frame has the
arity recorded by the checked inductive header. -/
def RecInfoArities (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size →
    recInfos[i]!.indices.size = stats.nindices[i]!

theorem RecInfoArities.empty (stats : AddInductive.InductiveStats) :
    RecInfoArities stats #[] := by
  intro i hi
  simp at hi

theorem RecInfoArities.push
    (H : RecInfoArities stats recInfos)
    (hnew : indices.size = stats.nindices[recInfos.size]!) :
    RecInfoArities stats (recInfos.push {
      motive, minors := #[], indices, major }) := by
  intro i hi
  by_cases hilast : i = recInfos.size
  · subst i
    simpa using hnew
  · have hiOld : i < recInfos.size := by
      have : i < recInfos.size + 1 := by simpa using hi
      omega
    have hget : (recInfos.push {
        motive, minors := #[], indices, major })[i]! = recInfos[i]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos hi, dif_pos hiOld]
      exact Array.getElem_push_lt hiOld
    rw [hget]
    exact H i hiOld

def RecInfoMinorsEmpty (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size → recInfos[i]!.minors.size = 0

theorem RecInfoMinorsEmpty.empty : RecInfoMinorsEmpty #[] := by
  intro i hi
  simp at hi

theorem RecInfoMinorsEmpty.push
    (H : RecInfoMinorsEmpty recInfos) :
    RecInfoMinorsEmpty (recInfos.push {
      motive, minors := #[], indices, major }) := by
  intro i hi
  by_cases hilast : i = recInfos.size
  · subst i
    simp
  · have hiOld : i < recInfos.size := by
      have : i < recInfos.size + 1 := by simpa using hi
      omega
    have hget : (recInfos.push {
        motive, minors := #[], indices, major })[i]! = recInfos[i]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos hi, dif_pos hiOld]
      exact Array.getElem_push_lt hiOld
    rw [hget]
    exact H i hiOld

/-- The executable rule-template row stays synchronized with the minor row.
The motive pass creates two empty rows; the minor pass appends one entry
to each in the same successful `withLocalDecl` continuation. -/
def RecInfoTemplateCounts (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size →
    recInfos[i]!.ruleTemplates.size = recInfos[i]!.minors.size

theorem RecInfoTemplateCounts.empty : RecInfoTemplateCounts #[] := by
  intro i hi
  simp at hi

theorem RecInfoTemplateCounts.pushEmpty
    (H : RecInfoTemplateCounts recInfos) :
    RecInfoTemplateCounts (recInfos.push {
      motive, minors := #[], indices, major }) := by
  intro i hi
  by_cases hilast : i = recInfos.size
  · subst i
    simp
  · have hiOld : i < recInfos.size := by
      have : i < recInfos.size + 1 := by simpa using hi
      omega
    have hget : (recInfos.push {
        motive, minors := #[], indices, major })[i]! = recInfos[i]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos hi, dif_pos hiOld]
      exact Array.getElem_push_lt hiOld
    rw [hget]
    exact H i hiOld

/-- After the motive pass there are no minors, so the two empty
template/minor rows satisfy `RuleTemplatesMatch` vacuously. -/
theorem RuleTemplatesMatch.ofEmpty
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hcounts : RecInfoTemplateCounts recInfos) :
    RuleTemplatesMatch stats recInfos Horigins where
  rows_size owner howner := by
    exact (Hcounts owner howner).trans (Horigins.minors owner howner).size_eq.symm
  entry owner howner localIndex hlocal := by
    have hsize := (Horigins.minors owner howner).size_eq
    rw [Hempty owner howner] at hsize
    omega
  fields_outer_fresh owner howner localIndex hlocal := by
    have hsize := (Horigins.minors owner howner).size_eq
    rw [Hempty owner howner] at hsize
    omega

theorem RuleTemplatesMatch.mono
    {Horigins : RecInfoBinderTypes c recInfos}
    (B : RuleTemplatesMatch stats recInfos Horigins)
    (hle : BindingContextLE c c') :
    RuleTemplatesMatch stats recInfos (Horigins.mono hle) where
  rows_size := B.rows_size
  entry owner howner localIndex hlocal := by
    simpa [RecInfoBinderTypes.mono] using
      B.entry owner howner localIndex hlocal
  fields_outer_fresh owner howner localIndex hlocal fv hfv := by
    simpa [RecInfoBinderTypes.mono] using
      B.fields_outer_fresh owner howner localIndex hlocal fv hfv

/-- If every recursor-info minor row is empty, the flattened minor
selection contains no identifiers either. -/
theorem RecInfoMinorsEmpty.flatMinors_fvars
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hbindings : RecInfoBindings c recInfos) :
    Hbindings.flatMinors.fvars = [] := by
  change (List.ofFn fun i : Fin recInfos.size =>
    (Hbindings.minors i i.isLt).fvars).flatten = []
  have hrows : (List.ofFn fun i : Fin recInfos.size =>
      (Hbindings.minors i i.isLt).fvars) =
      List.replicate recInfos.size [] := by
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      have hrow : (Hbindings.minors n hn).fvars = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [(Hbindings.minors n hn).length_fvars]
        exact Hempty n hn
      simpa using hrow
  rw [hrows]
  simp

theorem RecInfoArities.modifyMinors
    (H : RecInfoArities stats recInfos) (dIdx : Nat)
    (f : Array Expr → Array Expr) :
    RecInfoArities stats (recInfos.modify dIdx fun info =>
      { info with minors := f info.minors }) := by
  intro i hi
  have hiOld : i < recInfos.size := by simpa using hi
  by_cases hdi : dIdx = i
  · subst i
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hiOld]
    exact H dIdx hiOld
  · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
      hiOld hdi]
    exact H i hiOld

/-- Major-domain shapes ignore the minor array updated by the constructor
pass. -/
theorem MajorPremiseTypes.modifyMinors
    (H : MajorPremiseTypes stats recInfos majorTypes ok)
    (dIdx : Nat) (f : Array Expr → Array Expr) :
    MajorPremiseTypes stats
      (recInfos.modify dIdx fun info =>
        { info with minors := f info.minors }) majorTypes ok where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hiOld]
      exact H.shape dIdx hiOld
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
          hiOld hdi]
      exact H.shape i hiOld

/-- Motive declaration shapes likewise depend only on the indices
and major, not on the accumulating minor row. -/
theorem MotiveTypes.modifyMinors
    (H : MotiveTypes c recInfos motiveTypes elimLevel)
    (dIdx : Nat) (f : Array Expr → Array Expr) :
    MotiveTypes c
      (recInfos.modify dIdx fun info =>
        { info with minors := f info.minors }) motiveTypes elimLevel where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hiOld]
      exact H.shape dIdx hiOld
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
          hiOld hdi]
      exact H.shape i hiOld

def RecInfoBindings.empty (c : AddInductive.Context) :
    RecInfoBindings c #[] where
  motives := by simpa using FVarArrayIn.empty c
  majors := by simpa using FVarArrayIn.empty c
  indices i hi := by simp at hi
  minors i hi := by simp at hi

theorem RecInfoOuterOrder.empty
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hparams : FVarArrayIn c stats.params) :
    RecInfoOuterOrder R Hparams (RecInfoBindings.empty c) := by
  have hmotives : (RecInfoBindings.empty c).motives.fvars = [] :=
    FVarArrayIn.fvars_eq (RecInfoBindings.empty c).motives
      (FVarArrayIn.empty c) (by simp)
  have hminors : (RecInfoBindings.empty c).flatMinors.fvars = [] :=
    FVarArrayIn.fvars_eq (RecInfoBindings.empty c).flatMinors
      (FVarArrayIn.empty c) (by simp)
  have hcontext := congrArg VLCtx.fvars Hsuffix.context
  rw [VLCtx.fvars_append, Hsuffix.parameterDecls_fvars,
    Hparams.exprArrayFVarIds] at hcontext
  unfold RecInfoOuterOrder
  rw [hmotives, hminors]
  simp only [List.append_nil]
  rw [hcontext]
  exact (List.nil_sublist Hsuffix.ambientDecls.fvars).append
    (List.Sublist.refl Hparams.fvars.reverse)

/-- Adding one motive in the motive pass preserves the selected outer-binder order.
The declarations opened for its indices and major may be interleaved in the
executable context, but they are not part of the outer recursor
prefix. -/
theorem RecInfoOuterOrder.pushMotive
    {stats : AddInductive.InductiveStats}
    {Rold : RecursorContextWF old recLparams}
    {Rnew : RecursorContextWF new recLparams}
    {oldInfos newInfos : Array AddInductive.RecInfo}
    {oldParams : FVarArrayIn old stats.params}
    {newParams : FVarArrayIn new stats.params}
    {oldBindings : RecInfoBindings old oldInfos}
    {newBindings : RecInfoBindings new newInfos}
    {motive : FVarId} {interleaved : List FVarId}
    (Horder : RecInfoOuterOrder Rold oldParams oldBindings)
    (holdMinors : oldBindings.flatMinors.fvars = [])
    (hparams : newParams.fvars = oldParams.fvars)
    (hmotives : newBindings.motives.fvars =
      oldBindings.motives.fvars ++ [motive])
    (hnewMinors : newBindings.flatMinors.fvars = [])
    (hcontext : Rnew.mlctx.vlctx.fvars =
      motive :: interleaved ++ Rold.mlctx.vlctx.fvars) :
    RecInfoOuterOrder Rnew newParams newBindings := by
  unfold RecInfoOuterOrder at Horder ⊢
  rw [holdMinors] at Horder
  simp only [List.append_nil] at Horder
  have Horder' : oldBindings.motives.fvars.reverse ++
      oldParams.fvars.reverse <+ Rold.mlctx.vlctx.fvars := by
    simpa only [List.reverse_append] using Horder
  rw [hparams, hmotives, hnewMinors, hcontext]
  simp only [List.append_nil, List.reverse_append, List.reverse_singleton,
    List.singleton_append]
  exact ((List.nil_sublist interleaved).append Horder').cons_cons motive

/-- A newly installed minor becomes the newest selected outer binder when
its flattened row order appends it after the previous minors. -/
theorem RecInfoOuterOrder.addMinor
    {stats : AddInductive.InductiveStats}
    {Rold : RecursorContextWF old recLparams}
    {Rnew : RecursorContextWF new recLparams}
    {oldInfos newInfos : Array AddInductive.RecInfo}
    {oldParams : FVarArrayIn old stats.params}
    {newParams : FVarArrayIn new stats.params}
    {oldBindings : RecInfoBindings old oldInfos}
    {newBindings : RecInfoBindings new newInfos}
    {minor : FVarId}
    (Horder : RecInfoOuterOrder Rold oldParams oldBindings)
    (hparams : newParams.fvars = oldParams.fvars)
    (hmotives : newBindings.motives.fvars = oldBindings.motives.fvars)
    (hminors : newBindings.flatMinors.fvars =
      oldBindings.flatMinors.fvars ++ [minor])
    (hcontext : Rnew.mlctx.vlctx.fvars =
      minor :: Rold.mlctx.vlctx.fvars) :
    RecInfoOuterOrder Rnew newParams newBindings := by
  unfold RecInfoOuterOrder at Horder ⊢
  have Horder' : oldBindings.flatMinors.fvars.reverse ++
      oldBindings.motives.fvars.reverse ++ oldParams.fvars.reverse <+
      Rold.mlctx.vlctx.fvars := by
    simpa only [List.reverse_append, List.append_assoc] using Horder
  rw [hparams, hmotives, hminors, hcontext]
  simp only [List.reverse_append, List.reverse_singleton,
    List.singleton_append]
  simpa only [List.cons_append, List.append_assoc] using
    Horder'.cons_cons minor

def RecInfoBindings.mono
    (H : RecInfoBindings c recInfos) (hle : BindingContextLE c c') :
    RecInfoBindings c' recInfos where
  motives := H.motives.mono hle
  majors := H.majors.mono hle
  indices i hi := (H.indices i hi).mono hle
  minors i hi := (H.minors i hi).mono hle

/-- Recent local extensions only add a newest-first prefix, so any
previous outer selection remains ordered after weakening. -/
theorem RecInfoOuterOrder.monoRecent
    {stats : AddInductive.InductiveStats}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {recInfos : Array AddInductive.RecInfo} {args : Array Expr}
    {Hparams : FVarArrayIn root stats.params}
    {Hbindings : RecInfoBindings root recInfos}
    (Horder : RecInfoOuterOrder Rroot Hparams Hbindings)
    (Hrecent : RecursorFVarSuffix Rroot Rcurrent args) :
    RecInfoOuterOrder Rcurrent (Hparams.mono Hrecent.contextLE)
      (Hbindings.mono Hrecent.contextLE) := by
  unfold RecInfoOuterOrder at Horder ⊢
  change (Hparams.fvars ++ Hbindings.motives.fvars ++
    Hbindings.flatMinors.fvars).reverse <+ Rcurrent.mlctx.vlctx.fvars
  rw [Hrecent.contextFVars]
  exact (List.nil_sublist Hrecent.fvars.reverse).append Horder

/-- Select a motive in any later executable binding context.  All binder
types and the telescope shape are monotone; the abstract lookup is
then reconstructed from the later context's own `RecursorContextWF`. -/
theorem MotiveTypes.motiveBindingMono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rcurrent : RecursorContextWF current recLparams}
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoBinderTypes root recInfos)
    (Hshape : MotiveTypes root recInfos
      Horigins.motiveTypes elimLevel)
    (Hle : BindingContextLE root current)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (MotiveBinding Rcurrent recInfos[target]! elimLevel) := by
  let HbindingsCurrent := Hbindings.mono Hle
  let HoriginsCurrent := Horigins.mono Hle
  let HshapeCurrent := Hshape.mono Hbindings Hle
  exact HshapeCurrent.motiveBinding Rcurrent HbindingsCurrent
    HoriginsCurrent target htarget

/-- Consecutive higher-order suffix specialization of
`motiveBindingMono`. -/
theorem MotiveTypes.motiveBindingRecent
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams} {args : Array Expr}
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoBinderTypes root recInfos)
    (Hshape : MotiveTypes root recInfos
      Horigins.motiveTypes elimLevel)
    (Hrecent : RecursorFVarSuffix Rroot Rcurrent args)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (MotiveBinding Rcurrent recInfos[target]! elimLevel) :=
  Hshape.motiveBindingMono Hbindings Horigins Hrecent.contextLE target
    htarget

/-- Use the target-indexed motive applications `RecInfoMotiveApplications` after
a higher-order local suffix has been opened.  The executable traversal exposes a
terminal type only up to definitional equality; this lemma transports both
typehood and the major's typing back to the validated syntax target before
applying the motive property. -/
theorem RecInfoMotiveApplications.applyAtMono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (Happlications : RecInfoMotiveApplications Rroot stats decl recInfos
      elimLevel)
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoBinderTypes root recInfos)
    (Hshape : MotiveTypes root recInfos
      Horigins.motiveTypes elimLevel)
    (Hext : RecursorContextExtension Rroot Rcurrent)
    (target : Nat) (htarget : target < recInfos.size)
    {depth : Nat} {exposedType major : Expr}
    {syntaxTarget terminalTarget majorTarget : VExpr}
    (Hexposed : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      exposedType syntaxTarget)
    (Hdefeq : Rcurrent.venv.IsDefEqU recLparams.length
      Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget)
    (Hterminal : Rcurrent.venv.IsType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx terminalTarget)
    (Hmajor : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      major majorTarget)
    (HmajorType : Rcurrent.venv.HasType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx majorTarget terminalTarget)
    (Hvalidated : RecursorValidatedIndAppAt Rcurrent.venv recLparams
      Rcurrent.mlctx.vlctx stats decl depth exposedType syntaxTarget target) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[target]!.motive itIndices) major
    ∃ motiveTarget,
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        motiveApp motiveTarget ∧
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx motiveTarget := by
  rcases Hshape.motiveBindingMono Hbindings Horigins Hext.contextLE target
      htarget with ⟨Hbinding⟩
  have HsyntaxType : Rcurrent.venv.IsType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx syntaxTarget :=
    Hterminal.defeqU_l Rcurrent.checking.tr.wf
      Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm
  have HmajorType' : Rcurrent.venv.HasType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx majorTarget syntaxTarget :=
    HmajorType.defeqU_r Rcurrent.checking.tr.wf
      Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm
  exact Happlications.application target htarget Rcurrent Hext
    Hbinding Hexposed HsyntaxType Hmajor HmajorType' Hvalidated

theorem RecInfoBindings.empty_noAlias
    {stats : AddInductive.InductiveStats}
    (c : AddInductive.Context) (Hparams : FVarArrayIn c stats.params)
    (hparams : Hparams.fvars.Nodup) :
    RecInfoBindings.NoAlias stats.params #[] := by
  unfold RecInfoBindings.NoAlias RecInfoBindings.allFvars
  rw [Hparams.exprArrayFVarIds]
  simpa [ExprArrayFVarIds] using hparams

def RecInfoBindings.pushFrame
    {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : FVarArrayIn cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    RecInfoBindings cMotive (recInfos.push {
      motive := .fvar ⟨cMajor.ngen.curr⟩
      minors := #[]
      indices
      major := .fvar ⟨cIndices.ngen.curr⟩ }) := by
  dsimp only
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  let cMotive : AddInductive.Context := { cMajor with
    ngen := cMajor.ngen.next
    lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
      motiveName motiveTy motiveBi }
  let hMajor := BindingContextLE.withLocalDecl cIndices HcIndices
    majorName majorTy majorBi
  let hMotive := BindingContextLE.withLocalDecl cMajor
    (HcIndices.withLocalDecl majorName majorTy majorBi)
    motiveName motiveTy motiveBi
  let hall : BindingContextLE c cMotive := hle.trans (hMajor.trans hMotive)
  refine {
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
  }
  · simpa [cMajor, cMotive] using
      ((H.motives.mono (hle.trans hMajor)).pushCurrent
        motiveName motiveTy motiveBi)
  · simpa [cMajor, cMotive] using
      (((H.majors.mono hle).pushCurrent majorName majorTy majorBi).weaken
        motiveName motiveTy motiveBi)
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      simpa [cMajor, cMotive] using Hindices.mono (hMajor.trans hMotive)
    · have hiSize : i < recInfos.size + 1 := by simpa using hi
      have hiOld : i < recInfos.size := by omega
      have hget : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hget]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      simpa using FVarArrayIn.empty cMotive
    · have hiSize : i < recInfos.size + 1 := by simpa using hi
      have hiOld : i < recInfos.size := by omega
      have hget : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hget]
      exact (H.minors i hiOld).mono hall

def RecInfoBinderTypes.pushFrame
    {indices indexOrigins : Array Expr}
    (H : RecInfoBinderTypes c recInfos)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : FVarArrayBinderTypes cIndices indices indexOrigins)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    RecInfoBinderTypes cMotive (recInfos.push {
      motive := .fvar ⟨cMajor.ngen.curr⟩
      minors := #[]
      indices
      major := .fvar ⟨cIndices.ngen.curr⟩ }) := by
  dsimp only
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  let cMotive : AddInductive.Context := { cMajor with
    ngen := cMajor.ngen.next
    lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
      motiveName motiveTy motiveBi }
  let HcMajor := HcIndices.withLocalDecl majorName majorTy majorBi
  let hMajor := BindingContextLE.withLocalDecl cIndices HcIndices
    majorName majorTy majorBi
  let hMotive := BindingContextLE.withLocalDecl cMajor HcMajor
    motiveName motiveTy motiveBi
  let hall : BindingContextLE c cMotive := hle.trans (hMajor.trans hMotive)
  refine {
    motiveTypes := H.motiveTypes.push motiveTy
    majorTypes := H.majorTypes.push majorTy
    indexTypes := H.indexTypes.push indexOrigins
    minorTypes := H.minorTypes.push #[]
    indexTypes_size := by simpa using H.indexTypes_size
    minorTypes_size := by simpa using H.minorTypes_size
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
    minorShapes := ?_ }
  · simpa [cMajor, cMotive] using
      (H.motives.mono (hle.trans hMajor)).pushCurrent HcMajor
        motiveName motiveTy motiveBi
  · simpa [cMajor, cMotive] using
      ((H.majors.mono hle).pushCurrent HcIndices
        majorName majorTy majorBi).mono hMotive
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      have hindexOrigins :
          (H.indexTypes.push indexOrigins)[recInfos.size]! = indexOrigins := by
        rw [show recInfos.size = H.indexTypes.size from
          H.indexTypes_size.symm]
        simp
      rw [hindexOrigins]
      simpa [cMajor, cMotive] using Hindices.mono (hMajor.trans hMotive)
    · have hiOld : i < recInfos.size := by
        have : i < recInfos.size + 1 := by simpa using hi
        omega
      have hrec : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hrec]
      have hiTypes : i < H.indexTypes.size := by
        rw [H.indexTypes_size]
        exact hiOld
      have horigin : (H.indexTypes.push indexOrigins)[i]! =
          H.indexTypes[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        have hiPush : i < (H.indexTypes.push indexOrigins).size := by
          simp only [Array.size_push]
          omega
        rw [dif_pos hiPush, dif_pos hiTypes]
        exact Array.getElem_push_lt hiTypes
      rw [horigin]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      have horigin : (H.minorTypes.push #[])[recInfos.size]! = #[] := by
        rw [show recInfos.size = H.minorTypes.size from
          H.minorTypes_size.symm]
        simp
      rw [horigin]
      simpa using FVarArrayBinderTypes.empty cMotive
    · have hiOld : i < recInfos.size := by
        have : i < recInfos.size + 1 := by simpa using hi
        omega
      have hrec : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hrec]
      have hiTypes : i < H.minorTypes.size := by
        rw [H.minorTypes_size]
        exact hiOld
      have horigin : (H.minorTypes.push #[])[i]! = H.minorTypes[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        have hiPush : i < (H.minorTypes.push #[]).size := by
          simp only [Array.size_push]
          omega
        rw [dif_pos hiPush, dif_pos hiTypes]
        exact Array.getElem_push_lt hiTypes
      rw [horigin]
      exact (H.minors i hiOld).mono hall
  · intro i hi j hj
    by_cases hilast : i = recInfos.size
    · subst i
      have horigin : (H.minorTypes.push #[])[recInfos.size]! = #[] := by
        rw [show recInfos.size = H.minorTypes.size from
          H.minorTypes_size.symm]
        simp
      rw [horigin] at hj
      simp at hj
    · have hiOld : i < recInfos.size := by
        have : i < recInfos.size + 1 := by simpa using hi
        omega
      have hiTypes : i < H.minorTypes.size := by
        rw [H.minorTypes_size]
        exact hiOld
      have horigin : (H.minorTypes.push #[])[i]! = H.minorTypes[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        have hiPush : i < (H.minorTypes.push #[]).size := by
          simp only [Array.size_push]
          omega
        rw [dif_pos hiPush, dif_pos hiTypes]
        exact Array.getElem_push_lt hiTypes
      rw [horigin] at hj
      exact H.minorShapes i hiOld j hj
theorem RecInfoBindings.pushFrame_allFvars_perm
    (params : Array Expr) (recInfos : Array AddInductive.RecInfo)
    (indices : Array Expr) (major motive : FVarId) :
    (RecInfoBindings.allFvars params (recInfos.push {
      motive := .fvar motive, minors := #[], indices,
      major := .fvar major })).Perm
      (RecInfoBindings.allFvars params recInfos ++ ExprArrayFVarIds indices ++
        [major, motive]) := by
  simp only [RecInfoBindings.allFvars, Array.map_push, Array.flatMap_push,
    ExprArrayFVarIds, Array.toList_push,
    Array.toList_append, List.map_append, List.map_cons, List.map_nil,
    recursorFVarId]
  simp only [List.nil_append, List.append_assoc]
  apply List.Perm.append (List.Perm.refl _) <|
    List.Perm.append (List.Perm.refl _) ?_
  have reorder (minors oldIndices newIndices majors : List FVarId)
      (major motive : FVarId) :
      ([motive] ++ minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ~
        (minors ++ oldIndices ++ majors ++ newIndices ++ [major, motive]) := by
    have hswap : newIndices ++ majors ~ majors ++ newIndices :=
      List.perm_append_comm
    have hmiddle :
        minors ++ oldIndices ++ newIndices ++ majors ++ [major] ~
        minors ++ oldIndices ++ majors ++ newIndices ++ [major] := by
      simpa only [List.append_assoc] using
        (List.Perm.refl (minors ++ oldIndices)).append
          (hswap.append_right [major])
    have hmove :
        [motive] ++ (minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ~
        (minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ++
          [motive] := List.perm_append_comm
    exact hmove.trans <| by
      simpa [List.append_assoc] using hmiddle.append_right [motive]
  simpa only [List.append_assoc] using reorder
    ((Array.flatMap (fun x => x.minors) recInfos).toList.map recursorFVarId)
    ((Array.flatMap (fun x => x.indices) recInfos).toList.map recursorFVarId)
    (indices.toList.map recursorFVarId)
    ((Array.map (fun x => x.major) recInfos).toList.map recursorFVarId)
    major motive

theorem RecInfoBindings.pushFrame_noAlias
    {stats : AddInductive.InductiveStats} {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : FVarArrayAfter c cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo) :
    RecInfoBindings.NoAlias stats.params (recInfos.push {
      motive := .fvar ⟨cIndices.ngen.next.curr⟩, minors := #[], indices,
      major := .fvar ⟨cIndices.ngen.curr⟩ }) := by
  let old := RecInfoBindings.allFvars stats.params recInfos
  let indexFVars := Hindices.toFVarArrayIn.fvars
  let major : FVarId := ⟨cIndices.ngen.curr⟩
  let motive : FVarId := ⟨cIndices.ngen.next.curr⟩
  have hOldIndices : (old ++ indexFVars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnoalias, Hindices.nodup, ?_⟩
    intro fv hfv fv' hfv'
    exact fun heq => Hindices.fresh fv' hfv' <| heq ▸
      H.allFvars_members Hparams fv hfv
  have hMajorFresh : major ∉ old ++ indexFVars := by
    intro hmem
    simp only [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact HcIndices.current_not_mem <| hle <|
        H.allFvars_members Hparams major hmem
    · exact HcIndices.current_not_mem <|
        Hindices.toFVarArrayIn.members major hmem
  have hWithMajor : (old ++ indexFVars ++ [major]).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨hOldIndices, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hMajorFresh (heq ▸ hfv)⟩
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  have hMotiveFresh : motive ∉ old ++ indexFVars ++ [major] := by
    intro hmem
    apply (HcIndices.withLocalDecl majorName majorTy majorBi).current_not_mem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hOld | hIndex) | hMajor
    · exact Or.inr <| hle <| H.allFvars_members Hparams motive hOld
    · exact Or.inr <| Hindices.toFVarArrayIn.members motive hIndex
    · exact Or.inl hMajor
  have hCombined : (old ++ indexFVars ++ [major, motive]).Nodup := by
    rw [show [major, motive] = [major] ++ [motive] by rfl,
      ← List.append_assoc]
    apply List.nodup_append.mpr
    exact ⟨hWithMajor, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hMotiveFresh (heq ▸ hfv)⟩
  apply (RecInfoBindings.pushFrame_allFvars_perm stats.params recInfos indices
    ⟨cIndices.ngen.curr⟩ ⟨cIndices.ngen.next.curr⟩).symm.nodup
  simpa [old, indexFVars, major, motive, List.append_assoc,
    Hindices.toFVarArrayIn.exprArrayFVarIds] using hCombined

def RecInfoBindings.addMinor
    (H : RecInfoBindings c recInfos) (dIdx : Nat)
    (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    RecInfoBindings cMinor (recInfos.modify dIdx fun info =>
      { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }) := by
  dsimp only
  let cMinor : AddInductive.Context := { cMinorTy with
    ngen := cMinorTy.ngen.next
    lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
      minorName minorTy minorBi }
  let hstep := BindingContextLE.withLocalDecl cMinorTy HcMinorTy
    minorName minorTy minorBi
  let hall := hle.trans hstep
  refine {
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
  }
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map (·.motive) =
        recInfos.map (·.motive) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.motives.mono hall
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map (·.major) =
        recInfos.map (·.major) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.majors.mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases heq : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      exact (H.indices dIdx hidx).mono hall
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hiOld heq]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases heq : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      simpa [cMinor] using
        ((H.minors dIdx hidx).mono hle).pushCurrent
          minorName minorTy minorBi
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hiOld heq]
      exact (H.minors i hiOld).mono hall

def RecInfoBinderTypes.addMinor
    (H : RecInfoBinderTypes c recInfos) (dIdx : Nat)
    (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    (Hshape : MinorPremiseType) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    RecInfoBinderTypes cMinor (recInfos.modify dIdx fun info =>
      { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }) := by
  dsimp only
  let cMinor : AddInductive.Context := { cMinorTy with
    ngen := cMinorTy.ngen.next
    lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
      minorName minorTy minorBi }
  let hstep := BindingContextLE.withLocalDecl cMinorTy HcMinorTy
    minorName minorTy minorBi
  let hall := hle.trans hstep
  let nextMinorTypes := H.minorTypes.modify dIdx fun types =>
    types.push minorTy
  refine {
    motiveTypes := H.motiveTypes
    majorTypes := H.majorTypes
    indexTypes := H.indexTypes
    minorTypes := nextMinorTypes
    indexTypes_size := by simpa using H.indexTypes_size
    minorTypes_size := by simpa [nextMinorTypes] using H.minorTypes_size
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
    minorShapes := ?_ }
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map
          (·.motive) = recInfos.map (·.motive) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.motives.mono hall
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map
          (·.major) = recInfos.map (·.major) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.majors.mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      exact (H.indices dIdx hidx).mono hall
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
        hiOld hdi]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    have hiTypes : i < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hiOld
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      have horigin : nextMinorTypes[dIdx]! =
          (H.minorTypes[dIdx]!).push minorTy := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
          hiTypes]
      rw [horigin]
      simpa [cMinor] using
        ((H.minors dIdx hidx).mono hle).pushCurrent HcMinorTy
          minorName minorTy minorBi
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
        hiOld hdi]
      have horigin : nextMinorTypes[i]! = H.minorTypes[i]! := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx i _
          hiTypes hdi]
      rw [horigin]
      exact (H.minors i hiOld).mono hall
  · intro i hi j hj
    have hiOld : i < recInfos.size := by simpa using hi
    have hiTypes : i < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hiOld
    by_cases hdi : dIdx = i
    · subst i
      have horigin : nextMinorTypes[dIdx]! =
          (H.minorTypes[dIdx]!).push minorTy := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
          hiTypes]
      rw [horigin] at hj
      by_cases hjlast : j = H.minorTypes[dIdx]!.size
      · subst j
        have hlast : ((H.minorTypes[dIdx]!).push minorTy)[
            H.minorTypes[dIdx]!.size]! = minorTy := by
          have hpush : H.minorTypes[dIdx]!.size <
              (H.minorTypes[dIdx]!.push minorTy).size := by simp
          rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy)
            H.minorTypes[dIdx]!.size hpush]
          exact Array.getElem_push_eq
        exact Hshape
      · have hjOld : j < H.minorTypes[dIdx]!.size := by
          simp only [Array.size_push] at hj
          omega
        have hget : ((H.minorTypes[dIdx]!).push minorTy)[j]! =
            H.minorTypes[dIdx]![j]! := by
          have hjPush : j < (H.minorTypes[dIdx]!.push minorTy).size := by
            simp only [Array.size_push]
            omega
          rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy) j hjPush,
            getElem!_pos H.minorTypes[dIdx]! j hjOld]
          exact Array.getElem_push_lt hjOld
        exact H.minorShapes dIdx hidx j hjOld
    · have horigin : nextMinorTypes[i]! = H.minorTypes[i]! := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx i _
          hiTypes hdi]
      rw [horigin] at hj
      exact H.minorShapes i hiOld j hj

end VerifyInductive
end Lean4Lean
