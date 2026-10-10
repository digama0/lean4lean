import Lean4Lean.Theory.Inductive.Compilation

namespace Lean4Lean

/-!
# Inductive declarations

The shapes of recursor types, constructor types and ι-rule reducts (`VExpr.RecShape`,
`VExpr.CtorShape`, `VExpr.RuleShape`, with `VExpr.MotiveShape`/`VExpr.MinorFor` for the
motive and minor premises), the strict-positivity and result-type conditions on
constructors (`VExpr.CtorPositive`, `VExpr.CtorResult`), the large-elimination judgment
(`VInductDecl.LargeElim`), the staged environment extension `VEnv.addInduct` (type formers,
constructors, projections, recursors, ι rules), and the declaration well-formedness
predicate `VInductDecl.WF` it is checked against: the definitional source and formation
judgments (`VInductDecl.SourceWF`, `VInductDecl.FormationWF`), the compiled-recursor
certificate (`VInductDecl.RecsCompiled`) and the typing and shape of the recursors and
their rules. The syntactic constructor predicates (`CtorPositive`, `CtorResult`,
`LargeElim`) are no longer clauses of `WF`; `Tests/IotaShape.lean` decides them on the
kernel's data.
-/

namespace VExpr

/-! ### Positivity and the result type of a constructor (thesis §2.6.1) -/

/-- One of the constants `cs` occurs in the expression. Mirrors the kernel's `hasIndOcc`
(`Inductive/Add.lean`), used there over the type formers of the block being declared. -/
def MentionsConst (cs : List Name) : VExpr → Prop
  | .bvar _ | .sort _ => False
  | .const c _ => c ∈ cs
  | .proj _ _ e => MentionsConst cs e
  | .app e₁ e₂ | .lam e₁ e₂ | .forallE e₁ e₂ => MentionsConst cs e₁ ∨ MentionsConst cs e₂

/-- The boolean decision procedure behind `VExpr.MentionsConst`. -/
def mentionsConst (cs : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const c _ => decide (c ∈ cs)
  | .proj _ _ e => mentionsConst cs e
  | .app e₁ e₂ | .lam e₁ e₂ | .forallE e₁ e₂ => mentionsConst cs e₁ || mentionsConst cs e₂

theorem mentionsConst_iff {cs : List Name} :
    ∀ {e : VExpr}, e.mentionsConst cs = true ↔ e.MentionsConst cs
  | .bvar _ | .sort _ | .const .. => by simp [mentionsConst, MentionsConst]
  | .proj .. => by simp [mentionsConst, MentionsConst, mentionsConst_iff]
  | .app .. | .lam .. | .forallE .. => by
    simp [mentionsConst, MentionsConst, mentionsConst_iff]

/-- Thesis §2.6.1, the result type of a constructor of `T`: a Π-telescope of `np` parameters
and `nf` fields ending in `T` applied to the parameter variables in order and then `nind`
index terms. -/
def CtorResult (ty : VExpr) (T : Name) (np nf nind : Nat) : Prop :=
  ty.piArity = np + nf ∧
  ∃ us idx, idx.length = nind ∧ ty.piBody = (VExpr.const T us).mkApps (bvarsDesc nf np ++ idx)

theorem CtorResult_iff {ty : VExpr} {T : Name} {np nf nind : Nat} :
    ty.CtorResult T np nf nind ↔
      ty.piArity = np + nf ∧ ty.piBody.headConst? = some T ∧
        bvarsDesc nf np <+: ty.piBody.getAppArgs ∧
        (ty.piBody.getAppArgs.drop np).length = nind := by
  refine and_congr_right fun _ => ?_
  have : (∃ us idx, idx.length = nind ∧
      ty.piBody = (VExpr.const T us).mkApps (bvarsDesc nf np ++ idx)) ↔
      ∃ us idx, ty.piBody = (VExpr.const T us).mkApps (bvarsDesc nf np ++ idx) ∧
        idx.length = nind :=
    ⟨fun ⟨us, idx, h1, h2⟩ => ⟨us, idx, h2, h1⟩, fun ⟨us, idx, h1, h2⟩ => ⟨us, idx, h2, h1⟩⟩
  rw [this, eq_const_mkApps_append_iff (P := fun idx => idx.length = nind), bvarsDesc_length]

/-- Thesis §2.6.3, the major premise `z : P p x` of a recursor over `T`: `T` applied to
leading arguments over the recursor's parameters and to its index variables.

WAVE 3 COMPAT (restB): the leading arguments were the recursor's own parameter variables
(`bvarsDesc (nm + nmin + nind) np`), which is false for the auxiliary recursors of a nested
block: a restored `Tree.rec_1` has major `List (Tree α)`, the container at the specialization
arguments. They are now any terms over the `np` parameters only (lifted past the motives,
minors and indices), of any number (the container's parameter count);
`MajorApp.of_params` is the old shape. -/
def MajorApp (A : VExpr) (T : Name) (np nm nmin nind : Nat) : Prop :=
  ∃ us pre, A = (VExpr.const T us).mkApps (pre ++ bvarsDesc 0 nind) ∧
    ∀ a ∈ pre, ∃ a₀ : VExpr, a₀.ClosedN np ∧ a = a₀.liftN (nm + nmin + nind)

/-- The old major shape (the recursor's own parameter variables) is a `MajorApp`. -/
theorem MajorApp.of_params {A : VExpr} {T : Name} {np nm nmin nind : Nat}
    (h : ∃ us, A = (VExpr.const T us).mkApps (bvarsDesc (nm + nmin + nind) np ++ bvarsDesc 0 nind)) :
    A.MajorApp T np nm nmin nind := by
  obtain ⟨us, rfl⟩ := h
  refine ⟨us, _, rfl, fun a ha => ?_⟩
  simp only [bvarsDesc, List.mem_map, List.mem_reverse, List.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨.bvar i, by simpa [ClosedN] using hi, ?_⟩
  simp [liftN, liftVar]

/-- Decidable form of `MajorApp`. -/
theorem MajorApp_iff {A : VExpr} {T : Name} {np nm nmin nind : Nat} :
    A.MajorApp T np nm nmin nind ↔
      A.headConst? = some T ∧ nind ≤ A.getAppArgs.length ∧
        A.getAppArgs.drop (A.getAppArgs.length - nind) = bvarsDesc 0 nind ∧
        ∀ a ∈ A.getAppArgs.take (A.getAppArgs.length - nind),
          (a.unliftN (nm + nmin + nind) 0).ClosedN np ∧ a.Skips (nm + nmin + nind) 0 := by
  constructor
  · rintro ⟨us, pre, rfl, hpre⟩
    have hargs := (const_mkApps_spine (c := T) (us := us) (args := pre ++ bvarsDesc 0 nind)).2
    refine ⟨headConst?_eq_some.2 ⟨us, const_mkApps_spine.1⟩, ?_, ?_, ?_⟩ <;> rw [hargs]
    · simp
    · simp
    · intro a ha
      simp only [List.length_append, bvarsDesc_length, Nat.add_sub_cancel,
        List.take_left'] at ha
      obtain ⟨a₀, h0, rfl⟩ := hpre a ha
      exact ⟨by rw [unliftN_liftN]; exact h0, .liftN⟩
  · rintro ⟨h1, hlen, hdrop, htake⟩
    obtain ⟨us, hf⟩ := headConst?_eq_some.1 h1
    refine ⟨us, A.getAppArgs.take (A.getAppArgs.length - nind), ?_, fun a ha => ?_⟩
    · apply eq_const_mkApps_of_spine hf
      rw [← hdrop, List.take_append_drop]
    · obtain ⟨hc, hs⟩ := htake a ha
      exact ⟨_, hc, hs.symm⟩

/-- Thesis §2.6.1, the kernel's `isValidIndApp?`: an application of one of the block's type
formers `fs` to the block's parameter variables — seen from `d` binders below the field
level — and to index terms in which no former occurs. -/
def ValidIndApp (fs : List Name) (np d : Nat) (e : VExpr) : Prop :=
  ∃ T ∈ fs, ∃ us idx, e = (VExpr.const T us).mkApps (bvarsDesc d np ++ idx) ∧
    ∀ a ∈ idx, ¬ a.MentionsConst fs

theorem ValidIndApp_iff {fs : List Name} {np d : Nat} {e : VExpr} :
    e.ValidIndApp fs np d ↔
      (∃ T, e.headConst? = some T ∧ T ∈ fs) ∧ bvarsDesc d np <+: e.getAppArgs ∧
        ∀ a ∈ e.getAppArgs.drop np, ¬ a.MentionsConst fs := by
  simp only [ValidIndApp, eq_const_mkApps_append_iff, bvarsDesc_length]
  constructor
  · rintro ⟨T, hT, hc, hpre, hidx⟩; exact ⟨⟨T, hc, hT⟩, hpre, hidx⟩
  · rintro ⟨⟨T, hc, hT⟩, hpre, hidx⟩; exact ⟨T, hT, hc, hpre, hidx⟩

/-- Thesis §2.6.1, strict positivity of one constructor field, mirroring the kernel's
`checkPositivity`: either no former of `fs` occurs in the field type, or it is
`∀ x₁ … x_k, B` with no `xᵢ`'s type mentioning a former and `B` a `ValidIndApp`. The kernel
reduces the field type (and each `xᵢ`'s) to weak head normal form first; the model reads the
manifest binders only. -/
def FieldPositive (fs : List Name) (np d : Nat) (ty : VExpr) : Prop :=
  ¬ ty.MentionsConst fs ∨
    ((∀ A ∈ ty.piBinders, ¬ A.MentionsConst fs) ∧
      ty.piBody.ValidIndApp fs np (d + ty.piArity))

/-- Thesis §2.6.1, strict positivity of a constructor with `np` parameters: no former of
`fs` occurs in a parameter binder, and every later binder — field `i`, sitting under `np + i`
binders — is `FieldPositive`. The result type is pinned separately, by `CtorResult`. -/
def CtorPositive (fs : List Name) (np : Nat) (ty : VExpr) : Prop :=
  (∀ A ∈ ty.piBinders.take np, ¬ A.MentionsConst fs) ∧
  ∀ i < ty.piArity - np, ∃ A, ty.piBinders[np + i]? = some A ∧ A.FieldPositive fs np i

/-- Field `i` of a constructor with `np` parameters occurs among the index arguments of its
result type: the syntactic clause of the kernel's `isLargeEliminator`. -/
def FieldInIndices (ty : VExpr) (np i : Nat) : Prop :=
  VExpr.bvar (ty.piArity - np - 1 - i) ∈ ty.piBody.getAppArgs.drop np

/-- The de Bruijn context of field `i` of a constructor with `np` parameters: the parameter
and earlier-field binder types, innermost first. -/
def fieldCtx (ty : VExpr) (np i : Nat) : List VExpr := (ty.piBinders.take (np + i)).reverse

/-! ### Recursor, constructor and ι-reduct shapes (thesis §2.6.3–2.6.4) -/

/-- Thesis §2.6.3, the motive `C : ∀ a::α. P a → U`: a Π-telescope ending in a sort whose
last binder is headed by a constant (`VExpr.motiveFormer?`, that head). *Which* constant is
not pinned here — a bare `VEnv` has no notion of type former — and `RecShape` ties only the
eliminated motive's head to the major premise's; the heads of the other motives of a
mutual recursor are unconstrained. -/
def MotiveShape (A : VExpr) : Prop :=
  (∃ u, A.piBody = .sort u) ∧ A.motiveFormer?.isSome = true

/-- Thesis §2.6.3, the head `C` of the minor premise `ε_c = ∀ b::β. ∀ v::δ. C p[b] (c b)`:
the Π-body of minor `i` (counted from the outermost minor binder) is headed by one of the
`nm` motives. Under the minor's own `piArity` binders, the motive binders — which precede
minor `i` by `i` minors — are `bvar (piArity + i + k)` for `k < nm` (motive `nm - 1 - k`). -/
def MinorHeaded (A : VExpr) (i nm : Nat) : Prop :=
  ∃ k < nm, A.piBody.getAppFn = .bvar (A.piArity + i + k)

/-- Thesis §2.6.3, the minor premise `ε_c = ∀ b::β. ∀ v::δ. C p[b] (c b)` of constructor
`c`: a Π-telescope ending in an application of a bound variable (the motive, which
`RecShape` pins on the same binder) whose last argument is headed by `c`. -/
def MinorFor (A : VExpr) (c : Name) : Prop :=
  A.RecHeaded ∧ ∃ x, A.piBody.getAppArgs.getLast? = some x ∧ x.headConst? = some c

/-- Thesis §2.6.3: the recursor telescope is `∀ params motives minors indices major,
motive_j indices major`, with motive `j` counted from the outermost motive binder. Motive
binders have the shape `MotiveShape`, minor binders end in an application of one of the
motives (`MinorHeaded`), the major premise is the type former `T` applied to the parameter
and index variables (`MajorApp`), and `motive_j`'s last binder is headed by `T` too.
Parameter and index binders are unconstrained. -/
def RecShape (ty : VExpr) (np nm nmin nind : Nat) : Prop :=
  ty.piArity = np + nm + nmin + nind + 1 ∧
  (∀ i < nm, ∃ A, ty.piBinders[np + i]? = some A ∧ A.MotiveShape) ∧
  (∀ i < nmin, ∃ A, ty.piBinders[np + nm + i]? = some A ∧ A.MinorHeaded i nm) ∧
  ∃ j < nm,
    (∃ M, ty.piBinders[np + nm + nmin + nind]? = some M ∧
      ∃ T, M.headConst? = some T ∧ M.MajorApp T np nm nmin nind ∧
        ∃ A, ty.piBinders[np + j]? = some A ∧ A.motiveFormer? = some T) ∧
    ty.piBody =
      (VExpr.bvar (nind + nmin + 1 + (nm - 1 - j))).mkApps (VExpr.bvarsDesc 0 (nind + 1))

/-- The syntactic shape of a constructor type: exactly `arity` Π-binders ending in a constant
application (`CtorHeaded`). Which binders are parameters and whether the constant is a type
former, a bare `VEnv` cannot say. -/
def CtorShape (ty : VExpr) (arity : Nat) : Prop := ty.piArity = arity ∧ ty.CtorHeaded

/-- The type former a recursor type with major index `idx` eliminates: the head constant of
its major premise (the `idx`-th Π-binder). -/
def majorFormer? (ty : VExpr) (idx : Nat) : Option Name :=
  ty.piBinders[idx]?.bind VExpr.headConst?

/-- Thesis §2.6.4: the reduct of the ι rule using minor `j` (counted from the outermost
minor binder) is `λ params motives minors fields, minor_j fields v`, minor `j` applied
η-long to the fields and then to `nrec` further arguments `v` (`recArgs`). The terms `v` are
not pinned, syntactically or through typing: `VInductDecl.WF.rules_wf` types the reduct at
the redex's type, which forces only the *types* of `v` — those of the minor's binders after
the fields (`δ`, themselves unpinned by `MinorFor`) — not that they are the thesis's
recursive calls `rec … (u_i x)`. Their *number* is pinned: `VInductDecl.WF.rule_shape` sets
`nrec` to the number of the minor's binders after the fields (`v::δ` has the length of `δ`),
so the reduct applies the minor to exactly its binders — none beyond the fields for a
non-recursive constructor. -/
def RuleShape (rhs : VExpr) (np nm nmin nf nrec j : Nat) : Prop :=
  rhs.lamArity = np + nm + nmin + nf ∧
  ∃ recArgs : List VExpr, recArgs.length = nrec ∧
    rhs.lamBody = (VExpr.bvar (nf + (nmin - 1 - j))).mkApps (VExpr.bvarsDesc 0 nf ++ recArgs)

end VExpr

/-- A rule reduct is a λ-abstraction: its λ-arity counts at least the minor premises, of
which there is at least one (`j < nmin`). -/
theorem VExpr.RuleShape.lam {rhs : VExpr} {np nm nmin nf nrec j : Nat}
    (h : rhs.RuleShape np nm nmin nf nrec j) (hj : j < nmin) : ∃ A b, rhs = .lam A b := by
  have h1 := h.1
  cases rhs with
  | lam A b => exact ⟨A, b, rfl⟩
  | _ => simp [VExpr.lamArity] at h1; omega

/-- A recursor type is `RecHeaded`: its Π-body is a motive application. -/
theorem VExpr.RecShape.recHeaded {ty : VExpr} {np nm nmin nind : Nat}
    (h : ty.RecShape np nm nmin nind) : ty.RecHeaded :=
  h.2.2.2.elim fun _ hj => ⟨_, by rw [hj.2.2, VExpr.getAppFn_mkApps]; rfl⟩

/-- A recursor type has at least one motive. -/
theorem VExpr.RecShape.one_le_numMotives {ty : VExpr} {np nm nmin nind : Nat}
    (h : ty.RecShape np nm nmin nind) : 1 ≤ nm :=
  h.2.2.2.elim fun _ hj => Nat.lt_of_le_of_lt (Nat.zero_le _) hj.1

/-- The type former a `RecShape` recursor eliminates: the head constant of its major
premise, which `MajorApp` pins to an application of terms over the parameters and of the index
variables. -/
theorem VExpr.RecShape.majorFormer?_eq {ty : VExpr} {np nm nmin nind : Nat}
    (h : ty.RecShape np nm nmin nind) :
    ∃ T M, ty.piBinders[np + nm + nmin + nind]? = some M ∧
      ty.majorFormer? (np + nm + nmin + nind) = some T ∧ M.MajorApp T np nm nmin nind :=
  h.2.2.2.elim fun _ hj => hj.2.1.elim fun M hM => hM.2.elim fun T hT =>
    ⟨T, M, hM.1, by rw [VExpr.majorFormer?, hM.1]; exact hT.1, hT.2.1⟩

/-- A constructor returning its own type former has that constant as its Π-body's head. -/
theorem VExpr.CtorResult.ctorHeaded {ty : VExpr} {T : Name} {np nf nind : Nat}
    (h : ty.CtorResult T np nf nind) : ty.CtorHeaded := by
  obtain ⟨-, us, idx, -, hb⟩ := h
  exact ⟨T, us, by rw [hb, VExpr.getAppFn_mkApps]; rfl⟩

/-- A constructor returning its own type former has `CtorShape` of arity `np + nf`. -/
theorem VExpr.CtorResult.ctorShape {ty : VExpr} {T : Name} {np nf nind : Nat}
    (h : ty.CtorResult T np nf nind) : ty.CtorShape (np + nf) := ⟨h.1, h.ctorHeaded⟩

/-! ### Large elimination (thesis §2.6.2) -/

/-- Thesis §2.6.2, the kernel's `isLargeEliminator`: the block may eliminate into an
arbitrary sort. Either its result sort `ℓ` is never `Prop`, or the block is a single type
former with no constructor, or a single type former with one constructor each of whose
fields is a proposition or occurs among the indices of the constructor's result type. `env`
is the environment in which the fields are typed, the one with the type formers declared. -/
def VInductDecl.LargeElim (env : VEnv) (decl : VInductDecl) (ℓ : VLevel) : Prop :=
  ℓ.IsNeverZero ∨
  (∃ t, decl.types = [t] ∧ t.ctors = []) ∨
  (∃ t c, decl.types = [t] ∧ t.ctors = [c] ∧
    ∀ i < c.type.piArity - decl.nparams, ∃ F, c.type.piBinders[decl.nparams + i]? = some F ∧
      (env.HasType decl.uvars (c.type.fieldCtx decl.nparams i) F (.sort .zero) ∨
        c.type.FieldInIndices decl.nparams i))

/-- The syntactic half of `VInductDecl.LargeElim`, decidable: a block outside the never-`Prop`
case is a single type former with at most one constructor. Whether a field of that
constructor is a proposition is a typing judgment, not decided here. -/
def VInductDecl.LargeElimShape (decl : VInductDecl) : Prop :=
  decl.types.length = 1 ∧ ∀ t ∈ decl.types, t.ctors.length ≤ 1

/-- A block whose result sort can be `Prop` eliminates largely only in the shape
`LargeElimShape` allows. -/
theorem VInductDecl.LargeElim.shape {env : VEnv} {decl : VInductDecl} {ℓ : VLevel}
    (h : decl.LargeElim env ℓ) (hz : ¬ ℓ.IsNeverZero) : decl.LargeElimShape := by
  rcases h with h | ⟨t, ht, hc⟩ | ⟨t, c, ht, hc, -⟩
  · exact absurd h hz
  · refine ⟨by rw [ht]; rfl, fun t' ht' => ?_⟩
    rw [ht, List.mem_singleton] at ht'; subst ht'; simp [hc]
  · refine ⟨by rw [ht]; rfl, fun t' ht' => ?_⟩
    rw [ht, List.mem_singleton] at ht'; subst ht'; simp [hc]


/-- Abstract compilation, separate from the executable compiler: the shared
finite derivation `CompiledInductive` (ordinary compilation being its
zero-specialization case) generates the block. That the block lays out the
declaration's families, constructors and projections, and that its installed
names are distinct, are consequences (`CompilesTo.types`, `.ctors`,
`.projections`, `.names`). -/
abbrev VInductDecl.CompilesTo
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop :=
  CompiledInductive env decl block

theorem VInductDecl.CompilesTo.types {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) : block.types = decl.typeConstants :=
  CompiledInductive.types_eq H

theorem VInductDecl.CompilesTo.ctors {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) : block.ctors = decl.constructorConstants :=
  CompiledInductive.ctors_eq H

theorem VInductDecl.CompilesTo.projections {env : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : decl.CompilesTo env block) :
    block.projections = decl.projectionEntries :=
  CompiledInductive.projections_eq H

theorem VInductDecl.CompilesTo.names {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup :=
  CompiledInductive.names_nodup H

theorem InductiveSignature.FamilyTypesWF.mono {s : InductiveSignature}
    {env env' : VEnv} {uvars : Nat}
    (H : s.FamilyTypesWF env uvars) (hle : env ≤ env') :
    s.FamilyTypesWF env' uvars :=
  fun owner => ⟨(H owner).1.mono fun h => h.mono hle, (H owner).2.mono hle⟩

theorem InductiveSignature.Models.mono
    {s : InductiveSignature} {env env' envTypes' : VEnv} {decl : VInductDecl}
    (H : s.Models env decl) (henv : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes') :
    s.Models env' decl := by
  rcases H.constructors with ⟨envTypes, htypesOld, hctors⟩
  have hle := VEnv.addConstVals_mono henv htypesOld htypes
  refine { H with
    families := ?_
    constructors := ⟨envTypes', htypes, ?_⟩
    classifiedFields := ?_ }
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ _ h => h) H.families
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.mono hle⟩) hctors
  · rcases H.classifiedFields with hunsafe | ⟨envTypesPos, htypesPos, hpos⟩
    · exact .inl hunsafe
    · refine .inr ⟨envTypes', htypes, ?_⟩
      intro ctor hc i hi
      obtain ⟨normalized, hnormal, hshape⟩ := hpos ctor hc i hi
      exact ⟨normalized,
        hnormal.mono (VEnv.addConstVals_mono henv htypesPos htypes), hshape⟩

theorem VInductDecl.CompilesTo.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env')
    (Hblock : block.WF env')
    (H : decl.CompilesTo env block) : decl.CompilesTo env' block :=
  CompiledInductive.mono H henv Hblock

theorem VInductDecl.CompilesTo.sourceNames
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) : decl.sourceNames.Nodup := by
  have hprefix : ((block.types ++ block.ctors).map (·.name)).Nodup := by
    apply List.Nodup.sublist (l₂ :=
      (block.types ++ block.ctors ++ block.recursors).map (·.name))
    · simp [List.map_append, List.append_assoc]
    · exact H.names
  simpa [VInductDecl.sourceNames, H.types, H.ctors, List.map_append]
    using hprefix

/-! ## Ordinary-or-nested formation derivations

Nested formation refers only to prior, finitely derived installed inductive
blocks. Defining the installation of prior containers (`VEnv.InstalledBelow`) in the same
mutual induction as formation avoids both an uncheckable environment lookup and a definitional
cycle through `AddInduct`. -/

/-- Exact construction of one direct auxiliary constructor before its own
body is recursively lowered. -/
structure VInductDecl.SpecializedAuxConstructor
    (env : VEnv) (U : Nat)
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (containerFamily auxiliaryFamily : VInductiveType)
    (source target : VConstVal) : Prop where
  name : target.name = source.name.replacePrefix containerFamily.name
    auxiliaryFamily.name
  uvars : target.uvars = auxiliaryFamily.uvars
  type : env.IsDefEqU U [] target.type
    (VExpr.wrapForalls sourceParams
      (VExpr.instantiateForallPrefix (source.type.instL levels) baseArgs))

/-- A rigid head used to package two corresponding argument lists as one
expression relation.  Unlike a bound variable, it is stable when the
surrounding constructor telescope is lifted. -/
def VInductDecl.nestedTrailingMarker : VExpr :=
  .const `_nested.trailing []

mutual

/-- Formation is either the ordinary judgment or a finite nested
expansion into an independently ordinary well-formed declaration. -/
inductive VInductDecl.FormationWF : VEnv → VInductDecl → Prop
  | ordinary {env decl} : VInductDecl.OrdinaryFormationWF env decl →
      VInductDecl.FormationWF env decl
  | nested {base env decl} : VInductDecl.NestedFormationWF base decl →
      base ≤ env →
      VInductDecl.FormationWF env decl

/-- A prior container declaration. It has its own finite source/formation derivation, compiles
to the exact block, its recursors and rules are read off that well-formed block
(`VInductDecl.RecsOf`), and its staged installation `VEnv.addInduct` lies below the ambient
environment.

WAVE 2 COMPAT: restated on `VEnv.addInduct` (the installation the checker builds,
`VEnv.InductInstalled` in `Verify/Environment/Blocks.lean`) instead of `VInductBlock.install`,
which registered the generated rules as stored equations that no `addInduct` environment
contains. `VInductDecl.WF` cannot be named here (it refers back to `FormationWF`), so the
recursor-stage typing is carried by `block.WF base` together with `RecsOf`. -/
inductive VEnv.InstalledBelow : VEnv → VInductDecl → Prop
  | intro {env container base block installed} :
      VInductDecl.SourceWF base container →
      VInductDecl.FormationWF base container →
      container.CompilesTo base block →
      block.WF base →
      container.RecsOf block →
      base.addInduct container = some installed →
      installed ≤ env →
      VEnv.InstalledBelow env container

/-- One legal replacement of a maximal nested occurrence. The auxiliary family
is an exact parameter specialization of a family in a previously installed
container block, and its direct constructors are the corresponding exact
specializations with deterministic names.  The verification of the executable
lowering separately records that some concrete parameter syntax
mentions the finite lowering queue.  That occurrence is intentionally not a
premise here: `TrExprS` erases metadata and let types/values and interprets
projections opaquely, so a concrete occurrence need not survive in `VExpr`.
Such an erased-only occurrence may generate a semantically unused auxiliary;
this remains sound because the prior-container specialization is exact and
ordinary formation checks the complete expanded finite block. -/
inductive VInductDecl.NestedOccurrenceReplacement :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | intro {env sourceTypesEnv source generated depth input output container
      containerFamily auxiliaryFamily sourceParams baseArgs levels
      auxiliaryLevels inputBaseArgs sourceTrailing targetTrailing} :
      env.addConstVals source.typeConstants = some sourceTypesEnv →
      VEnv.InstalledBelow sourceTypesEnv container →
      containerFamily ∈ container.types →
      auxiliaryFamily ∈ generated →
      sourceParams.length = source.nparams →
      baseArgs.length = container.nparams →
      (∀ arg ∈ baseArgs, arg.ClosedN source.nparams) →
      levels.length = container.uvars →
      (∀ level ∈ levels, level.WF source.uvars) →
      auxiliaryFamily.uvars = source.uvars →
      sourceTypesEnv.IsDefEqU source.uvars [] auxiliaryFamily.type
        (VExpr.wrapForalls sourceParams
          (VExpr.instantiateForallPrefix
            (containerFamily.type.instL levels) baseArgs)) →
      List.Forall₂
        (VInductDecl.SpecializedAuxConstructor sourceTypesEnv source.uvars sourceParams
          baseArgs levels containerFamily auxiliaryFamily)
        containerFamily.ctors auxiliaryFamily.ctors →
      auxiliaryLevels.length = source.uvars →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker
          (baseArgs.map (fun arg => arg.liftN depth 0)))
        (VExpr.mkApps VInductDecl.nestedTrailingMarker inputBaseArgs) →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceTrailing)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker targetTrailing) →
      input = VExpr.mkApps (.const containerFamily.name levels)
        (inputBaseArgs ++ sourceTrailing) →
      output = VExpr.mkApps (.const auxiliaryFamily.name auxiliaryLevels)
        (source.paramVars depth ++ targetTrailing) →
      VInductDecl.NestedOccurrenceReplacement env source generated depth input output

/-- Specialized structural expansion used inside the mutual formation
derivation. It has a forgetful map to `VExpr.NestedExprExpansion`; spelling it
out here is required by Lean's strict-positivity checker for the mutual leaf. -/
inductive VInductDecl.NestedExprWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | occurrence {env source generated depth relativeDepth input output} :
      depth = source.nparams + relativeDepth →
      VInductDecl.NestedOccurrenceReplacement env source generated relativeDepth
        input output →
      VInductDecl.NestedExprWFExpansion env source generated depth input output
  | bvar {env source generated index depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.bvar index) (.bvar index)
  | sort {env source generated level depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.sort level) (.sort level)
  | const {env source generated name levels depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.const name levels) (.const name levels)
  | proj {env source generated typeName index depth sourceMajor targetMajor} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceMajor targetMajor →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.proj typeName index sourceMajor)
        (.proj typeName index targetMajor)
  | app {env source generated depth sourceFn targetFn sourceArg targetArg} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceFn targetFn →
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceArg targetArg →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.app sourceFn sourceArg) (.app targetFn targetArg)
  | lam {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.lam sourceDomain sourceBody) (.lam targetDomain targetBody)
  | forallE {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)

/-- Strictly-positive counterpart of `NestedForallPrefixExpansion` for the
mutually defined nested-formation leaf. -/
inductive VInductDecl.NestedForallPrefixWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → Nat → VExpr → VExpr → Prop
  | nil
      (Hbody : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth 0
        sourceBody targetBody
  | cons
      (Hdomain : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain)
      (Hbody : VInductDecl.NestedForallPrefixWFExpansion env source generated
        (depth + 1) arity sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth
        (arity + 1) (.forallE sourceDomain sourceBody)
          (.forallE targetDomain targetBody)

/-- Ordered constructor expansion without nesting the mutually defined leaf
inside an external `List.Forall₂`. -/
inductive VInductDecl.NestedConstructorWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VConstVal → List VConstVal → Prop
  | nil {env source generated} :
      VInductDecl.NestedConstructorWFExpansions env source generated [] []
  | cons {env source generated sourceCtor targetCtor sourceCtors targetCtors} :
      targetCtor.name = sourceCtor.name →
      targetCtor.uvars = sourceCtor.uvars →
      VInductDecl.NestedForallPrefixWFExpansion env source generated 0
        source.nparams sourceCtor.type targetCtor.type →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceCtors targetCtors →
      VInductDecl.NestedConstructorWFExpansions env source generated
        (sourceCtor :: sourceCtors) (targetCtor :: targetCtors)

/-- Ordered family expansion for the initial mutual block followed by the
direct, unlowered auxiliary queue. -/
inductive VInductDecl.NestedTypeWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VInductiveType → List VInductiveType → Prop
  | nil {env source generated} :
      VInductDecl.NestedTypeWFExpansions env source generated [] []
  | cons {env source generated sourceType targetType sourceTypes targetTypes} :
      targetType.name = sourceType.name →
      targetType.uvars = sourceType.uvars →
      env.IsDefEqU source.uvars [] sourceType.type targetType.type →
      targetType.numIndices = sourceType.numIndices →
      targetType.resultLevel = sourceType.resultLevel →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceType.ctors targetType.ctors →
      VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
        targetTypes →
      VInductDecl.NestedTypeWFExpansions env source generated
        (sourceType :: sourceTypes) (targetType :: targetTypes)

/-- A nested declaration is formed by expanding the source families and a
finite queue of direct auxiliary sources into a declaration satisfying the
ordinary source and formation judgments. -/
inductive VInductDecl.NestedFormationWF : VEnv → VInductDecl → Prop
  | intro {env source expanded generated} :
      VInductDecl.SourceWF env expanded →
      VInductDecl.OrdinaryFormationWF env expanded →
      VInductDecl.SourceParameterWF env source →
      expanded.uvars = source.uvars →
      expanded.nparams = source.nparams →
      expanded.isUnsafe = source.isUnsafe →
      VInductDecl.NestedTypeWFExpansions env source generated
        (source.types ++ generated) expanded.types →
      VInductDecl.NestedFormationWF env source

end

/-- Constructor expressions count every enclosing forall binder, whereas
`NestedOccurrenceReplacement` counts only constructor-field binders below the common
parameter prefix.  This wrapper is the explicit boundary between those two
depth conventions. -/
def VInductDecl.NestedOccurrenceReplacementAbs
    (env : VEnv) (source : VInductDecl)
    (generated : List VInductiveType) (depth : Nat)
    (input output : VExpr) : Prop :=
  ∃ relativeDepth,
    depth = source.nparams + relativeDepth ∧
    VInductDecl.NestedOccurrenceReplacement env source generated relativeDepth
      input output


theorem VExpr.getAppFnArgs_mkApps_const (name : Name) (levels : List VLevel)
    (args : List VExpr) :
    (VExpr.mkApps (.const name levels) args).getAppFnArgs =
      (.const name levels, args) := by
  suffices h : ∀ (fn : VExpr) (pre : List VExpr),
      fn.getAppFnArgs = (.const name levels, pre) →
      (VExpr.mkApps fn args).getAppFnArgs = (.const name levels, pre ++ args) by
    simpa using h (.const name levels) [] (by simp)
  induction args with
  | nil =>
    intro fn pre h
    simpa [VExpr.mkApps] using h
  | cons arg args ih =>
    intro fn pre h
    have := ih (.app fn arg) (pre ++ [arg]) (by simp [VExpr.getAppFnArgs_app, h])
    simpa [VExpr.mkApps, List.append_assoc] using this

/-- Every auxiliary-family leaf replaces a source expression by an
application headed by one of the auxiliary families. -/
theorem VInductDecl.NestedOccurrenceReplacementAbs.headConst
    {env : VEnv} {source : VInductDecl} {generated : List VInductiveType}
    {depth : Nat} {input output : VExpr}
    (H : VInductDecl.NestedOccurrenceReplacementAbs env source generated depth
      input output) :
    ∃ auxiliary ∈ generated, ∃ levels args,
      output.getAppFnArgs = (.const auxiliary.name levels, args) := by
  rcases H with ⟨relativeDepth, _hdepth, H⟩
  cases H with
  | intro _ _ _ hgen _ _ _ _ _ _ _ _ _ _ _ _ houtput =>
    exact ⟨_, hgen, _, _, by rw [houtput]; exact VExpr.getAppFnArgs_mkApps_const _ _ _⟩

theorem List.Forall₂.map_eq_of {α β γ : Type _} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (H : List.Forall₂ R l₁ l₂)
    (f : α → γ) (g : β → γ) (hf : ∀ a b, R a b → f a = g b) :
    l₁.map f = l₂.map g := by
  induction H with
  | nil => rfl
  | cons h _ ih => simp [hf _ _ h, ih]

/-- Raw constructor shapes of the source families follow from the raw
shapes of the expanded declaration through the ordered nested expansion. -/
theorem VInductDecl.rawShapesOfNestedExpansions
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
      (source.types ++ generated) expanded.types)
    (Hraw : ∀ type ∈ expanded.types, ∀ ctor ∈ type.ctors,
      expanded.RawCtorShape type ctor)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnodup : (expanded.types.map (·.name)).Nodup) :
    ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor := by
  have hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name) :=
    (Lean4Lean.List.Forall₂.map_eq_of Htypes (·.name) (·.name)
      (fun _ _ h => h.name.symm)).symm
  intro type htype ctor hctor
  rcases Lean4Lean.List.Forall₂.forall_exists_l Htypes type
      (List.mem_append_left _ htype) with ⟨target, htarget, Hexp⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_l Hexp.constructors ctor hctor with
    ⟨targetCtor, htargetCtor, Hctor⟩
  exact VInductDecl.RawCtorShape.ofNestedExpansion
    (fun h => VInductDecl.NestedOccurrenceReplacementAbs.headConst h)
    huvars hnparams hnames hnodup htype htarget Hexp.name Hexp.numIndices
    Hctor.type (Hraw target htarget targetCtor htargetCtor)

/-- Constructor telescope lengths agree positionally across the ordered
nested expansion of the source families. -/
theorem VInductDecl.constructorArityPrefixOfNestedExpansions
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
      (source.types ++ generated) expanded.types)
    (Hraw : ∀ type ∈ expanded.types, ∀ ctor ∈ type.ctors,
      expanded.RawCtorShape type ctor)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnodup : (expanded.types.map (·.name)).Nodup) :
    source.ConstructorArityPrefix expanded := by
  have hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name) :=
    (Lean4Lean.List.Forall₂.map_eq_of Htypes (·.name) (·.name)
      (fun _ _ h => h.name.symm)).symm
  intro familyIdx hsource hexpanded ctorIdx hsourceCtor hexpandedCtor
  have hprefix : familyIdx < (source.types ++ generated).length := by
    simp only [List.length_append]
    omega
  have Hexp := Lean4Lean.List.Forall₂.getElem_of Htypes familyIdx hprefix hexpanded
  have hget : (source.types ++ generated)[familyIdx] = source.types[familyIdx] :=
    List.getElem_append_left hsource
  rw [hget] at Hexp
  have Hctor := Lean4Lean.List.Forall₂.getElem_of Hexp.constructors ctorIdx
    hsourceCtor hexpandedCtor
  exact (VInductDecl.RawCtorShape.ofNestedExpansion_core
    (fun h => VInductDecl.NestedOccurrenceReplacementAbs.headConst h)
    huvars hnparams hnames hnodup (List.getElem_mem hsource)
    (List.getElem_mem hexpanded) Hexp.name Hexp.numIndices Hctor.type
    (Hraw _ (List.getElem_mem hexpanded) _ (List.getElem_mem hexpandedCtor))).2

/-- The recursors and rules of `decl` are those of a finite compilation of it
(`VInductDecl.CompilesTo`): the generator fixes every recursor type and every equation, and
`decl.recs` is read off that output (`VInductDecl.RecsOf`). Recursors and equations are never
accepted as input on the strength of their typing alone. -/
def VInductDecl.RecsCompiled (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ block, decl.CompilesTo env block ∧ decl.RecsOf block

/-- Well-formedness of an inductive declaration, staged like the kernel's checks and
`VEnv.addInduct`. The source judgment (headers typed, a common parameter telescope, constructor
types typed with the headers, raw constructor shapes) and formation (ordinary strict
positivity and universe bounds, or a finite nested expansion into an ordinary well-formed
declaration) are definitional (`SourceWF`, `FormationWF`, `Theory/Inductive/Formation.lean`),
so that a constructor field typed through a reducible alias is admitted exactly when the
kernel's `whnf`-based check admits it. The recursors are tied to the generator's output
(`RecsCompiled`), typed in the projection-stage environment (`recs_wf`), and their rules are
typed as schematic reduction rules in the recursor-stage environment (`rules_wf`,
`VEnv.PatTyped`, the typing half of `VEnv.PatWF`; the template shape is `rule_shape`).
The remaining clauses are the syntactic shapes of the kernel's recursor data: the telescope
split (`rec_shape`), one rule per constructor (`rules_nodup`), each rule firing on a
constructor constant of the right spine arity (`rules_ctor`, stated so that the auxiliary
recursors of a nested block, which fire on the constructors of a previously declared
container, are admissible) and the reduct shape (`rule_shape`). -/
structure VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop where
  /-- The source judgment: headers and constructors typed, names distinct, universes shared. -/
  source : decl.SourceWF env
  /-- Ordinary formation, or a finite nested expansion into an ordinary well-formed block. -/
  formation : decl.FormationWF env
  /-- The recursors and rules are read off a compilation of the declaration. -/
  recsCompiled : decl.RecsCompiled env
  /-- Recursors are typed once the constructors and projections are declared. -/
  recs_wf : ∀ envP, decl.addTypesCtorsProjs env = some envP →
    ∀ r ∈ decl.recs, r.toVConstVal.toVConstant.WF envP
  /-- §2.6.3: the recursor telescope split and the shapes of its motives, minors and
  major premise. -/
  rec_shape : ∀ r ∈ decl.recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  /-- A recursor has at most one rule per constructor. -/
  rules_nodup : ∀ r ∈ decl.recs, (r.rules.map (·.ctor)).Nodup
  /-- §2.6.4: every rule fires on a constructor constant of the constructor-stage environment
  whose type has `ctorParams + nfields` binders ending in a type-former application. For a
  direct block it is one of the block's own constructors; for the auxiliary recursor of a
  nested block it is a constructor of the container, declared earlier. -/
  rules_ctor : ∀ envC, decl.addTypesCtors env = some envC → ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ∃ ci, envC.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields)
  /-- §2.6.4, the reduct shape, tied to §2.6.3's constructor↔minor correspondence: the rule
  for `ru.ctor` reduces to minor `j`, a minor whose last argument is headed by `ru.ctor`,
  applied to the `nfields` fields and to exactly as many further arguments as the minor has
  binders after the fields (thesis `e_c b v`, `v::δ`). A count only: the terms `v` are
  pinned by nothing here. -/
  rule_shape : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
    r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
    ru.nfields ≤ A.piArity ∧
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j
  /-- §2.6.4 as a typing, the `VDefEq.WF` of an ι rule: as registered by `addRecRule`, in
  the recursor-stage environment, the rule is typed (`VEnv.PatTyped`) — its generic redex
  `rec params motives minors idx (c cargs fields)` and reduct `rhs params motives minors
  fields` are typed at a common type in the context of the parameters, motives, minors and
  fields. No kernel check performs it: it is the model's admissibility condition for
  registering the rule, the analogue of the thesis's regularity of reductions for the
  generic rule. -/
  rules_wf : ∀ envR, decl.addTypesCtorsProjsRecs env = some envR →
    ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
    envR.PatTyped
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true)

/-- Type formers are typed in `env` (`SourceWF`). -/
theorem VInductDecl.WF.types_wf {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    ∀ t ∈ decl.types, t.toVConstVal.toVConstant.WF env :=
  fun t ht => H.source.sourceTypes t ht

/-- Constructors are typed once the type formers are declared (`SourceWF`). -/
theorem VInductDecl.WF.ctors_wf {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    ∀ envT, decl.addTypes env = some envT →
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.toVConstant.WF envT := by
  intro envT hT t ht c hc
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  obtain ⟨envTypes', htypes', hwf⟩ := H.source.sourceConstructors
  cases Option.some.inj (htypes'.symm.trans hT)
  exact hwf c (List.mem_flatMap.2 ⟨t, ht, hc⟩)

/-- Type formers share the declaration's universe parameters. -/
theorem VInductDecl.WF.types_uvars {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    ∀ t ∈ decl.types, t.uvars = decl.uvars :=
  H.source.2.2.1

/-- So do the constructors. -/
theorem VInductDecl.WF.ctors_uvars {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.uvars = decl.uvars :=
  fun t ht c hc => H.source.2.2.2.1 c (List.mem_flatMap.2 ⟨t, ht, hc⟩)

/-- The constructor a rule of a well-formed `decl` fires on is registered in the
constructor-stage environment with a type of `CtorShape (ru.ctorParams + ru.nfields)`
(`VInductDecl.WF.rules_ctor`). -/
theorem VInductDecl.WF.rules_ctor_shape {env : VEnv} {decl : VInductDecl}
    (hwf : decl.WF env) : ∀ envC, decl.addTypesCtors env = some envC →
      ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ ci, envC.constants ru.ctor = some ci ∧
        ci.type.CtorShape (ru.ctorParams + ru.nfields) :=
  hwf.rules_ctor

/-- Source constructor typing at the exact header environment named by an
installation. -/
theorem VInductDecl.SourceWF.constructorsWF_at
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes := by
  rcases H.sourceConstructors with ⟨envTypes', htypes', hwf⟩
  cases Option.some.inj (htypes'.symm.trans htypes)
  exact hwf

/-- Both ordinary and nested formation retain the source
parameter judgment at any environment in which the headers install. -/
theorem VInductDecl.FormationWF.sourceParameterWF
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.FormationWF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    decl.SourceParameterWF env := by
  cases H with
  | ordinary H => exact H.sourceParameterWF
  | nested H hle =>
    cases H with
    | intro _ _ Hparams _ _ _ _ =>
      exact Hparams.mono_of_addConstVals hle htypes

theorem VInductDecl.WF.sourceParameterWF
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.WF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    decl.SourceParameterWF env :=
  H.formation.sourceParameterWF htypes

theorem VEnv.InstalledBelow.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : VEnv.InstalledBelow env decl) :
    VEnv.InstalledBelow env' decl := by
  cases H with
  | intro hsource hformation hcompile hblock hrecs hinstall hle =>
    exact .intro hsource hformation hcompile hblock hrecs hinstall (hle.trans henv)

/-- Every family of an installed declaration carries the declaration's
universe arity. -/
theorem VEnv.InstalledBelow.typeUvars
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl) :
    ∀ type ∈ decl.types, type.uvars = decl.uvars := by
  cases H with
  | intro Hsource _ _ _ _ _ _ => exact Hsource.2.2.1

/-- Every constructor of an installed declaration carries the declaration's
universe arity. -/
theorem VEnv.InstalledBelow.constructorUvars
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl) :
    ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars := by
  cases H with
  | intro Hsource _ _ _ _ _ _ => exact Hsource.2.2.2.1

end Lean4Lean
