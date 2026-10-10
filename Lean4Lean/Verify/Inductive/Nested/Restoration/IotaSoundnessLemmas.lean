import Lean4Lean.Theory.VExpr.TelescopeLemmas
import Lean4Lean.Theory.Inductive.RestorationNames
import Lean4Lean.Verify.Inductive.Nested.Restoration.SignatureVars
import Lean4Lean.Verify.Inductive.Install.RecursorShapesOf
import Lean4Lean.Verify.Inductive.Formation
import Lean4Lean.Theory.Inductive.RecursiveShapeCorrespondence
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Inductive.ConstructorArity
import Lean4Lean.Theory.Inductive.HypothesisTyping
import Lean4Lean.Theory.Inductive.Normalization
import Lean4Lean.Theory.Inductive.RawShape
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.SourceModelNames
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Typing.ConstructorCaptureTransport
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.ProjectionShape
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VLevel

/-! # Restoration and recursor-shape facts

Syntactic facts about the generator's variable spines, constructor field insertion, forall
telescopes, container specializations, block installation and restoration (restorable names,
restored heads, restored recursor majors and recursor types), used by both the specification
(`Theory/Inductive/RestorationProjNames.lean`) and the verification of nested inductive
declarations. -/

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem nested_vars_eq_bvarRange (n below : Nat) :
    vars n below = VExpr.bvarRange n (n + below) := by
  apply List.ext_getElem
  · simp [vars, VExpr.bvarRange]
  · intro i hi hi'
    simp [vars, VExpr.bvarRange] at hi hi' ⊢
    congr 1
    omega
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem insertBinders_getElem (F : List VExpr) (e i : Nat) (hi : i < (insertBinders F e).length) :
    (insertBinders F e)[i] = (F[i]'(by simpa [insertBinders_length] using hi)).liftN e i := by
  simp [insertBinders, List.getElem_zipIdx]

/-- Inserting `e` binders between a context `P` and a telescope prefix lifts the telescope's
domains as `insertBinders` does. -/
theorem insertBinders_liftN (F X P : List VExpr) (e : Nat) (hX : X.length = e) :
    ∀ i, i ≤ F.length → Ctx.LiftN e i ((F.take i).reverse ++ P)
      (((insertBinders F e).take i).reverse ++ X ++ P)
  | 0, _ => by simpa using Ctx.LiftN.zero (Γ := P) X hX
  | i + 1, hi => by
    have h1 := insertBinders_liftN F X P e hX i (by omega)
    have hiF : i < F.length := by omega
    have e1 : (F.take (i + 1)).reverse ++ P = F[i] :: ((F.take i).reverse ++ P) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hiF, Option.toList_some,
        List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons_append]
    have e2 : ((insertBinders F e).take (i + 1)).reverse ++ X ++ P =
        F[i].liftN e i :: (((insertBinders F e).take i).reverse ++ X ++ P) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (show i < (insertBinders F e).length by
        rw [insertBinders_length]; omega), insertBinders_getElem]
      simp
    rw [e1, e2]
    exact .succ h1
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace VerifyInductive
open InductiveSignature

theorem VExpr.instantiateForallPrefix_wrapForalls :
    ∀ (args pre : List VExpr) (body : VExpr), pre.length = args.length →
      VExpr.instantiateForallPrefix (VExpr.wrapForalls pre body) args =
        body.instOuter args
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, d :: ds, body, h => by
    have hlen : ds.length = as.length := by simpa using h
    change VExpr.instantiateForallPrefix
      ((VExpr.wrapForalls ds body).inst a) as = _
    rw [VExpr.wrapForalls_inst,
      VExpr.instantiateForallPrefix_wrapForalls as _ _ (by simpa using hlen)]
    simp [hlen]

theorem specializeType_eq_instantiateForallPrefix {type specialized : VExpr}
    {args : List VExpr} (H : specializeType type args = some specialized) :
    specialized = VExpr.instantiateForallPrefix type args := by
  unfold specializeType at H
  cases htake : type.takeForalls args.length with
  | none => simp [htake] at H
  | some out =>
    rcases out with ⟨pre, body⟩
    simp only [htake, bind, Option.bind_some, pure, Option.some.injEq] at H
    subst H
    obtain ⟨rfl, hlen⟩ := VExpr.takeForalls_rebuild htake
    rw [VExpr.instantiateForallPrefix_wrapForalls _ _ _ hlen, instantiateParams,
      VExpr.instOuter_eq_subst]
    rfl
end VerifyInductive
end Lean4Lean

namespace Lean4Lean
namespace VerifyInductive
open InductiveSignature

/-- The constructors of a direct family are the container constructors,
specialized at the arguments and closed over the given parameters. -/
theorem ContainerSpecialization.directFamily_ctors
    {a : ContainerSpecialization} {U : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.specializedFamily U params = some direct) :
    List.Forall₂ (fun ctor dc : VConstVal => dc.type = VExpr.wrapForalls params
        (VExpr.instantiateForallPrefix (ctor.type.instL a.levels) a.arguments))
      a.source.ctors direct.ctors := by
  unfold ContainerSpecialization.specializedFamily at H
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, ctors, hctors, he⟩ := H
  cases Option.some.inj he
  refine Lean4Lean.List.Forall₂.imp (fun ctor dc h => ?_) (List.mapM_eq_some.1 hctors)
  simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨spec, hspec, rfl⟩ := h
  rw [specializeType_eq_instantiateForallPrefix hspec]
end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open InductiveSignature

end Lean4Lean

namespace Lean4Lean
open InductiveSignature

theorem CompiledInductive.types_ctors {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block) :
    block.types = source.typeConstants ∧ block.ctors = source.constructorConstants :=
  ⟨H.types_eq, H.ctors_eq⟩
end Lean4Lean

namespace Lean4Lean
open InductiveSignature

end Lean4Lean

namespace Lean4Lean.InductiveSignature
open InductiveSignature

end Lean4Lean.InductiveSignature

namespace Lean4Lean.InductiveSignature
open InductiveSignature

theorem Restoration.recursorName_of_constants {r : Restoration} {env : VEnv}
    (hfresh : ∀ p ∈ r.recursors, env.constants p.1 = none)
    (hc : env.constants c = some ci) : r.recursorName c = c := by
  unfold Restoration.recursorName
  split
  · next pair hfind =>
    have hmem := List.mem_of_find?_eq_some hfind
    have heq := List.find?_some hfind
    simp only [beq_iff_eq] at heq
    have := hfresh _ hmem
    rw [heq, hc] at this
    cases this
  · rfl
end Lean4Lean.InductiveSignature

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- The constant head and parameters remaining after a family specialization
is restored. `arguments` is scoped under the recursor's common parameters,
not under the prior container's parameter telescope. -/
structure RestoredFamilyHead where
  name : Name
  levels : List VLevel
  arguments : List VExpr
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- Constructor restoration follows the same specialization table as the
family restoration. The table is generated by `compilationRestoration`. -/
def Restoration.restoredHeadName (r : Restoration) (name : Name) : Name :=
  match r.heads.find? (fun h => h.auxiliary == name) with
  | some h => h.target
  | none => name
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- Read the restored family application with the actual common parameters.
Failure remains explicit, including a partial auxiliary application. -/
def Instance.restoredFamilyHead {s : InductiveSignature}
    (g : Instance s) (r : Restoration) (owner : Fin s.families.size) :
    Option RestoredFamilyHead := do
  let application ← r.expr (g.familyApp owner (vars s.params.length 0) [])
  let (.const name levels, arguments) := application.getAppFnArgs | none
  return { name, levels, arguments }
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- Instantiating a scoped template at the parameter variables beneath `below`
further binders lifts it past those binders. -/
theorem instantiateParams_vars {e : VExpr} {n : Nat} (he : e.ClosedN n) (below : Nat) :
    instantiateParams e (vars n below) = e.liftN below := by
  change e.subst (VExpr.Subst.ofList (vars n below)) = _
  rw [VExpr.liftN_eq_subst]
  apply VExpr.subst_congr_closedN he
  intro i hi
  simp only [VExpr.Subst.ofList, VExpr.Subst.shift, vars, List.length_map, List.length_reverse,
    List.length_range, hi, dite_true, List.getElem_map, List.getElem_reverse, List.getElem_range]
  congr 1
  omega
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_recursorMajor_source (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size)
    (hfind : r.heads.find? (fun h => h.auxiliary == s.families[owner].name) = none)
    (hname : r.recursorName s.families[owner].name = s.families[owner].name) :
    r.expr (g.recursorMajor owner) = some (g.recursorMajor owner) := by
  simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp]
  rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars]
  simp only [Fin.getElem_fin] at hfind hname
  simp [Restoration.expr.go, hfind, hname]
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_recursorMajor_auxiliary (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size) {h : HeadSpecialization}
    (hfind : r.heads.find? (fun h => h.auxiliary == s.families[owner].name) = some h)
    (hlevels : g.levels.length = h.uvars) (hnparams : h.nparams = s.params.length)
    (hclosed : ∀ arg ∈ h.arguments, arg.ClosedN h.nparams) :
    r.expr (g.recursorMajor owner) =
      some (VExpr.mkApps (.const h.target (h.levels.map (·.inst g.levels)))
        (h.arguments.map (fun arg => (arg.instL g.levels).liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0)) := by
  simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp]
  rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars]
  have hlen : (vars s.params.length
      (s.families.size + s.constructors.size + s.families[owner].indices.length)).length =
      h.nparams := by simp [vars, hnparams]
  simp only [Fin.getElem_fin] at hfind hlen ⊢
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, Restoration.expr.go, hfind,
    HeadSpecialization.apply, hlevels, bne_self_eq_false, List.length_append, Bool.false_or]
  rw [if_neg (by simp; omega), List.take_left' hlen, List.drop_left' hlen]
  congr 3
  apply List.map_congr_left
  intro arg harg
  rw [← hnparams]
  exact instantiateParams_vars (hclosed arg harg).instL _
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
open InductiveSignature

theorem VInductDecl.RawCtorShape.constructorShape
    {decl : VInductDecl} {family : VInductiveType} {ctor : VConstVal} {env : VEnv}
    (H : decl.RawCtorShape family ctor) (hnames : decl.sourceNames.Nodup)
    (hfamily : family ∈ decl.types)
    (hlookup : env.constants ctor.name = some ⟨decl.uvars, ctor.type⟩) :
    ∃ fields, Nonempty (VConstructorShape env ctor.name decl.uvars decl.nparams
      fields family.numIndices family.name) := by
  rcases H with ⟨doms, result, htype, hparamsLe, hvalid, hhead⟩
  rcases hvalid with ⟨target, htarget, htargetName, levels, hfn, hlevels, hargs, hparams⟩
  rcases htargetName with hnone | htargetName
  · cases hnone
  have heq : target = family := VInductDecl.type_eq_of_mem_name hnames htarget hfamily
    (Option.some.inj htargetName).symm
  subst target
  change result.getAppFnArgs.2.length = decl.nparams + family.numIndices at hargs
  change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (doms.length - decl.nparams) at hparams
  refine ⟨doms.length - decl.nparams, ⟨{
    type := ctor.type
    const := hlookup
    doms := doms
    indices := result.getAppFnArgs.2.drop decl.nparams
    type_eq := ?_
    doms_length := by omega
    indices_length := by simp only [List.length_drop, hargs]; omega }⟩⟩
  rw [htype]
  congr 1
  calc
    result = VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 :=
      (VExpr.mkApps_getAppFnArgs_eq result).symm
    _ = VExpr.mkApps (.const family.name (VLevel.params decl.uvars))
        ((result.getAppFnArgs.2.take decl.nparams) ++ result.getAppFnArgs.2.drop decl.nparams) := by
      rw [List.take_append_drop, hhead]
    _ = _ := by
      rw [hparams]
      congr 2
      exact InductiveSignature.nested_vars_eq_bvarRange _ _
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

@[simp] theorem vars_length (n k : Nat) : (vars n k).length = n := by
  simp [vars]
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem nested_vars_map_liftN (n k : Nat) :
    (vars n 0).map (fun arg => arg.liftN k) = vars n k := by
  simp only [vars, List.map_map, Function.comp_def, VExpr.liftN, liftVar]
  apply List.map_congr_left
  intro i _
  simp [Nat.add_comm]
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.find?_of_nodup {heads : List HeadSpecialization}
    (hnodup : (heads.map (·.auxiliary)).Nodup) {x : HeadSpecialization}
    (hx : x ∈ heads) : heads.find? (fun y => y.auxiliary == x.auxiliary) = some x := by
  induction heads with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : (y.auxiliary == x.auxiliary) = false := by
        have : y.auxiliary ≠ x.auxiliary := fun h =>
          hnodup.1 (h ▸ List.mem_map_of_mem hx)
        simpa using this
      simp only [hne]
      exact ih hnodup.2 hx
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem declaration_ctor_mem (s : InductiveSignature) (index : Fin s.constructors.size)
    (howner : s.constructors[index].owner.val < s.declaration.types.length) :
    ({ name := s.constructors[index].name, uvars := s.uvars,
        type := s.constructorType s.constructors[index] } : VConstVal) ∈
      (s.declaration.types[s.constructors[index].owner.val]'howner).ctors := by
  simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx,
    List.mem_filterMap]
  refine ⟨s.constructors[index], Array.getElem_mem_toList _, ?_⟩
  simp
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem Restoration.expr_wrapLams_eq (r : Restoration) (doms : List VExpr) (body : VExpr) :
    r.expr (VExpr.wrapLams doms body) =
      (doms.mapM r.expr).bind fun doms' =>
        (r.expr body).map (VExpr.wrapLams doms') := by
  induction doms with
  | nil => cases hb : r.expr body <;> simp [VExpr.wrapLams, hb]
  | cons d ds ih =>
    change Restoration.expr.go r (.lam d (VExpr.wrapLams ds body)) [] = _
    simp only [Restoration.expr.go, List.mapM_cons]
    rw [← Restoration.expr_eq_go, ← Restoration.expr_eq_go, ih]
    cases hd : r.expr d <;> cases hds : ds.mapM r.expr <;>
      cases hb : r.expr body <;> simp [VExpr.mkApps, VExpr.wrapLams]
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem _root_.List.mapM_append_eq_some {f : α → Option β} {a b : List α} {c : List β}
    (h : (a ++ b).mapM f = some c) :
    ∃ ca cb, a.mapM f = some ca ∧ b.mapM f = some cb ∧ c = ca ++ cb := by
  rw [List.mapM_append] at h
  cases ha : a.mapM f with
  | none => simp [ha] at h
  | some ca =>
    cases hb : b.mapM f with
    | none => simp [ha, hb] at h
    | some cb =>
      simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨ca, cb, rfl, rfl, h.symm⟩

/-- Substitution through a telescope, binder by binder. -/
theorem _root_.Lean4Lean.VExpr.wrapForalls_subst_doms (σ : VExpr.Subst) :
    ∀ (ds : List VExpr) (b : VExpr), ∃ ds' b',
      (VExpr.wrapForalls ds b).subst σ = VExpr.wrapForalls ds' b' ∧
      ds'.length = ds.length ∧
      ∀ i (h : i < ds.length) (h' : i < ds'.length), ds'[i] = ds[i].subst (σ.liftN i)
  | [], b => ⟨[], b.subst σ, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | d :: ds, b => by
    obtain ⟨ds', b', heq, hlen, hget⟩ := VExpr.wrapForalls_subst_doms σ.lift ds b
    refine ⟨d.subst σ :: ds', b', ?_, by simp [hlen], ?_⟩
    · show VExpr.forallE (d.subst σ) ((VExpr.wrapForalls ds b).subst σ.lift) = _
      rw [heq]; rfl
    · intro i h h'
      cases i with
      | zero => rfl
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [hget i (by simpa using h) (by simpa using h'), VExpr.Subst.lift_liftN]

/-- Substituting the outer `args` beneath `i` binders is `instOuter` with the
lifted arguments followed by the `i` bound variables. -/
theorem _root_.Lean4Lean.VExpr.subst_liftN_ofList {d : VExpr} {args : List VExpr} {i : Nat}
    (hd : d.ClosedN (args.length + i)) :
    d.subst ((VExpr.Subst.ofList args).liftN i) =
      d.instOuter ((args.map (·.liftN i)) ++ VExpr.bvarRange i i) := by
  rw [VExpr.instOuter_eq_subst]
  apply VExpr.subst_congr_closedN hd
  intro k hk
  have hL : k < ((args.map (·.liftN i)) ++ VExpr.bvarRange i i).length := by simp; omega
  rw [VExpr.Subst.liftN_apply, VExpr.Subst.ofList_lt _ hL]
  have hlen : ((args.map (·.liftN i)) ++ VExpr.bvarRange i i).length = args.length + i := by simp
  split
  · rename_i hki
    rw [List.getElem_append_right (by simp; omega)]
    rw [VExpr.bvarRange_getElem _ _ _ (by simp; omega)]
    congr 1; simp; omega
  · rename_i hki
    rw [List.getElem_append_left (by simp; omega), List.getElem_map,
      VExpr.Subst.ofList_lt _ (by omega)]
    congr 2; simp; omega

/-- Lifting at a cutoff commutes with `instOuter` of a closed term. -/
theorem _root_.Lean4Lean.VExpr.liftN_at_instOuter {X : VExpr} {xs : List VExpr}
    (hX : X.ClosedN xs.length) (e k : Nat) :
    (X.instOuter xs).liftN e k = X.instOuter (xs.map (·.liftN e k)) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_eq_subst_at]
  erw [VExpr.subst_subst]
  apply VExpr.subst_congr_closedN hX
  intro i hi
  simp only [VExpr.Subst.comp, VExpr.Subst.ofList_lt _ hi, List.length_map,
    VExpr.Subst.ofList_lt (xs.map _) (by simpa using hi), List.getElem_map,
    VExpr.liftN_eq_subst_at]

/-- **The iota shape of a restored generated equation**, given the
restoration of its constructor application. -/
theorem Restoration.restored_iota_shape {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (index : Fin s.constructors.size) {env₀ env : VEnv} {df : VDefEq}
    {ctorName : Name} {levels : List VLevel} {params : List VExpr}
    (heq : r.equation (g.equation index) = some df)
    (hdef : env.defeqs df)
    (henv₀ : VEnv.WF env₀) (hle : env₀ ≤ env) (hconsts : ∀ n, env.constants n = env₀.constants n)
    (hrecType : ∃ type, r.expr (g.recursorType s.constructors[index].owner) = some type ∧
      env₀.constants (r.recursorName (g.recursorName s.constructors[index].owner)) =
        some ⟨g.uvars, type⟩)
    (hindices : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length)
    (hnotHead : r.heads.find?
      (fun h => h.auxiliary == g.recursorName s.constructors[index].owner) = none)
    (happ : r.expr (g.constructorApp s.constructors[index]
      (s.families.size + s.constructors.size) 0) =
      some (VExpr.mkApps (.const ctorName levels)
        (params.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
          vars s.constructors[index].fields.length 0)))
    (hheadsClosed : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (hfieldDoms : ∃ RP RF, s.params.mapM r.expr = some RP ∧
      (s.fieldTypes s.constructors[index]).mapM r.expr = some RF ∧
      ∀ ctorUvars ctorDoms ctorBody,
        env₀.constants ctorName = some ⟨ctorUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ →
        ∀ (_hclen : ctorDoms.length = params.length + s.constructors[index].fields.length)
          i (hi : i < s.constructors[index].fields.length) (hi' : i < RF.length),
          env₀.IsDefEqU g.uvars
            (((RF.map (·.instL g.levels)).take i).reverse ++ (RP.map (·.instL g.levels)).reverse)
            ((RF.map (·.instL g.levels))[i]'(by simpa using hi'))
            (((ctorDoms[params.length + i]'(by omega)).instL levels).instOuter
              ((params.map (·.liftN i)) ++ VExpr.bvarRange i i))) :
    Nonempty (VIotaRuleShape env (r.recursorName (g.recursorName s.constructors[index].owner))
      g.uvars s.params.length params.length s.families.size s.constructors.size
      s.families[s.constructors[index].owner].indices.length ctorName levels
      s.constructors[index].fields.length df params) := by
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  let lhsBody := VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
    (vars (s.params.length + extra) nf ++ indices ++ [major])
  let rhsBody := VExpr.mkApps (.bvar (nf + s.constructors.size - 1 - index.val))
    (vars nf 0 ++ (Instance.recursiveFields ctor).map fun (field, r) => g.recursiveCall ctor field r)
  let typeBody := VExpr.mkApps
    (.bvar (nf + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
    (indices ++ [major])
  have hdomains : domains.length =
      s.params.length + s.families.size + s.constructors.size + nf := by
    simp [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes, nf, Nat.add_assoc]
  have hlhs : (g.equation index).lhs = VExpr.wrapLams domains lhsBody := rfl
  have hrhs : (g.equation index).rhs = VExpr.wrapLams domains rhsBody := rfl
  have htype : (g.equation index).type = VExpr.wrapForalls domains typeBody := rfl
  have huv : (g.equation index).uvars = g.uvars := rfl
  simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at heq
  cases hl : r.expr (g.equation index).lhs with
  | none => simp [hl] at heq
  | some lhs =>
  cases hr : r.expr (g.equation index).rhs with
  | none => simp [hl, hr] at heq
  | some rhs =>
  cases ht : r.expr (g.equation index).type with
  | none => simp [hl, hr, ht] at heq
  | some type =>
  simp only [hl, hr, ht, Option.bind_some, Option.some.injEq] at heq
  subst heq
  rw [hlhs, r.expr_wrapLams_eq] at hl
  rw [hrhs, r.expr_wrapLams_eq] at hr
  rw [htype, r.expr_wrapForalls] at ht
  cases hD : domains.mapM r.expr with
  | none => simp [hD] at hl
  | some D' =>
  simp only [hD, Option.bind_some] at hl hr ht
  cases hlb : r.expr lhsBody with
  | none => simp [hlb] at hl
  | some lb =>
  cases hrb : r.expr rhsBody with
  | none => simp [hrb] at hr
  | some rb =>
  cases htb : r.expr typeBody with
  | none => simp [htb] at ht
  | some tb =>
  simp only [hlb, hrb, htb, Option.map_some, Option.some.injEq] at hl hr ht
  have hDlen : D'.length = domains.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hD)).symm
  -- the restored left-hand side body
  have hlb' := hlb
  simp only [lhsBody] at hlb'
  rw [r.expr_mkApps, List.mapM_append, List.mapM_append, r.mapM_expr_vars] at hlb'
  cases hI : indices.mapM r.expr with
  | none => simp [hI] at hlb'
  | some I' =>
  have hmajor : [major].mapM r.expr = some [VExpr.mkApps (.const ctorName levels)
      (params.map (fun arg => arg.liftN (extra + nf)) ++ vars nf 0)] := by
    have happ' : r.expr major = some (VExpr.mkApps (.const ctorName levels)
        (params.map (fun arg => arg.liftN (extra + nf)) ++ vars nf 0)) := happ
    simp [List.mapM_cons, happ']
  have hnotHead' : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none :=
    hnotHead
  simp only [hI, hmajor, Option.bind_some, Option.pure_def, Option.bind_eq_bind,
    Restoration.expr.go, hnotHead'] at hlb'
  have hIlen : I'.length = indices.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hI)).symm
  have hpat : lb = VExpr.mkApps
      (.const (r.recursorName (g.recursorName s.constructors[index].owner))
        (VLevel.params g.uvars))
      (VExpr.bvarRange (s.params.length + s.families.size + s.constructors.size) D'.length ++
        I' ++
        [VExpr.mkApps (.const ctorName levels)
          ((params.map fun p => p.liftN (s.families.size + s.constructors.size +
            s.constructors[index].fields.length)) ++
            VExpr.bvarRange s.constructors[index].fields.length
              s.constructors[index].fields.length)]) := by
    rw [← Option.some.inj hlb']
    simp only [hDlen, hdomains, nested_vars_eq_bvarRange, Nat.add_zero, List.append_assoc,
      extra, nf, ctor, Nat.add_assoc]
  have hDlen' : D'.length = s.params.length + s.families.size + s.constructors.size +
      s.constructors[index].fields.length := by rw [hDlen, hdomains]
  have hIlen' : I'.length = s.families[s.constructors[index].owner].indices.length := by
    rw [hIlen]; simpa [indices, ctor] using hindices
  refine ⟨{
    defeq := hdef
    uvars := huv
    doms := D'
    lhsBody := lb
    rhsBody := rb
    typeBody := tb
    lhs_eq := hl.symm
    rhs_eq := hr.symm
    type_eq := ht.symm
    doms_length := hDlen'
    indexArgs := I'
    indexArgs_length := hIlen'
    lhs_pattern := hpat
    rec_doms := ?_
    ctor_doms := ?_ }⟩
  · -- the parameter, motive and minor binders are restored as in the recursor
    intro recDoms recBody hc hlenR j hj
    obtain ⟨type, hty, hconstR⟩ := hrecType
    rw [hconsts, hconstR] at hc
    obtain ⟨pre, major', hpre, -, htypeEq⟩ := r.expr_recursorType_eq_some hty
    have htype' : VExpr.wrapForalls (pre ++ [major'])
        (g.recursorBody s.constructors[index].owner) = VExpr.wrapForalls recDoms recBody := by
      have := congrArg VConstant.type (Option.some.inj hc)
      simpa [htypeEq] using this
    have hprelen : pre.length = s.params.length + s.families.size +
        s.constructors.size + s.families[s.constructors[index].owner].indices.length := by
      rw [← g.recursorPrefix_length s.constructors[index].owner]
      exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
    obtain ⟨hrec, -⟩ := VExpr.wrapForalls_inj_of_length (by simp [hprelen, hlenR]) htype'
    subst hrec
    obtain ⟨A, B, hA, -, rfl⟩ := List.mapM_append_eq_some
      (a := g.params ++ g.motives ++ g.minors) hD
    obtain ⟨A', C, hA', -, rfl⟩ := List.mapM_append_eq_some
      (a := g.params ++ g.motives ++ g.minors) (by simpa [Instance.recursorPrefix] using hpre)
    rw [hA] at hA'
    cases hA'
    have hAlen : A.length = s.params.length + s.families.size + s.constructors.size := by
      rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hA)]
      simp [Instance.params, Instance.motives, Instance.minors]; omega
    rw [List.getElem?_append_left (by omega), List.append_assoc,
      List.getElem?_append_left (by omega)]
  · -- the field binders agree with the constructor's field domains
    intro ctorUvars ctorDoms ctorBody hc hclen i hi hd hcd
    rw [hconsts] at hc
    obtain ⟨RP, RF, hRP, hRF, Hfd⟩ := hfieldDoms
    have hRFlen : RF.length = nf := by
      rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRF)]
      simp [InductiveSignature.fieldTypes, nf, ctor]
    have hRPlen : RP.length = s.params.length :=
      (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP)).symm
    have h := Hfd ctorUvars ctorDoms ctorBody hc hclen i hi (by omega)
    -- the restored rule's binders
    obtain ⟨DA, DB, hDA, hDB, hD'⟩ := List.mapM_append_eq_some
      (a := g.params ++ g.motives ++ g.minors) hD
    obtain ⟨DP, DM, hDP, hDM, rfl⟩ := List.mapM_append_eq_some
      (a := g.params) (b := g.motives ++ g.minors) (by simpa [List.append_assoc] using hDA)
    have hDP' : DP = RP.map (·.instL g.levels) :=
      Option.some.inj (hDP.symm.trans (Restoration.mapM_expr_instL r hRP g.levels))
    have hDB' : DB = insertBinders (RF.map (·.instL g.levels)) extra :=
      Option.some.inj (hDB.symm.trans (Restoration.mapM_expr_insertBinders r hheadsClosed
        (Restoration.mapM_expr_instL r hRF g.levels) extra))
    subst hDP' hDB' hD'
    have hDMlen : DM.length = extra := by
      rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hDM)]
      simp [Instance.motives, Instance.minors, extra]
    have hW := h.weakN henv₀.ordered (insertBinders_liftN (RF.map (·.instL g.levels))
      DM.reverse (RP.map (·.instL g.levels)).reverse extra (by simp [hDMlen]) i
      (by simp; omega))
    have hmi : s.params.length + s.families.size + s.constructors.size + i =
        (RP.map (·.instL g.levels) ++ DM).length + i := by
      simp [hRPlen, hDMlen, extra]; omega
    have hctx : ((RP.map (·.instL g.levels) ++ DM ++
        insertBinders (RF.map (·.instL g.levels)) extra).take
          (s.params.length + s.families.size + s.constructors.size + i)).reverse =
        ((insertBinders (RF.map (·.instL g.levels)) extra).take i).reverse ++ DM.reverse ++
          (RP.map (·.instL g.levels)).reverse := by
      rw [hmi, List.take_append, List.take_of_length_le (by simp), Nat.add_sub_cancel_left]
      simp [List.reverse_append, List.append_assoc]
    have hdom : (RP.map (·.instL g.levels) ++ DM ++
        insertBinders (RF.map (·.instL g.levels)) extra)[
          s.params.length + s.families.size + s.constructors.size + i]'hd =
        ((RF.map (fun x : VExpr => x.instL g.levels))[i]'(by simp; omega)).liftN extra i := by
      rw [List.getElem_append_right (by simp [hRPlen, hDMlen, extra]; omega),
        insertBinders_getElem]
      congr 2 <;> simp [hRPlen, hDMlen, extra] <;> omega
    have hclosed := (VEnv.VEnv.constant_doms_closed henv₀ hc (ls := []) (U := 0)
      (by simp)).1 (params.length + i) (by simp; omega)
    simp only [List.getElem_map] at hclosed
    have hclosed' : ((ctorDoms[params.length + i]'(by omega)).instL levels).ClosedN
        (((params.map (·.liftN i)) ++ VExpr.bvarRange i i).length) := by
      simp only [List.length_append, List.length_map, VExpr.bvarRange_length]
      exact (VExpr.ClosedN.instL_rev hclosed).instL
    rw [VExpr.liftN_at_instOuter hclosed', List.map_append, List.map_map] at hW
    have hps : (params.map ((fun x => x.liftN extra i) ∘ fun p => p.liftN i)) =
        params.map fun p => p.liftN (s.families.size + s.constructors.size + i) := by
      apply List.map_congr_left
      intro p _
      simp only [Function.comp]
      rw [VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)]
      congr 1; simp [extra]; omega
    have hbv : (VExpr.bvarRange i i).map (fun x => x.liftN extra i) = VExpr.bvarRange i i := by
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_map]
      rw [VExpr.bvarRange_getElem _ _ _ (by simpa using h2)]
      simp only [VExpr.liftN]
      have hj : j < i := by simpa using h2
      rw [liftVar_lt (show i - 1 - j < i by omega)]
    rw [hps, hbv] at hW
    rw [hctx, hdom]
    exact (hW.mono hle)
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- **Field count of a restored rule.** In a well-formed environment, a typed
equation with the iota shape of a recursor whose constructor has a rigid
major family supplies exactly the constructor's fields. -/
theorem VIotaRuleShape.fieldCount {env env' : VEnv} (henv : env.WF)
    {recName ctorName indName : Name}
    {recUvars nparams cnparams nmotives nminors nindices nf ctorUvars fields nindices' : Nat}
    {ctorLevels indLevels : List VLevel} {df : VDefEq} {ctorParams : List VExpr}
    (I : VIotaRuleShape env' recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nf df ctorParams)
    (hwf : df.WF env)
    (hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices
      indName indLevels ctorParams)
    (hctor : VConstructorShape env ctorName ctorUvars cnparams fields nindices' indName)
    (hrigid : env.Rigid indName) : fields = nf := by
  have hleft := hwf.1
  rw [I.lhs_eq, I.type_eq, I.uvars] at hleft
  rcases VEnv.HasType.wrapLams_inv henv (by trivial) hleft with ⟨hctx, hbody⟩
  rw [I.lhs_pattern] at hbody
  have hpre : (VExpr.bvarRange (nparams + nmotives + nminors) I.doms.length ++
      I.indexArgs).length = nparams + nmotives + nminors + nindices := by
    simp [I.indexArgs_length]
  have hbody' : env.HasType recUvars (I.doms.reverse ++ [])
      (VExpr.mkApps (.const recName (VLevel.params recUvars))
        ((VExpr.bvarRange (nparams + nmotives + nminors) I.doms.length ++ I.indexArgs) ++
          [VExpr.mkApps (.const ctorName ctorLevels)
            ((ctorParams.map fun p => p.liftN (nmotives + nminors + nf)) ++
              VExpr.bvarRange nf nf)])) I.typeBody := by
    simpa only [List.append_assoc] using hbody
  have ⟨_, hmajor, _⟩ := hrec.spine_typing henv hctx VLevel.params_wf VLevel.params_length
    hpre ⟨_, hbody'⟩
  have hsat := hctor.saturated_of_hasType henv hctx hrigid hmajor
  have hlen : ctorParams.length = cnparams := hrec.ctorParams_length
  simp only [List.length_append, List.length_map, VExpr.bvarRange_length, hlen] at hsat
  omega
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

theorem ContainerSpecialization.directFamily_numIndices
    {a : ContainerSpecialization} {uvars : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.specializedFamily uvars params = some direct) :
    direct.numIndices = a.source.numIndices := by
  unfold ContainerSpecialization.specializedFamily at H
  cases htype : specializeType (a.source.type.instL a.levels) a.arguments with
  | none => simp [htype] at H
  | some type =>
    simp [htype] at H
    rcases H with ⟨ctors, _, H⟩
    cases H
    rfl
end InductiveSignature
end Lean4Lean

namespace Lean4Lean
open InductiveSignature

theorem CompiledInductive.sourceFacts {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block) :
    source.sourceNames.Nodup ∧
      (∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor) ∧
      ∀ ctor ∈ source.constructorConstants, ctor.uvars = source.uvars := by
  induction H using CompiledInductive.rec
    (motive_2 := fun _ _ _ => True) with
  | intro Hd _ _ =>
    exact ⟨Hd.sourceWF.2.1, Hd.sourceParameters.rawCtorShape, Hd.sourceWF.2.2.2.1⟩
  | replay _ _ _ ih => exact ih
  | nil => trivial
  | cons _ _ _ _ _ _ _ => trivial
end Lean4Lean

namespace Lean4Lean
open InductiveSignature

/-- The constructors of a declaration installed by `addInduct` are constants of the output. -/
theorem VEnv.addInduct_ctor_const {base installed : VEnv} {decl : VInductDecl}
    (h : base.addInduct decl = some installed) {c : VConstVal}
    (hc : c ∈ decl.constructorConstants) : installed.constants c.name = some c.toVConstant := by
  obtain ⟨envT, envC, envR, _, hC, hR, hP⟩ := VEnv.addInduct_stages h
  rw [VInductDecl.addCtors_eq_addConstVals] at hC
  exact ((VEnv.addProjs_le.trans (VEnv.addRecs_le hR)).trans (VEnv.addRules_le hP)).constants
    (VEnv.addConstVals_get hC hc)

/-- The constructors of a certified container are installed with their
recorded values and have the raw constructor shape of their container. -/
theorem ContainersInstalled.containerConstructors {env : VEnv} :
    ∀ {auxiliaries : List InductiveSignature.ContainerSpecialization},
      ContainersInstalled env auxiliaries →
      ∀ a ∈ auxiliaries, a.container.sourceNames.Nodup ∧
        ∀ type ∈ a.container.types, ∀ ctor ∈ type.ctors,
          a.container.RawCtorShape type ctor ∧
          env.constants ctor.name = some ⟨a.container.uvars, ctor.type⟩
  | [], _ => by intro a ha; cases ha
  | a0 :: rest, H => by
    cases H with
    | cons hcompiled _ _ hinstall hle hrest =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · have Hsrc := hcompiled.sourceFacts
      obtain ⟨-, hctors⟩ := hcompiled.types_ctors
      refine ⟨Hsrc.1, fun type htype ctor hctor => ⟨?_, ?_⟩⟩
      · exact Hsrc.2.1 type htype ctor hctor
      · have hmem : ctor ∈ a.container.constructorConstants :=
          List.mem_flatMap.mpr ⟨type, htype, hctor⟩
        have h := hle.constants (VEnv.addInduct_ctor_const hinstall hmem)
        have hu : ctor.uvars = a.container.uvars := Hsrc.2.2 ctor hmem
        rw [h, ← hu]
    · exact ContainersInstalled.containerConstructors hrest a ha
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- **The constructor shape of a restored rule's constructor.** Every
generated constructor restores to a constant (a source constructor, or a
constructor of a certified container) whose stored type has the constructor
shape at the restored family head of its owner, for some field count. -/
theorem CompilationData.restoredConstructorShape
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (Hcert : ContainersInstalled env auxiliaries)
    {envTypes envCtors : VEnv}
    (hadded : env.addConstVals source.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals source.constructorConstants = some envCtors)
    (hfresh : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envTypes.constants n = none)
    (hfreshCtors : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none)
    {venv : VEnv} (hle : envCtors ≤ venv)
    (index : Fin s.constructors.size) (owner : Fin s.families.size)
    (howner : s.constructors[index].owner = owner) :
    ∃ head : RestoredFamilyHead,
      g.restoredFamilyHead (compilationRestoration source auxiliaries) owner = some head ∧
      ∃ fields, Nonempty (VConstructorShape venv
        ((compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name)
        head.levels.length head.arguments.length fields
        s.families[owner].indices.length head.name) := by
  have henvLE : env ≤ envCtors :=
    (VEnv.addConstVals_le hadded).trans (VEnv.addConstVals_le hctorsAdded)
  obtain ⟨envTypes', direct, hadded', hdirect, hwellFormed, Hfam⟩ := Hd.correspondence
  have henv : envTypes = envTypes' := Option.some.inj (hadded.symm.trans hadded')
  subst henv
  obtain ⟨envExpandedTypes, -, Hadm⟩ := Hd.admissible
  have hlevelsLen : g.levels.length = source.uvars :=
    Hadm.levels_length.trans (Hd.model.uvars.trans Hd.uvars)
  have hnp : s.params.length = source.nparams := Hd.model.nparams.trans Hd.nparams
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have hown : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have hown' : owner.val < (source.types ++ direct).length := hlen ▸ hown
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val hown hown'
  have hdeclName : (s.declaration.types[owner.val]'hown).name = s.families[owner].name := by
    simp [InductiveSignature.declaration]
  have hdeclIdx : (s.declaration.types[owner.val]'hown).numIndices =
      s.families[owner].indices.length := by
    simp [InductiveSignature.declaration]
  have hname : s.families[owner].name = ((source.types ++ direct)[owner.val]'hown').name :=
    hdeclName.symm.trans Hat.name
  have hidxEq : ((source.types ++ direct)[owner.val]'hown').numIndices =
      s.families[owner].indices.length := Hat.indices.symm.trans hdeclIdx
  obtain ⟨sc, hsc, hscName⟩ : ∃ sc ∈ ((source.types ++ direct)[owner.val]'hown').ctors,
      s.constructors[index].name = sc.name := by
    have hmem := declaration_ctor_mem s index (by rw [howner]; exact hown)
    simp only [howner] at hmem
    obtain ⟨sc, hsc, hsc'⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l Hat.constructors _ hmem
    exact ⟨sc, hsc, hsc'.1⟩
  have hfreshHeads : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envTypes.constants n = none :=
    fun n hn => hfresh n (List.mem_append_left _ hn)
  have hfreshRecs : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envTypes.constants p.1 = none :=
    fun p hp => hfresh p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hfreshHeadsC : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envCtors.constants n = none :=
    fun n hn => hfreshCtors n (List.mem_append_left _ hn)
  by_cases hsrc : owner.val < source.types.length
  · -- a source family
    have hname' : s.families[owner].name = (source.types[owner.val]'hsrc).name := by
      rw [hname, List.getElem_append_left hsrc]
    have hconst : envTypes.constants s.families[owner].name =
        some (source.types[owner.val]'hsrc).toVConstVal.toVConstant := by
      rw [hname']
      exact VEnv.addConstVals_get hadded
        (List.mem_map.mpr ⟨_, List.getElem_mem hsrc, rfl⟩)
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = none := by
      apply Restoration.heads_find?_eq_none
      intro hmem
      rw [hfreshHeads _ hmem] at hconst
      cases hconst
    have hrecName : (compilationRestoration source auxiliaries).recursorName
        s.families[owner].name = s.families[owner].name :=
      Restoration.recursorName_of_constants hfreshRecs hconst
    refine ⟨⟨s.families[owner].name, g.levels, vars s.params.length 0⟩, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, hrecName]
      simp only [Option.bind_eq_bind, Option.bind_some,
        VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · rw [List.getElem_append_left hsrc] at hsc hidxEq
      have hscMem : sc ∈ source.constructorConstants :=
        List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrc, hsc⟩
      have hcconst : envCtors.constants s.constructors[index].name =
          some sc.toVConstant := by
        rw [hscName]
        exact VEnv.addConstVals_get hctorsAdded hscMem
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none := by
        apply Restoration.heads_find?_eq_none
        intro hmem
        rw [hfreshHeadsC _ hmem] at hcconst
        cases hcconst
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = sc.name := by
        simp only [Restoration.restoredHeadName, hcfind]
        exact hscName
      have hu : sc.uvars = source.uvars := Hd.sourceWF.2.2.2.1 sc hscMem
      have hlookup : venv.constants sc.name = some ⟨source.uvars, sc.type⟩ := by
        have h := hle.constants (VEnv.addConstVals_get hctorsAdded hscMem)
        rw [h, ← hu]
      have hraw := Hd.sourceParameters.rawCtorShape _ (List.getElem_mem hsrc) sc hsc
      rcases VInductDecl.RawCtorShape.constructorShape hraw Hd.sourceWF.2.1
        (List.getElem_mem hsrc) hlookup with ⟨fields, hshape⟩
      refine ⟨fields, ?_⟩
      rw [hchead]
      simpa only [vars_length, hlevelsLen, hnp, hidxEq, hname'] using hshape
  · -- an auxiliary family
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := hown'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hauxLen : auxiliaries.length = direct.length :=
      Lean4Lean.List.Forall₂.length_eq hFdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length := hauxLen ▸ hidx
    let a := auxiliaries[owner.val - source.types.length]'hidx'
    have ha : a ∈ auxiliaries := List.getElem_mem hidx'
    have hdf : a.specializedFamily source.uvars s.params =
        some (direct[owner.val - source.types.length]'hidx) :=
      Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hdirectName : (direct[owner.val - source.types.length]'hidx).name = a.auxiliary :=
      ContainerSpecialization.directFamily_name hdf
    have hname' : s.families[owner].name = a.auxiliary := by
      rw [hname, List.getElem_append_right hge]
      exact hdirectName
    let h : HeadSpecialization :=
      ⟨a.auxiliary, source.uvars, source.nparams, a.source.name, a.levels, a.arguments⟩
    have hmem : h ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = some h := by
      rw [hname']
      exact Restoration.find?_of_nodup Hd.restorationScoped.1 hmem
    obtain ⟨hargLen, hargsClosed, hlevLen, -, -⟩ := hwellFormed a ha
    have hclosedL : ∀ arg ∈ a.arguments, (arg.instL g.levels).ClosedN s.params.length := by
      intro arg harg
      rw [hnp]
      exact (hargsClosed arg harg).instL
    have hinst : ∀ k, a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
        (vars source.nparams k)) =
          a.arguments.map (fun arg => (arg.instL g.levels).liftN k) := by
      intro k
      apply List.map_congr_left
      intro arg harg
      rw [← hnp, instantiateParams_vars (hclosedL arg harg)]
    refine ⟨⟨a.source.name, a.levels.map (·.inst g.levels),
      a.arguments.map (fun arg => arg.instL g.levels)⟩, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, HeadSpecialization.apply,
        hlevelsLen, h, bne_self_eq_false, Bool.false_or, vars_length, hnp]
      rw [if_neg (by simp), List.take_of_length_le (by simp),
        List.drop_of_length_le (by simp), hinst 0]
      simp only [VExpr.liftN_zero, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        List.append_nil, VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · rw [List.getElem_append_right hge] at hsc hidxEq
      rw [ContainerSpecialization.directFamily_numIndices hdf] at hidxEq
      have hheads := a.directFamily_heads hdf
      simp only [ContainerSpecialization.heads, List.map_cons, List.map_map,
        List.cons.injEq] at hheads
      have hscMem : sc.name ∈ a.source.ctors.map a.constructorName := by
        have : sc.name ∈ (direct[owner.val - source.types.length]'hidx).ctors.map (·.name) :=
          List.mem_map_of_mem hsc
        rw [← hheads.2] at this
        simpa [Function.comp_def] using this
      obtain ⟨ctor, hctor, hctorName'⟩ := List.mem_map.mp hscMem
      have hcName : s.constructors[index].name = a.constructorName ctor :=
        hscName.trans hctorName'.symm
      let hc : HeadSpecialization :=
        ⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels,
          a.arguments⟩
      have hcmem : hc ∈ (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some hc := by
        rw [hcName]
        exact Restoration.find?_of_nodup Hd.restorationScoped.1 hcmem
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = ctor.name := by
        simp only [Restoration.restoredHeadName, hcfind, hc]
      obtain ⟨hnodupC, hctorsC⟩ := Hcert.containerConstructors a ha
      have hsrcMem : a.source ∈ a.container.types := List.getElem_mem _
      obtain ⟨hraw, hlookup⟩ := hctorsC a.source hsrcMem ctor hctor
      rcases VInductDecl.RawCtorShape.constructorShape hraw hnodupC hsrcMem
        ((henvLE.trans hle).constants hlookup) with ⟨fields, hshape⟩
      refine ⟨fields, ?_⟩
      rw [hchead]
      simpa only [List.length_map, hlevLen, hargLen, hidxEq] using hshape

/-- **Field domains of a restored rule's constructor.** The restoration of the
normalized constructor type is definitionally equal to the type of the
constant it restores to (`RestoresType`), specialized at the restored family
head's arguments for a constructor of a certified container. Injectivity of
`∀` identifies the field domains binder by binder, in the restored
parameters followed by the earlier restored fields. -/
theorem CompilationData.restoredConstructorFieldDomains
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (Hcert : ContainersInstalled env auxiliaries)
    {envTypes envCtors : VEnv}
    (hadded : env.addConstVals source.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals source.constructorConstants = some envCtors)
    (hfresh : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envTypes.constants n = none)
    (hfreshCtors : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none)
    {venv : VEnv} (hle : envCtors ≤ venv) (hvenv : venv.WF)
    (hlevelsWF : ∀ l ∈ g.levels, l.WF g.uvars)
    (index : Fin s.constructors.size) (owner : Fin s.families.size)
    (howner : s.constructors[index].owner = owner) :
    ∃ head : RestoredFamilyHead,
      g.restoredFamilyHead (compilationRestoration source auxiliaries) owner = some head ∧
      ∃ RP RF, s.params.mapM (compilationRestoration source auxiliaries).expr = some RP ∧
        (s.fieldTypes s.constructors[index]).mapM
          (compilationRestoration source auxiliaries).expr = some RF ∧
        ∀ ctorUvars ctorDoms ctorBody,
          venv.constants ((compilationRestoration source auxiliaries).restoredHeadName
            s.constructors[index].name) =
              some ⟨ctorUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ →
          ∀ (_hclen : ctorDoms.length =
            head.arguments.length + s.constructors[index].fields.length)
            i (hi : i < s.constructors[index].fields.length) (hi' : i < RF.length),
            venv.IsDefEqU g.uvars
              (((RF.map (·.instL g.levels)).take i).reverse ++
                (RP.map (·.instL g.levels)).reverse)
              ((RF.map (·.instL g.levels))[i]'(by simpa using hi'))
              (((ctorDoms[head.arguments.length + i]'(by omega)).instL head.levels).instOuter
                ((head.arguments.map (·.liftN i)) ++ VExpr.bvarRange i i)) := by
  have henvLE : env ≤ envCtors :=
    (VEnv.addConstVals_le hadded).trans (VEnv.addConstVals_le hctorsAdded)
  obtain ⟨envTypes', direct, hadded', hdirect, hwellFormed, Hfam⟩ := Hd.correspondence
  have henv : envTypes = envTypes' := Option.some.inj (hadded.symm.trans hadded')
  subst henv
  have htypesLE : envTypes ≤ venv := (VEnv.addConstVals_le hctorsAdded).trans hle
  obtain ⟨envExpandedTypes, -, Hadm⟩ := Hd.admissible
  have hlevelsLen : g.levels.length = source.uvars :=
    Hadm.levels_length.trans (Hd.model.uvars.trans Hd.uvars)
  have hnp : s.params.length = source.nparams := Hd.model.nparams.trans Hd.nparams
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have hown : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have hown' : owner.val < (source.types ++ direct).length := hlen ▸ hown
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val hown hown'
  have hdeclName : (s.declaration.types[owner.val]'hown).name = s.families[owner].name := by
    simp [InductiveSignature.declaration]
  have hname : s.families[owner].name = ((source.types ++ direct)[owner.val]'hown').name :=
    hdeclName.symm.trans Hat.name
  obtain ⟨sc, hsc, hscName, hRT⟩ : ∃ sc ∈ ((source.types ++ direct)[owner.val]'hown').ctors,
      s.constructors[index].name = sc.name ∧
      RestoresType (compilationRestoration source auxiliaries) envTypes source.uvars
        (s.constructorType s.constructors[index]) sc.type := by
    have hmem := declaration_ctor_mem s index (by rw [howner]; exact hown)
    simp only [howner] at hmem
    obtain ⟨sc, hsc, hsc'⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l Hat.constructors _ hmem
    exact ⟨sc, hsc, hsc'.1, hsc'.2.2⟩
  -- the restored normalized constructor type
  obtain ⟨R0, hR0, hdef0⟩ := hRT
  unfold InductiveSignature.constructorType at hR0
  rw [Restoration.expr_wrapForalls, Option.bind_eq_some_iff] at hR0
  obtain ⟨RD, hRD, hR0⟩ := hR0
  obtain ⟨Rb, -, hRb⟩ := Option.map_eq_some_iff.mp hR0
  subst hRb
  obtain ⟨RP, RF, hRP, hRF, rfl⟩ := List.mapM_append_eq_some hRD
  have hRPlen : RP.length = s.params.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP)).symm
  have hRFlen : RF.length = s.constructors[index].fields.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRF)]
    simp [InductiveSignature.fieldTypes]
  have hdefV : venv.IsDefEqU g.uvars []
      (VExpr.wrapForalls ((RP ++ RF).map (·.instL g.levels)) (Rb.instL g.levels))
      (sc.type.instL g.levels) := by
    have h := (hdef0.instL hlevelsWF).mono htypesLE
    simpa only [List.map_nil, VExpr.instL_wrapForalls] using h
  -- every presentation of the restored target as a telescope gives the field domains
  have finish : ∀ (Tdoms : List VExpr) (Tb : VExpr),
      sc.type.instL g.levels = VExpr.wrapForalls Tdoms Tb →
      Tdoms.length = s.params.length + s.constructors[index].fields.length →
      ∀ i (hi' : i < RF.length) (hT : s.params.length + i < Tdoms.length),
        venv.IsDefEqU g.uvars
          (((RF.map (·.instL g.levels)).take i).reverse ++ (RP.map (·.instL g.levels)).reverse)
          ((RF.map (·.instL g.levels))[i]'(by simpa using hi')) Tdoms[s.params.length + i] := by
    intro Tdoms Tb hT hTlen i hi' hTi
    rw [hT] at hdefV
    have h := VEnv.IsDefEqU.wrapForalls_doms hvenv (Γ := []) trivial
      (by simp [hRPlen, hRFlen, hTlen]) hdefV (s.params.length + i)
      (by simp [hRPlen]; omega) hTi
    have htake : ((RP ++ RF).map (·.instL g.levels)).take (s.params.length + i) =
        RP.map (·.instL g.levels) ++ (RF.map (·.instL g.levels)).take i := by
      rw [List.map_append, List.take_append, List.take_of_length_le (by simp [hRPlen])]
      simp [hRPlen]
    have hget : ((RP ++ RF).map (·.instL g.levels))[s.params.length + i]'(by
        simp [hRPlen]; omega) = (RF.map (·.instL g.levels))[i]'(by simpa using hi') := by
      simp only [List.map_append]
      rw [List.getElem_append_right (by simp [hRPlen])]
      simp [hRPlen]
    rw [htake, hget, List.reverse_append, List.append_nil] at h
    exact h
  have hfreshHeads : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envTypes.constants n = none :=
    fun n hn => hfresh n (List.mem_append_left _ hn)
  have hfreshRecs : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envTypes.constants p.1 = none :=
    fun p hp => hfresh p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hfreshHeadsC : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envCtors.constants n = none :=
    fun n hn => hfreshCtors n (List.mem_append_left _ hn)
  by_cases hsrc : owner.val < source.types.length
  · -- a source family
    have hname' : s.families[owner].name = (source.types[owner.val]'hsrc).name := by
      rw [hname, List.getElem_append_left hsrc]
    have hconst : envTypes.constants s.families[owner].name =
        some (source.types[owner.val]'hsrc).toVConstVal.toVConstant := by
      rw [hname']
      exact VEnv.addConstVals_get hadded
        (List.mem_map.mpr ⟨_, List.getElem_mem hsrc, rfl⟩)
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = none := by
      apply Restoration.heads_find?_eq_none
      intro hmem
      rw [hfreshHeads _ hmem] at hconst
      cases hconst
    have hrecName : (compilationRestoration source auxiliaries).recursorName
        s.families[owner].name = s.families[owner].name :=
      Restoration.recursorName_of_constants hfreshRecs hconst
    refine ⟨⟨s.families[owner].name, g.levels, vars s.params.length 0⟩, ?_,
      RP, RF, hRP, hRF, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, hrecName]
      simp only [Option.bind_eq_bind, Option.bind_some,
        VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · intro ctorUvars ctorDoms ctorBody hc hclen i hi hi'
      rw [List.getElem_append_left hsrc] at hsc
      have hscMem : sc ∈ source.constructorConstants :=
        List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrc, hsc⟩
      have hcconst : envCtors.constants s.constructors[index].name =
          some sc.toVConstant := by
        rw [hscName]
        exact VEnv.addConstVals_get hctorsAdded hscMem
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none := by
        apply Restoration.heads_find?_eq_none
        intro hmem
        rw [hfreshHeadsC _ hmem] at hcconst
        cases hcconst
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = sc.name := by
        simp only [Restoration.restoredHeadName, hcfind]
        exact hscName
      have hlookup : venv.constants sc.name = some sc.toVConstant :=
        hle.constants (VEnv.addConstVals_get hctorsAdded hscMem)
      rw [hchead] at hc
      have hty : sc.type = VExpr.wrapForalls ctorDoms ctorBody := by
        have := congrArg VConstant.type (Option.some.inj (hlookup.symm.trans hc))
        simpa using this
      simp only [vars_length] at hclen ⊢
      have hTi : s.params.length + i < (ctorDoms.map (·.instL g.levels)).length := by
        simp; omega
      have h := finish (ctorDoms.map (·.instL g.levels)) (ctorBody.instL g.levels)
        (by rw [hty, VExpr.instL_wrapForalls]) (by simp; omega) i hi' hTi
      have hclosed := (VEnv.VEnv.constant_doms_closed hvenv hc
        hlevelsWF).1 (s.params.length + i) hTi
      simp only [List.getElem_map] at hclosed
      have hid := VExpr.instOuter_insert_bvars _ s.params.length i 0 hclosed
      simp only [Nat.zero_add, VExpr.liftN_zero] at hid
      have hv : vars s.params.length 0 = VExpr.bvarRange s.params.length s.params.length := by
        rw [nested_vars_eq_bvarRange, Nat.add_zero]
      rw [← hv] at hid
      rw [hid]
      simpa using h
  · -- an auxiliary family
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := hown'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hauxLen : auxiliaries.length = direct.length :=
      Lean4Lean.List.Forall₂.length_eq hFdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length := hauxLen ▸ hidx
    let a := auxiliaries[owner.val - source.types.length]'hidx'
    have ha : a ∈ auxiliaries := List.getElem_mem hidx'
    have hdf : a.specializedFamily source.uvars s.params =
        some (direct[owner.val - source.types.length]'hidx) :=
      Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hdirectName : (direct[owner.val - source.types.length]'hidx).name = a.auxiliary :=
      ContainerSpecialization.directFamily_name hdf
    have hname' : s.families[owner].name = a.auxiliary := by
      rw [hname, List.getElem_append_right hge]
      exact hdirectName
    let h : HeadSpecialization :=
      ⟨a.auxiliary, source.uvars, source.nparams, a.source.name, a.levels, a.arguments⟩
    have hmem : h ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = some h := by
      rw [hname']
      exact Restoration.find?_of_nodup Hd.restorationScoped.1 hmem
    obtain ⟨hargLen, hargsClosed, hlevLen, -, -⟩ := hwellFormed a ha
    have hclosedL : ∀ arg ∈ a.arguments, (arg.instL g.levels).ClosedN s.params.length := by
      intro arg harg
      rw [hnp]
      exact (hargsClosed arg harg).instL
    have hinst : ∀ k, a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
        (vars source.nparams k)) =
          a.arguments.map (fun arg => (arg.instL g.levels).liftN k) := by
      intro k
      apply List.map_congr_left
      intro arg harg
      rw [← hnp, instantiateParams_vars (hclosedL arg harg)]
    refine ⟨⟨a.source.name, a.levels.map (·.inst g.levels),
      a.arguments.map (fun arg => arg.instL g.levels)⟩, ?_, RP, RF, hRP, hRF, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, HeadSpecialization.apply,
        hlevelsLen, h, bne_self_eq_false, Bool.false_or, vars_length, hnp]
      rw [if_neg (by simp), List.take_of_length_le (by simp),
        List.drop_of_length_le (by simp), hinst 0]
      simp only [VExpr.liftN_zero, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        List.append_nil, VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · intro ctorUvars ctorDoms ctorBody hc hclen i hi hi'
      rw [List.getElem_append_right hge] at hsc
      have hheads := a.directFamily_heads hdf
      simp only [ContainerSpecialization.heads, List.map_cons, List.map_map,
        List.cons.injEq] at hheads
      have Hct := VerifyInductive.ContainerSpecialization.directFamily_ctors hdf
      obtain ⟨j, hj, hscj⟩ := List.getElem_of_mem hsc
      have hjs : j < a.source.ctors.length := by
        rw [Lean4Lean.List.Forall₂.length_eq Hct]; exact hj
      let ctor := a.source.ctors[j]'hjs
      have hctor : ctor ∈ a.source.ctors := List.getElem_mem hjs
      have hsct := Lean4Lean.List.forall₂_getElem Hct j hjs hj
      rw [hscj] at hsct
      have hctorName' : a.constructorName ctor = sc.name := by
        have hn := congrArg (fun l => l[j]?) hheads.2
        simp only [List.getElem?_map, List.getElem?_eq_getElem hjs,
          List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq,
          Function.comp_def] at hn
        rw [hn, hscj]
      have hcName : s.constructors[index].name = a.constructorName ctor :=
        hscName.trans hctorName'.symm
      let hc' : HeadSpecialization :=
        ⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels,
          a.arguments⟩
      have hcmem : hc' ∈ (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some hc' := by
        rw [hcName]
        exact Restoration.find?_of_nodup Hd.restorationScoped.1 hcmem
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = ctor.name := by
        simp only [Restoration.restoredHeadName, hcfind, hc']
      obtain ⟨-, hctorsC⟩ := Hcert.containerConstructors a ha
      have hsrcMem : a.source ∈ a.container.types := List.getElem_mem _
      obtain ⟨-, hlookup⟩ := hctorsC a.source hsrcMem ctor hctor
      have hlookup' := (henvLE.trans hle).constants hlookup
      rw [hchead] at hc
      have hty : ctor.type = VExpr.wrapForalls ctorDoms ctorBody := by
        have := congrArg VConstant.type (Option.some.inj (hlookup'.symm.trans hc))
        simpa using this
      have hclen' : ctorDoms.length =
          a.arguments.length + s.constructors[index].fields.length := by
        simpa using hclen
      -- the specialized constructor type, as a telescope
      have hcn : a.arguments.length ≤ (ctorDoms.map (·.instL a.levels)).length := by
        simp; omega
      have hspec : VExpr.instantiateForallPrefix (ctor.type.instL a.levels) a.arguments =
          (VExpr.wrapForalls ((ctorDoms.map (·.instL a.levels)).drop a.arguments.length)
            (ctorBody.instL a.levels)).instOuter a.arguments := by
        rw [hty, VExpr.instL_wrapForalls,
          ← List.take_append_drop a.arguments.length (ctorDoms.map (·.instL a.levels)),
          VExpr.wrapForalls_append, VerifyInductive.VExpr.instantiateForallPrefix_wrapForalls _ _ _
            (by simp; omega)]
        simp only [List.take_append_drop]
      obtain ⟨ds', b', hsub, hds'len, hds'get⟩ := VExpr.wrapForalls_subst_doms
        (VExpr.Subst.ofList (a.arguments.map (·.instL g.levels)))
        (((ctorDoms.map (·.instL a.levels)).drop a.arguments.length).map (·.instL g.levels))
        ((ctorBody.instL a.levels).instL g.levels)
      have hT : sc.type.instL g.levels =
          VExpr.wrapForalls (s.params.map (·.instL g.levels) ++ ds') b' := by
        rw [hsct, VExpr.instL_wrapForalls, hspec, VExpr.instL_instOuter,
          VExpr.instL_wrapForalls, VExpr.instOuter_eq_subst, hsub, VExpr.wrapForalls_append]
      have hTlen : (s.params.map (·.instL g.levels) ++ ds').length =
          s.params.length + s.constructors[index].fields.length := by
        rw [List.length_append, hds'len]
        simp only [List.length_map, List.length_drop, hclen']
        omega
      have hTi : s.params.length + i < (s.params.map (·.instL g.levels) ++ ds').length := by
        rw [hTlen]; omega
      have h := finish _ _ hT hTlen i hi' hTi
      have hdi : i < ds'.length := by rw [hds'len]; simp; omega
      have hget : (s.params.map (·.instL g.levels) ++ ds')[s.params.length + i]'hTi =
          ds'[i]'hdi := by
        rw [List.getElem_append_right (by simp)]
        simp
      rw [hget, hds'get i (by simp; omega) hdi] at h
      have hdom : (((ctorDoms.map (·.instL a.levels)).drop a.arguments.length).map
          (·.instL g.levels))[i]'(by simp; omega) =
          (ctorDoms[a.arguments.length + i]'(by omega)).instL (a.levels.map (·.inst g.levels)) := by
        simp [VExpr.instL_instL]
      have hclosed := (VEnv.VEnv.constant_doms_closed hvenv hc
        hlevelsWF).1 (a.arguments.length + i) (by simp; omega)
      have hclosed' : ((ctorDoms[a.arguments.length + i]'(by omega)).instL
          (a.levels.map (·.inst g.levels))).ClosedN
          ((a.arguments.map (·.instL g.levels)).length + i) := by
        simp only [List.length_map]
        exact (VExpr.ClosedN.instL_rev (by simpa using hclosed)).instL
      rw [hdom, VExpr.subst_liftN_ofList hclosed'] at h
      simpa [List.map_map, Function.comp_def] using h

end InductiveSignature
end Lean4Lean

namespace Lean4Lean
namespace InductiveSignature
open InductiveSignature

/-- **The restored family head of a compiled owner.** For a source family it
is the family itself at the instance's universe levels and the parameter
variables; for an auxiliary family it is the specialized container. Every
constructor of the owner restores to the restored constructor head applied
to the head's arguments and the fields. -/
theorem CompilationData.restoredFamilyHead_spec
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    {envTypes envCtors : VEnv}
    (hadded : env.addConstVals source.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals source.constructorConstants = some envCtors)
    (hfresh : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envTypes.constants n = none)
    (hfreshCtors : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none)
    (owner : Fin s.families.size) :
    ∃ head : RestoredFamilyHead,
      g.restoredFamilyHead (compilationRestoration source auxiliaries) owner = some head ∧
      head.name = (compilationRestoration source auxiliaries).restoredHeadName
        s.families[owner].name ∧
      (∀ level ∈ head.levels, level.WF g.uvars) ∧
      (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
      (compilationRestoration source auxiliaries).expr (g.familyApp owner
        (vars s.params.length
          (s.families.size + s.constructors.size + s.families[owner].indices.length))
        (vars s.families[owner].indices.length 0)) =
        some (VExpr.mkApps (.const head.name head.levels)
          (head.arguments.map (fun arg => arg.liftN
            (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
            vars s.families[owner].indices.length 0)) ∧
      ∀ index : Fin s.constructors.size, s.constructors[index].owner = owner →
        (((compilationRestoration source auxiliaries).heads.find?
            (fun h => h.auxiliary == s.families[owner].name) = none ∧
          (compilationRestoration source auxiliaries).restoredHeadName
            s.constructors[index].name = s.constructors[index].name) ∨
          ∃ a ∈ auxiliaries, s.families[owner].name = a.auxiliary ∧
            ∃ ctor ∈ a.source.ctors, s.constructors[index].name = a.constructorName ctor) ∧
        (compilationRestoration source auxiliaries).expr
          (g.constructorApp s.constructors[index] (s.families.size + s.constructors.size) 0) =
          some (VExpr.mkApps (.const ((compilationRestoration source auxiliaries).restoredHeadName
              s.constructors[index].name) head.levels)
            (head.arguments.map (fun arg => arg.liftN
              (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
              vars s.constructors[index].fields.length 0)) := by
  obtain ⟨envTypes', direct, hadded', hdirect, hwellFormed, Hfam⟩ := Hd.correspondence
  have henv : envTypes = envTypes' := Option.some.inj (hadded.symm.trans hadded')
  subst henv
  obtain ⟨envExpandedTypes, -, Hadm⟩ := Hd.admissible
  have hlevelsLen : g.levels.length = source.uvars :=
    Hadm.levels_length.trans (Hd.model.uvars.trans Hd.uvars)
  have hnp : s.params.length = source.nparams := Hd.model.nparams.trans Hd.nparams
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have howner : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have howner' : owner.val < (source.types ++ direct).length := hlen ▸ howner
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val howner howner'
  have hdeclName : (s.declaration.types[owner.val]'howner).name = s.families[owner].name := by
    simp [InductiveSignature.declaration]
  have hname : s.families[owner].name = ((source.types ++ direct)[owner.val]'howner').name :=
    hdeclName.symm.trans Hat.name
  -- every constructor of the owner names a constructor of the corresponding family
  have hctorName : ∀ index : Fin s.constructors.size, s.constructors[index].owner = owner →
      ∃ sc ∈ ((source.types ++ direct)[owner.val]'howner').ctors,
        s.constructors[index].name = sc.name := by
    intro index hindex
    have hmem := declaration_ctor_mem s index (by rw [hindex]; exact howner)
    simp only [hindex] at hmem
    obtain ⟨sc, hsc, hsc'⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l Hat.constructors _ hmem
    exact ⟨sc, hsc, hsc'.1⟩
  have hfreshHeads : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envTypes.constants n = none :=
    fun n hn => hfresh n (List.mem_append_left _ hn)
  have hfreshRecs : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envTypes.constants p.1 = none :=
    fun p hp => hfresh p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hfreshHeadsC : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envCtors.constants n = none :=
    fun n hn => hfreshCtors n (List.mem_append_left _ hn)
  have hfreshRecsC : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envCtors.constants p.1 = none :=
    fun p hp => hfreshCtors p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  by_cases hsrc : owner.val < source.types.length
  · -- a source family
    have hname' : s.families[owner].name = (source.types[owner.val]'hsrc).name := by
      rw [hname, List.getElem_append_left hsrc]
    have hconst : envTypes.constants s.families[owner].name =
        some (source.types[owner.val]'hsrc).toVConstVal.toVConstant := by
      rw [hname']
      exact VEnv.addConstVals_get hadded
        (List.mem_map.mpr ⟨_, List.getElem_mem hsrc, rfl⟩)
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = none := by
      apply Restoration.heads_find?_eq_none
      intro hmem
      rw [hfreshHeads _ hmem] at hconst
      cases hconst
    have hrecName : (compilationRestoration source auxiliaries).recursorName
        s.families[owner].name = s.families[owner].name :=
      Restoration.recursorName_of_constants hfreshRecs hconst
    refine ⟨⟨s.families[owner].name, g.levels, vars s.params.length 0⟩, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, hrecName]
      simp only [Option.bind_eq_bind, Option.bind_some,
        VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · simp only [Restoration.restoredHeadName, hfind]
    · exact Hadm.levels_wf
    · intro arg harg
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at harg
      obtain ⟨i, hi, rfl⟩ := harg
      simp [VExpr.ClosedN, hi]
    · rw [show g.familyApp owner _ _ = g.recursorMajor owner from rfl,
        (compilationRestoration source auxiliaries).expr_recursorMajor_source g owner hfind
          hrecName]
      simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp,
        nested_vars_map_liftN]
    · intro index hindex
      obtain ⟨sc, hsc, hscName⟩ := hctorName index hindex
      rw [List.getElem_append_left hsrc] at hsc
      have hcconst : envCtors.constants s.constructors[index].name =
          some sc.toVConstant := by
        rw [hscName]
        exact VEnv.addConstVals_get hctorsAdded
          (List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrc, hsc⟩)
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none := by
        apply Restoration.heads_find?_eq_none
        intro hmem
        rw [hfreshHeadsC _ hmem] at hcconst
        cases hcconst
      have hcrec : (compilationRestoration source auxiliaries).recursorName
          s.constructors[index].name = s.constructors[index].name :=
        Restoration.recursorName_of_constants hfreshRecsC hcconst
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = s.constructors[index].name := by
        simp only [Restoration.restoredHeadName, hcfind]
      refine ⟨.inl ⟨hfind, hchead⟩, ?_⟩
      rw [hchead]
      simp only [Instance.constructorApp]
      rw [(compilationRestoration source auxiliaries).expr_mkApps, List.mapM_append,
        (compilationRestoration source auxiliaries).mapM_expr_vars,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Restoration.expr.go, hcfind, hcrec, nested_vars_map_liftN, Nat.add_zero]
      rfl
  · -- an auxiliary family
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := howner'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hauxLen : auxiliaries.length = direct.length :=
      Lean4Lean.List.Forall₂.length_eq hFdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length := hauxLen ▸ hidx
    let a := auxiliaries[owner.val - source.types.length]'hidx'
    have ha : a ∈ auxiliaries := List.getElem_mem hidx'
    have hdf : a.specializedFamily source.uvars s.params =
        some (direct[owner.val - source.types.length]'hidx) :=
      Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hdirectName : (direct[owner.val - source.types.length]'hidx).name = a.auxiliary :=
      ContainerSpecialization.directFamily_name hdf
    have hname' : s.families[owner].name = a.auxiliary := by
      rw [hname, List.getElem_append_right hge]
      exact hdirectName
    let h : HeadSpecialization :=
      ⟨a.auxiliary, source.uvars, source.nparams, a.source.name, a.levels, a.arguments⟩
    have hmem : h ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = some h := by
      rw [hname']
      exact Restoration.find?_of_nodup Hd.restorationScoped.1 hmem
    obtain ⟨-, hargsClosed, -, hlevelsWF, -⟩ := hwellFormed a ha
    have hclosed : ∀ arg ∈ h.arguments, arg.ClosedN h.nparams := hargsClosed
    have hclosedL : ∀ arg ∈ a.arguments, (arg.instL g.levels).ClosedN s.params.length := by
      intro arg harg
      rw [hnp]
      exact (hargsClosed arg harg).instL
    have hinst : ∀ k, a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
        (vars source.nparams k)) =
          a.arguments.map (fun arg => (arg.instL g.levels).liftN k) := by
      intro k
      apply List.map_congr_left
      intro arg harg
      rw [← hnp, instantiateParams_vars (hclosedL arg harg)]
    refine ⟨⟨a.source.name, a.levels.map (·.inst g.levels),
      a.arguments.map (fun arg => arg.instL g.levels)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, HeadSpecialization.apply,
        hlevelsLen, h, bne_self_eq_false, Bool.false_or, vars_length, hnp]
      rw [if_neg (by simp), List.take_of_length_le (by simp),
        List.drop_of_length_le (by simp), hinst 0]
      simp only [VExpr.liftN_zero, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        List.append_nil, VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · simp only [Restoration.restoredHeadName, hfind, h]
    · intro level hlevel
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hlevel
      exact VLevel.WF.inst Hadm.levels_wf
    · intro arg' harg'
      obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp harg'
      exact hclosedL arg harg
    · rw [show g.familyApp owner _ _ = g.recursorMajor owner from rfl,
        (compilationRestoration source auxiliaries).expr_recursorMajor_auxiliary g owner hfind
          hlevelsLen hnp.symm hclosed]
      simp only [List.map_map, Function.comp_def, h]
    · intro index hindex
      obtain ⟨sc, hsc, hscName⟩ := hctorName index hindex
      rw [List.getElem_append_right hge] at hsc
      have hheads := a.directFamily_heads hdf
      simp only [ContainerSpecialization.heads, List.map_cons, List.map_map,
        List.cons.injEq] at hheads
      have hscMem : sc.name ∈ a.source.ctors.map a.constructorName := by
        have : sc.name ∈ (direct[owner.val - source.types.length]'hidx).ctors.map (·.name) :=
          List.mem_map_of_mem hsc
        rw [← hheads.2] at this
        simpa [Function.comp_def] using this
      obtain ⟨ctor, hctor, hctorName'⟩ := List.mem_map.mp hscMem
      have hcName : s.constructors[index].name = a.constructorName ctor :=
        hscName.trans hctorName'.symm
      let hc : HeadSpecialization :=
        ⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels,
          a.arguments⟩
      have hcmem : hc ∈ (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some hc := by
        rw [hcName]
        exact Restoration.find?_of_nodup Hd.restorationScoped.1 hcmem
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = ctor.name := by
        simp only [Restoration.restoredHeadName, hcfind, hc]
      refine ⟨.inr ⟨a, ha, hname', ctor, hctor, hcName⟩, ?_⟩
      rw [hchead]
      simp only [Instance.constructorApp]
      rw [(compilationRestoration source auxiliaries).expr_mkApps, List.mapM_append,
        (compilationRestoration source auxiliaries).mapM_expr_vars,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Restoration.expr.go, hcfind, HeadSpecialization.apply,
        hlevelsLen, hc, bne_self_eq_false, Bool.false_or, List.length_append, vars_length,
        hnp, Nat.add_zero]
      rw [if_neg (by simp), List.take_left' (vars_length _ _),
        List.drop_left' (vars_length _ _), hinst]
      simp only [List.map_map, Function.comp_def]
end InductiveSignature
end Lean4Lean
