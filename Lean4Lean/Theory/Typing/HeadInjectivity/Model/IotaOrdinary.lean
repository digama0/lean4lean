import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaPat
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.CtorNames

/-! # The static data of the ι rules of an ordinary block

For the generated equation `g.equation index` of an ordinary compilation, the generated
recursor's type carries the `IotaStatic` data of the rule (`Instance.iotaStatic`): its telescope
is `recDoms`, its major domain is the family applied to the parameter and index variables, and
the constructor's minor premise `g.minor` records the constructor's indices, which the equation's
lead `eqLead` carries lifted over the motives and minors. -/

namespace Lean4Lean

theorem VExpr.mkApps_snoc_last_inj {f f' x x' : VExpr} {l l' : List VExpr}
    (h : VExpr.mkApps f (l ++ [x]) = VExpr.mkApps f' (l' ++ [x'])) : x = x' := by
  rw [VExpr.mkApps_snoc, VExpr.mkApps_snoc] at h
  injection h

theorem VExpr.mkApps_const_name_inj {c c' : Name} {ls ls' : List VLevel} {a a' : List VExpr}
    (h : VExpr.mkApps (.const c ls) a = VExpr.mkApps (.const c' ls') a') : c = c' := by
  have := congrArg VExpr.getAppFn h
  simp only [VExpr.getAppFn_mkApps, VExpr.getAppFn] at this
  injection this

/-- `vars` unfolded, as a rewriting lemma. -/
theorem InductiveSignature.vars_unfold (count below : Nat) :
    vars count below = (List.range count).reverse.map fun i => VExpr.bvar (below + i) := rfl

namespace InductiveSignature.Instance
open VEnv.Model

variable {s : InductiveSignature} (g : Instance s)

theorem recDoms_minor (owner : Fin s.families.size) (i : Fin s.constructors.size) :
    (g.recDoms owner)[s.params.length + s.families.size + i.val]? =
      some (g.minor s.constructors[i] i.val) := by
  have hpl : g.params.length = s.params.length := params_length g
  have hml : g.motives.length = s.families.size := motives_length g
  have hnl : g.minors.length = s.constructors.size := minors_length g
  simp only [recDoms, List.append_assoc]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
    List.getElem?_append_left (by omega)]
  simp only [hpl, hml, show s.params.length + s.families.size + i.val - s.params.length -
    s.families.size = i.val by omega, minors, List.getElem?_map, List.getElem?_zipIdx]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

theorem minor_endsInCtor {c : Name} {ctor : Constructor s.families.size} {prior : Nat}
    (h : EndsInCtor c (g.minor ctor prior)) : c = ctor.name := by
  obtain ⟨f, args, lsC, margs, e⟩ := h
  simp only [minor, constructorApp] at e
  rw [VExpr.mkApps_snoc, piBody_wrapForalls_app, ← VExpr.mkApps_snoc] at e
  exact VExpr.mkApps_const_name_inj (VExpr.mkApps_snoc_last_inj e).symm


/-- **The `IotaStatic` data of a generated equation.** -/
theorem iotaStatic (index : Fin s.constructors.size)
    (harity : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length)
    (hnames : ∀ i : Fin s.constructors.size,
      s.constructors[i].name = s.constructors[index].name → i = index) :
    IotaStatic (g.recursor s.constructors[index].owner).toVConstant s.constructors[index].name
      (s.params.length + (s.families.size + s.constructors.size))
      s.families[s.constructors[index].owner].indices.length
      s.constructors[index].fields.length
      (g.eqDoms index) (g.recDoms s.constructors[index].owner)
      (g.recBody s.constructors[index].owner) s.families[s.constructors[index].owner].name
      g.levels
      (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length) ++
        vars s.families[s.constructors[index].owner].indices.length 0)
      (g.eqLead index) := by
  have hpos := g.recDoms_minor s.constructors[index].owner index
  refine ⟨g.eqDoms_length index, g.recursorType_eq_recDoms _, by rw [g.recDoms_length],
    by rw [show s.params.length + (s.families.size + s.constructors.size) +
      s.families[s.constructors[index].owner].indices.length = s.params.length +
      (s.families.size + s.constructors.size) +
      s.families[s.constructors[index].owner].indices.length from rfl]; exact g.recDoms_major _,
    s.params.length, s.params.length + s.families.size + index.val,
    (recursiveFields s.constructors[index]).length,
    s.constructors[index].fields.length + (recursiveFields s.constructors[index]).length +
      index.val + (s.families.size - 1 - s.constructors[index].owner.val),
    s.params.length + s.constructors[index].owner.val,
    s.constructors[index].indices.map (·.instL g.levels),
    insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + index.val) ++
      (recursiveFields s.constructors[index]).zipIdx.map (fun ((field, r), i) =>
        g.hypothesis s.constructors[index] index.val i field r),
    vars s.params.length ((s.families.size + index.val) + s.constructors[index].fields.length +
        (recursiveFields s.constructors[index]).length) ++
      vars s.constructors[index].fields.length (recursiveFields s.constructors[index]).length,
    g.levels,
    by omega, by have := index.isLt; omega, by simpa using harity, ?_,
    by have := s.constructors[index].owner.isLt; omega, ?_, ⟨vars (insertBinders (s.families[s.constructors[index].owner].indices.map
      (·.instL g.levels)) (s.families.size + s.constructors.size)).length 1 ++ [.bvar 0], ?_⟩,
    ?_, ?_, ?_⟩
  · simp [insertBinders, fieldTypes]
  · simp only [insertBinders, List.length_append, List.length_map, List.length_zipIdx, fieldTypes]
    have := s.constructors[index].owner.isLt
    omega
  · simp only [recBody, insertBinders, List.length_map, List.length_zipIdx]
    congr 2
    have := s.constructors[index].owner.isLt
    omega
  · rw [hpos]
    simp only [minor, constructorApp, List.map_map, Option.some.injEq, List.length_map,
      List.length_zipIdx, show s.params.length + s.families.size + index.val - s.params.length =
        s.families.size + index.val by omega, Function.comp_def]
  · simp only [eqLead, iotaLead, eqIndices, vars_unfold, List.map_map]
    congr 1
    · congr 1; funext i; simp; omega
    · congr 1; funext e; simp only [Function.comp]; congr 1; omega
  · intro pos' A h1 h2 hA hE
    obtain ⟨i', rfl⟩ : ∃ i', pos' = s.params.length + s.families.size + i' :=
      ⟨pos' - (s.params.length + s.families.size), by omega⟩
    have hi' : i' < s.constructors.size := by omega
    rw [g.recDoms_minor _ ⟨i', hi'⟩] at hA
    cases hA
    have := hnames ⟨i', hi'⟩ (g.minor_endsInCtor hE.endsInCtor).symm
    have : i' = index.val := congrArg Fin.val this
    omega

end InductiveSignature.Instance


namespace VEnv.Model
open InductiveSignature

theorem lamArity_wrapLams (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapLams ds b).lamArity = ds.length + b.lamArity := by
  induction ds with
  | nil => simp [VExpr.wrapLams]
  | cons d ds ih =>
    simp only [VExpr.wrapLams, List.foldr_cons, VExpr.lamArity, List.length_cons] at ih ⊢
    rw [ih]; omega

theorem lamArity_mkApps_bvar (i : Nat) : ∀ args : List VExpr,
    (VExpr.mkApps (.bvar i) args).lamArity = 0 := by
  intro args
  induction args using List.reverseRecOn with
  | nil => rfl
  | snoc args a _ => rw [VExpr.mkApps_snoc]; rfl

theorem getAppArgs_length_eq_of_mkApps_bvar {i j : Nat} {a b : List VExpr}
    (h : VExpr.mkApps (.bvar i) a = VExpr.mkApps (.bvar j) b) : a.length = b.length := by
  have := congrArg VExpr.getAppArgs h
  simp only [VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append] at this
  rw [this]

/-- **The data of an ordinary rule**: the generated equation it is read off, the generated
recursor, and the split of its counts. -/
theorem ordinary_rule_data {base env : VEnv} {decl expanded : VInductDecl}
    {s : InductiveSignature} {g : InductiveSignature.Instance s} {block : VInductBlock}
    (hdecl : decl.WF env) (hrecsOf : decl.RecsOf block)
    (C : InductiveSignature.CompilationData base decl expanded s g [] block)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules)
    {df : VDefEq} (hdf : df ∈ block.rules) (H : VRecRule.OfEquation rec ru df) :
    ∃ index : Fin s.constructors.size, df = g.equation index ∧
      rec.toVConstVal = g.recursor s.constructors[index].owner ∧
      ru.ctor = s.constructors[index].name ∧ ru.rhs = (g.equation index).rhs ∧
      rec.numParams + rec.numMotives + rec.numMinors =
        s.params.length + (s.families.size + s.constructors.size) ∧
      rec.numIndices = s.families[s.constructors[index].owner].indices.length ∧
      ru.ctorParams = s.params.length ∧ ru.nfields = s.constructors[index].fields.length ∧
      s.constructors[index].indices.length =
        s.families[s.constructors[index].owner].indices.length := by
  obtain ⟨index, rfl, hn, hmaj, hctor, hcf, hrhs⟩ := C.ordinary_rule hdf H
  have harity : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length :=
    C.model.constructorArity s.constructors[index] (by simp)
  -- the recursor
  have hmemB : rec.toVConstVal ∈ g.recursors := by
    rw [← C.ordinary_recursors, ← hrecsOf.recursors]; exact List.mem_map_of_mem hrec
  have hmemG := g.recursor_mem s.constructors[index].owner
  have hnd : (g.recursors.map (·.name)).Nodup := by
    have := C.names
    rw [C.ordinary_recursors] at this
    simp only [List.map_append] at this
    exact (List.nodup_append.1 this).2.1
  have hrv : rec.toVConstVal = g.recursor s.constructors[index].owner :=
    VEnv.inj_on_of_nodup_map hnd hmemB hmemG hn
  -- the number of indices, from the recursor's shape
  obtain ⟨-, -, -, j, hj, -, hbody⟩ := hdecl.rec_shape rec hrec
  have htype : rec.type = g.recursorType s.constructors[index].owner :=
    congrArg (fun c : VConstVal => c.type) hrv
  rw [htype, show g.recursorType s.constructors[index].owner =
    (g.recursor s.constructors[index].owner).type from rfl,
    InductiveSignature.Instance.recursorType_eq_recDoms (g := g)] at hbody
  simp only [InductiveSignature.Instance.recBody] at hbody
  rw [VExpr.mkApps_snoc, Model.piBody_wrapForalls_app, ← VExpr.mkApps_snoc] at hbody
  have hlenI := getAppArgs_length_eq_of_mkApps_bvar hbody
  simp only [List.length_append, InductiveSignature.length_vars, List.length_singleton,
    VExpr.bvarsDesc_length, InductiveSignature.insertBinders, List.length_map,
    List.length_zipIdx] at hlenI
  have hmaj' : rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices =
      s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].indices.length := hmaj
  -- the number of fields, from the rule's shape
  obtain ⟨_, -, _, -, -, -, hrs⟩ := hdecl.rule_shape rec hrec ru hru
  have hla := hrs.1
  rw [hrhs, InductiveSignature.Instance.equation_rhs_eq, lamArity_wrapLams,
    InductiveSignature.Instance.eqDoms_length] at hla
  simp only [InductiveSignature.Instance.eqBody, lamArity_mkApps_bvar] at hla
  refine ⟨index, rfl, hrv, hctor, hrhs, by omega, by omega, by omega, by omega, harity⟩

end VEnv.Model

end Lean4Lean
