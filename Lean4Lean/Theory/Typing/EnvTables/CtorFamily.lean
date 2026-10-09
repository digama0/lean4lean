import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.SchemaStructCompat
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Typing.EnvTables.CaseMajors
import Lean4Lean.Theory.Typing.Env

/-!
# Constructor families in the tables of a well-formed environment

The family of a constructor is the head constant of the body of its type (`familyOfType`,
`ctorFamily`). The major constructor of a generic case equation of a registered schema is in
the constructor table, or it is a source constructor of the schema whose source family is its
family (`generic_major_cases`). Every table constructor has the recorded shape
(`ctorOf_ctorShape`).
-/

/-!
# The family of a constructor type

`familyOfType` reads the head constant of the body of a forall telescope; on a telescope ending
in an application of a constant it is that constant (`familyOfType_shape`).
-/

namespace Lean4Lean.EnvTables
open InductiveSignature

/-- The family of a constructor type: the head constant of the body of its forall telescope. -/
def familyOfType (ty : VExpr) : Option Name :=
  match ty.forallResult.getAppFnArgs.1 with
  | .const F _ => some F
  | _ => none

/-! ## Lemmas -/

theorem familyOfType_shape (doms : List VExpr) (F : Name) (ls : List VLevel) (args : List VExpr) :
    familyOfType (VExpr.wrapForalls doms (VExpr.mkApps (.const F ls) args)) = some F := by
  unfold familyOfType
  rw [VExpr.forallResult_wrapForalls,
    VExpr.forallResult_of_head (VExpr.getAppFnArgs_mkApps_head _ _),
    VExpr.getAppFnArgs_mkApps_const]

end Lean4Lean.EnvTables


/-!
# Majors of generic eliminator equations

The left body of a generic case equation of a registered schema applies the abstract head to
the prefix variables, the index expressions and a constructor application. That constructor is
recorded in the tables, or it is a source constructor of the schema in the schema's own view.
-/

namespace Lean4Lean.EnvTables
open InductiveSignature CaseSchema

/-- The family of a declared constant's type (`familyOfType`). -/
def ctorFamily (env : VEnv) (c : Name) : Option Name :=
  (env.constants c).bind fun ci => familyOfType ci.type

theorem CtorShape.family {env : VEnv} {c : Name} {k : CtorData} (h : CtorShape env c k) :
    ctorFamily env c = some k.family := by
  obtain ⟨ci, doms, idx, hc, _, ht, _⟩ := h
  simp [ctorFamily, hc, ht, familyOfType_shape]

theorem view_ctor_name_mem {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    (j : Fin schema.signature.constructors.size) (hj : schema.signature.constructors[j].owner = owner) :
    schema.signature.constructors[j].name ∈
      (schema.view owner).constructors.toList.map (·.name) := by
  simp only [CaseSchema.view, List.toList_toArray, List.map_filterMap, List.mem_filterMap]
  refine ⟨schema.signature.constructors[j], Array.mem_toList_iff.mpr (Array.getElem_mem _), ?_⟩
  have hj' : schema.signature.constructors[j.val].owner = owner := hj
  simp [hj', CaseSchema.caseConstructor]

/-- The major constructor of a generic equation of a registered schema is in the constructor
table, or it is a source constructor of the schema at a source slot whose source family is
the constructor's family. -/
theorem generic_major_cases {env : VEnv} (H : env.WF) {schema : CaseSchema}
    (hreg : env.eliminators key schema) {owner : Fin schema.signature.families.size}
    {rules : List VDefEq} (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules)
    (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ctorOf env c ≠ none ∨ (schema.sourceFamilies[owner.val]? = ctorFamily env c ∧
      c ∈ (schema.view owner).constructors.toList.map (·.name)) := by
  obtain ⟨base, source, block, _, hle, hcert, _, hconsts⟩ := H.eliminator_installed hreg
  have hcert' := hcert
  obtain ⟨expanded, aux, hdata, hprior, hr, hnames, hrfresh⟩ := hcert'
  obtain ⟨j, hown, e, _, hrestore⟩ := generic_major hgen hdf hm
  rw [hr] at hrestore
  rcases CaseCompilationData.ctorApp_cases hdata hrfresh j hrestore with
    ⟨F, hF, hFget, c', hc', hcn, hmaj⟩ | ⟨a, ha, hge, haget, c', hc', _, hmaj⟩
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    rw [hown] at hFget
    have hconst : env.constants c'.name = some c'.toVConstant :=
      hconsts c' (List.mem_append_right _ (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc'⟩))
    obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
    have hshape := ctorShape_of_raw (hraw F hF c' hc')
      (hdata.sourceWF.2.2.2.1 c' (List.mem_flatMap.mpr ⟨F, hF, hc'⟩)) hconst
    refine .inr ⟨?_, ?_⟩
    · rw [hshape.family, hnames, List.getElem?_map, hFget]; rfl
    · rw [hcn]; exact view_ctor_name_mem j hown
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    have hk := container_ctor (envTables_inv H) hprior hle ha hc'
    exact .inl (by simp [ctorOf, hk])

end Lean4Lean.EnvTables


namespace Lean4Lean.EnvTables
open InductiveSignature

variable {env : VEnv}

theorem ctorOf_ctorShape (H : env.WF) (h : ctorOf env c = some k) : CtorShape env c k :=
  ctorOf_shape H h

/-! ## The constructor lists of families -/

end Lean4Lean.EnvTables
