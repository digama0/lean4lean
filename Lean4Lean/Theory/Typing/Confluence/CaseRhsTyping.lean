import Lean4Lean.Theory.Typing.EtaOpening
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Inductive.CaseProjections

/-! Typing the generated abstract-case RHS from its original case-type
formation. This uses the selected minor's own telescope, in the same context;
it does not assert formation before the case equations are registered. -/

namespace Lean4Lean
open VExpr

namespace InductiveSignature

private theorem subst_eq_of_closed {e : VExpr} (he : e.ClosedN k)
    (h : ∀ i, i < k → σ i = τ i) : e.subst σ = e.subst τ := by
  induction e generalizing k σ τ with
  | bvar i => exact h i he
  | sort | const | elim => rfl
  | app _ _ ihf iha => simp only [subst, ihf he.1 h, iha he.2 h]
  | proj _ _ _ ih => simp only [subst, ih he h]
  | lam _ _ ihd ihb | forallE _ _ ihd ihb =>
    have hb : ∀ i, i < k + 1 → σ.lift i = τ.lift i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [Subst.lift]; rw [h i (by omega)]
    simp only [subst, ihd he.1 h, ihb he.2 hb]

private theorem instantiateParams_rename {e : VExpr} {args : List VExpr}
    (he : e.ClosedN args.length) (ρ : Lift) :
    (instantiateParams e args).lift' ρ =
      instantiateParams e (args.map (·.lift' ρ)) := by
  let σ : VExpr.Subst := fun i =>
    if hi : i < args.length then args[args.length - 1 - i] else .bvar (i - args.length)
  change (e.subst σ).lift' ρ = _
  rw [lift'_subst]
  unfold instantiateParams
  dsimp only [σ]
  apply subst_eq_of_closed he
  intro i hi
  simp only [Subst.lift_r, List.length_map, dif_pos hi, List.getElem_map]

private theorem instantiateParams_liftN {e : VExpr} {args : List VExpr}
    (he : e.ClosedN args.length) (n k : Nat) :
    (instantiateParams e args).liftN n k =
      instantiateParams e (args.map (·.liftN n k)) := by
  simpa only [lift'_consN_skipN] using
    instantiateParams_rename he (.consN (.skipN .refl n) k)

private theorem specialization_liftN {h : HeadSpecialization}
    (hc : ∀ e ∈ h.arguments, e.ClosedN h.nparams) (levels : List VLevel)
    (args : List VExpr) (n k : Nat) :
    (h.apply levels args).map (·.liftN n k) =
      h.apply levels (args.map (·.liftN n k)) := by
  unfold HeadSpecialization.apply
  simp only [List.length_map]
  split
  · rfl
  · rename_i hgood
    have hlen : h.nparams ≤ args.length := by
      apply Nat.le_of_not_gt
      intro ht
      simp [ht] at hgood
    simp only [Option.pure_def, Option.map_some, liftN_mkApps, liftN, List.map_append,
      List.map_map, Function.comp_def, List.map_drop]
    congr 2
    apply congrArg (· ++ _)
    apply List.map_congr_left
    intro e he
    rw [← List.map_take]
    apply instantiateParams_liftN
    simpa only [List.length_take, Nat.min_eq_left hlen] using (hc e he).instL

private theorem restoration_liftN (r : Restoration)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (e : VExpr) (n k : Nat) :
    (r.expr e).map (·.liftN n k) = r.expr (e.liftN n k) := by
  suffices ∀ args, (Restoration.expr.go r e args).map (·.liftN n k) =
      Restoration.expr.go r (e.liftN n k) (args.map (·.liftN n k)) from this []
  induction e generalizing k with
  | app fn arg ihf iha =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have ha := iha k []
    simp only [List.map_nil] at ha
    rw [← ha]
    cases Restoration.expr.go r arg [] <;>
      simp only [Option.map_none, Option.map_some, bind, Option.bind_none,
        Option.bind_some, Option.map_none]
    exact ihf k (_ :: args)
  | const name levels =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    split
    · rename_i spec hs
      exact specialization_liftN (hc spec (List.mem_of_find?_eq_some hs)) _ _ _ _
    · simp only [Option.map_some, liftN_mkApps, liftN]
  | bvar | sort | elim =>
    intro args
    simp only [Restoration.expr.go, liftN, Option.map_some, liftN_mkApps]
  | lam domain body ihd ihb | forallE domain body ihd ihb =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have hd := ihd k []
    have hb := ihb (k + 1) []
    simp only [List.map_nil] at hd hb
    rw [← hd, ← hb]
    cases Restoration.expr.go r domain [] <;> cases Restoration.expr.go r body [] <;>
      simp [liftN_mkApps, liftN]
  | proj name index major ih =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have hm := ih k []
    simp only [List.map_nil] at hm
    rw [← hm]
    cases Restoration.expr.go r major [] <;> simp [liftN_mkApps, liftN]

private def liftDomains (ds : List VExpr) (n k : Nat) : List VExpr :=
  ds.zipIdx.map fun (d, i) => d.liftN n (k + i)

private theorem liftDomains_cons (d : VExpr) (ds : List VExpr) (n k : Nat) :
    liftDomains (d :: ds) n k = d.liftN n k :: liftDomains ds n (k + 1) := by
  apply List.ext_getElem
  · simp [liftDomains]
  · intro i hi hj
    cases i with
    | zero => simp [liftDomains]
    | succ i => simp [liftDomains, Nat.add_comm, Nat.add_left_comm]

private theorem lift_wrapForalls (ds : List VExpr) (body : VExpr) (n k : Nat) :
    (wrapForalls ds body).liftN n k =
      wrapForalls (liftDomains ds n k) (body.liftN n (k + ds.length)) := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    change VExpr.forallE (d.liftN n k) ((wrapForalls ds body).liftN n (k + 1)) = _
    rw [ih, liftDomains_cons]
    simp only [wrapForalls, List.foldr_cons, List.length_cons]
    congr 3
    omega

private theorem liftDomains_insert (ds : List VExpr) (extra n : Nat) :
    liftDomains (insertBinders ds extra) n 0 = insertBinders ds (extra + n) := by
  apply List.ext_getElem
  · simp [liftDomains, insertBinders]
  · intro i hi hj
    simp only [liftDomains, insertBinders, List.getElem_map, List.getElem_zipIdx,
      Nat.zero_add]
    exact liftN'_liftN_hi ..

private theorem lift_vars_above (count below n k : Nat) (h : k ≤ below) :
    (vars count below).map (·.liftN n k) = vars count (below + n) := by
  simp only [vars, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  simp only [liftN, liftVar, if_neg (by omega : ¬below + i < k)]
  congr 1
  omega

private theorem lift_constructorApp {s : InductiveSignature} (g : Instance s)
    (ctor : Constructor s.families.size) (extra n : Nat) :
    (g.constructorApp ctor extra 0).liftN n ctor.fields.length =
      g.constructorApp ctor (extra + n) 0 := by
  simp only [Instance.constructorApp, liftN_mkApps, liftN, List.map_append, Nat.add_zero]
  rw [lift_vars_above _ _ _ _ (by omega)]
  have hfields : (vars ctor.fields.length 0).map (·.liftN n ctor.fields.length) =
      vars ctor.fields.length 0 := by
    simp only [vars, List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : i < ctor.fields.length := by simpa using hi
    simp [liftN, liftVar, hi']
  rw [hfields]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem minor_lift {s : InductiveSignature} (g : Instance s)
    (ctor : Constructor s.families.size) (prior n : Nat)
    (hnorec : Instance.recursiveFields ctor = []) :
    (g.minor ctor prior).liftN n =
      wrapForalls
        (insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
          (s.families.size + prior + n))
        (mkApps (.bvar (ctor.fields.length + prior + n +
            (s.families.size - 1 - ctor.owner.val)))
          (ctor.indices.map (fun e => (e.instL g.levels).liftN
              (s.families.size + prior + n) ctor.fields.length) ++
            [g.constructorApp ctor (s.families.size + prior + n) 0])) := by
  simp only [Instance.minor, hnorec, List.zipIdx_nil, List.map_nil, List.length_nil,
    List.append_nil, liftN_zero, Nat.add_zero]
  rw [lift_wrapForalls, liftDomains_insert]
  simp only [insertBinders, fieldTypes, List.length_map, List.length_zipIdx,
    Nat.zero_add, liftN_mkApps, List.map_append, List.map_cons, List.map_nil, liftN]
  rw [lift_constructorApp]
  congr 2
  · simp only [liftVar, if_neg (by omega :
        ¬ctor.fields.length + prior + (s.families.size - 1 - ctor.owner.val) <
          ctor.fields.length)]
    congr 1
    omega
  · simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro e he
    exact liftN'_liftN_hi ..

private def casePrefix {s : InductiveSignature} (g : Instance s) : List VExpr :=
  g.params ++ g.motives ++ g.minors

private theorem prefix_length {s : InductiveSignature} (g : Instance s) :
    (casePrefix g).length = s.params.length + s.families.size + s.constructors.size := by
  simp [casePrefix, Instance.params, Instance.motives, Instance.minors, Nat.add_assoc]

private theorem prefix_minor {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) :
    (casePrefix g)[s.params.length + s.families.size + index.val]'(by
      rw [prefix_length]; omega) = g.minor s.constructors[index] index.val := by
  simp only [casePrefix]
  rw [List.getElem_append_right (by simp [Instance.params, Instance.motives])]
  simp [Instance.params, Instance.motives, Instance.minors]

private theorem equation_type_minor {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) (mode : HeadMode)
    (hnorec : Instance.recursiveFields s.constructors[index] = []) :
    (g.equation index mode).type =
      wrapForalls (casePrefix g)
        ((g.minor s.constructors[index] index.val).liftN (s.constructors.size - index.val)) := by
  rw [minor_lift _ _ _ _ hnorec]
  have hsize : s.families.size + index.val + (s.constructors.size - index.val) =
      s.families.size + s.constructors.size := by omega
  have hnf : s.constructors[index].fields.length + index.val +
      (s.constructors.size - index.val) =
      s.constructors[index].fields.length + s.constructors.size := by omega
  rw [hsize, hnf]
  simp only [Instance.equation, casePrefix, wrapForalls, List.foldr_append]

private theorem restore_foralls (r : Restoration) (ds : List VExpr) (body : VExpr) :
    r.expr (wrapForalls ds body) = (do
      let ds' ← ds.mapM r.expr
      let body' ← r.expr body
      pure (wrapForalls ds' body')) := by
  induction ds with
  | nil =>
    simp only [wrapForalls, List.foldr_nil, List.mapM_nil, bind]
    cases r.expr body <;> rfl
  | cons d ds ih =>
    change (do let d' ← r.expr d; let b' ← r.expr (wrapForalls ds body)
               pure (VExpr.forallE d' b')) = _
    rw [ih]
    simp only [List.mapM_cons]
    cases r.expr d <;> cases ds.mapM r.expr <;> cases r.expr body <;> rfl

private theorem restore_lams (r : Restoration) (ds : List VExpr) (body : VExpr) :
    r.expr (wrapLams ds body) = (do
      let ds' ← ds.mapM r.expr
      let body' ← r.expr body
      pure (wrapLams ds' body')) := by
  induction ds with
  | nil =>
    simp only [wrapLams, List.foldr_nil, List.mapM_nil, bind]
    cases r.expr body <;> rfl
  | cons d ds ih =>
    change (do let d' ← r.expr d; let b' ← r.expr (wrapLams ds body)
               pure (VExpr.lam d' b')) = _
    rw [ih]
    simp only [List.mapM_cons]
    cases r.expr d <;> cases ds.mapM r.expr <;> cases r.expr body <;> rfl

private theorem restore_bvar_apps (r : Restoration) (i count below : Nat) :
    r.expr (mkApps (.bvar i) (vars count below)) =
      some (mkApps (.bvar i) (vars count below)) := by
  change Restoration.expr.go r (mkApps _ _) [] = _
  rw [restoration_mkApps]
  have hv : (vars count below).mapM r.expr = some (vars count below) := by
    simp only [vars]
    generalize (List.range count).reverse = is
    induction is with
    | nil => rfl
    | cons i is ih => simpa [List.mapM_cons, Restoration.expr, Restoration.expr.go,
        VExpr.mkApps] using ih
  simp [hv, Restoration.expr.go]

private theorem mapM_lookup {r : Restoration} {ds ds' : List VExpr}
    (h : ds.mapM r.expr = some ds') (i : Nat) (hi : i < ds.length)
    (hi' : i < ds'.length) : r.expr ds[i] = some ds'[i] := by
  have ht := List.mapM_eq_some.mp h
  clear h
  induction ht generalizing i with
  | nil => simp at hi
  | cons hh ht ih =>
    cases i with
    | zero => exact hh
    | succ i => exact ih i (by simpa using hi) (by simpa using hi')

private theorem wrapForalls_injective (ds : List VExpr) :
    Function.Injective (wrapForalls ds) := by
  induction ds with
  | nil => exact fun _ _ h => h
  | cons d ds ih => exact fun _ _ h => ih (VExpr.forallE.inj h).2

private theorem restored_equation_layout {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) (owner : Fin s.families.size) (mode : HeadMode)
    (r : Restoration) (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (hnorec : Instance.recursiveFields s.constructors[index] = [])
    (ht : r.expr (g.recursorType owner) = some type)
    (he : r.equation (g.equation index mode) = some equation) :
    ∃ (pre fields : List VExpr) (tail result : VExpr) (j : Nat) (hj : j < pre.length),
      type = wrapForalls pre tail ∧
      equation.rhs = wrapLams (pre ++ fields)
        (mkApps (.bvar (fields.length + (pre.length - 1 - j))) (vars fields.length 0)) ∧
      equation.type = wrapForalls pre (wrapForalls fields result) ∧
      pre[j].liftN (pre.length - j) = wrapForalls fields result := by
  let ctor := s.constructors[index]
  let ds := insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
    (s.families.size + s.constructors.size)
  let result := mkApps
    (.bvar (ctor.fields.length + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
    (ctor.indices.map (fun e => (e.instL g.levels).liftN
        (s.families.size + s.constructors.size) ctor.fields.length) ++
      [g.constructorApp ctor (s.families.size + s.constructors.size) 0])
  have hds : ds.length = ctor.fields.length := by simp [ds, insertBinders, fieldTypes]
  have htypeShape : ∃ tail, g.recursorType owner = wrapForalls (casePrefix g) tail := by
    let indices := insertBinders ((s.families[owner]).indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)
    let major := g.familyApp owner
      (vars s.params.length (s.families.size + s.constructors.size + indices.length))
      (vars indices.length 0)
    let motive := VExpr.bvar (indices.length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val))
    refine ⟨wrapForalls (indices ++ [major])
      (mkApps motive (vars indices.length 1 ++ [.bvar 0])), ?_⟩
    simp only [Instance.recursorType, casePrefix, wrapForalls, List.foldr_append]
    rfl
  obtain ⟨tail, htypeShape⟩ := htypeShape
  rw [htypeShape, restore_foralls] at ht
  simp only [bind, Option.bind_eq_some_iff] at ht
  obtain ⟨pre, hp, tail', ht', htype⟩ := ht
  have hplen : pre.length = (casePrefix g).length := (List.Forall₂.length_eq (List.mapM_eq_some.mp hp)).symm
  have hplen' : pre.length = s.params.length + s.families.size + s.constructors.size :=
    hplen.trans (prefix_length g)
  let j := s.params.length + s.families.size + index.val
  have hj : j < pre.length := by dsimp [j]; rw [hplen']; omega
  have hjRaw : j < (casePrefix g).length := by rwa [← hplen]
  have hminor := mapM_lookup hp j hjRaw hj
  rw [prefix_minor] at hminor
  have hgap : pre.length - j = s.constructors.size - index.val := by
    dsimp [j]; rw [hplen']; omega
  have hlift := restoration_liftN r hc (g.minor s.constructors[index] index.val)
    (s.constructors.size - index.val) 0
  rw [hminor, Option.map_some] at hlift
  have hminorShape : (g.minor ctor index.val).liftN (s.constructors.size - index.val) =
      wrapForalls ds result := by
    have h := equation_type_minor g index mode hnorec
    apply (wrapForalls_injective (casePrefix g))
    rw [← h]
    simp only [Instance.equation, casePrefix, ctor, ds, result, wrapForalls, List.foldr_append]
  change some (pre[j].liftN (s.constructors.size - index.val)) =
    r.expr ((g.minor ctor index.val).liftN (s.constructors.size - index.val)) at hlift
  rw [hminorShape, restore_foralls] at hlift
  have hlift' := hlift.symm
  simp only [bind, Option.bind_eq_some_iff] at hlift'
  obtain ⟨fields, hf, result', hr, hinner⟩ := hlift'
  have hflen : fields.length = ctor.fields.length :=
    (List.Forall₂.length_eq (List.mapM_eq_some.mp hf)).symm.trans hds
  have hiBody : ctor.fields.length + s.constructors.size - 1 - index.val =
      fields.length + (pre.length - 1 - j) := by
    rw [hflen, hplen']; dsimp [j]; have := index.isLt; omega
  have hparts := Restoration.equation_parts he
  have hrhs : (g.equation index mode).rhs = wrapLams (casePrefix g ++ ds)
      (mkApps (.bvar (ctor.fields.length + s.constructors.size - 1 - index.val))
        (vars ctor.fields.length 0)) := by
    simp only [Instance.equation, hnorec, List.map_nil, List.append_nil]
    rfl
  have hetype : (g.equation index mode).type = wrapForalls (casePrefix g ++ ds) result := rfl
  have hright := hparts.2.1
  rw [hrhs, restore_lams, List.mapM_append, hp, hf,
    restore_bvar_apps] at hright
  have hresult := hparts.2.2
  rw [hetype, restore_foralls, List.mapM_append, hp, hf, hr] at hresult
  refine ⟨pre, fields, tail', result', j, hj, (Option.some.inj htype).symm, ?_, ?_, ?_⟩
  · simpa only [bind, Option.bind_some, pure, hiBody, hflen] using
      (Option.some.inj hright).symm
  · have hresult' := (Option.some.inj hresult).symm
    simpa only [wrapForalls, List.foldr_append] using hresult'
  · rw [hgap]
    exact (Option.some.inj hinner).symm

end InductiveSignature

namespace VEnv
open InductiveSignature
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {ds : List VExpr}
  {body result : VExpr} {packed : List VLevel} {level : VLevel}

end VEnv

namespace InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {type : VExpr}
  {packed : List VLevel} {level : VLevel}

/-- The generated RHS is a fixed lambda telescope followed by applications
of its selected minor. The minor's stored type is related to the equation type
by this literal lift, without dependent type alignment. -/
theorem Generates.rhs_layout {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hgen : schema.Generates block owner rule)
    (htype : schema.genericType owner = some type)
    (hscope : schema.restoration.Scoped) :
    ∃ (pre fields : List VExpr) (tail result : VExpr) (j : Nat) (hj : j < pre.length),
      type = wrapForalls pre tail ∧
      rule.equation.rhs = wrapLams (pre ++ fields)
        (mkApps (.bvar (fields.length + (pre.length - 1 - j))) (vars fields.length 0)) ∧
      rule.equation.type = wrapForalls pre (wrapForalls fields result) ∧
      pre[j].liftN (pre.length - j) = wrapForalls fields result := by
  obtain ⟨rules, hrules, hmem, _⟩ := hgen
  obtain ⟨index, he⟩ := equation_of_mem hrules hmem
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  have hnorec : Instance.recursiveFields (schema.view owner).constructors[index] = [] := by
    obtain ⟨ctor, _, _, hc⟩ := view_constructor_eq_caseConstructor index
    rw [hc]
    unfold Instance.recursiveFields
    apply List.filterMap_eq_nil_iff.mpr
    intro pair hp
    obtain ⟨field, i⟩ := pair
    have hfield := List.fst_mem_of_mem_zipIdx hp
    obtain ⟨domain, _, hd⟩ := List.mem_map.mp hfield
    cases hd
    rfl
  exact restored_equation_layout g index (schema.viewOwner owner) (.elim block owner.val)
    schema.restoration (fun h hh => (hscope.2.2.1 h hh).2) hnorec htype he

end InductiveSignature.CaseSchema
end Lean4Lean

/-! The original closed case header supplies the scope of every generated
right-hand side. The selected minor's literal telescope supplies the field
domains; no equation-typing or equation-scope oracle is required. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr

private theorem forall_domain_scope {domains : List VExpr} {body : VExpr}
    (closed : (wrapForalls domains body).ClosedN count)
    (index : Nat) (bound : index < domains.length) :
    domains[index].ClosedN (count + index) := by
  induction domains generalizing count index with
  | nil => simp at bound
  | cons domain domains ih =>
    cases index with
    | zero => exact closed.1
    | succ index =>
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1] using
        ih closed.2 index (by simpa using bound)

/-- The generated case equation uses only domains already scoped by its
original generic header, followed by the selected minor's own fields. -/
theorem Generates.rhs_closed {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule} {type : VExpr}
    (generated : schema.Generates block owner rule)
    (header : schema.genericType owner = some type)
    (restoration : schema.restoration.Scoped) (closed : type.Closed) :
    rule.equation.rhs.Closed := by
  obtain ⟨pre, fields, tail, result, index, bound, headerShape,
    rhsShape, _, minorShape⟩ := generated.rhs_layout header restoration
  have prefixScope : ∀ i (hi : i < pre.length), pre[i].ClosedN i := by
    intro i hi
    simpa only [Nat.zero_add] using
      forall_domain_scope (count := 0) (headerShape ▸ closed) i hi
  have minorScope : (wrapForalls fields result).ClosedN pre.length := by
    rw [← minorShape]
    have scope := (prefixScope index bound).liftN (n := pre.length - index) (j := 0)
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt bound)] using scope
  rw [rhsShape]
  apply ClosedN.wrapLams_closed
  · intro i hi
    simp only [Nat.zero_add]
    by_cases before : i < pre.length
    · simpa only [List.getElem_append_left before] using prefixScope i before
    · rw [List.getElem_append_right (by omega)]
      have scope := forall_domain_scope minorScope (i - pre.length) (by
        simp only [List.length_append] at hi
        omega)
      simpa only [Nat.add_sub_of_le (by omega : pre.length ≤ i)] using scope
  · apply ClosedN.mkApps_closed
    · change fields.length + (pre.length - 1 - index) < 0 + (pre ++ fields).length
      simp only [List.length_append]
      omega
    · intro argument member
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at member
      obtain ⟨i, hi, rfl⟩ := member
      change 0 + i < 0 + (pre ++ fields).length
      simp only [List.length_append]
      omega

end Lean4Lean.InductiveSignature.CaseSchema
