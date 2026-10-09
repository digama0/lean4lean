import Lean4Lean.Theory.Inductive.HypothesisTyping
import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.Injectivity

/-! The recorded shape of a recursive field agrees with the field's normal form.

`Models.classifiedFields` says that a recursive field's type is definitionally a telescope over
family-free domains ending in an application of a family. The generator builds the field's
induction hypothesis from the recorded `Recursive` shape instead. When that hypothesis is
well typed (`Instance.GeneratedIHsWellTyped`), unique typing and the injectivity of rigid family
heads identify the two (`Instance.recursiveShape_correspondence`): same target family, same
number of binders, and definitionally equal binders and indices after the generator's embedding.
Since definitional equality is never moved to a smaller context (section 5.1 of
the design notes), the binder and index comparisons are stated under all of the
hypothesis' binders. -/

namespace Lean4Lean

namespace VExpr

theorem liftN_wrapForalls_at (N : List VExpr) (B : VExpr) (n k : Nat) :
    (VExpr.wrapForalls N B).liftN n k =
      VExpr.wrapForalls (N.mapIdx fun l d => d.liftN n (k + l)) (B.liftN n (k + N.length)) := by
  induction N generalizing k with
  | nil => simp [VExpr.wrapForalls]
  | cons d ds ih =>
    show VExpr.forallE (d.liftN n k) ((VExpr.wrapForalls ds B).liftN n (k + 1)) = _
    rw [ih, List.mapIdx_cons]
    show _ = VExpr.forallE _ (VExpr.wrapForalls _ _)
    simp only [Nat.add_zero, List.length_cons]
    congr 2
    · congr 1; funext l d; congr 1; omega
    · congr 1; omega

/-- Instantiating the first `k` of `n` inserted binders at their variables. -/
theorem liftN_instOuter_bvarRange (d : VExpr) {n k : Nat} (hk : k ≤ n) :
    (d.liftN n k).instOuter (bvarRange k n) = d.liftN (n - k) := by
  rw [instOuter_eq_subst, liftN_subst, liftN_eq_subst]
  congr 1
  funext x
  simp only [Subst.lift_l, Lift.liftVar_consN_skipN, Subst.shift]
  by_cases hx : x < k
  · rw [liftVar_lt hx, Subst.ofList_lt _ (by simpa using hx), bvarRange_getElem _ _ _ (by
      simp at *; omega)]
    congr 1; simp; omega
  · rw [liftVar_le (Nat.le_of_not_gt hx)]
    simp only [Subst.ofList, bvarRange_length]
    rw [dif_neg (by omega)]
    congr 1; omega

end VExpr

namespace InductiveSignature

theorem vars_eq_bvarRange (count below : Nat) :
    vars count below = VExpr.bvarRange count (below + count) := by
  apply List.ext_getElem
  · simp [vars]
  · intro k h1 h2
    simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.length_range]
    rw [VExpr.bvarRange_getElem _ _ _ (by simpa [vars] using h1)]
    congr 1; simp [vars] at h1; omega

theorem vars_map_liftN (count n : Nat) :
    (vars count 0).map (·.liftN n count) = vars count 0 := by
  simp only [vars, List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_reverse, List.mem_range] at hx
  simp [VExpr.liftN, liftVar, hx]

theorem vars_map_instOuter (args : List VExpr) :
    (vars args.length 0).map (·.instOuter args) = args := by
  rw [vars_eq_bvarRange, Nat.zero_add,
    VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (Nat.le_refl _)]
  simp

end InductiveSignature

namespace VEnv

variable {env : VEnv} {U : Nat}

/-- `HasType.mkApps_rigid_arity` with possibly different rigid heads on the two sides. -/
theorem HasType.mkApps_rigid_arity₂ (henv : VEnv.WF env)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hc : env.Rigid c) (hc' : env.Rigid c')
    {f : VExpr} {domains args xs ys : List VExpr} {ls ls' : List VLevel}
    (hf : env.HasType U Γ f (VExpr.wrapForalls domains (VExpr.mkApps (.const c ls) xs)))
    (ht : env.HasType U Γ (VExpr.mkApps f args) (VExpr.mkApps (.const c' ls') ys)) :
    args.length = domains.length := by
  induction args generalizing f domains xs with
  | nil =>
    cases domains with
    | nil => rfl
    | cons domain domains =>
      have ⟨_, hT⟩ := ht.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hc' hT
        (hf.uniqU henv hΓ ht).symm).elim
  | cons arg args ih =>
    have hfa : VExpr.WF env U Γ (.app f arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f arg) ⟨_, ht⟩
    rcases hfa.app_inv henv.ordered hΓ with ⟨A, B, hfun, harg⟩
    cases domains with
    | nil =>
      have ⟨_, hT⟩ := hf.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hc hT
        (hf.uniqU henv hΓ hfun)).elim
    | cons domain domains =>
      rcases (hf.uniqU henv hΓ hfun).forallE_inv henv hΓ with ⟨⟨_, hd⟩, _⟩
      have ha := harg.defeqU_r henv hΓ ⟨_, hd.symm⟩
      have hfa' := hf.app ha
      change env.HasType U Γ (.app f arg)
        ((VExpr.wrapForalls domains (VExpr.mkApps (.const c ls) xs)).inst arg) at hfa'
      rw [VExpr.wrapForalls_inst, VExpr.inst_mkApps] at hfa'
      have hlen := ih hfa' ht
      simpa [VExpr.instDomains] using hlen

/-- A term `f` whose type is a telescope `N` ending in a rigid family application, applied
under a telescope `D` to the variables of `D`, at a type headed by a rigid constant: the two
telescopes have the same length, the heads agree, the domains agree pointwise (seen under all
of `D`, since no strengthening is available), and the family arguments agree pointwise. -/
theorem spine_correspondence (henv : VEnv.WF env) {Δ D N xs ys : List VExpr} {f : VExpr}
    {c c' : Name} {ls ls' : List VLevel}
    (hΓ : OnCtx (D.reverse ++ Δ) (env.IsType U)) (hc : env.Rigid c) (hc' : env.Rigid c')
    (hf : env.HasType U Δ f (VExpr.wrapForalls N (VExpr.mkApps (.const c ls) xs)))
    (ht : env.HasType U (D.reverse ++ Δ)
      (VExpr.mkApps (f.liftN D.length) (InductiveSignature.vars D.length 0))
      (VExpr.mkApps (.const c' ls') ys)) :
    N.length = D.length ∧ c = c' ∧
    (∀ k (hk : k < D.length) (hk' : k < N.length),
      env.IsDefEqU U (D.reverse ++ Δ) (D[k].liftN (D.length - k)) (N[k].liftN (D.length - k))) ∧
    List.Forall₂ (env.IsDefEqU U (D.reverse ++ Δ)) xs ys := by
  have W : Ctx.LiftN D.length 0 Δ (D.reverse ++ Δ) := .zero D.reverse (by simp)
  have hfn := hf.weakN henv.ordered W
  rw [VExpr.liftN_wrapForalls_at, VExpr.liftN_mkApps,
    show (VExpr.const c ls).liftN D.length (0 + N.length) = .const c ls from rfl] at hfn
  simp only [Nat.zero_add] at hfn
  have hlen := HasType.mkApps_rigid_arity₂ henv hΓ hc hc' hfn ht
  simp only [InductiveSignature.vars, List.length_map, List.length_reverse, List.length_range,
    List.length_mapIdx] at hlen
  rw [InductiveSignature.vars_eq_bvarRange, Nat.zero_add] at ht
  have ⟨hargs, hres⟩ := HasType.mkApps_wrapForalls henv hΓ hfn ⟨_, ht⟩
    (by simp [hlen])
  have hX : ∀ x : VExpr, (x.liftN D.length N.length).instOuter (VExpr.bvarRange D.length D.length)
      = x := by
    intro x
    rw [← hlen, VExpr.liftN_instOuter_bvarRange x (Nat.le_refl _)]
    simp
  simp only [VExpr.instOuter_mkApps, VExpr.instOuter_const] at hres
  rw [show (xs.map fun x => x.liftN D.length N.length).map
      (fun x => x.instOuter (VExpr.bvarRange D.length D.length)) = xs by
    simp [List.map_map, Function.comp_def, hX]] at hres
  have hdef := hres.uniqU henv hΓ ht
  have ⟨_, hsort⟩ := hres.isType henv.ordered hΓ
  have hcc : c = c' := by
    refine Classical.byContradiction fun hne => ?_
    exact VEnv.IsDefEqU.rigidApp_ne henv hΓ hc hc' hne hsort hdef
  subst hcc
  refine ⟨hlen.symm, rfl, fun k hk hk' => ?_,
    (VEnv.IsDefEqU.rigidApp_inv henv hΓ hc hdef hsort).2⟩
  have hk1 := hargs k (by simpa using hk) (by simpa using hk')
  rw [List.getElem_mapIdx, VExpr.bvarRange_take _ _ _ (Nat.le_of_lt hk),
    VExpr.liftN_instOuter_bvarRange _ (Nat.le_of_lt hk), VExpr.bvarRange_getElem _ _ _ hk]
    at hk1
  have hk2 : env.HasType U (D.reverse ++ Δ) (.bvar (D.length - 1 - k))
      (D[k].liftN (D.length - k)) := .bvar (Lookup.reverse_append D Δ k hk)
  exact hk2.uniqU henv hΓ hk1

/-- An application of a variable whose type is a telescope over index domains and a major
domain ending in a sort: the arguments match the index domains, and the major argument is typed
at the major domain with the indices substituted. -/
theorem motive_spine_typing (henv : VEnv.WF env) {Γ I P idx : List VExpr} {m major : VExpr}
    {name : Name} {ls : List VLevel} {u : VLevel} {nI : Nat}
    (hΓ : OnCtx Γ (env.IsType U)) (hnI : I.length = nI)
    (hm : env.HasType U Γ m (VExpr.wrapForalls
      (I ++ [VExpr.mkApps (.const name ls) (P ++ InductiveSignature.vars nI 0)]) (.sort u)))
    (hbody : env.IsType U Γ (VExpr.mkApps m (idx ++ [major]))) :
    idx.length = nI ∧
    env.HasType U Γ major (VExpr.mkApps (.const name ls) (P.map (·.instOuter idx) ++ idx)) := by
  subst hnI
  have ⟨_, hb⟩ := hbody
  have hlen := HasType.mkApps_sort_arity henv hΓ hm hb
  simp only [List.length_append, List.length_singleton] at hlen
  have hlen' : idx.length = I.length := by omega
  have ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hm ⟨_, hb⟩ (by simp [hlen'])
  have h := hargs idx.length (by simp) (by simp [hlen'])
  rw [List.getElem_append_right (Nat.le_refl _), List.take_left] at h
  simp only [Nat.sub_self, List.getElem_singleton] at h
  rw [List.getElem_append_right (by omega)] at h
  simp only [hlen', Nat.sub_self, List.getElem_singleton, VExpr.instOuter_mkApps,
    VExpr.instOuter_const, List.map_append] at h
  refine ⟨hlen', ?_⟩
  rw [← hlen', InductiveSignature.vars_map_instOuter] at h
  exact h

end VEnv

namespace InductiveSignature

theorem forall₂_getElem {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs →
      ∀ (i : Nat) (ha : i < as.length) (hb : i < bs.length), R as[i] bs[i]
  | _, _, .nil, _, ha, _ => absurd ha (Nat.not_lt_zero _)
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ H, i + 1, ha, hb =>
    forall₂_getElem H i (by simpa using ha) (by simpa using hb)

/-- Every family of a signature modelling a declaration is named by a family of the
declaration. -/
theorem Models.family_name_mem {s : InductiveSignature} {env : VEnv} {decl : VInductDecl}
    (hM : s.Models env decl) (t : Fin s.families.size) :
    ∃ type ∈ decl.types, type.name = s.families[t].name := by
  have hlen := Lean4Lean.List.Forall₂.length_eq hM.families
  have ht : t.val < s.declaration.types.length := by simp [declaration]
  have ht' : t.val < decl.types.length := by omega
  have h := forall₂_getElem hM.families t.val ht ht'
  refine ⟨_, List.getElem_mem ht', ?_⟩
  rw [← h.1]
  simp [declaration]

theorem getElem_fieldTypes (s : InductiveSignature) (ctor : Constructor s.families.size)
    (i : Nat) (hi : i < (s.fieldTypes ctor).length) :
    (s.fieldTypes ctor)[i] = s.fieldType i (ctor.fields[i]'(by simpa [fieldTypes] using hi)) := by
  simp [fieldTypes, List.getElem_zipIdx]

theorem length_fieldTypes (s : InductiveSignature) (ctor : Constructor s.families.size) :
    (s.fieldTypes ctor).length = ctor.fields.length := by
  simp [fieldTypes]

theorem length_insertBinders (L : List VExpr) (n : Nat) : (insertBinders L n).length = L.length := by
  simp [insertBinders]

theorem getElem_insertBinders (L : List VExpr) (n i : Nat) (hi : i < (insertBinders L n).length) :
    (insertBinders L n)[i] = (L[i]'(by simpa [insertBinders] using hi)).liftN n i := by
  simp [insertBinders, List.getElem_zipIdx]

/-- Inserting `n` binders below a telescope, as a context lift. -/
theorem ctx_liftN_insertBinders (L Γ As : List VExpr) (n : Nat) (hAs : As.length = n) :
    ∀ i ≤ L.length, Ctx.LiftN n i ((L.take i).reverse ++ Γ)
      (((insertBinders L n).take i).reverse ++ (As ++ Γ))
  | 0, _ => by simpa using Ctx.LiftN.zero (Γ := Γ) As hAs
  | i + 1, hi => by
    have ih := ctx_liftN_insertBinders L Γ As n hAs i (by omega)
    have hi' : i < L.length := by omega
    have hi'' : i < (insertBinders L n).length := by rw [length_insertBinders]; exact hi'
    rw [List.take_succ_eq_append_getElem hi', List.take_succ_eq_append_getElem hi'',
      getElem_insertBinders]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    exact ih.succ

namespace Instance

variable {s : InductiveSignature}

/-- The embedding the generator applies to the syntax of a recursive field when it forms the
field's induction hypothesis (`hypothesis`). -/
def hypEmbed (g : Instance s) (ctor : Constructor s.families.size)
    (prior priorIHs field : Nat) (e : VExpr) (localDepth : Nat) : VExpr :=
  underFields (e.instL g.levels) field ctor.fields.length priorIHs
    (s.families.size + prior) localDepth

/-- The binder domains of a generated induction hypothesis. -/
def hypothesisDomains (g : Instance s) (ctor : Constructor s.families.size)
    (prior priorIHs field : Nat) (r : Recursive s.families.size) : List VExpr :=
  r.binders.zipIdx.map fun (e, k) => g.hypEmbed ctor prior priorIHs field e k

theorem length_hypothesisDomains (g : Instance s) (ctor : Constructor s.families.size)
    (prior priorIHs field : Nat) (r : Recursive s.families.size) :
    (g.hypothesisDomains ctor prior priorIHs field r).length = r.binders.length := by
  simp [hypothesisDomains]

theorem getElem_hypothesisDomains (g : Instance s) (ctor : Constructor s.families.size)
    (prior priorIHs field : Nat) (r : Recursive s.families.size) (k : Nat)
    (hk : k < (g.hypothesisDomains ctor prior priorIHs field r).length) :
    (g.hypothesisDomains ctor prior priorIHs field r)[k] =
      g.hypEmbed ctor prior priorIHs field
        (r.binders[k]'(by simpa [length_hypothesisDomains] using hk)) k := by
  simp [hypothesisDomains, List.getElem_zipIdx]

theorem hypothesis_eq (g : Instance s) (ctor : Constructor s.families.size)
    (prior priorIHs field : Nat) (r : Recursive s.families.size) :
    g.hypothesis ctor prior priorIHs field r =
      VExpr.wrapForalls (g.hypothesisDomains ctor prior priorIHs field r)
        (VExpr.mkApps (.bvar (ctor.fields.length + priorIHs +
            (g.hypothesisDomains ctor prior priorIHs field r).length + prior +
            (s.families.size - 1 - r.target.val)))
          (r.indices.map (g.hypEmbed ctor prior priorIHs field · 
              (g.hypothesisDomains ctor prior priorIHs field r).length) ++
            [VExpr.mkApps (.bvar (ctor.fields.length - 1 - field + priorIHs +
                (g.hypothesisDomains ctor prior priorIHs field r).length))
              (vars (g.hypothesisDomains ctor prior priorIHs field r).length 0)])) := rfl

theorem recursiveFields_getElem {ctor : Constructor s.families.size} {j i : Nat}
    {r : Recursive s.families.size}
    (hj : j < (recursiveFields ctor).length) (hp : (recursiveFields ctor)[j] = (i, r)) :
    ∃ hi : i < ctor.fields.length, ∃ type, ctor.fields[i] = .recursive type r := by
  have hmem := List.getElem_mem hj
  rw [hp] at hmem
  simp only [recursiveFields, List.mem_filterMap] at hmem
  obtain ⟨⟨field, i⟩, hm, hf⟩ := hmem
  rw [List.mem_zipIdx_iff_getElem?] at hm
  cases field with
  | external => simp at hf
  | recursive type r =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.1 hm
    exact ⟨hi, type, hget⟩

theorem embed_comm (e : VExpr) {i nf j extra k : Nat} (hi : i ≤ nf) :
    (e.liftN extra (i + k)).liftN (j + (nf - i)) k =
      underFields e i nf j extra k := by
  rw [underFields, VExpr.liftN_liftN_comm _ _ _ _ _ (by omega)]
  congr 1
  · congr 1; omega
  · omega

theorem getElem_motives (g : Instance s) (t : Nat) (ht : t < g.motives.length) :
    g.motives[t] = g.motive (s.families[t]'(by simpa [motives] using ht)) t := by
  simp [motives, List.getElem_zipIdx]

theorem length_motives (g : Instance s) : g.motives.length = s.families.size := by
  simp [motives]

theorem motive_eq (g : Instance s) (family : Family) (prior : Nat) :
    g.motive family prior =
      VExpr.wrapForalls (insertBinders (family.indices.map (·.instL g.levels)) prior ++
        [VExpr.mkApps (.const family.name g.levels)
          (vars s.params.length
              (prior + (insertBinders (family.indices.map (·.instL g.levels)) prior).length) ++
            vars (insertBinders (family.indices.map (·.instL g.levels)) prior).length 0)])
        (.sort g.targetLevel) := rfl

open VEnv in
/-- **Recursive shapes correspond to the normal forms of recursive fields.**

Let `s` model `decl`, and consider the `j`-th recursive field `i` of a constructor, recorded with
shape `r`.  `Models.classifiedFields` gives a normal form `wrapForalls domains result` of the
field type, with `result` an application of a family `family` of `decl`.  If the induction
hypothesis the generator forms for this field is a well-formed type in its context (the clause
`GeneratedIHsWellTyped`, in any well-formed environment `env'` extending the family headers in
which the families are rigid), then the recorded shape is that normal form:

* the target family of `r` is `family`;
* `r` has exactly as many binders as the normal form has domains, and as many indices as its
  target family;
* the binders of `r` and the domains of the normal form, both embedded as the generator embeds
  them (`hypEmbed`: universe instantiation at `g.levels` and `underFields`), are definitionally
  equal; since definitional equality cannot be moved to a smaller context, this is stated in
  the context extended by all of the hypothesis' binders;
* the indices of `r` and the index arguments of `result`, both embedded, are definitionally
  equal in the same context. -/
theorem recursiveShape_correspondence {env env' envTypes : VEnv} {decl : VInductDecl}
    (g : Instance s) (hM : s.Models env decl) (hsafe : s.isUnsafe = false)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) (hle : envTypes ≤ env')
    (henv : env'.WF) (hls : ∀ l ∈ g.levels, l.WF g.uvars)
    (hrigid : ∀ type ∈ decl.types, env'.Rigid type.name)
    {ctor : Constructor s.families.size} (hctor : ctor ∈ s.constructors.toList)
    {prior j i : Nat} {r : Recursive s.families.size} (hprior : prior < s.constructors.size)
    (hj : j < (recursiveFields ctor).length) (hp : (recursiveFields ctor)[j] = (i, r))
    (hΓ : OnCtx (g.hypothesisContext ctor prior j) (env'.IsType g.uvars))
    (hIH : env'.IsType g.uvars (g.hypothesisContext ctor prior j)
      (g.hypothesis ctor prior j i r)) :
    ∃ (hi : i < ctor.fields.length) (domains : List VExpr) (result : VExpr)
      (family : VInductiveType),
      envTypes.IsDefEqU decl.uvars (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse)
        (s.fieldType i ctor.fields[i]) (VExpr.wrapForalls domains result) ∧
      (∀ domain ∈ domains, domain.SourceConstFree (decl.types.map (·.name))) ∧
      decl.ValidIndAppAt none (i + domains.length) result ∧
      family ∈ decl.types ∧
      result.getAppFnArgs.1 = .const family.name (VLevel.params decl.uvars) ∧
      s.families[r.target].name = family.name ∧
      r.binders.length = domains.length ∧
      r.indices.length = s.families[r.target].indices.length ∧
      (∀ k (hk : k < r.binders.length) (hk' : k < domains.length),
        env'.IsDefEqU g.uvars
          ((g.hypothesisDomains ctor prior j i r).reverse ++ g.hypothesisContext ctor prior j)
          ((g.hypEmbed ctor prior j i r.binders[k] k).liftN (r.binders.length - k))
          ((g.hypEmbed ctor prior j i domains[k] k).liftN (r.binders.length - k))) ∧
      List.Forall₂ (env'.IsDefEqU g.uvars
          ((g.hypothesisDomains ctor prior j i r).reverse ++ g.hypothesisContext ctor prior j))
        (r.indices.map (g.hypEmbed ctor prior j i · r.binders.length))
        ((result.getAppFnArgs.2.drop decl.nparams).map
          (g.hypEmbed ctor prior j i · r.binders.length)) := by
  obtain ⟨hi, type, hfield⟩ := recursiveFields_getElem hj hp
  rcases hM.classifiedFields with hunsafe | ⟨envT, htypesT, hfields⟩
  · rw [hsafe] at hunsafe; cases hunsafe
  rw [htypes] at htypesT
  cases htypesT
  obtain ⟨normalized, hdef, hshape⟩ := hfields ctor hctor i hi
  rw [hfield] at hshape
  obtain ⟨domains, result, rfl, hfree, hvalid, family, hfam, hhead⟩ := hshape
  refine ⟨hi, domains, result, family, hdef, hfree, hvalid, hfam, hhead, ?_⟩
  -- The pieces of the hypothesis context.
  have hnf := length_fieldTypes s ctor
  generalize hFS : insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
    (s.families.size + prior) = FS
  generalize hIHS : ((recursiveFields ctor).zipIdx.map fun ((field, r), i) =>
    g.hypothesis ctor prior i field r).take j = IHS
  have hΓh : g.hypothesisContext ctor prior j = IHS.reverse ++ (FS.reverse ++
      ((g.minors.take prior).reverse ++ (g.motives.reverse ++ g.params.reverse))) := by
    rw [← hFS, ← hIHS]
    simp only [hypothesisContext, List.append_assoc]
  have hIHSlen : IHS.length = j := by rw [← hIHS]; simp; omega
  have hFSlen : FS.length = ctor.fields.length := by
    rw [← hFS, length_insertBinders, List.length_map, hnf]
  have hMilen : (g.minors.take prior).length = prior := by simp [length_minors]; omega
  have hMolen := length_motives g
  -- Transport the normal form to the hypothesis context.
  have h1 := (hdef.mono hle).instL hls
  simp only [List.map_append, List.map_reverse, List.map_take] at h1
  have W1 := ctx_liftN_insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
    (s.params.map (·.instL g.levels)).reverse ((g.minors.take prior).reverse ++ g.motives.reverse)
    (s.families.size + prior) (by simp [hMilen, hMolen]; omega) i (by simp [hnf]; omega)
  rw [hFS, List.append_assoc] at W1
  have h2 := h1.weakN henv.ordered W1
  have W2 : Ctx.LiftN (j + (ctor.fields.length - i)) 0
      ((FS.take i).reverse ++ ((g.minors.take prior).reverse ++ (g.motives.reverse ++
        g.params.reverse))) (g.hypothesisContext ctor prior j) := by
    have e : g.hypothesisContext ctor prior j = (IHS.reverse ++ (FS.drop i).reverse) ++
        ((FS.take i).reverse ++ ((g.minors.take prior).reverse ++ (g.motives.reverse ++
          g.params.reverse))) := by
      rw [hΓh, show FS.reverse = (FS.drop i).reverse ++ (FS.take i).reverse by
        rw [← List.reverse_append, List.take_append_drop]]
      simp only [List.append_assoc]
    rw [e]
    refine .zero (IHS.reverse ++ (FS.drop i).reverse) ?_
    simp [hIHSlen, hFSlen]
  have h3 := h2.weakN henv.ordered W2
  -- The field variable.
  have hL1 := Lookup.reverse_append FS ((g.minors.take prior).reverse ++ (g.motives.reverse ++
    g.params.reverse)) i (by rw [hFSlen]; exact hi)
  have hL2 := Lookup.weakN (Ctx.LiftN.zero IHS.reverse (by simp [hIHSlen]) :
    Ctx.LiftN j 0 _ (IHS.reverse ++ _)) hL1
  rw [← hΓh] at hL2
  have hfvar := VEnv.HasType.bvar (env := env') (U := g.uvars) hL2
  have hFSi : FS[i]'(by rw [hFSlen]; exact hi) =
      ((s.fieldType i ctor.fields[i]).instL g.levels).liftN (s.families.size + prior) i := by
    subst hFS
    rw [getElem_insertBinders, List.getElem_map, getElem_fieldTypes]
  simp only [hFSi, hFSlen, VExpr.liftN_liftN, liftVar_base'] at hfvar
  rw [show ctor.fields.length - i + j = j + (ctor.fields.length - i) by omega] at hfvar
  have hfvar' := hfvar.defeqU_r henv hΓ h3
  have hargslen : decl.nparams ≤ result.getAppFnArgs.2.length := by
    unfold VInductDecl.ValidIndAppAt at hvalid
    obtain ⟨type', _, _, _, _, _, hlen, _⟩ := hvalid
    have hlen' : result.getAppFnArgs.2.length = decl.nparams + type'.numIndices := hlen
    omega
  have hres := VExpr.mkApps_getAppFnArgs result
  rw [hhead] at hres
  generalize result.getAppFnArgs.2 = args at hres hargslen ⊢
  subst hres
  simp only [VExpr.instL_wrapForalls, VExpr.liftN_wrapForalls_at, VExpr.instL_mkApps,
    VExpr.liftN_mkApps, VExpr.instL, VExpr.liftN, List.map_map, Nat.zero_add,
    List.length_mapIdx, List.length_map] at hfvar'
  -- The hypothesis.
  rw [hypothesis_eq] at hIH
  have hDlen := length_hypothesisDomains g ctor prior j i r
  have hDget : ∀ k (hk : k < r.binders.length), (g.hypothesisDomains ctor prior j i r)[k]? =
      some (g.hypEmbed ctor prior j i r.binders[k] k) := by
    intro k hk
    rw [List.getElem?_eq_getElem (by rw [length_hypothesisDomains]; exact hk),
      getElem_hypothesisDomains]
  generalize g.hypothesisDomains ctor prior j i r = D at hIH hDlen hDget ⊢
  obtain ⟨hΓn, hbody⟩ := IsType.wrapForalls_inv henv hΓ hIH
  -- The motive variable.
  have hMlook := Lookup.reverse_append g.motives g.params.reverse r.target.val
    (by rw [hMolen]; exact r.target.isLt)
  have W3 : Ctx.LiftN (D.length + j + ctor.fields.length + prior) 0
      (g.motives.reverse ++ g.params.reverse) (D.reverse ++ g.hypothesisContext ctor prior j) := by
    have e : D.reverse ++ g.hypothesisContext ctor prior j =
        (D.reverse ++ IHS.reverse ++ FS.reverse ++ (g.minors.take prior).reverse) ++
          (g.motives.reverse ++ g.params.reverse) := by
      rw [hΓh]; simp only [List.append_assoc]
    rw [e]
    refine .zero _ ?_
    simp [hIHSlen, hFSlen, hMilen]
    omega
  have hmot := VEnv.HasType.bvar (env := env') (U := g.uvars) (Lookup.weakN W3 hMlook)
  rw [getElem_motives, motive_eq, VExpr.liftN_liftN, VExpr.liftN_wrapForalls_at,
    List.mapIdx_concat] at hmot
  simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, Nat.zero_add, vars_map_liftN,
    hMolen, liftVar_base'] at hmot
  rw [show s.families.size - 1 - r.target.val + (D.length + j + ctor.fields.length + prior) =
    ctor.fields.length + j + D.length + prior + (s.families.size - 1 - r.target.val) by omega]
    at hmot
  obtain ⟨hidxlen, hmajor⟩ := motive_spine_typing henv hΓn (by simp) hmot hbody
  rw [show VExpr.bvar (ctor.fields.length - 1 - i + j + D.length) =
    (VExpr.bvar (ctor.fields.length - 1 - i + j)).liftN D.length by simp [VExpr.liftN]] at hmajor
  -- Compare the field's normal form with the hypothesis.
  obtain ⟨t', ht'mem, ht'name⟩ := hM.family_name_mem r.target
  obtain ⟨hNlen, hcc, hdoms, hxs⟩ := spine_correspondence henv hΓn (hrigid family hfam)
    (ht'name ▸ hrigid t' ht'mem) hfvar' hmajor
  simp only [List.length_mapIdx, List.length_map] at hNlen
  simp only [List.length_map, length_insertBinders] at hidxlen
  have hembed : ∀ (e : VExpr) (k : Nat),
      VExpr.liftN (j + (ctor.fields.length - i))
        (VExpr.liftN (s.families.size + prior) (e.instL g.levels) (i + k)) k =
      g.hypEmbed ctor prior j i e k := fun e k => by
    rw [embed_comm _ (by omega)]; rfl
  refine ⟨hcc.symm, by omega, hidxlen, fun k hk hk' => ?_, ?_⟩
  · have hDk : D[k]'(by omega) = g.hypEmbed ctor prior j i r.binders[k] k := by
      have := hDget k hk
      rw [List.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    have := hdoms k (by omega) (by simp; omega)
    simp only [List.getElem_mapIdx, List.getElem_map, hembed, hDk, hDlen] at this
    exact this
  · have hsplit := hxs
    rw [← List.take_append_drop decl.nparams args, List.map_append] at hsplit
    obtain ⟨_, hdrop⟩ := List.forall₂_append_split hsplit (by
      have := hM.nparams
      simp [vars]; omega)
    have hsym := List.forall₂_symm (fun _ _ h => VEnv.IsDefEqU.symm h) hdrop
    simp only [Function.comp_def, hembed] at hsym
    rw [hNlen, hDlen] at hsym
    exact hsym

open VEnv in
/-- `recursiveShape_correspondence` for the hypotheses of a constructor's minor premise, in an
environment in which some generated recursor type is well formed (which gives both the typing of
the induction hypotheses, `generatedIHsWellTyped_of_recursorType`, and of their contexts). -/
theorem recursiveShape_correspondence_of_recursorType {env env' envTypes : VEnv}
    {decl : VInductDecl} (g : Instance s) (hM : s.Models env decl) (hsafe : s.isUnsafe = false)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) (hle : envTypes ≤ env')
    (henv : env'.WF) (hls : ∀ l ∈ g.levels, l.WF g.uvars)
    (hrigid : ∀ type ∈ decl.types, env'.Rigid type.name)
    (owner : Fin s.families.size) (H : env'.IsType g.uvars [] (g.recursorType owner))
    (index : Fin s.constructors.size) {j i : Nat} {r : Recursive s.families.size}
    (hj : j < (recursiveFields s.constructors[index]).length)
    (hp : (recursiveFields s.constructors[index])[j] = (i, r)) :
    ∃ (hi : i < s.constructors[index].fields.length) (domains : List VExpr) (result : VExpr)
      (family : VInductiveType),
      envTypes.IsDefEqU decl.uvars
        (((s.fieldTypes s.constructors[index]).take i).reverse ++ s.params.reverse)
        (s.fieldType i s.constructors[index].fields[i]) (VExpr.wrapForalls domains result) ∧
      (∀ domain ∈ domains, domain.SourceConstFree (decl.types.map (·.name))) ∧
      decl.ValidIndAppAt none (i + domains.length) result ∧
      family ∈ decl.types ∧
      result.getAppFnArgs.1 = .const family.name (VLevel.params decl.uvars) ∧
      s.families[r.target].name = family.name ∧
      r.binders.length = domains.length ∧
      r.indices.length = s.families[r.target].indices.length ∧
      (∀ k (hk : k < r.binders.length) (hk' : k < domains.length),
        env'.IsDefEqU g.uvars
          ((g.hypothesisDomains s.constructors[index] index.val j i r).reverse ++
            g.hypothesisContext s.constructors[index] index.val j)
          ((g.hypEmbed s.constructors[index] index.val j i r.binders[k] k).liftN
            (r.binders.length - k))
          ((g.hypEmbed s.constructors[index] index.val j i domains[k] k).liftN
            (r.binders.length - k))) ∧
      List.Forall₂ (env'.IsDefEqU g.uvars
          ((g.hypothesisDomains s.constructors[index] index.val j i r).reverse ++
            g.hypothesisContext s.constructors[index] index.val j))
        (r.indices.map (g.hypEmbed s.constructors[index] index.val j i · r.binders.length))
        ((result.getAppFnArgs.2.drop decl.nparams).map
          (g.hypEmbed s.constructors[index] index.val j i · r.binders.length)) := by
  have hO := hypothesis_onCtx_of_recursorType g henv owner H index j hj
  simp only [hp] at hO
  exact recursiveShape_correspondence g hM hsafe htypes hle henv hls hrigid
    (Array.getElem_mem_toList _) index.isLt hj hp hO.1 hO.2

end Instance
end InductiveSignature

end Lean4Lean
