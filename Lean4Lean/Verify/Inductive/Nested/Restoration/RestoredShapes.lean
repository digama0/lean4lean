import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.RestorationHead
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
import Lean4Lean.Verify.Inductive.Recursor.Signature.GeneratedShapes

/-! # Syntactic shapes of the restored recursors and equations

The restoration analogues of `Recursor/Signature/GeneratedShapes.lean`: the clauses
`rec_shape` and `rule_shape` of `VInductDecl.WF` for a recursor type and an equation read off
the generator (`Instance.recursorType`, `Instance.equation`) through a restoration table `r`,
and the closedness of a restored reduct.

Restoration fixes bound variables and maps every application spine to a spine with the same
head kind, so the Π- and λ-telescopes keep their lengths and their bvar-headed bodies. Only the
major premise changes shape: an auxiliary family restores to its container at the specialized
arguments (`HeadSpecialization.apply`), which are the specialization templates lifted past the
motives, minors and indices (`instantiateParams_vars`). That is the weakened
`VExpr.MajorApp`. The heads' templates must be scoped by the block's parameters (`r.Scoped`)
and every head must specialize exactly the block's `s.params.length` parameters. -/

namespace Lean4Lean
namespace InductiveSignature

open VExpr

/-! ### Telescope and list helpers -/

private theorem wrapForalls_piBinders_piBody : ∀ e : VExpr,
    VExpr.wrapForalls e.piBinders e.piBody = e
  | .forallE A B => by
    simp only [VExpr.piBinders, VExpr.piBody]
    exact congrArg (VExpr.forallE A) (wrapForalls_piBinders_piBody B)
  | .bvar _ | .sort _ | .const .. | .app .. | .proj .. | .lam .. => rfl

/-- A spine headed by a bound variable is neither a Π nor a λ. -/
private theorem bvar_spine (k : Nat) (args : List VExpr) :
    ((VExpr.bvar k).mkApps args).piBinders = [] ∧
      ((VExpr.bvar k).mkApps args).piBody = (VExpr.bvar k).mkApps args ∧
      ((VExpr.bvar k).mkApps args).lamArity = 0 ∧
      ((VExpr.bvar k).mkApps args).lamBody = (VExpr.bvar k).mkApps args := by
  have h : ((VExpr.bvar k).mkApps args).getAppFn = .bvar k := by simp [VExpr.getAppFn]
  generalize (VExpr.bvar k).mkApps args = e at h
  cases e <;> simp_all [VExpr.getAppFn, VExpr.piBinders, VExpr.piBody, VExpr.lamArity,
    VExpr.lamBody]

private theorem mapM_some_getElem? {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ {i : Nat} {a : α}, l[i]? = some a →
      ∃ b, l'[i]? = some b ∧ f a = some b
  | [], _, _, _, _, h => by simp at h
  | a :: as, l', h, i, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx ⊢; subst hx
              exact ⟨b, rfl, hb⟩
    | succ i => simpa using mapM_some_getElem? hbs (i := i) (by simpa using hx)

/-! ### Restoration of telescopes and spines -/

theorem Restoration.expr_wrapForalls_eq_some {r : Restoration} {ds : List VExpr}
    {body e : VExpr} (h : r.expr (VExpr.wrapForalls ds body) = some e) :
    ∃ ds' body', ds.mapM r.expr = some ds' ∧ r.expr body = some body' ∧
      e = VExpr.wrapForalls ds' body' := by
  rw [r.expr_wrapForalls] at h
  cases hd : ds.mapM r.expr <;> cases hb : r.expr body <;> simp [hd, hb] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem Restoration.expr_wrapLams_eq_some {r : Restoration} {ds : List VExpr}
    {body e : VExpr} (h : r.expr (VExpr.wrapLams ds body) = some e) :
    ∃ ds' body', ds.mapM r.expr = some ds' ∧ r.expr body = some body' ∧
      e = VExpr.wrapLams ds' body' := by
  induction ds generalizing e with
  | nil => exact ⟨[], e, rfl, h, rfl⟩
  | cons d ds ih =>
    obtain ⟨d', b', hd, hb, rfl⟩ := Restoration.expr_lam_parts h
    obtain ⟨ds', body', hds, hbody, rfl⟩ := ih hb
    refine ⟨d' :: ds', body', ?_, hbody, rfl⟩
    simp [List.mapM_cons, hd, hds]

theorem Restoration.expr_mkApps_bvar_eq_some {r : Restoration} {k : Nat} {args : List VExpr}
    {e : VExpr} (h : r.expr ((VExpr.bvar k).mkApps args) = some e) :
    ∃ args', args.mapM r.expr = some args' ∧ e = (VExpr.bvar k).mkApps args' := by
  rw [r.expr_mkApps_bvar] at h
  cases ha : args.mapM r.expr <;> simp [ha] at h
  exact ⟨_, rfl, h.symm⟩

/-- A restored constant spine is headed by the restored head name. -/
theorem Restoration.expr_mkApps_const_headConst {r : Restoration} {name : Name}
    {levels : List VLevel} {args : List VExpr} {e : VExpr}
    (h : r.expr ((VExpr.const name levels).mkApps args) = some e) :
    e.headConst? = some (r.headName name) := by
  obtain ⟨args', rfl⟩ := r.const_mkApps_exact h
  exact VExpr.headConst?_eq_some.2 ⟨_, by rw [getAppFn_mkApps]; rfl⟩

/-- Restoring a term whose Π-body is a bvar-headed spine keeps its Π-arity and the head of its
Π-body. -/
theorem Restoration.expr_bvarBody {r : Restoration} {e e' : VExpr} {k : Nat}
    {args : List VExpr} (hbody : e.piBody = (VExpr.bvar k).mkApps args)
    (h : r.expr e = some e') :
    e'.piArity = e.piArity ∧ (∃ ds', e.piBinders.mapM r.expr = some ds' ∧ e'.piBinders = ds') ∧
      ∃ args', args.mapM r.expr = some args' ∧ e'.piBody = (VExpr.bvar k).mkApps args' := by
  rw [← wrapForalls_piBinders_piBody e, hbody] at h
  obtain ⟨ds', body', hds, hb, rfl⟩ := Restoration.expr_wrapForalls_eq_some h
  obtain ⟨args', ha, rfl⟩ := Restoration.expr_mkApps_bvar_eq_some hb
  have hs := bvar_spine k args'
  refine ⟨?_, ⟨ds', hds, by rw [piBinders_wrapForalls, hs.1, List.append_nil]⟩, args', ha,
    by rw [piBody_wrapForalls, hs.2.1]⟩
  rw [← piBinders_length, ← piBinders_length, piBinders_wrapForalls, hs.1, List.append_nil,
    List.mapM_some_length hds]

/-! ### Closedness -/

private theorem ClosedN.subst_closed : ∀ {e : VExpr} {n k : Nat} {σ : VExpr.Subst},
    e.ClosedN n → (∀ i < n, (σ i).ClosedN k) → (e.subst σ).ClosedN k
  | .bvar i, _, _, _, he, hσ => hσ i he
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ => trivial
  | .app f a, _, _, _, he, hσ => ⟨ClosedN.subst_closed he.1 hσ, ClosedN.subst_closed he.2 hσ⟩
  | .proj _ _ e, _, _, _, he, hσ => ClosedN.subst_closed (e := e) he hσ
  | .lam d b, _, _, σ, he, hσ | .forallE d b, _, _, σ, he, hσ => by
    refine ⟨ClosedN.subst_closed he.1 hσ, ClosedN.subst_closed (n := _ + 1) he.2 ?_⟩
    intro i hi
    cases i with
    | zero => show (VExpr.bvar 0).ClosedN _; simp [VExpr.ClosedN]
    | succ i =>
      show ((σ i).liftN 1 0).ClosedN (_ + 1)
      exact (hσ i (by omega)).liftN

theorem Restoration.go_closedN {r : Restoration}
    (hsc : ∀ h ∈ r.heads, ∀ a ∈ h.arguments, a.ClosedN h.nparams) :
    ∀ {e : VExpr} {args : List VExpr} {e' : VExpr} {k : Nat}, e.ClosedN k →
      (∀ a ∈ args, a.ClosedN k) → Restoration.expr.go r e args = some e' → e'.ClosedN k
  | .app f a, args, e', k, he, hargs, h => by
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff] at h
    obtain ⟨a', ha, hf⟩ := h
    have ha' := Restoration.go_closedN (args := []) hsc he.2 (fun _ h => by cases h) ha
    exact Restoration.go_closedN hsc he.1 (by
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      exacts [ha', hargs x hx]) hf
  | .const name levels, args, e', k, _, hargs, h => by
    simp only [Restoration.expr.go] at h
    split at h
    · rename_i spec hs
      have hspec := hsc spec (List.mem_of_find?_eq_some hs)
      unfold HeadSpecialization.apply at h
      split at h
      · cases h
      · rename_i hgood
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        have hlen : spec.nparams ≤ args.length := by
          apply Nat.le_of_not_gt; intro ht; simp [ht] at hgood
        refine VExpr.ClosedN.mkApps_closed trivial ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          refine ClosedN.subst_closed (n := (args.take spec.nparams).length) ?_ ?_
          · simpa [List.length_take, Nat.min_eq_left hlen] using (hspec a ha).instL
          · intro i hi
            simp only [hi, dite_true]
            exact hargs _ (List.mem_of_mem_take (List.getElem_mem _))
        · exact hargs x (List.mem_of_mem_drop hx)
    · cases h
      exact VExpr.ClosedN.mkApps_closed trivial hargs
  | .bvar i, args, e', k, he, hargs, h => by
    cases h; exact VExpr.ClosedN.mkApps_closed he hargs
  | .sort u, args, e', k, _, hargs, h => by
    cases h; exact VExpr.ClosedN.mkApps_closed trivial hargs
  | .lam d b, args, e', k, he, hargs, h | .forallE d b, args, e', k, he, hargs, h => by
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact VExpr.ClosedN.mkApps_closed
      ⟨Restoration.go_closedN (args := []) hsc he.1 (fun _ h => by cases h) hd,
        Restoration.go_closedN (args := []) hsc he.2 (fun _ h => by cases h) hb⟩ hargs
  | .proj n i m, args, e', k, he, hargs, h => by
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨m', hm, rfl⟩ := h
    have hm' : m'.ClosedN k :=
      Restoration.go_closedN (e := m) (args := []) (e' := m') hsc he (fun _ h => by cases h) hm
    exact VExpr.ClosedN.mkApps_closed (fn := .proj n i m') hm' hargs

/-- Restoration preserves `ClosedN` when the heads' templates are scoped by their
parameters. -/
theorem Restoration.expr_closedN {r : Restoration}
    (hsc : ∀ h ∈ r.heads, ∀ a ∈ h.arguments, a.ClosedN h.nparams) {e e' : VExpr} {k : Nat}
    (he : e.ClosedN k) (h : r.expr e = some e') : e'.ClosedN k :=
  Restoration.go_closedN (args := []) hsc he (fun _ h => by cases h) h

/-- (3) The reduct of a restored equation is closed when the generated one is. -/
theorem Restoration.equation_rhs_closed {r : Restoration} (hr : r.Scoped)
    {equation df : VDefEq} (hdf : r.equation equation = some df)
    (hc : equation.rhs.Closed) : df.rhs.Closed :=
  Restoration.expr_closedN (fun h hh => (hr.2.2.1 h hh).2) hc (Restoration.equation_parts hdf).2.1

/-! ### The restored binders of the recursor telescope -/

section

variable {s : InductiveSignature}

/-- A restored motive has the motive shape, its last binder headed by the restored family. -/
theorem Restoration.expr_motive {r : Restoration} (g : Instance s) {family : Family}
    {prior : Nat} {A : VExpr} (h : r.expr (g.motive family prior) = some A) :
    A.MotiveShape ∧ A.motiveFormer? = some (r.headName family.name) := by
  simp only [Instance.motive] at h
  obtain ⟨ds', body', hds, hb, rfl⟩ := Restoration.expr_wrapForalls_eq_some h
  simp only [Restoration.expr_sort, Option.some.injEq] at hb
  subst hb
  obtain ⟨is', ms, -, hm, rfl⟩ := List.mapM_append_eq_some hds
  obtain ⟨m', hm', rfl⟩ : ∃ m', r.expr (VExpr.mkApps (.const family.name g.levels)
      (vars s.params.length (prior + (insertBinders (family.indices.map (·.instL g.levels))
        prior).length) ++ vars (insertBinders (family.indices.map (·.instL g.levels))
          prior).length 0)) = some m' ∧ ms = [m'] := by
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hm
    obtain ⟨m', hm', _, rfl, rfl⟩ := hm
    exact ⟨m', hm', rfl⟩
  have hhead := Restoration.expr_mkApps_const_headConst hm'
  have hformer : (VExpr.wrapForalls (is' ++ [m']) (.sort g.targetLevel)).motiveFormer? =
      some (r.headName family.name) := by
    simp only [VExpr.motiveFormer?, piBinders_wrapForalls]
    simp [VExpr.piBinders, hhead]
  refine ⟨⟨⟨g.targetLevel, ?_⟩, by rw [hformer]; rfl⟩, hformer⟩
  rw [piBody_wrapForalls]; rfl

/-- A restored minor keeps its Π-arity, stays `MinorHeaded`, and is `MinorFor` the restored
constructor. -/
theorem Restoration.expr_minor {r : Restoration} (g : Instance s)
    {ctor : Constructor s.families.size} {prior : Nat} {A : VExpr}
    (h : r.expr (g.minor ctor prior) = some A) :
    A.piArity = (g.minor ctor prior).piArity ∧ A.MinorHeaded prior s.families.size ∧
      A.MinorFor (r.headName ctor.name) := by
  obtain ⟨-, args, hbody⟩ := g.minor_pi ctor prior
  obtain ⟨harity, -, args', hargs, hbody'⟩ := Restoration.expr_bvarBody hbody h
  obtain ⟨pre', last, -, hlast, rfl⟩ := List.mapM_append_eq_some hargs
  obtain ⟨c', hc', rfl⟩ : ∃ c', r.expr (g.constructorApp ctor (s.families.size + prior)
      (Instance.recursiveFields ctor).length) = some c' ∧ last = [c'] := by
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hlast
    obtain ⟨c', hc', _, rfl, rfl⟩ := hlast
    exact ⟨c', hc', rfl⟩
  refine ⟨harity, ?_, ⟨_, by rw [hbody', getAppFn_mkApps]; rfl⟩, c', ?_, ?_⟩
  · obtain ⟨k, hk, hfn⟩ := g.minor_minorHeaded ctor prior
    rw [hbody, getAppFn_mkApps] at hfn
    exact ⟨k, hk, by rw [hbody', getAppFn_mkApps, harity]; exact hfn⟩
  · rw [hbody', VExpr.getAppArgs_mkApps]; simp [VExpr.getAppArgs]
  · simp only [Instance.constructorApp] at hc'
    exact Restoration.expr_mkApps_const_headConst hc'

/-- The restored major premise: the restored family at terms over the parameters (the
specialization templates for an auxiliary family) and the index variables. -/
theorem Restoration.expr_recursorMajor {r : Restoration} (hr : r.Scoped)
    (hnp : ∀ h ∈ r.heads, h.nparams = s.params.length) (g : Instance s)
    (owner : Fin s.families.size) {M : VExpr} (h : r.expr (g.recursorMajor owner) = some M) :
    M.headConst? = some (r.headName s.families[owner].name) ∧
      M.MajorApp (r.headName s.families[owner].name) s.params.length s.families.size
        s.constructors.size s.families[owner].indices.length := by
  have hhead : M.headConst? = some (r.headName s.families[owner].name) := by
    simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp] at h
    exact Restoration.expr_mkApps_const_headConst h
  refine ⟨hhead, ?_⟩
  simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp] at h
  rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars] at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at h
  simp only [Restoration.expr.go] at h
  split at h
  · rename_i spec hs
    have hmem := List.mem_of_find?_eq_some hs
    have hname : r.headName s.families[owner].name = spec.target := by
      unfold Restoration.headName; rw [hs]
    have hspecnp := hnp spec hmem
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      rw [hname, hspecnp, List.take_left' (by simp), List.drop_left' (by simp)]
      refine ⟨_, _, rfl, fun a ha => ?_⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      exact ⟨t.instL g.levels, by simpa [hspecnp] using ((hr.2.2.1 spec hmem).2 t ht).instL,
        instantiateParams_vars (by simpa [hspecnp] using ((hr.2.2.1 spec hmem).2 t ht).instL) _⟩
  · rename_i hs
    have hname : r.headName s.families[owner].name =
        r.recursorName s.families[owner].name := by
      unfold Restoration.headName; rw [hs]
    cases h
    rw [hname]
    exact VExpr.MajorApp.of_params ⟨g.levels, rfl⟩

private theorem Instance.recursorPrefix_motive (g : Instance s) (owner : Fin s.families.size)
    (i : Nat) (hi : i < s.families.size) :
    (g.recursorPrefix owner)[s.params.length + i]? = some (g.motive s.families[i] i) := by
  simp only [Instance.recursorPrefix, List.append_assoc]
  rw [List.getElem?_append_add i (by simp [Instance.params]), List.getElem?_append_left
    (by simp [Instance.motives, hi])]
  simp [Instance.motives, hi]

private theorem Instance.recursorPrefix_minor (g : Instance s) (owner : Fin s.families.size)
    (i : Nat) (hi : i < s.constructors.size) :
    (g.recursorPrefix owner)[s.params.length + s.families.size + i]? =
      some (g.minor s.constructors[i] i) := by
  simp only [Instance.recursorPrefix, List.append_assoc]
  rw [Nat.add_assoc, List.getElem?_append_add _ (by simp [Instance.params]),
    List.getElem?_append_add i (by simp [Instance.motives]), List.getElem?_append_left
    (by simp [Instance.minors, hi])]
  simp [Instance.minors, hi]

/-- (1) `rec_shape` of a restored generated recursor. -/
theorem Restoration.recursorType_recShape {r : Restoration} (hr : r.Scoped)
    (hnp : ∀ h ∈ r.heads, h.nparams = s.params.length) (g : Instance s)
    (owner : Fin s.families.size) {T : VExpr} (h : r.expr (g.recursorType owner) = some T) :
    T.RecShape s.params.length s.families.size s.constructors.size
      s.families[owner].indices.length := by
  obtain ⟨pre, major, hpre, hmajor, rfl⟩ := r.expr_recursorType_eq_some h
  have hbody := bvar_spine (s.families[owner].indices.length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val))
    (vars s.families[owner].indices.length 1 ++ [.bvar 0])
  have hbinders : (VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner)).piBinders =
      pre ++ [major] := by
    rw [piBinders_wrapForalls, Instance.recursorBody, hbody.1, List.append_nil]
  have hprelen : pre.length = s.params.length + s.families.size + s.constructors.size +
      s.families[owner].indices.length := by
    rw [List.mapM_some_length hpre, g.recursorPrefix_length]
  have hpos : ∀ {i : Nat} {a : VExpr}, (g.recursorPrefix owner)[i]? = some a →
      ∃ b, (VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner)).piBinders[i]? =
        some b ∧ r.expr a = some b := by
    intro i a hi
    obtain ⟨b, hb, hab⟩ := mapM_some_getElem? hpre hi
    refine ⟨b, ?_, hab⟩
    rw [hbinders, List.getElem?_append_left (by
      have := (List.getElem?_eq_some_iff.mp hb).1; exact this)]
    exact hb
  have hmot : ∀ i (hi : i < s.families.size), ∃ A,
      (VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner)).piBinders[
        s.params.length + i]? = some A ∧ A.MotiveShape ∧
        A.motiveFormer? = some (r.headName s.families[i].name) := by
    intro i hi
    obtain ⟨A, hA, hrA⟩ := hpos (g.recursorPrefix_motive owner i hi)
    exact ⟨A, hA, Restoration.expr_motive g hrA⟩
  obtain ⟨hmhead, hmapp⟩ := Restoration.expr_recursorMajor hr hnp g owner hmajor
  refine ⟨?_, ?_, ?_, owner.val, owner.isLt, ?_, ?_⟩
  · rw [← piBinders_length, hbinders]; simp [hprelen]
  · intro i hi
    obtain ⟨A, hA, hshape, -⟩ := hmot i hi
    exact ⟨A, hA, hshape⟩
  · intro i hi
    obtain ⟨A, hA, hrA⟩ := hpos (g.recursorPrefix_minor owner i hi)
    exact ⟨A, hA, (Restoration.expr_minor g hrA).2.1⟩
  · refine ⟨major, ?_, _, hmhead, hmapp, ?_⟩
    · rw [hbinders, ← hprelen, List.getElem?_append_right (by omega)]; simp
    · obtain ⟨A, hA, -, hformer⟩ := hmot owner.val owner.isLt
      exact ⟨A, hA, by simpa using hformer⟩
  · rw [piBody_wrapForalls, Instance.recursorBody, hbody.2.1, bvarsDesc_succ_zero]
    change _ = VExpr.mkApps _ (vars s.families[owner].indices.length 1 ++ [.bvar 0])
    congr 2; omega

/-- (2) `rule_shape` of a restored generated equation: its reduct is a `RuleShape` reduct for
minor `index` of the restored recursor of its owner, the minor binder being `MinorFor` the
restored constructor. -/
theorem Restoration.equation_ruleShape {r : Restoration} (g : Instance s)
    (index : Fin s.constructors.size) {T : VExpr} {df : VDefEq}
    (hT : r.expr (g.recursorType s.constructors[index].owner) = some T)
    (hdf : r.equation (g.equation index) = some df) :
    ∃ j < s.constructors.size, ∃ A, T.piBinders[s.params.length + s.families.size + j]? =
        some A ∧ A.MinorFor (r.headName s.constructors[index].name) ∧
      s.constructors[index].fields.length ≤ A.piArity ∧
      df.rhs.RuleShape s.params.length s.families.size s.constructors.size
        s.constructors[index].fields.length
        (A.piArity - s.constructors[index].fields.length) j := by
  obtain ⟨pre, major, hpre, -, rfl⟩ := r.expr_recursorType_eq_some hT
  have hbody := bvar_spine (s.families[s.constructors[index].owner].indices.length + 1 +
      s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val))
    (vars s.families[s.constructors[index].owner].indices.length 1 ++ [.bvar 0])
  obtain ⟨A, hA, hrA⟩ := mapM_some_getElem? hpre
    (g.recursorPrefix_minor s.constructors[index].owner index.val index.isLt)
  obtain ⟨harity, -, hfor⟩ := Restoration.expr_minor g hrA
  obtain ⟨hmarity, -⟩ := g.minor_pi s.constructors[index] index.val
  refine ⟨index.val, index.isLt, A, ?_, by simpa using hfor, ?_, ?_⟩
  · rw [piBinders_wrapForalls, Instance.recursorBody, hbody.1, List.append_nil,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp hA).1]
    exact hA
  · rw [harity]; simp only [Fin.getElem_fin] at hmarity ⊢; rw [hmarity]; simp
  · rw [harity]; simp only [Fin.getElem_fin] at hmarity ⊢; rw [hmarity, Nat.add_sub_cancel_left]
    have hrhs := (Restoration.equation_parts hdf).2.1
    simp only [Instance.equation] at hrhs
    obtain ⟨ds', body', hds, hb, hdfeq⟩ := Restoration.expr_wrapLams_eq_some hrhs
    obtain ⟨args', hargs, rfl⟩ := Restoration.expr_mkApps_bvar_eq_some hb
    obtain ⟨vs, calls', hvs, hcalls, rfl⟩ := List.mapM_append_eq_some hargs
    rw [r.mapM_expr_vars, Option.some.injEq] at hvs
    subst hvs
    have hs := bvar_spine (s.constructors[index].fields.length + s.constructors.size - 1 -
      index.val) (vars s.constructors[index].fields.length 0 ++ calls')
    refine ⟨?_, calls', ?_, ?_⟩
    · rw [hdfeq, lamArity_wrapLams, hs.2.2.1, List.mapM_some_length hds]
      simp [insertBinders, fieldTypes, Instance.params, Instance.motives, Instance.minors]
      omega
    · rw [List.mapM_some_length hcalls]; simp
    · rw [hdfeq, lamBody_wrapLams, hs.2.2.2]
      change VExpr.mkApps _ (bvarsDesc 0 _ ++ calls') = _
      simp only [Fin.getElem_fin]
      congr 2; omega

end

end InductiveSignature
end Lean4Lean
