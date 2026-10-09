import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRuleAvoidance
import Lean4Lean.Verify.Inductive.Nested.CaseEliminators.Avoidance

/-! # Guardedness of the restored generated equations, from the generator

The right-hand side of a generated equation (`Instance.equation`) is the
minor premise applied to the constructor fields and to the generated
recursive calls (`Instance.recursiveCall`). Restoration (`Restoration.expr`)
keeps this spine: it renames the recursor heads and restores the binder
domains and indices. Once the restored domains and indices mention no block
recursor (`mentionsAnyConst`), the restored right-hand side is guarded
(`GuardedIota`) for the recursive field variables of the generator, and the
complete closed right-hand side satisfies `GuardedRuleRhs`.

The avoidance is reduced to the avoidance of the generated recursor type
(`recursorType_pieces_avoid`): the generated recursor type contains every
parameter, motive and minor premise, hence every field type, constructor
index and recursive binder and index, up to lifting and universe
instantiation. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

theorem VExpr.IsFieldApp.mkApps {field depth : Nat} {fieldVars : List Nat}
    (hfield : field ∈ fieldVars) (args : List VExpr) :
    (VExpr.mkApps (.bvar (field + depth)) args).IsFieldApp fieldVars depth := by
  refine ⟨field, hfield, args, ?_⟩
  simpa [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] using
    VExpr.getAppFnArgs_mkApps (.bvar (field + depth)) args

/-! ### Guardedness from constant avoidance -/

/-- An expression mentioning no recursor is guarded, for any field variables
and at any depth. -/
theorem VExpr.GuardedIota.of_mentionsAnyConst {N : List Name} {fv : List Nat} :
    ∀ {e : VExpr} {d : Nat}, e.mentionsAnyConst N = false → e.GuardedIota N fv d
  | .bvar _, _, _ => .bvar
  | .sort _, _, _ => .sort
  | .elim .., _, _ => .elim
  | .const _ _, _, h => .const (by simpa [VExpr.mentionsAnyConst] using h)
  | .app _ _, _, h => by
    simp only [VExpr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    exact .app (of_mentionsAnyConst h.1) (of_mentionsAnyConst h.2)
  | .lam _ _, _, h => by
    simp only [VExpr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    exact .lam (of_mentionsAnyConst h.1) (of_mentionsAnyConst h.2)
  | .forallE _ _, _, h => by
    simp only [VExpr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    exact .forallE (of_mentionsAnyConst h.1) (of_mentionsAnyConst h.2)
  | .proj _ _ _, _, h => by
    simp only [VExpr.mentionsAnyConst] at h
    exact .proj (of_mentionsAnyConst h)

/-- Closing a guarded body over recursor-free lambda domains. -/
theorem VExpr.GuardedIota.wrapLams_of_mentions {N : List Name} {fv : List Nat} :
    ∀ {D : List VExpr} {body : VExpr} {depth : Nat},
      (∀ d ∈ D, d.mentionsAnyConst N = false) →
      body.GuardedIota N fv (depth + D.length) →
      (VExpr.wrapLams D body).GuardedIota N fv depth
  | [], _, _, _, h => by simpa [VExpr.wrapLams] using h
  | d :: D, _, _, hD, h => by
    simp only [VExpr.wrapLams, List.foldr_cons]
    refine .lam (of_mentionsAnyConst (hD d List.mem_cons_self)) ?_
    exact wrapLams_of_mentions (fun d' hd' => hD d' (List.mem_cons_of_mem _ hd'))
      (by simpa [Nat.add_assoc, Nat.add_comm 1 D.length] using h)

/-- A closed rule right-hand side whose lambda telescope mentions no recursor
and whose body is guarded. -/
theorem VExpr.GuardedRuleRhs.wrapLams_of_mentions {N : List Name} {fv : List Nat} :
    ∀ {D : List VExpr} {body : VExpr},
      (∀ d ∈ D, d.mentionsAnyConst N = false) →
      body.GuardedIota N fv 0 →
      (VExpr.wrapLams D body).GuardedRuleRhs N
  | [], _, _, h => .body fv (by simpa [VExpr.wrapLams] using h)
  | d :: D, _, hD, h => by
    simp only [VExpr.wrapLams, List.foldr_cons]
    exact .lam (VExpr.GuardedIota.of_mentionsAnyConst (hD d List.mem_cons_self))
      (wrapLams_of_mentions (fun d' hd' => hD d' (List.mem_cons_of_mem _ hd')) h)

/-! ### List helpers -/

private theorem forall₂_concat_left {R : α → β → Prop} :
    ∀ {l : List α} {x : α} {r : List β}, List.Forall₂ R (l ++ [x]) r →
      ∃ r' y, r = r' ++ [y] ∧ List.Forall₂ R l r' ∧ R x y
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨r', y, rfl, Hl, Hx⟩ := forall₂_concat_left t
    exact ⟨_ :: r', y, rfl, .cons h Hl, Hx⟩

private theorem forall₂_mem_right {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → ∀ y ∈ r, ∃ x ∈ l, R x y
  | _, _, .nil, _, hy => by simp at hy
  | _, _, .cons h t, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hxy⟩ := forall₂_mem_right t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

private theorem mem_insertBinders {l : List VExpr} {c : Nat} {e : VExpr} (he : e ∈ l) :
    ∃ i, e.liftN c i ∈ insertBinders l c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  refine ⟨i, List.mem_map.mpr ⟨(l[i], i), ?_, rfl⟩⟩
  exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hi])

private theorem mem_zipIdx_map {l : List α} {f : α × Nat → β} {x : α} (hx : x ∈ l) :
    ∃ i, f (x, i) ∈ l.zipIdx.map f := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact ⟨i, List.mem_map.mpr ⟨(l[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp [hi]), rfl⟩⟩

/-! ### The pieces of a generated recursor type -/

/-- The recursive fields of a constructor are listed at strictly increasing
field positions below the field count. -/
theorem recursiveFields_positions {s : InductiveSignature} (ctor : Constructor s.families.size) :
    ((Instance.recursiveFields ctor).map Prod.fst).Pairwise (· < ·) ∧
      ∀ p ∈ Instance.recursiveFields ctor, p.1 < ctor.fields.length := by
  have hsplit : (Instance.recursiveFields ctor).map Prod.fst =
      ((ctor.fields.zipIdx.filter fun p => match p.1 with
        | .external _ => false | .recursive _ _ => true)).map Prod.snd := by
    simp only [Instance.recursiveFields]
    generalize ctor.fields.zipIdx = l
    induction l with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨field, i⟩ := p
      cases field <;> simp [ih]
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    have h : (ctor.fields.zipIdx.map Prod.snd).Pairwise (· < ·) := by
      rw [List.zipIdx_map_snd]
      exact List.pairwise_lt_range' 1 (by omega)
    exact (h.sublist ((List.filter_sublist).map Prod.snd))
  · intro p hp
    simp only [Instance.recursiveFields, List.mem_filterMap] at hp
    obtain ⟨⟨field, i⟩, hmem, hsome⟩ := hp
    have hi : i < ctor.fields.length := by
      have := List.mem_zipIdx_iff_getElem?.mp hmem
      simp only at this
      exact (List.getElem?_eq_some_iff.mp this).1
    cases field <;> simp at hsome
    subst hsome
    exact hi

/-- The recursive arguments of a constructor's generated equation form a
sublist of its field variables. -/
theorem recursiveFields_args_sublist {s : InductiveSignature}
    (ctor : Constructor s.families.size) :
    List.Sublist (((Instance.recursiveFields ctor).map Prod.fst).map fun i =>
        VExpr.bvar (ctor.fields.length - 1 - i))
      (vars ctor.fields.length 0) := by
  simp only [List.map_map, Function.comp_def]
  have hvars : vars ctor.fields.length 0 =
      ctor.fields.zipIdx.map fun p => VExpr.bvar (ctor.fields.length - 1 - p.2) := by
    apply List.ext_getElem
    · simp [vars]
    · intro i h1 h2
      simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, List.getElem_zipIdx]
      simp only [vars, List.length_map, List.length_reverse, List.length_range] at h1
      congr 1
      omega
  have hsplit : (Instance.recursiveFields ctor).map (fun p =>
        VExpr.bvar (ctor.fields.length - 1 - p.1)) =
      ((ctor.fields.zipIdx.filter fun p => match p.1 with
        | .external _ => false | .recursive _ _ => true)).map
        (fun p => VExpr.bvar (ctor.fields.length - 1 - p.2)) := by
    simp only [Instance.recursiveFields]
    generalize ctor.fields.zipIdx = l
    induction l with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨field, i⟩ := p
      cases field <;> simp [ih]
  rw [hsplit, hvars]
  exact (List.filter_sublist).map _

/-- Avoidance of the generated recursor type of any owner is avoidance of
every parameter, motive and minor premise, of every field type and index of
every constructor, and of the binders and indices of its recursive fields. -/
theorem recursorType_pieces_avoid {s : InductiveSignature} (g : Instance s) {L : List Name}
    (o : Fin s.families.size) (h : (g.recursorType o).containsAnyConst L = false) :
    (∀ d ∈ g.params ++ g.motives ++ g.minors, d.containsAnyConst L = false) ∧
    ∀ k : Fin s.constructors.size,
      (∀ e ∈ s.fieldTypes s.constructors[k], e.containsAnyConst L = false) ∧
      (∀ e ∈ s.constructors[k].indices, e.containsAnyConst L = false) ∧
      ∀ p ∈ Instance.recursiveFields s.constructors[k],
        (∀ b ∈ p.2.binders, b.containsAnyConst L = false) ∧
        (∀ e ∈ p.2.indices, e.containsAnyConst L = false) := by
  unfold Instance.recursorType at h
  have hdoms := (VExpr.containsAnyConst_wrapForalls_eq_false_iff.mp h).1
  have hprefix : ∀ d ∈ g.params ++ g.motives ++ g.minors, d.containsAnyConst L = false :=
    fun d hd => hdoms d (List.mem_append_left _ (List.mem_append_left _ hd))
  refine ⟨hprefix, fun k => ?_⟩
  have hminor : (g.minor s.constructors[k] k.val).containsAnyConst L = false := by
    apply hprefix
    refine List.mem_append_right _ (List.mem_map.mpr ⟨(s.constructors[k], k.val), ?_, rfl⟩)
    exact List.mem_zipIdx_iff_getElem?.mpr (by simp)
  unfold Instance.minor at hminor
  obtain ⟨hmdoms, hmbody⟩ := VExpr.containsAnyConst_wrapForalls_eq_false_iff.mp hminor
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi⟩ := mem_insertBinders (c := s.families.size + k.val)
      (List.mem_map_of_mem (f := (·.instL g.levels)) he)
    simpa using hmdoms _ (List.mem_append_left _ hi)
  · intro e he
    have hargs := ((VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mp hmbody).2
    simpa using hargs _ (List.mem_append_left _ (List.mem_map_of_mem he))
  · intro p hp
    obtain ⟨j, hj⟩ := mem_zipIdx_map (f := fun (x : (Nat × Recursive s.families.size) × Nat) =>
      g.hypothesis s.constructors[k] k.val x.2 x.1.1 x.1.2) hp
    have hhyp := hmdoms _ (List.mem_append_right _ hj)
    unfold Instance.hypothesis at hhyp
    obtain ⟨hhdoms, hhbody⟩ := VExpr.containsAnyConst_wrapForalls_eq_false_iff.mp hhyp
    refine ⟨fun b hb => ?_, fun e he => ?_⟩
    · obtain ⟨i, hi⟩ := mem_zipIdx_map (f := fun (x : VExpr × Nat) =>
        Instance.underFields (x.1.instL g.levels) p.1 s.constructors[k].fields.length j
          (s.families.size + k.val) x.2) hb
      simpa [Instance.underFields] using hhdoms _ hi
    · have hargs := ((VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mp hhbody).2
      simpa [Instance.underFields] using hargs _ (List.mem_append_left _ (List.mem_map_of_mem he))

/-! ### Restoration of the generated right-hand side -/

theorem Restoration.expr_mkApps_const_of_find_none {r : Restoration} {c : Name}
    {ls : List VLevel} (args : List VExpr)
    (h : r.heads.find? (fun h => h.auxiliary == c) = none) :
    r.expr (VExpr.mkApps (.const c ls) args) =
      (args.mapM r.expr).map fun args' => VExpr.mkApps (.const (r.recursorName c) ls) args' := by
  rw [Restoration.expr_mkApps]
  cases ha : args.mapM r.expr with
  | none => rfl
  | some args' => simp [Restoration.expr.go, h]

private theorem restored_vars {r : Restoration} {n below : Nat} {out : List VExpr}
    (H : List.Forall₂ (fun a b => r.expr a = some b) (vars n below) out) : out = vars n below := by
  have h := List.mapM_eq_some.mpr H
  rw [Restoration.mapM_expr_vars] at h
  exact (Option.some.inj h).symm

private theorem restored_bvar_mkApps_vars {r : Restoration} {i n below : Nat} {out : VExpr}
    (h : r.expr (VExpr.mkApps (.bvar i) (vars n below)) = some out) :
    out = VExpr.mkApps (.bvar i) (vars n below) := by
  rw [Restoration.expr_mkApps_bvar, Restoration.mapM_expr_vars] at h
  exact (Option.some.inj h).symm

private theorem guarded_bvar_mkApps_vars {N : List Name} {fv : List Nat} {d i n below : Nat} :
    (VExpr.mkApps (.bvar i) (vars n below)).GuardedIota N fv d := by
  apply VExpr.GuardedIota.mkApps .bvar
  intro a ha
  simp only [vars, List.mem_map] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact .bvar

/-- **A restored generated recursive call is guarded**: its lambda domains
mention no recursor, its head is the restored name of a block recursor, its
leading arguments are variables and restored indices mentioning no recursor,
and its major premise is the field variable applied to the local binders. -/
theorem restoredRecursiveCall_guarded {s : InductiveSignature} (g : Instance s)
    (r : Restoration) {N L : List Name} {fv : List Nat}
    (hmention : ∀ e out, e.containsAnyConst L = false → r.expr e = some out →
      out.mentionsAnyConst N = false)
    (hhead : ∀ o, r.heads.find? (fun h => h.auxiliary == g.recursorName o) = none)
    (hmem : ∀ o, r.recursorName (g.recursorName o) ∈ N)
    (ctor : Constructor s.families.size) (field : Nat) (rec : Recursive s.families.size)
    (hbinders : ∀ b ∈ rec.binders, b.containsAnyConst L = false)
    (hindices : ∀ e ∈ rec.indices, e.containsAnyConst L = false)
    (hfield : ctor.fields.length - 1 - field ∈ fv)
    {out : VExpr} (h : r.expr (g.recursiveCall ctor field rec) = some out) :
    out.GuardedIota N fv 0 := by
  unfold Instance.recursiveCall at h
  simp only [Instance.recursorHead] at h
  rw [Restoration.expr_wrapLams_eq] at h
  obtain ⟨doms', hdoms, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body', hbody, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [Restoration.expr_mkApps_const_of_find_none _ (hhead _)] at hbody
  obtain ⟨args', hargs, rfl⟩ := Option.map_eq_some_iff.mp hbody
  have Hd := List.mapM_eq_some.mp hdoms
  have Ha := List.mapM_eq_some.mp hargs
  have hlen : doms'.length = rec.binders.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq Hd]; simp
  apply VExpr.GuardedIota.wrapLams_of_mentions
  · intro d hd
    obtain ⟨d0, hd0, hr⟩ := forall₂_mem_right Hd d hd
    refine hmention d0 d ?_ hr
    simp only [List.mem_map] at hd0
    obtain ⟨⟨b, i⟩, hbi, rfl⟩ := hd0
    simpa [Instance.underFields] using hbinders b (List.fst_mem_of_mem_zipIdx hbi)
  · obtain ⟨init', major', rfl, Hinit, Hmajor⟩ := forall₂_concat_left Ha
    have hmajor := restored_bvar_mkApps_vars Hmajor
    subst hmajor
    refine .recCall (hmem _) ?_ ?_
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨a0, ha0, hr⟩ := forall₂_mem_right Hinit a ha
        rcases List.mem_append.mp ha0 with ha0 | ha0
        · simp only [vars, List.mem_map] at ha0
          obtain ⟨_, _, rfl⟩ := ha0
          simp only [Restoration.expr_bvar, Option.some.injEq] at hr
          subst hr
          exact .bvar
        · apply VExpr.GuardedIota.of_mentionsAnyConst
          refine hmention a0 a ?_ hr
          simp only [List.mem_map] at ha0
          obtain ⟨e, he, rfl⟩ := ha0
          simpa [Instance.underFields] using hindices e he
      · simp only [List.mem_singleton] at ha
        subst ha
        exact guarded_bvar_mkApps_vars
    · have hidx : ctor.fields.length - 1 - field +
          (rec.binders.zipIdx.map fun (x : VExpr × Nat) =>
            Instance.underFields (x.1.instL g.levels) field ctor.fields.length 0
              (s.families.size + s.constructors.size) x.2).length =
          ctor.fields.length - 1 - field + (0 + doms'.length) := by
        simp [hlen]
      rw [hidx]
      exact VExpr.IsFieldApp.mkApps hfield _

/-- The field variables of the recursive fields of a constructor, as de
Bruijn indices beneath the fields of its generated equation. -/
def recursiveFieldVars {s : InductiveSignature} (ctor : Constructor s.families.size) :
    List Nat :=
  ((Instance.recursiveFields ctor).map Prod.fst).map fun i => ctor.fields.length - 1 - i

/-- **The restored right-hand side of a generated equation.** Under the
avoidance of the generated recursor type's pieces, the restoration of the
right-hand side of the `k`-th generated equation is the restored domain
telescope over the minor premise applied to the field variables and to the
restored recursive calls; the domains mention no recursor and the body is
guarded for the recursive field variables. -/
theorem restoredEquation_rhs {s : InductiveSignature} (g : Instance s)
    (r : Restoration) {N L : List Name}
    (hmention : ∀ e out, e.containsAnyConst L = false → r.expr e = some out →
      out.mentionsAnyConst N = false)
    (hhead : ∀ o, r.heads.find? (fun h => h.auxiliary == g.recursorName o) = none)
    (hmem : ∀ o, r.recursorName (g.recursorName o) ∈ N)
    (hprefix : ∀ d ∈ g.params ++ g.motives ++ g.minors, d.containsAnyConst L = false)
    (k : Fin s.constructors.size)
    (hfields : ∀ e ∈ s.fieldTypes s.constructors[k], e.containsAnyConst L = false)
    (hrec : ∀ p ∈ Instance.recursiveFields s.constructors[k],
      (∀ b ∈ p.2.binders, b.containsAnyConst L = false) ∧
      (∀ e ∈ p.2.indices, e.containsAnyConst L = false))
    {rule : VDefEq} (hrule : r.equation (g.equation k) = some rule) :
    ∃ D calls,
      (g.params ++ g.motives ++ g.minors ++
        insertBinders ((s.fieldTypes s.constructors[k]).map (·.instL g.levels))
          (s.families.size + s.constructors.size)).mapM r.expr = some D ∧
      (∀ d ∈ D, d.mentionsAnyConst N = false) ∧
      calls.length = (Instance.recursiveFields s.constructors[k]).length ∧
      rule.rhs = VExpr.wrapLams D (VExpr.mkApps
        (.bvar (s.constructors[k].fields.length + s.constructors.size - 1 - k.val))
        (vars s.constructors[k].fields.length 0 ++ calls)) ∧
      (VExpr.mkApps
        (.bvar (s.constructors[k].fields.length + s.constructors.size - 1 - k.val))
        (vars s.constructors[k].fields.length 0 ++ calls)).GuardedIota N
          (recursiveFieldVars s.constructors[k]) 0 := by
  obtain ⟨-, hrhs, -⟩ := Restoration.equation_parts hrule
  simp only [Instance.equation] at hrhs
  rw [Restoration.expr_wrapLams_eq] at hrhs
  obtain ⟨D, hD, hrhs⟩ := Option.bind_eq_some_iff.mp hrhs
  obtain ⟨body', hbody, hbodyEq⟩ := Option.map_eq_some_iff.mp hrhs
  rw [Restoration.expr_mkApps_bvar] at hbody
  obtain ⟨args', hargs, rfl⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨vars', calls', rfl, Hvars, Hcalls⟩ :=
    List.Forall₂.append_inv (List.mapM_eq_some.mp hargs)
  have hvars := restored_vars Hvars
  subst hvars
  refine ⟨D, calls', hD, ?_, ?_, hbodyEq.symm, ?_⟩
  · intro d hd
    obtain ⟨d0, hd0, hr⟩ := forall₂_mem_right (List.mapM_eq_some.mp hD) d hd
    refine hmention d0 d ?_ hr
    rcases List.mem_append.mp hd0 with hd0 | hd0
    · exact hprefix d0 hd0
    · simp only [insertBinders, List.mem_map] at hd0
      obtain ⟨⟨e, i⟩, hei, rfl⟩ := hd0
      have he := List.fst_mem_of_mem_zipIdx hei
      simp only [List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      simpa using hfields e0 he0
  · rw [← Lean4Lean.List.Forall₂.length_eq Hcalls]; simp
  · apply VExpr.GuardedIota.mkApps .bvar
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · simp only [vars, List.mem_map] at ha
      obtain ⟨_, _, rfl⟩ := ha
      exact .bvar
    · obtain ⟨c0, hc0, hr⟩ := forall₂_mem_right Hcalls a ha
      simp only [List.mem_map] at hc0
      obtain ⟨⟨field, rec⟩, hp, rfl⟩ := hc0
      exact restoredRecursiveCall_guarded g r hmention hhead hmem _ field rec
        (hrec _ hp).1 (hrec _ hp).2
        (by
          unfold recursiveFieldVars
          exact List.mem_map_of_mem (List.mem_map_of_mem hp)) hr

/-! ### Avoidance of the restored block recursors in a validated nested run -/

/-- **The restored generated pieces mention no restored block recursor.** For
a restored block base of a validated nested run, there is a name list `L`
such that the generated recursor type of every owner avoids `L`, and the
restoration of every expression avoiding `L` mentions none of the block's
recursors.

`L` consists of the renamed auxiliary recursor names and of the block
recursor names that are not restoration heads. The generated recursor types
are well formed in the lowered constructor environment (with its case
eliminators and projections), where these names are fresh: the auxiliary
recursor names by `restorationRecursorNames`, the block recursor names because
they are installed fresh over the source constructor environment, which
contains the base environment and the names of the source families (the
remaining lowered names are restoration heads). The restoration targets and
specialization arguments are typed in the source header environment, where
the block recursor names are fresh. -/
theorem NestedRun.restoredGeneratedAvoidance
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hauxNames : auxiliaries.map (·.auxiliary) =
      (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map (·.name))
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered) :
    ∃ L : List Name,
      (∀ e out, e.containsAnyConst L = false →
        (compilationRestoration sourceDecl auxiliaries).expr e = some out →
        out.mentionsAnyConst ((C.sourceRecursors ++ C.auxiliaryRecursors).map (·.name)) =
          false) ∧
      ∀ o, (E.lowered.recursors.canonicalGeneration.recursorType o).containsAnyConst L =
        false := by
  let r := compilationRestoration sourceDecl auxiliaries
  let N := (C.sourceRecursors ++ C.auxiliaryRecursors).map (·.name)
  let Hd := r.heads.map (·.auxiliary)
  let R := r.recursors.map Prod.fst
  let L := R ++ N.filter (fun n => !(Hd.contains n))
  -- the source stages
  have hTypesAdded := C.install.abstract_types
  rw [C.typeValues] at hTypesAdded
  have henvTypes : envTypes = C.install.venvTypes :=
    Option.some.inj (hadded.symm.trans hTypesAdded)
  subst henvTypes
  have hCtorsAdded := C.install.abstract_ctors
  rw [C.constructorValues] at hCtorsAdded
  have hRecsAdded := C.install.recursorsAdded.abstract
  rw [C.recursorValues] at hRecsAdded
  have hbaseLe : ves.venv (if isUnsafe then .unsafe else .safe) ≤ C.install.venvCtors :=
    (VEnv.addConstVals_le hadded).trans (VEnv.addConstVals_le hCtorsAdded)
  have hbigLe : C.install.venvTypes ≤
      (C.install.venvCtors.addEliminators C.install.eliminators).addProjections
        sourceDecl.projectionEntries :=
    ((VEnv.addConstVals_le hCtorsAdded).trans VEnv.addEliminators_le).trans
      VEnv.addProjections_le
  have hbigOrd := C.install.projectedWF.ordered
  have hNfresh : ∀ n ∈ N, C.install.venvCtors.constants n = none := by
    intro n hn
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
    have h := (VEnv.addConstVals_names_fresh hRecsAdded).2 ci hci
    simpa using h
  have hNbig : ∀ n ∈ N, ((C.install.venvCtors.addEliminators C.install.eliminators).addProjections
      sourceDecl.projectionEntries).constants n = none := by
    intro n hn; simpa using hNfresh n hn
  have hNbase : ∀ n ∈ N, (ves.venv (if isUnsafe then .unsafe else .safe)).constants n = none :=
    fun n hn => hbaseLe.constants_eq_none_left (hNfresh n hn)
  have hNnot : ∀ {n}, C.install.venvCtors.constants n ≠ none → n ∉ N :=
    fun hn hmem => hn (hNfresh _ hmem)
  -- the source family names are constants of the source constructor environment
  have hsourcePresent : ∀ n ∈ familyNames sourceDecl.types,
      C.install.venvCtors.constants n ≠ none := by
    intro n hn
    obtain ⟨t, ht, hn⟩ := mem_familyNames.mp hn
    rcases hn with rfl | ⟨c, hc, rfl⟩
    · have hmem : t.toVConstVal ∈ sourceDecl.typeConstants := List.mem_map_of_mem ht
      have := (VEnv.addConstVals_le hCtorsAdded).constants (VEnv.addConstVals_get hadded hmem)
      rw [show t.name = t.toVConstVal.name from rfl, this]
      simp
    · have hmem : c ∈ sourceDecl.constructorConstants := List.mem_flatMap.mpr ⟨t, ht, hc⟩
      have := VEnv.addConstVals_get hCtorsAdded hmem
      simp [this]
  -- restoration heads
  have hheads : ∀ h ∈ r.heads, N.contains h.target = false ∧
      ∀ a ∈ h.arguments, a.mentionsAnyConst N = false := by
    intro h hh
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hh
    obtain ⟨gen, -, ev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
    have htargs : h.arguments = a.arguments ∧
        (h.target = a.source.name ∨ ∃ ctor ∈ a.source.ctors, h.target = ctor.name) := by
      simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
      rcases hh with rfl | ⟨ctor, hctor, rfl⟩
      · exact ⟨rfl, .inl rfl⟩
      · exact ⟨rfl, .inr ⟨ctor, hctor, rfl⟩⟩
    refine ⟨?_, ?_⟩
    · have hpresent : (ves.venv (if isUnsafe then .unsafe else .safe)).constants h.target ≠
          none := by
        rcases htargs.2 with ht | ⟨ctor, hctor, ht⟩
        · rw [ht]
          have := ev.installed.familyConstant a.family.val a.family.isLt
          change (ves.venv _).constants a.source.name = _ at this
          simp [this]
        · rw [ht]
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
          have := ev.installed.constructorConstant a.family.val j a.family.isLt hj
          change (ves.venv _).constants (a.source.ctors[j]).name = _ at this
          simp [this]
      apply Bool.eq_false_iff.mpr
      intro hc
      exact hpresent (hNbase _ (by simpa using hc))
    · rw [htargs.1]
      obtain ⟨sp, -, -, hctx, htyped, -⟩ := ev.application
      have hctx' : OnCtx sp.reverse
          (((C.install.venvCtors.addEliminators C.install.eliminators).addProjections
            sourceDecl.projectionEntries).IsType sourceDecl.uvars) :=
        hctx.mono fun ⟨u, hu⟩ => ⟨u, hu.mono hbigLe⟩
      have hctxN := hbigOrd.ctxNoFreshConsts hNbig hctx'
      have happ := (VEnv.IsDefEq.noFreshConsts hbigOrd hNbig hctxN (htyped.mono hbigLe)).1
      obtain ⟨_, hargs⟩ := (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mp happ
      intro arg harg
      exact VExpr.mentionsAnyConst_of_containsAnyConst (hargs arg harg)
  -- renaming of non-head constants
  have hconst : ∀ name, name ∉ Hd → L.contains name = false →
      N.contains (r.recursorName name) = false := by
    intro name hnotH hnotL
    have hnotR : name ∉ R := by
      intro hR
      have : L.contains name = true := by simp [L, hR]
      rw [hnotL] at this
      cases this
    rw [Restoration.recursorName_of_not_mem hnotR]
    apply Bool.eq_false_iff.mpr
    intro hc
    have : L.contains name = true := by
      simp only [L, List.contains_append, Bool.or_eq_true]
      right
      simp only [List.elem_eq_mem, decide_eq_true_eq, List.mem_filter,
        Bool.not_eq_eq_eq_not, Bool.not_true]
      refine ⟨by simpa using hc, ?_⟩
      simpa using hnotH
    rw [hnotL] at this
    cases this
  refine ⟨L, fun e out he hout => Restoration.expr_mentions hheads hconst he hout, ?_⟩
  -- the lowered constructor environment
  have hinit : E.lowered.initialEnv = ves.venv (if isUnsafe then .unsafe else .safe) :=
    E.lowered_initialEnv
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.lowered.loweredDecl.typeConstants =
        some E.lowered.constructors.toConstructorCheck.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.lowered.loweredDecl.typeConstants =
          some E.lowered.constructors.toConstructorCheck.headerVEnv) hinit)
      E.lowered.constructors.toConstructorCheck.core.typesAdded
  have hloweredCtors := E.lowered.constructors.toConstructorCheck.core.ctorsAdded
  have hloweredDecl : C.formationAssembly.expanded = E.lowered.loweredDecl := by
    rw [C.formationExpanded, hC]
  obtain ⟨hRfresh, -⟩ := E.restorationRecursorNames wf Hsources C.formationAssembly hloweredDecl
    hadded Haux Hexpansion hauxNames
  have hHeads : Hd = familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
    show (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) = _
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  -- the lowered names are source names or heads
  have HT := C.formationAssembly.types
  rw [hloweredDecl] at HT
  obtain ⟨r₁, r₂, hsplit, HT₁, -⟩ := List.Forall₂.append_inv HT
  have hlen₁ : r₁.length = sourceDecl.types.length := (Lean4Lean.List.Forall₂.length_eq HT₁).symm
  have hr₂ : r₂ = E.lowered.loweredDecl.types.drop sourceDecl.types.length := by
    rw [hsplit, ← hlen₁, List.drop_left]
  have hr₁ : familyNames r₁ = familyNames sourceDecl.types := by
    refine (familyNames_eq_of_forall₂ ?_).symm
    refine Lean4Lean.List.Forall₂.imp (fun src tgt h => ⟨h.name.symm, ?_⟩) HT₁
    exact ctorNames_eq_of_forall₂ h.constructors (fun _ _ hc => hc.name.symm)
  have hloweredNames : ∀ n, n ∈ E.lowered.loweredDecl.sourceNames →
      n ∈ familyNames sourceDecl.types ∨ n ∈ Hd := by
    intro n hn
    have hfam : n ∈ familyNames E.lowered.loweredDecl.types := by
      apply (familyNames_perm E.lowered.loweredDecl.types).mem_iff.mpr
      simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
        VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
        using hn
    rw [hsplit, familyNames_append] at hfam
    rcases List.mem_append.mp hfam with h | h
    · exact .inl (hr₁ ▸ h)
    · exact .inr (hHeads ▸ hr₂ ▸ h)
  have hLfresh : ∀ n ∈ L, E.lowered.constructors.toConstructorCheck.context.venv.constants n = none := by
    intro n hn
    rw [E.lowered.constructors.toConstructorCheck.contextVEnv]
    simp only [VEnv.addProjections_constants, VEnv.addEliminators_constants]
    cases hlook : E.lowered.constructors.toConstructorCheck.ctorVEnv.constants n with
    | none => rfl
    | some ci =>
      exfalso
      have horigin : (ves.venv (if isUnsafe then .unsafe else .safe)).constants n ≠ none ∨
          n ∈ E.lowered.loweredDecl.sourceNames := by
        rcases VEnv.addConstVals_lookup_cases hloweredCtors hlook with h | ⟨e, he, rfl, _⟩
        · rcases VEnv.addConstVals_lookup_cases hloweredTypes h with h | ⟨e, he, rfl, _⟩
          · exact .inl (by simp [h])
          · exact .inr (List.mem_append_left _ (List.mem_map_of_mem he))
        · exact .inr (List.mem_append_right _ (List.mem_map_of_mem he))
      rcases List.mem_append.mp hn with hR | hN
      · obtain ⟨hb, hs, hl⟩ := hRfresh n hR
        rcases horigin with h | h
        · exact h hb
        · exact hl h
      · obtain ⟨hnN, hnH⟩ := List.mem_filter.mp hN
        rcases horigin with h | h
        · exact h (hNbase n hnN)
        · rcases hloweredNames n h with h | h
          · exact hNnot (hsourcePresent n h) hnN
          · simp [h] at hnH
  -- the generated recursor types are types in the lowered environment
  intro o
  let H := E.lowered.recursorConstruction
  have ho : o.val < E.lowered.indTypes.size := by
    have := H.generator.familyCount
    have ho := o.isLt
    change o.val < H.generator.signature.families.size at ho
    omega
  obtain ⟨type, Htr, Htype⟩ := H.recursorTypeTranslation o.val ho
  have heq := Htr.uniqueS (H.generator.types o.val o.isLt)
  have hord := E.lowered.constructors.toConstructorCheck.context.checking.tr.wf.ordered
  obtain ⟨u, hu⟩ := Htype
  have := (VEnv.IsDefEq.noFreshConsts hord hLfresh (by intro t ht; simp at ht) hu).1
  rw [heq] at this
  exact this

/-! ### Nested iota rules from generated equations -/

theorem vars_take (n m k : Nat) :
    (vars (n + m) k).take n = vars n (k + m) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, vars, List.getElem_map, List.getElem_reverse,
      List.getElem_range, List.length_range]
    congr 1
    simp only [vars, List.length_map, List.length_reverse, List.length_range] at h2
    omega

private theorem vars_getElem (n below i : Nat) (h : i < (vars n below).length) :
    (vars n below)[i] = .bvar (below + (n - 1 - i)) := by
  simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range]

private theorem filterMap_bvarHead_map (f : Nat → Nat) :
    ∀ l : List Nat, (l.map fun i => VExpr.bvar (f i)).filterMap VExpr.bvarHead? = l.map f
  | [] => rfl
  | i :: l => by
    simp only [List.map_cons, List.filterMap_cons]
    exact congrArg (List.cons _) (filterMap_bvarHead_map f l)

/-- **A nested iota rule from the shape of a restored generated equation.**
The left-hand side applies the restored recursor to the leading variables and
indices and to the constructor applied to the parameters and fields; the
right-hand side applies the minor premise to the field variables and to one
result per recursive field position, and is guarded for the field variables
of those positions. -/
def nestedIotaRuleOfGenerated
    {decl : VInductDecl} {block : VInductBlock} {owner : VInductiveType}
    {ctor : VConstVal} {rule : VDefEq}
    (recursor : VConstVal) (hrecursorMem : recursor ∈ block.recursors)
    (S : decl.NestedRecursorShape owner recursor)
    (hruleUvars : rule.uvars = recursor.uvars)
    (D : List VExpr) (np nf extra : Nat) (recLevels ctorLevels : List VLevel)
    (idx calls : List VExpr) (positions : List Nat) (minorVar : Nat) (typeBody : VExpr)
    (hnp : decl.nparams = np)
    (hextra : extra = S.motives.length + S.minors.length)
    (hD : D.length = np + extra + nf)
    (hidx : idx.length = owner.numIndices)
    (hlhs : rule.lhs = VExpr.wrapLams D (VExpr.mkApps (.const recursor.name recLevels)
      (vars (np + extra) nf ++ idx ++
        [VExpr.mkApps (.const ctor.name ctorLevels) (vars np (extra + nf + 0) ++ vars nf 0)])))
    (hrhs : rule.rhs = VExpr.wrapLams D (VExpr.mkApps (.bvar minorVar) (vars nf 0 ++ calls)))
    (htype : rule.type = VExpr.wrapForalls D typeBody)
    (hrecLevels : recLevels.length = recursor.uvars)
    (hctorLevels : ctorLevels.length = decl.uvars)
    (hminor : minorVar < D.length)
    (hord : positions.Pairwise (· < ·)) (hlt : ∀ i ∈ positions, i < nf)
    (hsub : List.Sublist (positions.map fun i => VExpr.bvar (nf - 1 - i)) (vars nf 0))
    (hcalls : calls.length = positions.length)
    (hguard : (VExpr.mkApps (.bvar minorVar) (vars nf 0 ++ calls)).GuardedIota
      (block.recursors.map (·.name)) (positions.map fun i => nf - 1 - i) 0) :
    decl.NestedIotaRule block owner ctor rule := by
  subst hnp
  have hctorDrop : (vars decl.nparams (extra + nf + 0) ++ vars nf 0).drop decl.nparams =
      vars nf 0 := by
    rw [List.drop_append_of_le_length (by simp)]
    simp
  have hctorCount : (vars decl.nparams (extra + nf + 0) ++ vars nf 0).length - decl.nparams =
      nf := by simp
  refine {
    recursor := recursor
    recursor_mem := hrecursorMem
    recursor_shape := S
    rule_uvars := hruleUvars
    domains := D
    lhsBody := _
    rhsBody := _
    typeBody := typeBody
    lhs_wrapped := hlhs
    rhs_wrapped := hrhs
    type_wrapped := htype
    recursorLevels := recLevels
    leadingArgs := vars (decl.nparams + extra) nf ++ idx
    ctorLevels := ctorLevels
    ctorArgs := vars decl.nparams (extra + nf + 0) ++ vars nf 0
    lhs_pattern := rfl
    recursor_levels := hrecLevels
    ctor_levels := hctorLevels
    leading_arity := by
      simp only [List.length_append, vars_length, hidx, hextra]
      omega
    constructor_arity := by simp
    parameter_args := by
      rw [List.take_append_of_le_length (by simp), List.take_append_of_le_length (by simp)]
      rw [List.take_of_length_le (by simp), vars_take]
      congr 1
      omega
    domains_arity := by
      rw [hctorCount, hD, hextra]
      omega
    recursiveFields := positions.map fun i => { fieldIndex := i, arg := .bvar (nf - 1 - i) }
    fieldPositions := positions
    fieldPositions_eq := by simp [Function.comp_def]
    fieldPositions_ordered := hord
    fields_at_positions := ?_
    recursiveArgs := positions.map fun i => VExpr.bvar (nf - 1 - i)
    recursiveArgs_eq := by simp
    recursive_args := by rw [hctorDrop]; exact hsub
    fieldVars := positions.map fun i => nf - 1 - i
    fieldVars_eq := (filterMap_bvarHead_map _ _).symm
    fields_in_scope := ?_
    minorVar := minorVar
    minor_in_scope := hminor
    rhsArgs := vars nf 0 ++ calls
    rhs_spine := VExpr.getAppFnArgs_mkApps_bvar _ _
    field_args := by
      rw [hctorCount, hctorDrop, List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp)]
    recursive_results := by
      rw [hctorCount, List.drop_append_of_le_length (by simp)]
      simp [hcalls]
    rhs_guarded := hguard }
  · intro field hfield
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hfield
    have hin := hlt i hi
    have key : ∀ l, l = vars nf 0 → ∃ h : i < l.length,
        VExpr.bvar (nf - 1 - i) = l[i]'h := by
      rintro l rfl
      refine ⟨by simpa using hin, ?_⟩
      rw [vars_getElem]
      simp
    exact key _ hctorDrop
  · intro field hfield
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hfield
    have := hlt i hi
    omega

theorem stepValues_names {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {env : VEnv} :
    ∀ {names : List Name} {added : List VConstVal},
      List.Forall₂ (fun (name : Name) (w : VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
          auxRec allIndNames name s t), RecursorRestorationStepValue env Hstep w) names added →
      added.map (·.name) = names.map (fun oldName => auxRec.getD oldName oldName)
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    obtain ⟨_, _, Hstep, hname, -, -⟩ := h
    simp only [List.map_cons, stepValues_names t, hname, Hstep.restored.mappedName]

theorem RestoredBlockBase.recursors_names
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety) :
    (C.sourceRecursors ++ C.auxiliaryRecursors).map (·.name) =
      sourceTypes.map (fun indType =>
        let oldName := Lean.mkRecName indType.name
        auxRec.getD oldName oldName) ++
      auxRecNames.map (fun oldName => auxRec.getD oldName oldName) := by
  obtain ⟨added, hadded', Hadded⟩ := C.auxiliaryRecursorTrace.recursorSteps
  simp only [List.nil_append] at hadded'
  rw [List.map_append, C.sourceTranslations.recursorNames, hadded', stepValues_names Hadded]

/-- The restored name of every generated recursor is a recursor of the
restored block base. -/
theorem NestedRun.restoredRecursorName_mem
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (C : RestoredBlockBase E.restoration sourceEnv sourceDecl lparams
      nparams isUnsafe safety)
    (o : Fin E.lowered.recursors.generationSignature.families.size) :
    (compilationRestoration sourceDecl auxiliaries).recursorName
        (E.lowered.recursors.canonicalGeneration.recursorName o) ∈
      (C.sourceRecursors ++ C.auxiliaryRecursors).map (·.name) := by
  have hnames := E.recursorNames_order C.sourceNonempty
  have hmem : E.lowered.recursors.canonicalGeneration.recursorName o ∈
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
    rw [← hnames]
    exact List.mem_map_of_mem (List.mem_finRange o)
  rw [C.recursors_names, D.recursorName]
  simp only [nameMap_getD_eq]
  rcases List.mem_append.mp hmem with h | h
  · obtain ⟨t, ht, heq⟩ := List.mem_map.mp h
    rw [← heq]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨_, h, rfl⟩)

end VerifyInductive
end Lean4Lean
