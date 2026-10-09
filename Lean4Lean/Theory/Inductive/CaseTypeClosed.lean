import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas

/-! Every registered eliminator schema has, for every owner slot, a generic
case type, and that type is closed (`VEnv.WF.eliminator_genericType_closed`). The proof shows
that restoration succeeds on the generated case type (`Restorable`) and that the restored type
is closed, from the scoping facts of the case certificate and the header agreement. -/

namespace Lean4Lean.EnvTables
open InductiveSignature VExpr

/-- The syntactic condition under which restoration succeeds: every
auxiliary head occurs with its universe arity and at least its parameter
count of arguments (`n` counts the arguments supplied by the spine). -/
def Restorable (r : Restoration) : VExpr → Nat → Prop
  | .app fn arg, n => Restorable r arg 0 ∧ Restorable r fn (n + 1)
  | .const name levels, n => ∀ h, r.heads.find? (fun h => h.auxiliary == name) = some h →
      levels.length = h.uvars ∧ h.nparams ≤ n
  | .lam d b, _ => Restorable r d 0 ∧ Restorable r b 0
  | .forallE d b, _ => Restorable r d 0 ∧ Restorable r b 0
  | .proj _ _ m, _ => Restorable r m 0
  | _, _ => True

theorem restore_go_isSome (r : Restoration) (e : VExpr) (args : List VExpr) :
    (Restoration.expr.go r e args).isSome ↔ Restorable r e args.length := by
  induction e generalizing args with
  | app fn arg ihf iha =>
    simp only [Restoration.expr.go, bind, Restorable]
    cases h : Restoration.expr.go r arg [] with
    | none =>
      have : ¬ Restorable r arg 0 := fun hok => by simpa [h] using (iha []).mpr hok
      simp [this]
    | some a' =>
      have : Restorable r arg 0 := (iha []).mp (by simp [h])
      simp [this, ihf]
  | const name levels =>
    simp only [Restoration.expr.go, Restorable]
    split
    · rename_i h hh
      simp only [HeadSpecialization.apply, pure]
      constructor
      · intro hs h' hh'
        rw [hh] at hh'
        cases hh'
        split at hs
        · simp at hs
        · rename_i hc
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
            Classical.not_not, Nat.not_lt] at hc
          exact hc
      · intro H
        obtain ⟨h1, h2⟩ := H h hh
        rw [if_neg (by simp [h1]; omega)]
        rfl
    · rename_i hh
      simp only [Option.isSome_some, true_iff]
      intro h' hh'
      rw [hh] at hh'
      cases hh'
  | lam d b ihd ihb | forallE d b ihd ihb =>
    simp only [Restoration.expr.go, bind, Restorable]
    cases h1 : Restoration.expr.go r d [] with
    | none =>
      have : ¬ Restorable r d 0 := fun hok => by simpa [h1] using (ihd []).mpr hok
      simp [this]
    | some d' =>
      have : Restorable r d 0 := (ihd []).mp (by simp [h1])
      cases h2 : Restoration.expr.go r b [] with
      | none =>
        have : ¬ Restorable r b 0 := fun hok => by simpa [h2] using (ihb []).mpr hok
        simp [*]
      | some b' =>
        have : Restorable r b 0 := (ihb []).mp (by simp [h2])
        simp [*]
  | proj n i m ih =>
    simp only [Restoration.expr.go, bind, Restorable]
    cases h : Restoration.expr.go r m [] with
    | none =>
      have : ¬ Restorable r m 0 := fun hok => by simpa [h] using (ih []).mpr hok
      simp [this]
    | some m' =>
      have : Restorable r m 0 := (ih []).mp (by simp [h])
      simp [this]
  | bvar | sort | elim => simp [Restoration.expr.go, Restorable]

theorem restorable_instL (r : Restoration) (ls : List VLevel) :
    ∀ (e : VExpr) (n : Nat), Restorable r (e.instL ls) n ↔ Restorable r e n
  | .app f a, n => by simp only [instL, Restorable, restorable_instL r ls f, restorable_instL r ls a]
  | .lam d b, n | .forallE d b, n => by
    simp only [instL, Restorable, restorable_instL r ls d, restorable_instL r ls b]
  | .proj _ _ m, n => by simp only [instL, Restorable, restorable_instL r ls m]
  | .const c us, n => by simp [instL, Restorable]
  | .bvar _, _ | .sort _, _ | .elim .., _ => by simp [instL, Restorable]

theorem restorable_liftN (r : Restoration) (k : Nat) :
    ∀ (e : VExpr) (j n : Nat), Restorable r (e.liftN k j) n ↔ Restorable r e n
  | .app f a, j, n => by
    simp only [liftN, Restorable, restorable_liftN r k f, restorable_liftN r k a]
  | .lam d b, j, n | .forallE d b, j, n => by
    simp only [liftN, Restorable, restorable_liftN r k d, restorable_liftN r k b]
  | .proj _ _ m, j, n => by simp only [liftN, Restorable, restorable_liftN r k m]
  | .const c us, _, n => by simp [liftN, Restorable]
  | .bvar _, _, _ | .sort _, _, _ | .elim .., _, _ => by simp [liftN, Restorable]

theorem restorable_mkApps (r : Restoration) (fn : VExpr) (args : List VExpr) (n : Nat) :
    Restorable r (mkApps fn args) n ↔
      (∀ a ∈ args, Restorable r a 0) ∧ Restorable r fn (n + args.length) := by
  induction args generalizing fn n with
  | nil => simp [mkApps]
  | cons a args ih =>
    simp only [mkApps, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [Restorable, List.mem_cons, forall_eq_or_imp, List.length_cons]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, h1⟩, by simpa [Nat.add_assoc, Nat.add_comm 1] using h3⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩; exact ⟨h1, h2, by simpa [Nat.add_assoc, Nat.add_comm 1] using h3⟩

theorem restorable_wrapForalls (r : Restoration) (doms : List VExpr) (body : VExpr) :
    Restorable r (wrapForalls doms body) 0 ↔
      (∀ d ∈ doms, Restorable r d 0) ∧ Restorable r body 0 := by
  induction doms with
  | nil => simp [wrapForalls]
  | cons d ds ih =>
    simp only [wrapForalls, List.foldr_cons] at ih ⊢
    simp only [Restorable, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem restorable_vars (r : Restoration) (count below : Nat) :
    ∀ a ∈ vars count below, Restorable r a 0 := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  trivial


theorem instantiateParams_closedN {e : VExpr} {params : List VExpr}
    (he : e.ClosedN params.length) (hp : ∀ p ∈ params, p.ClosedN k) :
    (instantiateParams e params).ClosedN k := by
  unfold instantiateParams
  apply ClosedN.subst_closed he
  intro i hi
  simp only [hi, dite_true]
  exact hp _ (List.getElem_mem _)

theorem restore_go_closedN (r : Restoration)
    (hheads : ∀ h ∈ r.heads, ∀ a ∈ h.arguments, a.ClosedN h.nparams) :
    ∀ (e : VExpr) (args : List VExpr) (k : Nat) (out : VExpr), e.ClosedN k →
      (∀ a ∈ args, a.ClosedN k) → Restoration.expr.go r e args = some out → out.ClosedN k
  | .app fn arg, args, k, out, he, ha, hgo => by
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff] at hgo
    obtain ⟨a', h1, h2⟩ := hgo
    have ha' := restore_go_closedN r hheads arg [] k a' he.2 (by simp) h1
    exact restore_go_closedN r hheads fn (a' :: args) k out he.1
      (by simpa [ha'] using ha) h2
  | .const name levels, args, k, out, _, ha, hgo => by
    simp only [Restoration.expr.go] at hgo
    split at hgo
    · rename_i h hh
      have hmem := List.mem_of_find?_eq_some hh
      simp only [HeadSpecialization.apply, pure] at hgo
      split at hgo
      · cases hgo
      · rename_i hc
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
          Classical.not_not, Nat.not_lt] at hc
        cases hgo
        apply ClosedN.mkApps_closed (fn := .const _ _) (by simp [ClosedN])
        intro a hmemA
        rcases List.mem_append.mp hmemA with hs | hd
        · obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp hs
          apply instantiateParams_closedN
          · rw [List.length_take, Nat.min_eq_left hc.2]
            exact (hheads h hmem arg harg).instL
          · intro p hp; exact ha p (List.mem_of_mem_take hp)
        · exact ha a (List.mem_of_mem_drop hd)
    · cases hgo
      exact ClosedN.mkApps_closed (fn := .const _ _) (by simp [ClosedN]) ha
  | .bvar i, args, k, out, he, ha, hgo => by
    simp only [Restoration.expr.go, Option.some.injEq] at hgo
    subst hgo; exact ClosedN.mkApps_closed he ha
  | .sort u, args, k, out, he, ha, hgo => by
    simp only [Restoration.expr.go, Option.some.injEq] at hgo
    subst hgo; exact ClosedN.mkApps_closed he ha
  | .elim b o ls, args, k, out, he, ha, hgo => by
    simp only [Restoration.expr.go, Option.some.injEq] at hgo
    subst hgo; exact ClosedN.mkApps_closed he ha
  | .lam d b, args, k, out, he, ha, hgo => by
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff, pure] at hgo
    obtain ⟨d', h1, b', h2, hout⟩ := hgo
    cases hout
    exact ClosedN.mkApps_closed
      ⟨restore_go_closedN r hheads d [] k d' he.1 (by simp) h1,
        restore_go_closedN r hheads b [] (k+1) b' he.2 (by simp) h2⟩ ha
  | .forallE d b, args, k, out, he, ha, hgo => by
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff, pure] at hgo
    obtain ⟨d', h1, b', h2, hout⟩ := hgo
    cases hout
    exact ClosedN.mkApps_closed
      ⟨restore_go_closedN r hheads d [] k d' he.1 (by simp) h1,
        restore_go_closedN r hheads b [] (k+1) b' he.2 (by simp) h2⟩ ha
  | .proj n i m, args, k, out, he, ha, hgo => by
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff, pure] at hgo
    obtain ⟨m', h1, hout⟩ := hgo
    cases hout
    exact ClosedN.mkApps_closed (restore_go_closedN r hheads m [] k m' he (by simp) h1) ha


/-! ## Scoped telescopes -/

/-- Each domain of a telescope is closed in the binders before it. -/
def ScopedDoms (n : Nat) (doms : List VExpr) : Prop :=
  ∀ i (hi : i < doms.length), doms[i].ClosedN (n + i)

theorem closedN_wrapForalls_inv :
    ∀ {doms : List VExpr} {body : VExpr} {n : Nat},
      (wrapForalls doms body).ClosedN n → ScopedDoms n doms ∧ body.ClosedN (n + doms.length)
  | [], body, n, h => ⟨fun i hi => absurd hi (by simp), by simpa [wrapForalls] using h⟩
  | d :: ds, body, n, h => by
    have h' : (VExpr.forallE d (wrapForalls ds body)).ClosedN n := h
    obtain ⟨hd, hrest⟩ := h'
    obtain ⟨hs, hb⟩ := closedN_wrapForalls_inv hrest
    refine ⟨fun i hi => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hb⟩
    cases i with
    | zero => simpa using hd
    | succ i =>
      have := hs i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem ScopedDoms.append {A B : List VExpr} (hA : ScopedDoms n A)
    (hB : ScopedDoms (n + A.length) B) : ScopedDoms n (A ++ B) := by
  intro i hi
  by_cases h : i < A.length
  · rw [List.getElem_append_left h]; exact hA i h
  · rw [List.getElem_append_right (by omega)]
    have := hB (i - A.length) (by simp at hi; omega)
    rwa [show n + A.length + (i - A.length) = n + i by omega] at this

theorem ScopedDoms.map_instL {l : List VExpr} (h : ScopedDoms n l) (ls : List VLevel) :
    ScopedDoms n (l.map (·.instL ls)) := by
  intro i hi
  simpa using (h i (by simpa using hi)).instL

theorem ScopedDoms.insertBinders {l : List VExpr} (h : ScopedDoms n l) (k : Nat) :
    ScopedDoms (n + k) (insertBinders l k) := by
  intro i hi
  simp only [InductiveSignature.insertBinders, List.length_map, List.length_zipIdx] at hi
  simp only [InductiveSignature.insertBinders, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have := (h i hi).liftN (n := k) (j := i)
  rwa [show n + i + k = n + k + i by omega] at this

theorem ScopedDoms.singleton {x : VExpr} (h : x.ClosedN n) : ScopedDoms n [x] := by
  intro i hi
  simp at hi; subst hi; simpa using h

theorem closedN_mkApps_args : ∀ {fn : VExpr} {args : List VExpr} {n : Nat},
    (mkApps fn args).ClosedN n → ∀ a ∈ args, a.ClosedN n
  | _, [], _, _ => by simp
  | fn, a :: as, n, h => by
    have h' := closedN_mkApps_args (fn := .app fn a) (args := as) h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have hf : (VExpr.app fn b).ClosedN n := by
        have : ∀ {f : VExpr} {xs : List VExpr}, (mkApps f xs).ClosedN n → f.ClosedN n := by
          intro f xs
          induction xs generalizing f with
          | nil => exact id
          | cons x xs ih => exact fun h => (ih h).1
        exact this h
      exact hf.2
    · exact h' b hb

theorem vars_closedN (count below : Nat) :
    ∀ a ∈ vars count below, a.ClosedN (below + count) := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  simp only [List.mem_reverse, List.mem_range] at hi
  show below + i < below + count
  omega

theorem vars_closedN_of_le {count below n : Nat} (h : below + count ≤ n) :
    ∀ a ∈ vars count below, a.ClosedN n :=
  fun a ha => (vars_closedN count below a ha).mono h

/-! ## The case view -/

theorem view_constructors_mem {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    {ctor : Constructor (schema.view owner).families.size}
    (h : ctor ∈ (schema.view owner).constructors.toList) :
    ∃ c ∈ schema.signature.constructors.toList, c.owner = owner ∧ ctor = schema.caseConstructor c := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have := CaseSchema.view_constructor_eq_caseConstructor (schema := schema) (owner := owner) ⟨i, by rw [← Array.length_toList]; exact hi⟩
  obtain ⟨c, hc, ho, he⟩ := this
  exact ⟨c, hc, ho, by rw [Array.getElem_toList]; exact he⟩

theorem mem_zipIdx_getElem (l : List α) (i : Nat) (h : i < l.length) : (l[i], i) ∈ l.zipIdx :=
  List.mem_iff_getElem.mpr ⟨i, by simpa using h, by simp⟩

theorem mem_insertBinders {l : List VExpr} {x : VExpr} (h : x ∈ l) (k : Nat) :
    ∃ j, x.liftN k j ∈ insertBinders l k := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  exact ⟨j, List.mem_map.mpr ⟨(l[j], j), mem_zipIdx_getElem l j hj, rfl⟩⟩


/-! ## Restoration success -/

/-! ### The case type -/

theorem case_restorable (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    {r : Restoration}
    (hp : ∀ p ∈ schema.signature.params, Restorable r p 0)
    (hc : ∀ c ∈ schema.signature.constructors.toList,
      (∀ f ∈ schema.signature.fieldTypes c, Restorable r f 0) ∧ ∀ e ∈ c.indices, Restorable r e 0)
    (hi : ∀ e ∈ schema.signature.families[owner].indices, Restorable r e 0)
    (hconst : ∀ name n, schema.signature.params.length ≤ n →
      Restorable r (.const name schema.genericLevels) n) :
    Restorable r ((schema.specialize owner schema.genericUvars schema.genericLevels
      (.param 0)).recursorType (schema.viewOwner owner)) 0 := by
  simp only [Instance.recursorType]
  rw [restorable_wrapForalls]
  refine ⟨?_, ?_⟩
  · intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with ((((hd | hd) | hd) | hd) | rfl)
    · -- parameters
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hd
      exact (restorable_instL r _ p 0).mpr (hp p hpm)
    · -- the single motive
      simp [Instance.motives, CaseSchema.view] at hd
      subst hd
      simp only [Instance.motive]
      rw [restorable_wrapForalls]
      refine ⟨?_, trivial⟩
      intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · obtain ⟨⟨x, j⟩, hx, rfl⟩ := List.mem_map.mp hd
        obtain ⟨_, _, hxe⟩ := List.mem_zipIdx hx
        simp only at hxe ⊢
        rw [restorable_liftN, hxe]
        simp only [List.getElem_map, Nat.sub_zero]
        rw [restorable_instL]
        exact hi _ (List.getElem_mem _)
      · rw [restorable_mkApps]
        refine ⟨fun a ha => ?_, hconst _ _ ?_⟩
        · rcases List.mem_append.mp ha with ha | ha <;>
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; trivial
        · simp [vars]
    · -- minors
      obtain ⟨⟨ctor, j⟩, hx, rfl⟩ := List.mem_map.mp hd
      have hctor : ctor ∈ (schema.view owner).constructors.toList := by
        obtain ⟨_, _, hxe⟩ := List.mem_zipIdx hx
        rw [hxe]; exact List.getElem_mem _
      obtain ⟨c, hcm, _, rfl⟩ := view_constructors_mem hctor
      obtain ⟨hf, hix⟩ := hc c hcm
      simp only [Instance.minor, CaseSchema.caseConstructor_recursiveFields, CaseSchema.view_fieldTypes_case,
        List.zipIdx_nil, List.map_nil, List.append_nil, List.length_nil]
      rw [restorable_wrapForalls]
      refine ⟨fun d hd => ?_, ?_⟩
      · obtain ⟨⟨x, k⟩, hx, rfl⟩ := List.mem_map.mp hd
        obtain ⟨_, _, hxe⟩ := List.mem_zipIdx hx
        simp only at hxe ⊢
        rw [restorable_liftN, hxe]
        simp only [List.getElem_map, Nat.sub_zero]
        rw [restorable_instL]
        exact hf _ (List.getElem_mem _)
      · rw [restorable_mkApps]
        refine ⟨fun a ha => ?_, trivial⟩
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
          rw [restorable_liftN, restorable_liftN, restorable_instL]
          exact hix e (by simpa [CaseSchema.caseConstructor] using he)
        · simp only [List.mem_singleton] at ha
          subst ha
          simp only [Instance.constructorApp]
          rw [restorable_mkApps]
          refine ⟨fun a ha => ?_, hconst _ _ ?_⟩
          · rcases List.mem_append.mp ha with ha | ha <;>
            · obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; trivial
          · simp [vars, CaseSchema.view]
    · -- indices
      obtain ⟨⟨x, j⟩, hx, rfl⟩ := List.mem_map.mp hd
      obtain ⟨_, _, hxe⟩ := List.mem_zipIdx hx
      simp only at hxe ⊢
      rw [restorable_liftN, hxe]
      simp only [List.getElem_map, Nat.sub_zero]
      rw [restorable_instL]
      exact hi _ (List.getElem_mem _)
    · -- major premise
      simp only [Instance.familyApp, InductiveSignature.familyApp]
      rw [restorable_mkApps]
      refine ⟨fun a ha => ?_, hconst _ _ ?_⟩
      · rcases List.mem_append.mp ha with ha | ha <;>
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; trivial
      · simp [vars, CaseSchema.view]
  · rw [restorable_mkApps]
    refine ⟨fun a ha => ?_, trivial⟩
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; trivial
    · simp only [List.mem_singleton] at ha; subst ha; trivial


/-! ## Closedness of the generated case type -/

theorem ScopedDoms.append_of_length {A B : List VExpr} (hA : ScopedDoms n A) (hlen : A.length = a)
    (hB : ScopedDoms (n + a) B) : ScopedDoms n (A ++ B) :=
  hA.append (hlen ▸ hB)

theorem ScopedDoms.shift {l : List VExpr} (h : ScopedDoms n l) (hn : n = n') : ScopedDoms n' l :=
  hn ▸ h

theorem case_closedN (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (hp : ScopedDoms 0 schema.signature.params)
    (hc : ∀ c ∈ schema.signature.constructors.toList,
      ScopedDoms schema.signature.params.length (schema.signature.fieldTypes c) ∧
      ∀ e ∈ c.indices, e.ClosedN (schema.signature.params.length + c.fields.length))
    (hi : ScopedDoms schema.signature.params.length schema.signature.families[owner].indices) :
    ((schema.specialize owner schema.genericUvars schema.genericLevels
      (.param 0)).recursorType (schema.viewOwner owner)).ClosedN 0 := by
  have hconst : ∀ name (ls : List VLevel) n, (VExpr.const name ls).ClosedN n := fun _ _ _ => trivial
  have hfam : (schema.view owner).families[schema.viewOwner owner] =
      schema.signature.families[owner] := rfl
  simp only [Instance.recursorType, hfam]
  apply ClosedN.wrapForalls_closed
  · refine ScopedDoms.append_of_length (a := schema.signature.params.length + 1 +
      (schema.view owner).constructors.size + schema.signature.families[owner].indices.length)
      (ScopedDoms.append_of_length (a := schema.signature.params.length + 1 +
        (schema.view owner).constructors.size)
        (ScopedDoms.append_of_length (a := schema.signature.params.length + 1)
          (ScopedDoms.append_of_length (a := schema.signature.params.length)
            (hp.map_instL _) (by simp [Instance.params, CaseSchema.view]) ?motive)
          (by simp [Instance.params, Instance.motives, CaseSchema.view] <;> omega) ?minors)
        (by simp [Instance.params, Instance.motives, Instance.minors, CaseSchema.view] <;> omega)
        ?indices)
      (by simp [Instance.params, Instance.motives, Instance.minors, CaseSchema.view, insertBinders] <;> omega)
      (ScopedDoms.singleton ?major)
    case motive =>
      show ScopedDoms _ [_]
      apply ScopedDoms.singleton
      simp only [Instance.motive]
      apply ClosedN.wrapForalls_closed
      · refine ScopedDoms.append_of_length (a := schema.signature.families[owner].indices.length)
          (((hi.map_instL _).insertBinders 0).shift (by omega)) (by simp [insertBinders]) (ScopedDoms.singleton ?_)
        apply ClosedN.mkApps_closed (hconst _ _ _)
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact vars_closedN_of_le (by simp [insertBinders, CaseSchema.view] <;> omega) a ha
        · exact vars_closedN_of_le (by simp [insertBinders, CaseSchema.view]) a ha
      · trivial
    case minors =>
      intro i hi'
      simp only [Instance.minors, List.length_map, List.length_zipIdx] at hi'
      simp only [Instance.minors, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      obtain ⟨c, hcm, _, hce⟩ := view_constructors_mem (List.getElem_mem hi')
      rw [hce]
      obtain ⟨hf, hix⟩ := hc c hcm
      simp only [Instance.minor, CaseSchema.caseConstructor_recursiveFields, CaseSchema.view_fieldTypes_case,
        List.zipIdx_nil, List.map_nil, List.append_nil, List.length_nil]
      apply ClosedN.wrapForalls_closed
      · exact ((hf.map_instL _).insertBinders _).shift (by simp [CaseSchema.view] <;> omega)
      · have hnf : (schema.caseConstructor c).fields.length = c.fields.length := by
          simp [CaseSchema.caseConstructor, fieldTypes]
        apply ClosedN.mkApps_closed
        · show _ < _
          simp [insertBinders, fieldTypes, hnf]; omega
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
          have he' := hix e (by simpa [CaseSchema.caseConstructor] using he)
          simp only [liftN_zero]
          have := (he'.instL (ls := schema.genericLevels)).liftN
            (n := (schema.view owner).families.size + i) (j := (schema.caseConstructor c).fields.length + 0)
          refine this.mono ?_
          simp [insertBinders, fieldTypes, CaseSchema.view] <;> omega
        · simp only [List.mem_singleton] at ha
          subst ha
          simp only [Instance.constructorApp]
          apply ClosedN.mkApps_closed (hconst _ _ _)
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact vars_closedN_of_le (by simp [insertBinders, fieldTypes, hnf, CaseSchema.view] <;> omega) a ha
          · exact vars_closedN_of_le (by simp [insertBinders, fieldTypes, hnf, CaseSchema.view] <;> omega) a ha
    case indices =>
      exact ((hi.map_instL _).insertBinders _).shift (by simp [CaseSchema.view] <;> omega)
    case major =>
      simp only [Instance.familyApp, InductiveSignature.familyApp]
      apply ClosedN.mkApps_closed (hconst _ _ _)
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact vars_closedN_of_le (by simp [insertBinders, CaseSchema.view] <;> omega) a ha
      · exact vars_closedN_of_le (by simp [insertBinders, CaseSchema.view] <;> omega) a ha
  · apply ClosedN.mkApps_closed
    · show _ < _
      simp [insertBinders, Instance.params, Instance.motives, Instance.minors, CaseSchema.view]
      <;> omega
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact vars_closedN_of_le (by
        simp [insertBinders, Instance.params, Instance.motives, Instance.minors, CaseSchema.view]
        <;> omega) a ha
    · show 0 < _
      simp only [List.length_append, List.length_singleton]
      omega


/-! ## Scoping facts from the certified compilation -/

theorem ScopedDoms.append_inv {A B : List VExpr} (h : ScopedDoms n (A ++ B)) :
    ScopedDoms n A ∧ ScopedDoms (n + A.length) B := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h i (by simp; omega)
    rwa [List.getElem_append_left hi] at this
  · have := h (A.length + i) (by simp; omega)
    rw [List.getElem_append_right (by omega)] at this
    simpa [Nat.add_assoc] using this

private theorem ctxClosed_of_onCtx {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → CtxClosed Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ =>
    ⟨ctxClosed_of_onCtx henv h1, VExpr.WF.closedN henv ⟨_, h2⟩ (ctxClosed_of_onCtx henv h1)⟩

private theorem wrapForalls_sort_closedN {level : VLevel} :
    ∀ {domains Γ : List VExpr}, CtxClosed (domains.reverse ++ Γ) →
      (wrapForalls domains (.sort level)).ClosedN Γ.length
  | [], _, _ => trivial
  | d :: ds, Γ, H => by
    have H' : CtxClosed (ds.reverse ++ d :: Γ) := by
      simpa [List.reverse_cons, List.append_assoc] using H
    have hd : CtxClosed (d :: Γ) := OnCtx.of_append H'
    exact ⟨hd.2, wrapForalls_sort_closedN (Γ := d :: Γ) H'⟩

theorem CaseCompilationData.case_scoping
    {s : InductiveSignature}
    (hdata : CaseCompilationData base source expanded s auxiliaries block) (hbase : base.WF)
    (owner : Fin s.families.size) :
    ScopedDoms 0 s.params ∧
    (∀ c ∈ s.constructors.toList,
      ScopedDoms s.params.length (s.fieldTypes c) ∧
      ∀ e ∈ c.indices, e.ClosedN (s.params.length + c.fields.length)) ∧
    ScopedDoms s.params.length s.families[owner].indices := by
  obtain ⟨envET, envEC, es, hT, hC, -, hfamWF⟩ := hdata.familyTypesWF
  obtain ⟨_, hnodup, _, hcu, envT', envC', hT', hC', htWF, hcWF⟩ := hdata.expandedWF
  have e1 : envET = envT' := Option.some.inj (hT.symm.trans hT')
  subst e1
  have e2 : envEC = envC' := Option.some.inj (hC.symm.trans hC')
  subst e2
  have hbaseOrd := hbase.ordered
  have hETOrd : envET.Ordered := hbaseOrd.addConstVals (by
    intro ci hci
    obtain ⟨type, htype, rfl⟩ := List.mem_map.mp hci
    exact htWF type htype) hT
  have hECOrd : envEC.Ordered := hETOrd.addConstVals hcWF hC
  obtain ⟨_, _, _, _, _, _, hraw⟩ := hdata.expandedFormation
  have hfamOrd := VEnv.Ordered.inductProjections (es := es)
    (block := ⟨expanded.typeConstants, expanded.constructorConstants, [], [],
      expanded.projectionEntries, []⟩)
    hbaseOrd hECOrd hnodup htWF hcu hcWF hdata.expandedFormation.sourceParameterWF hraw
    rfl rfl rfl hT hC
  have hfamClosed := wrapForalls_sort_closedN (level := s.families[owner].resultLevel) (Γ := [])
    (domains := s.params ++ s.families[owner].indices)
    (by simpa [List.reverse_append] using ctxClosed_of_onCtx hfamOrd (hfamWF owner).1)
  obtain ⟨hfs, -⟩ := closedN_wrapForalls_inv hfamClosed
  obtain ⟨hp, hi⟩ := hfs.append_inv
  refine ⟨hp, fun c hc => ?_, by simpa using hi⟩
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hc
  obtain ⟨_, _, _, _, hdef⟩ := hdata.model.constructor ⟨i, by simpa using hi'⟩ hT
  obtain ⟨_, hdef⟩ := hdef
  have hcl := VExpr.WF.closedN hETOrd ⟨_, hdef.hasType.1⟩ trivial
  simp only [List.length_nil, constructorType] at hcl
  obtain ⟨hs, hbody⟩ := closedN_wrapForalls_inv hcl
  obtain ⟨-, hf⟩ := hs.append_inv
  have hflen : (s.fieldTypes s.constructors.toList[i]).length =
      s.constructors.toList[i].fields.length := by simp [fieldTypes]
  refine ⟨by simpa using hf, fun e he => ?_⟩
  have := closedN_mkApps_args hbody e (List.mem_append_right _ (by simpa using he))
  have hflen' : (s.fieldTypes s.constructors[i]).length = s.constructors[i].fields.length := by
    simp [fieldTypes]
  simpa [hflen'] using this


/-! ## The generic case type of a registered schema -/

/-- A certified schema has, at every owner slot, a closed generic case type. Restoration of the
parameters and family indices is the registration's header agreement; restoration of the
constructor field types and indices is the certified constructor correspondence. -/
theorem CaseSchema.Certified.genericType_closed {schema : CaseSchema}
    (hcert : schema.Certified base source block) (hheader : schema.HeaderAgreement base source)
    (hbase : base.WF) (owner : Fin schema.signature.families.size) :
    ∃ type, schema.genericType owner = some type ∧ type.Closed := by
  obtain ⟨expanded, auxiliaries, hdata, _, hr, _, _⟩ := hcert
  obtain ⟨RP, hRP, hRI⟩ := hheader
  rw [hr] at hRP hRI
  let r := compilationRestoration source auxiliaries
  have hOK : ∀ e e', r.expr e = some e' → Restorable r e 0 := by
    intro e e' he
    have := (restore_go_isSome r e []).mp (by
      change (r.expr e).isSome = true; rw [he]; rfl)
    simpa using this
  have hmapOK : ∀ (l L : List VExpr), l.mapM r.expr = some L → ∀ e ∈ l, Restorable r e 0 := by
    intro l L hl e he
    obtain ⟨e', _, he'⟩ := Lean4Lean.List.Forall₂.forall_exists_l (List.mapM_eq_some.mp hl) _ he
    exact hOK e e' he'
  have hpOK : ∀ p ∈ schema.signature.params, Restorable r p 0 := hmapOK _ _ hRP
  have hiOK : ∀ e ∈ schema.signature.families[owner].indices, Restorable r e 0 := by
    obtain ⟨RI, hRI', -⟩ := hRI owner
    exact hmapOK _ _ hRI'
  have hcOK : ∀ c ∈ schema.signature.constructors.toList,
      (∀ f ∈ schema.signature.fieldTypes c, Restorable r f 0) ∧
        ∀ e ∈ c.indices, Restorable r e 0 := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    let index : Fin schema.signature.constructors.size := ⟨i, by simpa using hi⟩
    have hcidx : schema.signature.constructors.toList[i] = schema.signature.constructors[index] := by
      simp [index]
    rw [hcidx]
    have hctorOK : Restorable r
        (schema.signature.constructorType schema.signature.constructors[index]) 0 := by
      obtain ⟨_, _, _, _, _, hfamilies⟩ := hdata.correspondence
      obtain ⟨src, -, hrest⟩ := Lean4Lean.List.Forall₂.forall_exists_l hfamilies _
        (schema.signature.declarationFamily_mem schema.signature.constructors[index].owner)
      obtain ⟨_, -, -, -, restored, hrestored, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l
        hrest.constructors _ (schema.signature.declarationCtor_family index)
      exact hOK _ restored hrestored
    simp only [constructorType] at hctorOK
    rw [restorable_wrapForalls] at hctorOK
    obtain ⟨hdoms, hbody⟩ := hctorOK
    refine ⟨fun f hf => hdoms f (List.mem_append_right _ hf), fun e he => ?_⟩
    simp only [familyApp] at hbody
    rw [restorable_mkApps] at hbody
    exact hbody.1 e (List.mem_append_right _ he)
  -- every head has the source universe and parameter arity
  have hheads : ∀ h ∈ r.heads, h.uvars = source.uvars ∧ h.nparams = source.nparams := by
    intro h hh
    simp only [r, compilationRestoration, List.mem_flatMap] at hh
    obtain ⟨a, _, hh⟩ := hh
    simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
    rcases hh with rfl | ⟨_, _, rfl⟩ <;> exact ⟨rfl, rfl⟩
  have huvars : schema.signature.uvars = source.uvars := hdata.model.uvars.trans hdata.uvars
  have hnparams : schema.signature.params.length = source.nparams :=
    hdata.model.nparams.trans hdata.nparams
  have hconst : ∀ name n, schema.signature.params.length ≤ n →
      Restorable r (.const name schema.genericLevels) n := by
    intro name n hn h hfind
    obtain ⟨hu, hp⟩ := hheads h (List.mem_of_find?_eq_some hfind)
    refine ⟨?_, ?_⟩
    · simp [CaseSchema.genericLevels, hu, huvars]
    · omega
  have hok := case_restorable schema owner hpOK hcOK hiOK hconst
  obtain ⟨type, htype⟩ := Option.isSome_iff_exists.mp
    ((restore_go_isSome r _ []).mpr (by simpa using hok))
  obtain ⟨hp, hc, hi⟩ := CaseCompilationData.case_scoping hdata hbase owner
  have hclosed := case_closedN schema owner hp hc hi
  have hscoped : ∀ h ∈ r.heads, ∀ a ∈ h.arguments, a.ClosedN h.nparams :=
    fun h hh a ha => (hdata.restorationScoped.2.2.1 h hh).2 a ha
  refine ⟨type, ?_, restore_go_closedN r hscoped _ [] 0 type hclosed (by simp) htype⟩
  simp only [CaseSchema.genericType, CaseSchema.type, hr]
  exact htype

/-- Every registered eliminator schema has, at every owner slot, a
closed generic case type. -/
theorem VEnv.WF.eliminator_genericType_closed {env : VEnv} (H : env.WF)
    {key : Name} {schema : CaseSchema} (hlookup : env.eliminators key schema)
    (owner : Fin schema.signature.families.size) :
    ∃ type, schema.genericType owner = some type ∧ type.Closed := by
  obtain ⟨base, source, block, hbase, _, hcert, hheader, _⟩ := H.eliminator_headerAgreement hlookup
  exact CaseSchema.Certified.genericType_closed hcert hheader hbase owner

end Lean4Lean.EnvTables
