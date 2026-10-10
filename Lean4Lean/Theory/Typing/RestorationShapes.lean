import Lean4Lean.Theory.Inductive.RestorationNames
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.Inductive.SignatureData

/-! Restoration of generated recursor telescopes and its commutation with lifting.

WAVE 3 COMPAT: port of the source branch's file (the `elim` case of `Restoration.expr` is
gone). `instantiateParams_liftN` is the source's `CaseReduction.lean` lemma. -/

namespace Lean4Lean
namespace InductiveSignature

theorem Restoration.mapM_expr_bvars (r : Restoration) (l : List VExpr)
    (hl : ∀ e ∈ l, ∃ i, e = .bvar i) : l.mapM r.expr = some l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rcases hl a (by simp) with ⟨i, rfl⟩
    simp [List.mapM_cons, ih (fun e he => hl e (by simp [he]))]

theorem Restoration.expr_mkApps_bvar (r : Restoration) (i : Nat) (args : List VExpr) :
    r.expr (VExpr.mkApps (.bvar i) args) =
      (args.mapM r.expr).map (VExpr.mkApps (.bvar i)) := by
  rw [r.expr_mkApps]
  cases args.mapM r.expr <;> rfl

/-- Restoration commutes with a `forallE` telescope. -/
theorem Restoration.expr_wrapForalls (r : Restoration) (doms : List VExpr) (body : VExpr) :
    r.expr (VExpr.wrapForalls doms body) =
      (doms.mapM r.expr).bind fun doms' =>
        (r.expr body).map (VExpr.wrapForalls doms') := by
  induction doms with
  | nil => cases hb : r.expr body <;> simp [VExpr.wrapForalls, hb]
  | cons d ds ih =>
    change Restoration.expr.go r (.forallE d (VExpr.wrapForalls ds body)) [] = _
    simp only [Restoration.expr.go, List.mapM_cons]
    rw [← Restoration.expr_eq_go, ← Restoration.expr_eq_go, ih]
    cases hd : r.expr d <;> cases hds : ds.mapM r.expr <;>
      cases hb : r.expr body <;> simp [VExpr.mkApps, VExpr.wrapForalls]

/-! The generator's recursor type, split into prefix, major and body. -/

/-- Parameters, motives, minors, and indices of the generated recursor telescope. -/
def Instance.recursorPrefix {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) : List VExpr :=
  g.params ++ g.motives ++ g.minors ++
    insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)

/-- The generated major domain: the owner family at the parameter and index variables. -/
def Instance.recursorMajor {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) : VExpr :=
  g.familyApp owner
    (vars s.params.length
      (s.families.size + s.constructors.size + s.families[owner].indices.length))
    (vars s.families[owner].indices.length 0)

/-- The generated motive application ending the recursor telescope. -/
def Instance.recursorBody {s : InductiveSignature} (_g : Instance s)
    (owner : Fin s.families.size) : VExpr :=
  VExpr.mkApps
    (.bvar (s.families[owner].indices.length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val)))
    (vars s.families[owner].indices.length 1 ++ [.bvar 0])

theorem Instance.recursorType_eq {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    g.recursorType owner =
      VExpr.wrapForalls (g.recursorPrefix owner ++ [g.recursorMajor owner])
        (g.recursorBody owner) := by
  simp [Instance.recursorType, Instance.recursorPrefix, Instance.recursorMajor,
    Instance.recursorBody, insertBinders]

theorem Instance.recursorPrefix_length {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    (g.recursorPrefix owner).length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
  simp [Instance.recursorPrefix, Instance.params, Instance.motives, Instance.minors,
    insertBinders, Nat.add_assoc]

/-- The motive application is restored to itself. -/
theorem Restoration.expr_recursorBody (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size) :
    r.expr (g.recursorBody owner) = some (g.recursorBody owner) := by
  rw [Instance.recursorBody, r.expr_mkApps_bvar,
    r.mapM_expr_bvars _ (by
      simp only [vars, List.mem_append, List.mem_map, List.mem_reverse, List.mem_range,
        List.mem_singleton]
      rintro e (⟨a, _, rfl⟩ | rfl) <;> exact ⟨_, rfl⟩)]
  rfl

/-- Restoring the generator's recursor type restores each telescope domain
separately; the motive application is unchanged. -/
theorem Restoration.expr_recursorType (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size) :
    r.expr (g.recursorType owner) =
      ((g.recursorPrefix owner).mapM r.expr).bind fun pre =>
        (r.expr (g.recursorMajor owner)).map fun major =>
          VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner) := by
  rw [g.recursorType_eq, r.expr_wrapForalls, r.expr_recursorBody, List.mapM_append]
  cases hp : (g.recursorPrefix owner).mapM r.expr <;>
    cases hm : r.expr (g.recursorMajor owner) <;> simp [hm]

theorem Restoration.expr_recursorType_eq_some (r : Restoration) {s : InductiveSignature}
    {g : Instance s} {owner : Fin s.families.size} {type : VExpr}
    (h : r.expr (g.recursorType owner) = some type) :
    ∃ pre major, (g.recursorPrefix owner).mapM r.expr = some pre ∧
      r.expr (g.recursorMajor owner) = some major ∧
      type = VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner) := by
  rw [r.expr_recursorType] at h
  cases hp : (g.recursorPrefix owner).mapM r.expr <;>
    cases hm : r.expr (g.recursorMajor owner) <;> simp [hp, hm] at h
  exact ⟨_, _, rfl, rfl, by simpa using h.symm⟩

/-- Simultaneous parameter substitution of a term scoped by the parameters commutes with
lifting. -/
theorem instantiateParams_liftN {body : VExpr} {arguments : List VExpr}
    (hc : body.ClosedN arguments.length) (n k : Nat) :
    (instantiateParams body arguments).liftN n k =
      instantiateParams body (arguments.map fun arg => arg.liftN n k) := by
  rw [← (VExpr.lift'_consN_skipN (e := instantiateParams body arguments))]
  refine VExpr.lift'_subst.trans (VExpr.subst_congr_closedN hc ?_)
  intro i hi
  simp [VExpr.Subst.lift_r, hi, VExpr.lift'_consN_skipN]

theorem HeadSpecialization.apply_liftN {h : HeadSpecialization}
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
    simp only [Option.pure_def, Option.map_some, VExpr.liftN_mkApps, VExpr.liftN,
      List.map_append, List.map_map, Function.comp_def, List.map_drop]
    congr 2
    apply congrArg (· ++ _)
    apply List.map_congr_left
    intro e he
    rw [← List.map_take]
    apply instantiateParams_liftN
    simpa only [List.length_take, Nat.min_eq_left hlen] using (hc e he).instL

/-- Restoration commutes with lifting when every head's specialization
arguments are scoped by its parameters. -/
theorem Restoration.expr_liftN (r : Restoration)
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
      exact HeadSpecialization.apply_liftN (hc spec (List.mem_of_find?_eq_some hs)) _ _ _ _
    · simp only [Option.map_some, VExpr.liftN_mkApps, VExpr.liftN]
  | bvar | sort =>
    intro args
    simp only [Restoration.expr.go, VExpr.liftN, Option.map_some, VExpr.liftN_mkApps]
  | lam domain body ihd ihb | forallE domain body ihd ihb =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have hd := ihd k []
    have hb := ihb (k + 1) []
    simp only [List.map_nil] at hd hb
    rw [← hd, ← hb]
    cases Restoration.expr.go r domain [] <;> cases Restoration.expr.go r body [] <;>
      simp [VExpr.liftN_mkApps, VExpr.liftN]
  | proj name i major ih =>
    intro args
    simp only [VExpr.liftN, Restoration.expr.go]
    have hm := ih k []
    simp only [List.map_nil] at hm
    rw [← hm]
    cases Restoration.expr.go r major [] <;>
      simp [VExpr.liftN_mkApps, VExpr.liftN]

theorem Restoration.mapM_expr_instL (r : Restoration) {l l' : List VExpr}
    (h : l.mapM r.expr = some l') (L : List VLevel) :
    (l.map (·.instL L)).mapM r.expr = some (l'.map (·.instL L)) := by
  rw [List.mapM_eq_some] at h ⊢
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (by rw [← Restoration.expr_instL, hab]; rfl) ih

private theorem mapM_zipIdx_lift (r : Restoration)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams) (e : Nat) :
    ∀ {l l' : List VExpr} (k : Nat), l.mapM r.expr = some l' →
      ((l.zipIdx k).map fun (t, i) => t.liftN e i).mapM r.expr =
        some ((l'.zipIdx k).map fun (t, i) => t.liftN e i)
  | [], l', k, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | a :: as, l', k, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a', ha, as', has, rfl⟩ := h
    have ih := mapM_zipIdx_lift r hc e (k + 1) has
    simp only [List.zipIdx_cons, List.map_cons, List.mapM_cons]
    rw [← Restoration.expr_liftN r hc, ha, Option.map_some]
    simp only [ih, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem Restoration.mapM_expr_insertBinders (r : Restoration)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {l l' : List VExpr} (h : l.mapM r.expr = some l') (e : Nat) :
    (insertBinders l e).mapM r.expr = some (insertBinders l' e) :=
  mapM_zipIdx_lift r hc e 0 h

end InductiveSignature
end Lean4Lean
