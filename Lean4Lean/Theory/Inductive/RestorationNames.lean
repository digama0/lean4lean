import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.Formation

/-! # Names of a restoration table and basic facts about `Restoration.expr`

WAVE 3 COMPAT: the helpers the restoration metatheory (`Theory/Typing/RestorationShapes.lean`,
`Theory/Inductive/RestorationInterpretation.lean`, `RestorationHead.lean`) reads off a
`Restoration`, collected from the source branch's `IotaSoundnessLemmas.lean`,
`CaseRuleConstructors.lean`, `CaseReductionLemmas.lean`, `CaseSchemaLemmas.lean`,
`RestorationProjNames.lean`, `ProjNamesAvoid.lean` and `CaseProjections.lean` (all otherwise
dropped with the case eliminators):

* `Restoration.restorableNames`: the auxiliary heads and the renamed recursors;
* `Restoration.headName`: the constant a restored head is renamed to;
* `Restoration.expr` on application spines (`expr_mkApps`), equations (`equation_parts`) and
  on terms avoiding the restorable names (`expr_of_avoid`);
* `VExpr.projNamesAvoid` and two closedness lemmas for λ-telescopes and spines. -/

namespace Lean4Lean

namespace VExpr

/-- No projection type name of the term is in `names`. -/
def projNamesAvoid (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ | .const .. => true
  | .app f a | .lam f a | .forallE f a => f.projNamesAvoid names && a.projNamesAvoid names
  | .proj n _ e => !names.contains n && e.projNamesAvoid names

theorem ClosedN.mkApps_closed {fn : VExpr} {args : List VExpr} {n : Nat} (hf : fn.ClosedN n)
    (ha : ∀ arg ∈ args, arg.ClosedN n) : (VExpr.mkApps fn args).ClosedN n := by
  induction args generalizing fn with
  | nil => exact hf
  | cons a args ih => exact ih ⟨hf, ha _ (.head _)⟩ (fun _ h => ha _ (.tail _ h))

/-- Close a lambda telescope whose domains are scoped in binder order. -/
theorem ClosedN.wrapLams_closed {domains : List VExpr} {body : VExpr} {n : Nat}
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapLams domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      rwa [Nat.add_comm i 1, ← Nat.add_assoc] at hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

end VExpr

namespace InductiveSignature

/-- The names a restoration replaces: its auxiliary heads and its renamed recursors. -/
def Restoration.restorableNames (r : Restoration) : List Name :=
  r.heads.map (·.auxiliary) ++ r.recursors.map Prod.fst

theorem Restoration.heads_find?_eq_none {r : Restoration} {name : Name}
    (h : name ∉ r.heads.map (·.auxiliary)) :
    r.heads.find? (fun h => h.auxiliary == name) = none := by
  apply List.find?_eq_none.mpr
  intro head hmem heq
  exact h (List.mem_map.mpr ⟨head, hmem, by simpa using heq⟩)

theorem Restoration.recursorName_of_not_mem {r : Restoration} {name : Name}
    (h : name ∉ r.recursors.map Prod.fst) : r.recursorName name = name := by
  unfold Restoration.recursorName
  rw [List.find?_eq_none.mpr]
  intro pair hpair heq
  exact h (List.mem_map.mpr ⟨pair, hpair, by simpa using heq⟩)

/-- The constant a restored head becomes: the target of a specialized head, the renamed
recursor otherwise. -/
def Restoration.headName (r : Restoration) (name : Name) : Name :=
  match r.heads.find? (fun h => h.auxiliary == name) with
  | some h => h.target
  | none => r.recursorName name

theorem Restoration.expr_eq_go (r : Restoration) (e : VExpr) :
    r.expr e = Restoration.expr.go r e [] := rfl

theorem Restoration.go_mkApps (r : Restoration) (f : VExpr) (args acc : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps f args) acc =
      (args.mapM r.expr).bind fun args' => Restoration.expr.go r f (args' ++ acc) := by
  induction args generalizing f acc with
  | nil => simp [VExpr.mkApps]
  | cons a as ih =>
    have hm : VExpr.mkApps f (a :: as) = VExpr.mkApps (.app f a) as := rfl
    rw [hm, ih]
    simp only [Restoration.expr.go, List.mapM_cons]
    cases ha : Restoration.expr.go r a [] <;>
      cases has : as.mapM r.expr <;> simp [ha, Restoration.expr_eq_go]

theorem Restoration.expr_mkApps (r : Restoration) (f : VExpr) (args : List VExpr) :
    r.expr (VExpr.mkApps f args) =
      (args.mapM r.expr).bind fun args' => Restoration.expr.go r f args' := by
  simp [Restoration.expr_eq_go, Restoration.go_mkApps]

/-- `go_mkApps` in the `do` form of the source branch. -/
theorem restoration_mkApps (r : Restoration) (fn : VExpr) (inputArgs args : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps fn inputArgs) args = (do
      let restoredArgs ← inputArgs.mapM r.expr
      Restoration.expr.go r fn (restoredArgs ++ args)) :=
  Restoration.go_mkApps r fn inputArgs args

theorem Restoration.equation_parts {r : Restoration} {source restored : VDefEq}
    (h : r.equation source = some restored) :
    r.expr source.lhs = some restored.lhs ∧ r.expr source.rhs = some restored.rhs ∧
      r.expr source.type = some restored.type := by
  simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at h
  obtain ⟨lhs, hl, rhs, hr, type, ht, h⟩ := h
  cases h
  exact ⟨hl, hr, ht⟩

theorem Restoration.go_of_avoid {r : Restoration} :
    ∀ {e : VExpr} {args : List VExpr}, e.containsAnyConst r.restorableNames = false →
      Restoration.expr.go r e args = some (VExpr.mkApps e args)
  | .bvar _, _, _ | .sort _, _, _ => rfl
  | .const name levels, args, h => by
    have hn : name ∉ r.restorableNames := by simpa [VExpr.containsAnyConst] using h
    have hh : name ∉ r.heads.map (·.auxiliary) := fun hm =>
      hn (List.mem_append_left _ hm)
    have hrec : name ∉ r.recursors.map Prod.fst := fun hm =>
      hn (List.mem_append_right _ hm)
    simp only [Restoration.expr.go, Restoration.heads_find?_eq_none hh,
      Restoration.recursorName_of_not_mem hrec]
  | .app f a, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Restoration.expr.go, go_of_avoid h.2, Option.bind_eq_bind, Option.bind_some]
    exact go_of_avoid (args := _ :: args) h.1
  | .lam d b, args, h | .forallE d b, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp [Restoration.expr.go, Restoration.expr_eq_go, go_of_avoid h.1, go_of_avoid h.2,
      VExpr.mkApps]
  | .proj n i e, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp [Restoration.expr.go, Restoration.expr_eq_go, go_of_avoid h.2, VExpr.mkApps]

/-- Restoration fixes every term that avoids its restorable names. -/
theorem Restoration.expr_of_avoid {r : Restoration} {e : VExpr}
    (h : e.containsAnyConst r.restorableNames = false) : r.expr e = some e :=
  Restoration.go_of_avoid (args := []) h

theorem Restoration.mapM_expr_of_avoid {r : Restoration} :
    ∀ {l : List VExpr}, (∀ e ∈ l, e.containsAnyConst r.restorableNames = false) →
      l.mapM r.expr = some l
  | [], _ => rfl
  | e :: l, h => by
    rw [List.mapM_cons, Restoration.expr_of_avoid (h e List.mem_cons_self),
      mapM_expr_of_avoid (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

end InductiveSignature
end Lean4Lean
