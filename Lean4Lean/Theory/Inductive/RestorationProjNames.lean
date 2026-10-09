import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.CaseProjNames
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas

/-! # Restoration and projection names

Generic facts used to certify the case schema of a nested declaration: restoration fixes
every term avoiding its restorable names (`Restoration.expr_of_avoid`), and preserves
projection names whenever the arguments of its heads do (`Restoration.expr_projNamesOK`), so a
restored schema projects only out of the structures its pieces and head arguments project out
of (`CaseSchema.projNamesOK_of_pieces_restored`). Monotonicity of the case certificate itself
is in `CaseCertificateMono.lean`. -/

namespace Lean4Lean

namespace VExpr

theorem ProjNamesOK.instL {ok : Name → Prop} {ls : List VLevel} :
    ∀ {e : VExpr}, e.ProjNamesOK ok → (e.instL ls).ProjNamesOK ok
  | .bvar _, _ | .sort _, _ | .const .., _ | .elim .., _ => trivial
  | .app _ _, h | .lam _ _, h | .forallE _ _, h => ⟨ProjNamesOK.instL h.1, ProjNamesOK.instL h.2⟩
  | .proj _ _ _, h => ⟨h.1, ProjNamesOK.instL h.2⟩

theorem ProjNamesOK.subst {ok : Name → Prop} :
    ∀ {e : VExpr} {σ : Subst}, e.ProjNamesOK ok → (∀ i, (σ i).ProjNamesOK ok) →
      (e.subst σ).ProjNamesOK ok
  | .bvar i, _, _, hσ => hσ i
  | .sort _, _, _, _ | .const .., _, _, _ | .elim .., _, _, _ => trivial
  | .app _ _, _, h, hσ => ⟨ProjNamesOK.subst h.1 hσ, ProjNamesOK.subst h.2 hσ⟩
  | .proj _ _ _, _, h, hσ => ⟨h.1, ProjNamesOK.subst h.2 hσ⟩
  | .lam _ _, σ, h, hσ | .forallE _ _, σ, h, hσ => by
    refine ⟨ProjNamesOK.subst h.1 hσ, ProjNamesOK.subst h.2 ?_⟩
    intro i
    cases i with
    | zero => trivial
    | succ i => exact ProjNamesOK.liftN (hσ i)

theorem ProjNamesOK.mkApps {ok : Name → Prop} :
    ∀ {f : VExpr} {args : List VExpr}, f.ProjNamesOK ok → (∀ a ∈ args, a.ProjNamesOK ok) →
      (VExpr.mkApps f args).ProjNamesOK ok
  | _, [], hf, _ => hf
  | _, a :: args, hf, hargs =>
    ProjNamesOK.mkApps (f := .app _ a) (args := args) ⟨hf, hargs a List.mem_cons_self⟩
      fun x hx => hargs x (List.mem_cons_of_mem _ hx)

theorem containsAnyConst_wrapForalls_inv {names : List Name} :
    ∀ {ds : List VExpr} {b : VExpr}, (VExpr.wrapForalls ds b).containsAnyConst names = false →
      (∀ d ∈ ds, d.containsAnyConst names = false) ∧ b.containsAnyConst names = false
  | [], _, h => ⟨by simp, h⟩
  | d :: ds, b, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.containsAnyConst,
      Bool.or_eq_false_iff] at h
    obtain ⟨hds, hb⟩ := containsAnyConst_wrapForalls_inv (ds := ds) h.2
    refine ⟨fun x hx => ?_, hb⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact hds x hx

end VExpr

namespace InductiveSignature

/-! ### Restoration of terms avoiding the restorable names -/

theorem Restoration.recursorName_of_not_mem {r : Restoration} {name : Name}
    (h : name ∉ r.recursors.map Prod.fst) : r.recursorName name = name := by
  unfold Restoration.recursorName
  rw [List.find?_eq_none.mpr]
  intro pair hpair heq
  exact h (List.mem_map.mpr ⟨pair, hpair, by simpa using heq⟩)

theorem Restoration.go_of_avoid {r : Restoration} :
    ∀ {e : VExpr} {args : List VExpr}, e.containsAnyConst r.restorableNames = false →
      Restoration.expr.go r e args = some (VExpr.mkApps e args)
  | .bvar _, _, _ | .sort _, _, _ | .elim .., _, _ => rfl
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
    simp only [Restoration.expr.go, go_of_avoid h.2, Option.bind_eq_bind, Option.bind_some,
      go_of_avoid h.1]
    rfl
  | .lam d b, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp [Restoration.expr.go, go_of_avoid h.2, go_of_avoid h.1, VExpr.mkApps]
  | .forallE d b, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp [Restoration.expr.go, go_of_avoid h.2, go_of_avoid h.1, VExpr.mkApps]
  | .proj n i e, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp [Restoration.expr.go, go_of_avoid h.2, VExpr.mkApps]

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

/-! ### Restoration preserves projection names -/

theorem instantiateParams_projNamesOK {ok : Name → Prop} {body : VExpr} {args : List VExpr}
    (hbody : body.ProjNamesOK ok) (hargs : ∀ a ∈ args, a.ProjNamesOK ok) :
    (instantiateParams body args).ProjNamesOK ok := by
  unfold instantiateParams
  apply VExpr.ProjNamesOK.subst hbody
  intro i
  split
  · exact hargs _ (List.getElem_mem _)
  · trivial

theorem HeadSpecialization.apply_projNamesOK {ok : Name → Prop} {h : HeadSpecialization}
    {levels : List VLevel} {args : List VExpr} {out : VExpr}
    (hh : ∀ a ∈ h.arguments, a.ProjNamesOK ok) (hargs : ∀ a ∈ args, a.ProjNamesOK ok)
    (happly : h.apply levels args = some out) : out.ProjNamesOK ok := by
  unfold HeadSpecialization.apply at happly
  split at happly
  · cases happly
  · simp only [Option.pure_def, Option.some.injEq] at happly
    subst happly
    apply VExpr.ProjNamesOK.mkApps (f := .const _ _) trivial
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨arg, harg, rfl⟩ := List.mem_map.1 ha
      exact instantiateParams_projNamesOK (VExpr.ProjNamesOK.instL (hh arg harg))
        (fun x hx => hargs x (List.mem_of_mem_take hx))
    · exact hargs a (List.mem_of_mem_drop ha)

theorem Restoration.go_projNamesOK {ok : Name → Prop} {r : Restoration}
    (hheads : ∀ h ∈ r.heads, ∀ a ∈ h.arguments, a.ProjNamesOK ok) :
    ∀ {e : VExpr} {args : List VExpr} {out : VExpr}, e.ProjNamesOK ok →
      (∀ a ∈ args, a.ProjNamesOK ok) → Restoration.expr.go r e args = some out →
      out.ProjNamesOK ok
  | .bvar _, _, _, _, hargs, hgo | .sort _, _, _, _, hargs, hgo
  | .elim .., _, _, _, hargs, hgo => by
    simp only [Restoration.expr.go, Option.some.injEq] at hgo
    subst hgo
    exact VExpr.ProjNamesOK.mkApps (by first | exact trivial) hargs
  | .const name levels, args, out, _, hargs, hgo => by
    simp only [Restoration.expr.go] at hgo
    split at hgo
    · next h hfind =>
      exact h.apply_projNamesOK (hheads h (List.mem_of_find?_eq_some hfind)) hargs hgo
    · simp only [Option.some.injEq] at hgo
      subst hgo
      exact VExpr.ProjNamesOK.mkApps (f := .const _ _) trivial hargs
  | .app f a, args, out, he, hargs, hgo => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at hgo
    cases ha : Restoration.expr.go r a [] with
    | none => simp [ha] at hgo
    | some a' =>
      simp only [ha, Option.bind_some] at hgo
      have ha' := go_projNamesOK hheads he.2 (by simp) ha
      refine go_projNamesOK hheads he.1 ?_ hgo
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha'
      · exact hargs x hx
  | .lam d b, args, out, he, hargs, hgo | .forallE d b, args, out, he, hargs, hgo => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at hgo
    cases hd : Restoration.expr.go r d [] with
    | none => simp [hd] at hgo
    | some d' =>
      cases hb : Restoration.expr.go r b [] with
      | none => simp [hd, hb] at hgo
      | some b' =>
        simp only [hd, hb, Option.bind_some, Option.pure_def, Option.some.injEq] at hgo
        subst hgo
        exact VExpr.ProjNamesOK.mkApps
          ⟨go_projNamesOK hheads he.1 (by simp) hd, go_projNamesOK hheads he.2 (by simp) hb⟩
          hargs
  | .proj n i e, args, out, he, hargs, hgo => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at hgo
    cases hm : Restoration.expr.go r e [] with
    | none => simp [hm] at hgo
    | some e' =>
      simp only [hm, Option.bind_some, Option.pure_def, Option.some.injEq] at hgo
      subst hgo
      exact VExpr.ProjNamesOK.mkApps ⟨he.1, go_projNamesOK hheads he.2 (by simp) hm⟩ hargs

/-- Restoration projects only out of the structures its input and the arguments of its heads
project out of. -/
theorem Restoration.expr_projNamesOK {ok : Name → Prop} {r : Restoration}
    (hheads : ∀ h ∈ r.heads, ∀ a ∈ h.arguments, a.ProjNamesOK ok)
    {e out : VExpr} (he : e.ProjNamesOK ok) (hr : r.expr e = some out) : out.ProjNamesOK ok :=
  Restoration.go_projNamesOK hheads he (by simp) hr


namespace CaseSchema

/-- A schema projects only out of structures satisfying `ok` when every piece of its signature
and every argument of a head of its restoration does. -/
theorem projNamesOK_of_pieces_restored {schema : CaseSchema} {ok : Name → Prop}
    (hheads : ∀ h ∈ schema.restoration.heads, ∀ a ∈ h.arguments, a.ProjNamesOK ok)
    (hparams : ∀ e ∈ schema.signature.params, e.ProjNamesOK ok)
    (hindices : ∀ f ∈ schema.signature.families.toList, ∀ e ∈ f.indices, e.ProjNamesOK ok)
    (hfields : ∀ c ∈ schema.signature.constructors.toList,
      ∀ e ∈ schema.signature.fieldTypes c, e.ProjNamesOK ok)
    (hcindices : ∀ c ∈ schema.signature.constructors.toList, ∀ e ∈ c.indices, e.ProjNamesOK ok)
    (key : Name) :
    (∀ owner type, schema.genericType owner = some type → type.ProjNamesOK ok) ∧
    (∀ owner rules, schema.genericEquations key owner = some rules → ∀ df ∈ rules,
      df.lhs.ProjNamesOK ok ∧ df.rhs.ProjNamesOK ok ∧ df.type.ProjNamesOK ok) := by
  have htype : ∀ owner n, ¬ ok n →
      ((schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).recursorType
        (schema.viewOwner owner)).projNamesAvoid [n] = true := by
    intro owner n hn
    apply Instance.recursorType_projNamesAvoid
    · intro e he
      exact VExpr.projNamesOK_iff_avoid.1 (hparams e he) n hn
    · intro f hf e he
      simp only [view, List.mem_singleton] at hf
      have : f = schema.signature.families[owner] := by simpa using hf
      subst this
      exact VExpr.projNamesOK_iff_avoid.1
        (hindices _ (Array.getElem_mem_toList _) e he) n hn
    · intro c hc
      change c ∈ (List.filterMap (fun ctor => if ctor.owner == owner then
          some (schema.caseConstructor ctor) else none) schema.signature.constructors.toList :
            List (Constructor 1)).toArray.toList at hc
      rw [List.toList_toArray] at hc
      obtain ⟨c0, hc0, hc⟩ := List.mem_filterMap.1 hc
      split at hc
      · cases hc
        refine ⟨CaseSchema.caseConstructor_recursiveFields c0, ?_, ?_⟩
        · intro e he
          rw [CaseSchema.view_fieldTypes_case] at he
          exact VExpr.projNamesOK_iff_avoid.1 (hfields c0 hc0 e he) n hn
        · intro e he
          exact VExpr.projNamesOK_iff_avoid.1 (hcindices c0 hc0 e he) n hn
      · cases hc
  refine ⟨fun owner type h => ?_, fun owner rules h df hdf => ?_⟩
  · simp only [genericType, CaseSchema.type] at h
    exact Restoration.expr_projNamesOK hheads (VExpr.projNamesOK_iff_avoid.2 (htype owner)) h
  · simp only [genericEquations, CaseSchema.equations] at h
    obtain ⟨df0, hdf0, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp h) df hdf
    unfold Instance.equations at hdf0
    obtain ⟨index, -, rfl⟩ := List.mem_map.1 hdf0
    have hall := fun n hn =>
      Instance.equation_projNamesAvoid_of_recursorType _ _ (htype owner n hn) index
        (.elim key owner.val)
    unfold Restoration.equation at hrestore
    simp only [Option.bind_eq_bind, Option.pure_def] at hrestore
    cases hl : schema.restoration.expr
        ((schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).equation
          index (.elim key owner.val)).lhs with
    | none => simp [hl] at hrestore
    | some l =>
      cases hr : schema.restoration.expr
          ((schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).equation
            index (.elim key owner.val)).rhs with
      | none => simp [hl, hr] at hrestore
      | some r' =>
        cases ht : schema.restoration.expr
            ((schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).equation
              index (.elim key owner.val)).type with
        | none => simp [hl, hr, ht] at hrestore
        | some t =>
          simp only [hl, hr, ht, Option.bind_some, Option.some.injEq] at hrestore
          subst hrestore
          exact ⟨Restoration.expr_projNamesOK hheads
              (VExpr.projNamesOK_iff_avoid.2 fun n hn => (hall n hn).1) hl,
            Restoration.expr_projNamesOK hheads
              (VExpr.projNamesOK_iff_avoid.2 fun n hn => (hall n hn).2.1) hr,
            Restoration.expr_projNamesOK hheads
              (VExpr.projNamesOK_iff_avoid.2 fun n hn => (hall n hn).2.2) ht⟩

end CaseSchema


end InductiveSignature
end Lean4Lean
