import Lean4Lean.Theory.Typing.IotaLemmas

/-!
# Iota reduction from the shape of a stored recursor rule

A recursor rule is stored as a closed lambda-wrapped equation whose left-hand side is the recursor
applied to its parameters, motives, minors, indices, and a constructor application. This file shows
that such a rule, applied to the actual arguments of a recursor application whose major premise
reduces to a constructor application, yields the instantiated right-hand side. Everything is
derived from the syntactic shape of the rule together with unique typing and injectivity of the
inductive type constant: the arguments are typed at the rule's binders because the pattern
variables of the left-hand side are typed at the recursor's own telescope.
-/

namespace Lean4Lean

namespace VExpr

/-- The simultaneous substitution performed by `instOuter`: the first argument replaces the
outermost variable. -/
def Subst.ofList (args : List VExpr) : Subst := fun k =>
  if h : k < args.length then args[args.length - 1 - k] else .bvar (k - args.length)

theorem Subst.liftN_apply (σ : Subst) (n k : Nat) :
    σ.liftN n k = if k < n then .bvar k else (σ (k - n)).liftN n := by
  induction n generalizing k with
  | zero => simp [Subst.liftN, liftN_zero]
  | succ n ih =>
    cases k with
    | zero => simp [Subst.liftN, Subst.lift]
    | succ k =>
      simp only [Subst.liftN, Subst.lift, ih, Nat.succ_lt_succ_iff, Nat.succ_sub_succ]
      split
      · show VExpr.liftN 1 (bvar k) = bvar (k + 1)
        rw [VExpr.liftN, liftVar_base']
      · rw [← liftN_succ]

theorem instOuter_eq_subst_aux (a : VExpr) (as : List VExpr) :
    (a.liftN as.length).subst (Subst.ofList as) = a := by
  rw [liftN_subst]
  conv => rhs; rw [← subst_id (e := a)]
  congr 1
  funext k
  simp only [Subst.lift_l, Subst.id, Lift.liftVar_consN_skipN, liftVar_base', Subst.ofList]
  rw [dif_neg (by omega)]
  congr 1; omega

theorem instOuter_eq_subst (body : VExpr) (args : List VExpr) :
    body.instOuter args = body.subst (Subst.ofList args) := by
  induction args generalizing body with
  | nil =>
    have : Subst.ofList [] = Subst.id := by funext k; simp [Subst.ofList, Subst.id]
    simp [this]
  | cons a as ih =>
    rw [instOuter_cons, ih, instN_eq, subst_subst]
    congr 1
    funext k
    simp only [Subst.comp, Subst.liftN_apply, Subst.ofList, List.length_cons]
    by_cases hk : k < as.length
    · rw [if_pos hk]
      simp only [subst_bvar, Subst.ofList, dif_pos hk, dif_pos (Nat.lt_succ_of_lt hk)]
      rw [List.getElem_cons]
      split
      · omega
      · congr 1; omega
    · rw [if_neg hk]
      by_cases hk' : k = as.length
      · subst hk'
        simp only [Subst.one, Subst.cons, Nat.sub_self, dif_pos (Nat.lt_succ_self _),
          Nat.add_sub_cancel, List.getElem_cons_zero]
        rw [instOuter_eq_subst_aux]
      · have hk2 : as.length < k := by omega
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        obtain ⟨d, hd⟩ : ∃ d, k' + 1 - as.length = d + 1 := ⟨k' - as.length, by omega⟩
        rw [hd]
        simp only [Subst.one, Subst.cons, Subst.id, liftN, liftVar_base', subst_bvar, Subst.ofList]
        rw [dif_neg (by omega), dif_neg (by omega)]
        congr 1
        omega

def Subst.shift (n : Nat) : Subst := fun i => .bvar (i + n)

theorem liftN_eq_subst (e : VExpr) (n : Nat) :
    e.liftN n = e.subst (Subst.shift n) := by
  have := liftN_subst (e := e) (n := n) (k := 0) (σ := Subst.id)
  rw [subst_id] at this
  rw [this]
  congr 1
  funext i
  simp [Subst.lift_l, Subst.id, Lift.liftVar_skipN, Subst.shift]

theorem Subst.ofList_lt (args : List VExpr) (h : k < args.length) :
    Subst.ofList args k = args[args.length - 1 - k] := dif_pos h

/-- Instantiating an instantiation is instantiating at the instantiated arguments. -/
theorem instOuter_instOuter (X : VExpr) (vs args : List VExpr) (hX : X.ClosedN vs.length) :
    (X.instOuter vs).instOuter args = X.instOuter (vs.map (·.instOuter args)) := by
  simp only [instOuter_eq_subst, subst_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.comp, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (vs.map _) (by simpa using hi), List.getElem_map]


/-- Instantiating at the variables of an enclosing context is a lift. -/
theorem instOuter_range_bvar (X : VExpr) (j n : Nat) (hX : X.ClosedN j) (hj : j ≤ n) :
    X.instOuter ((List.range j).map fun k => VExpr.bvar (n - 1 - k)) = X.liftN (n - j) := by
  simp only [instOuter_eq_subst, liftN_eq_subst]
  apply subst_congr_closedN hX
  intro i hi
  rw [Subst.ofList_lt _ (by simpa using hi)]
  simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range, Subst.shift]
  congr 1
  omega

/-- The first `n` of `total` binders, seen from under all `total` binders: the outermost binder
first. -/
def bvarRange (n total : Nat) : List VExpr :=
  (List.range n).map fun j => VExpr.bvar (total - 1 - j)

@[simp] theorem bvarRange_length (n total : Nat) : (bvarRange n total).length = n := by
  simp [bvarRange]

theorem bvarRange_getElem (n total : Nat) (j : Nat) (h : j < n) :
    (bvarRange n total)[j]'(by simpa using h) = VExpr.bvar (total - 1 - j) := by
  simp [bvarRange]

theorem bvarRange_take (n total k : Nat) (h : k ≤ n) :
    (bvarRange n total).take k = bvarRange k total := by
  simp only [bvarRange, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem bvarRange_zero (total : Nat) : bvarRange 0 total = [] := rfl

@[simp] theorem instL_bvarRange (n total : Nat) (ls : List VLevel) :
    (bvarRange n total).map (VExpr.instL ls) = bvarRange n total := by
  simp [bvarRange, List.map_map, Function.comp_def, VExpr.instL]

theorem bvarRange_map_liftN (n total k : Nat) (h : n ≤ total) :
    (bvarRange n total).map (VExpr.liftN k) = bvarRange n (total + k) := by
  simp only [bvarRange, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  simp only [Function.comp_def, VExpr.liftN, liftVar_base']
  congr 1
  omega

/-- Instantiating the variables of a binder range selects the corresponding arguments. -/
theorem instOuter_bvarRange (n total : Nat) (args : List VExpr) (hn : n ≤ total)
    (htot : total ≤ args.length) :
    (bvarRange n total).map (·.instOuter args) = (args.drop (args.length - total)).take n := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [List.length_map, bvarRange_length] at h1
    simp only [List.getElem_map, bvarRange_getElem n total j h1]
    rw [instOuter_bvar args (by omega), List.getElem_take, List.getElem_drop]
    congr 1
    omega

theorem instOuter_range_bvar' (X : VExpr) (j n : Nat) (hX : X.ClosedN j) (hj : j ≤ n) :
    X.instOuter (bvarRange j n) = X.liftN (n - j) :=
  instOuter_range_bvar X j n hX hj

theorem instOuter_lift_prefix {p : VExpr} (hp : p.ClosedN n)
    (args : List VExpr) (hlen : args.length = n + k) :
    (p.liftN k).instOuter args = p.instOuter (args.take n) := by
  have h := instOuter_range_bvar' p n (n + k) hp (by omega)
  simp only [Nat.add_sub_cancel_left] at h
  rw [← h, instOuter_instOuter p _ _ (by simpa using hp),
    instOuter_bvarRange _ _ _ (by omega) (by omega)]
  simp [hlen]


theorem _root_.Lean4Lean.Lookup.of_getElem : ∀ {Γ : List VExpr} {i : Nat} (h : i < Γ.length),
    Lookup Γ i (Γ[i].liftN (i + 1))
  | _ :: _, 0, _ => .zero
  | _ :: Γ, i + 1, h => by
    have := Lookup.of_getElem (Γ := Γ) (i := i) (by simpa using h)
    simp only [List.getElem_cons_succ]
    rw [VExpr.liftN_succ]
    exact .succ this

/-- The variable for the `j`-th binder of a reversed telescope. -/
theorem _root_.Lean4Lean.Lookup.reverse_append (doms Γ : List VExpr) (j : Nat)
    (hj : j < doms.length) :
    Lookup (doms.reverse ++ Γ) (doms.length - 1 - j) (doms[j].liftN (doms.length - j)) := by
  have := Lookup.of_getElem (Γ := doms.reverse ++ Γ) (i := doms.length - 1 - j) (by simp; omega)
  rw [List.getElem_append_left (by simp; omega), List.getElem_reverse] at this
  have e1 : doms.length - 1 - (doms.length - 1 - j) = j := by omega
  have e2 : doms.length - 1 - j + 1 = doms.length - j := by omega
  have e3 : doms[doms.length - 1 - (doms.length - 1 - j)]'(by omega) = doms[j] := by
    congr 1
  rwa [e3, e2] at this

theorem ClosedN.of_mkApps_fn {fn : VExpr} {args : List VExpr}
    (h : (VExpr.mkApps fn args).ClosedN k) : fn.ClosedN k := by
  induction args generalizing fn with
  | nil => exact h
  | cons a as ih => exact (ih h).1

theorem ClosedN.of_mkApps_arg {fn : VExpr} {args : List VExpr}
    (h : (VExpr.mkApps fn args).ClosedN k) : ∀ a ∈ args, a.ClosedN k := by
  induction args generalizing fn with
  | nil => simp
  | cons a as ih =>
    simp only [VExpr.mkApps, List.foldl_cons] at h
    have := ih h
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact (ClosedN.of_mkApps_fn h).2
    · exact this b hb

/-- Lifting at depth `k` as a substitution. -/
theorem liftN_eq_subst_at (e : VExpr) (n k : Nat) :
    e.liftN n k = e.subst (fun i => if i < k then .bvar i else .bvar (i + n)) := by
  have := liftN_subst (e := e) (n := n) (k := k) (σ := Subst.id)
  rw [subst_id] at this
  rw [this]
  congr 1
  funext i
  simp only [Subst.lift_l, Subst.id]
  rw [Lift.liftVar_consN_skipN]
  simp only [liftVar]
  split <;> first | rfl | (congr 1; omega)


/-- Instantiating the outer variables of a telescope over parameters and fields at the parameters
lifted past `e` inserted binders, and the fields themselves, inserts the binders. -/
theorem instOuter_insert_bvars (X : VExpr) (a b e : Nat) (hX : X.ClosedN (a + b)) :
    X.instOuter (((bvarRange a a).map fun p => p.liftN (e + b)) ++ bvarRange b b) =
      X.liftN e b := by
  rw [instOuter_eq_subst, liftN_eq_subst_at]
  apply subst_congr_closedN hX
  intro i hi
  rw [Subst.ofList_lt _ (by simp; omega)]
  simp only [List.length_append, List.length_map, bvarRange_length]
  by_cases hib : i < b
  · rw [if_pos hib, List.getElem_append_right (by simp; omega)]
    simp only [bvarRange, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
    congr 1; omega
  · rw [if_neg hib, List.getElem_append_left (by simp; omega)]
    simp only [bvarRange, List.getElem_map, List.getElem_range, liftN, liftVar]
    split <;> (congr 1; omega)

end VExpr
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Peeling a lambda telescope typed at the matching forall telescope. -/
theorem HasType.wrapLams_inv (henv : VEnv.WF env) :
    ∀ {doms : List VExpr} {Γ : List VExpr} {body T : VExpr},
      OnCtx Γ (env.IsType U) →
      env.HasType U Γ (VExpr.wrapLams doms body) (VExpr.wrapForalls doms T) →
      OnCtx (doms.reverse ++ Γ) (env.IsType U) ∧
      env.HasType U (doms.reverse ++ Γ) body T := by
  intro doms
  induction doms with
  | nil => intro Γ body T hΓ H; exact ⟨hΓ, H⟩
  | cons d ds ih =>
    intro Γ body T hΓ H
    change env.HasType U Γ (.lam d (VExpr.wrapLams ds body)) (.forallE d (VExpr.wrapForalls ds T)) at H
    have ⟨B, hB, hbody⟩ := H.lam_inv_forallE henv hΓ
    have hd : env.IsType U Γ d := (IsType.forallE_inv henv.ordered (H.isType henv.ordered hΓ)).1
    have hΓ' : OnCtx (d :: Γ) (env.IsType U) := And.intro hΓ hd
    have ⟨_, _, hBT⟩ := hB.forallE_inv henv hΓ
    have hbody' := hbody.defeqU_r henv hΓ' ⟨_, hBT⟩
    have := ih hΓ' hbody'
    simpa [List.reverse_cons, List.append_assoc] using this

/-- Every domain of a well-formed telescope is closed under the binders before it. -/
theorem IsType.wrapForalls_inv (henv : VEnv.WF env) :
    ∀ {doms : List VExpr} {Γ : List VExpr} {body : VExpr},
      OnCtx Γ (env.IsType U) →
      env.IsType U Γ (VExpr.wrapForalls doms body) →
      OnCtx (doms.reverse ++ Γ) (env.IsType U) ∧
      env.IsType U (doms.reverse ++ Γ) body := by
  intro doms
  induction doms with
  | nil => intro Γ body hΓ H; exact ⟨hΓ, H⟩
  | cons d ds ih =>
    intro Γ body hΓ H
    change env.IsType U Γ (.forallE d (VExpr.wrapForalls ds body)) at H
    have ⟨hd, hrest⟩ := IsType.forallE_inv henv.ordered H
    have hΓ' : OnCtx (d :: Γ) (env.IsType U) := And.intro hΓ hd
    have := ih hΓ' hrest
    simpa [List.reverse_cons, List.append_assoc] using this

theorem _root_.Lean4Lean.OnCtx.getElem_closedN (henv : VEnv.WF env) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (i : Nat) (hi : i < Γ.length) :
    Γ[i].ClosedN (Γ.length - 1 - i) := by
  induction Γ generalizing i with
  | nil => simp at hi
  | cons A Γ ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero]
      have ⟨_, h⟩ := hΓ.2
      exact h.closedN henv.ordered (CtxWF.closed henv.ordered hΓ.1)
    | succ i =>
      simp only [List.getElem_cons_succ, List.length_cons]
      have := ih hΓ.1 i (by simp at hi; omega)
      rwa [show Γ.length + 1 - 1 - (i + 1) = Γ.length - 1 - i by omega]

/-- The domains of a closed telescope are closed under the binders before them. -/
theorem _root_.Lean4Lean.OnCtx.reverse_getElem_closedN (henv : VEnv.WF env) {doms Γ : List VExpr}
    (hΓ : OnCtx (doms.reverse ++ Γ) (env.IsType U)) (j : Nat) (hj : j < doms.length) :
    doms[j].ClosedN (j + Γ.length) := by
  have := hΓ.getElem_closedN henv (doms.length - 1 - j) (by simp; omega)
  rw [List.getElem_append_left (by simp; omega), List.getElem_reverse] at this
  simp only [List.length_append, List.length_reverse] at this
  have e1 : doms.length - 1 - (doms.length - 1 - j) = j := by omega
  have e2 : doms.length + Γ.length - 1 - (doms.length - 1 - j) = j + Γ.length := by omega
  rw [e2] at this
  have e3 : doms[doms.length - 1 - (doms.length - 1 - j)] = doms[j] := by simp only [e1]
  rwa [e3] at this

/-- Instantiating a reversed domain list one binder at a time. -/
theorem _root_.Lean4Lean.Ctx.InstN.reverse (ds : List VExpr) :
    ∀ {k Γ₁ Γ₂}, Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ₂ →
      Ctx.InstN Γ₀ e₀ A₀ (ds.length + k) (ds.reverse ++ Γ₁)
        ((VExpr.instDomains ds e₀ k).reverse ++ Γ₂) := by
  induction ds with
  | nil => intro k Γ₁ Γ₂ W; simpa [VExpr.instDomains] using W
  | cons d ds ih =>
    intro k Γ₁ Γ₂ W
    have := ih (k := k + 1) (Γ₁ := d :: Γ₁) (Γ₂ := d.inst e₀ k :: Γ₂) (.succ W)
    simp only [List.length_cons, VExpr.instDomains, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    rwa [show ds.length + 1 + k = ds.length + (k + 1) by omega]

/-- A defeq under a telescope, instantiated at arguments typed along the telescope. -/
theorem IsDefEqU.instOuter_telescope (henv : VEnv.WF env) :
    ∀ {doms args : List VExpr} {Γ : List VExpr} {X Y : VExpr},
      env.IsDefEqU U (doms.reverse ++ Γ) X Y → args.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length),
        env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) →
      env.IsDefEqU U Γ (X.instOuter args) (Y.instOuter args) := by
  intro doms args
  induction args generalizing doms with
  | nil =>
    intro Γ X Y H hlen _
    cases doms with
    | nil => simpa using H
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro Γ X Y H hlen hty
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons] at hlen
      have ha : env.HasType U Γ a d := by
        have := hty 0 (by simp) (by simp)
        simpa only [List.getElem_cons_zero, List.take_zero, VExpr.instOuter_nil] using this
      have W : Ctx.InstN Γ a d (ds.length + 0) (ds.reverse ++ d :: Γ)
          ((VExpr.instDomains ds a 0).reverse ++ Γ) := Ctx.InstN.reverse ds .zero
      have H' : env.IsDefEqU U (ds.reverse ++ d :: Γ) X Y := by
        simpa [List.reverse_cons, List.append_assoc] using H
      obtain ⟨A, H'⟩ := H'
      have H'' := H'.instN henv.ordered ha W
      simp only [VExpr.instOuter_cons]
      rw [show as.length = ds.length + 0 by omega]
      refine ih (doms := VExpr.instDomains ds a 0) ⟨_, H''⟩ (by simpa using hlen) ?_
      intro j hj hj'
      have := hty (j + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
        List.length_take] at this
      rw [VExpr.instDomains_getElem ds a 0 j (by simpa using hj')]
      rwa [show min j as.length = 0 + j by omega] at this

/-- Left congruence of an application spine: the head may be replaced by a definitionally equal
head as long as the spine is well formed. -/
theorem IsDefEqU.mkApps_congr_left (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {f f' : VExpr},
      env.IsDefEqU U Γ f f' → VExpr.WF env U Γ (VExpr.mkApps f args) →
      env.IsDefEqU U Γ (VExpr.mkApps f args) (VExpr.mkApps f' args) := by
  intro args
  induction args with
  | nil => intro f f' H _; simpa [VExpr.mkApps] using H
  | cons a as ih =>
    intro f f' H hwf
    simp only [VExpr.mkApps, List.foldl_cons] at hwf ⊢
    have hfa : VExpr.WF env U Γ (.app f a) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f a) hwf
    have ⟨A, B, hf, ha⟩ := hfa.app_inv henv.ordered hΓ
    have hff' : env.IsDefEq U Γ f f' (.forallE A B) := H.of_l henv hΓ hf
    exact ih ⟨_, hff'.appDF ha⟩ hwf

end VEnv

/-! ## Shapes of recursors, constructors, and iota rules -/

/-- A recursor telescope with an explicit specialization of its major family.
`ctorParams` is scoped under the recursor parameters, before motives, minors,
and indices are introduced. Its length is the constructor's parameter count;
there is no inequality between that count and the recursor's parameter count. -/
structure VRecursorShape (env : VEnv) (recName : Name)
    (recUvars nparams cnparams nmotives nminors nindices : Nat) (indName : Name)
    (indLevels : List VLevel)
    (ctorParams : List VExpr := VExpr.bvarRange cnparams nparams) where
  ctorParams_length : ctorParams.length = cnparams
  ctorParams_closed : ∀ p ∈ ctorParams, p.ClosedN nparams
  type : VExpr
  const : env.constants recName = some ⟨recUvars, type⟩
  doms : List VExpr
  result : VExpr
  type_eq : type = VExpr.wrapForalls doms result
  doms_length : doms.length = nparams + nmotives + nminors + nindices + 1
  major_eq : doms[nparams + nmotives + nminors + nindices]? =
    some (VExpr.mkApps (.const indName indLevels)
      ((ctorParams.map fun p => p.liftN (nmotives + nminors + nindices)) ++
        VExpr.bvarRange nindices nindices))

/-- The syntactic shape of a constructor's type: a telescope of parameters and fields whose result
is the inductive type at the universe parameters, applied to the parameter variables and index
expressions. -/
structure VConstructorShape (env : VEnv) (ctorName : Name)
    (ctorUvars nparams nfields nindices : Nat) (indName : Name) where
  type : VExpr
  const : env.constants ctorName = some ⟨ctorUvars, type⟩
  doms : List VExpr
  indices : List VExpr
  type_eq : type = VExpr.wrapForalls doms
    (VExpr.mkApps (.const indName (VLevel.params ctorUvars))
      (VExpr.bvarRange nparams (nparams + nfields) ++ indices))
  doms_length : doms.length = nparams + nfields
  indices_length : indices.length = nindices

/-- A typed application whose head has a syntactic telescope ending in a type headed by a
rigid constant has supplied exactly that telescope when the application itself has a type
headed by the same rigid constant. This is `HasType.mkApps_sort_arity` with the rigid-head
against Pi separation `IsDefEqU.rigidApp_forallE_inv` in place of `sort_forallE_inv`. -/
theorem VEnv.HasType.mkApps_rigid_arity (henv : VEnv.WF env)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hrigid : env.Rigid c)
    {f : VExpr} {domains args xs familyArgs : List VExpr} {ls levels : List VLevel}
    (hf : env.HasType U Γ f (VExpr.wrapForalls domains (VExpr.mkApps (.const c ls) xs)))
    (ht : env.HasType U Γ (VExpr.mkApps f args) (VExpr.mkApps (.const c levels) familyArgs)) :
    args.length = domains.length := by
  induction args generalizing f domains xs with
  | nil =>
    cases domains with
    | nil => rfl
    | cons domain domains =>
      have ⟨_, hT⟩ := ht.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hrigid hT
        (hf.uniqU henv hΓ ht).symm).elim
  | cons arg args ih =>
    have hfa : VExpr.WF env U Γ (.app f arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f arg) ⟨_, ht⟩
    rcases hfa.app_inv henv.ordered hΓ with ⟨A, B, hfun, harg⟩
    cases domains with
    | nil =>
      have ⟨_, hT⟩ := hf.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hrigid hT
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

/-- A constructor whose application has its inductive family as type is fully
applied. This is a typing inversion obligation, not a runtime arity check.
In particular, the parameter count here belongs to the constructor, not to a
recursor that happens to eliminate it. -/
theorem VConstructorShape.saturated_of_hasType (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : VConstructorShape env ctorName ctorUvars nparams nfields nindices indName)
    (hrigid : env.Rigid indName)
    (ht : env.HasType U Γ (VExpr.mkApps (.const ctorName cls) args)
      (VExpr.mkApps (.const indName levels) familyArgs)) :
    args.length = nparams + nfields := by
  have hhead : VExpr.WF env U Γ (.const ctorName cls) :=
    VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  obtain ⟨ci, hci, hcls, hlen⟩ := hhead.const_inv henv.ordered hΓ
  cases H.const.symm.trans hci
  have hc := VEnv.HasType.const (Γ := Γ) H.const hcls hlen
  rw [H.type_eq, VExpr.instL_wrapForalls, VExpr.instL_mkApps] at hc
  simpa [H.doms_length] using VEnv.HasType.mkApps_rigid_arity henv hΓ hrigid hc ht

/-- Universe instantiation commutes with outer instantiation. -/
theorem VExpr.instL_instOuter (e : VExpr) (args : List VExpr) (ls : List VLevel) :
    (e.instOuter args).instL ls = (e.instL ls).instOuter (args.map (·.instL ls)) := by
  induction args generalizing e with
  | nil => rfl
  | cons a as ih => simp [VExpr.instOuter_cons, ih, VExpr.instL_instN]

/-- A stored iota pattern with explicit constructor-parameter specialization.
The recursor and its rules share `ctorParams`; these expressions are lifted
past the motive, minor, and field binders when forming the constructor pattern.
This is an implementation alignment contract, not an inductive formation rule. -/
structure VIotaRuleShape (env : VEnv) (recName : Name)
    (recUvars nparams cnparams nmotives nminors nindices : Nat) (ctorName : Name)
    (ctorLevels : List VLevel) (nfields : Nat) (df : VDefEq)
    (ctorParams : List VExpr := VExpr.bvarRange cnparams nparams) where
  defeq : env.defeqs df
  uvars : df.uvars = recUvars
  doms : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_eq : df.lhs = VExpr.wrapLams doms lhsBody
  rhs_eq : df.rhs = VExpr.wrapLams doms rhsBody
  type_eq : df.type = VExpr.wrapForalls doms typeBody
  doms_length : doms.length = nparams + nmotives + nminors + nfields
  indexArgs : List VExpr
  indexArgs_length : indexArgs.length = nindices
  lhs_pattern : lhsBody = VExpr.mkApps (.const recName (VLevel.params recUvars))
    (VExpr.bvarRange (nparams + nmotives + nminors) doms.length ++ indexArgs ++
      [VExpr.mkApps (.const ctorName ctorLevels)
        ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
          VExpr.bvarRange nfields nfields)])
  /-- The rule's parameter, motive and minor binders are the recursor's own binders. -/
  rec_doms : ∀ recDoms recBody,
    env.constants recName = some ⟨recUvars, VExpr.wrapForalls recDoms recBody⟩ →
    recDoms.length = nparams + nmotives + nminors + nindices + 1 →
    ∀ j, j < nparams + nmotives + nminors → doms[j]? = recDoms[j]?
  /-- The rule's field binders agree with the constructor's field domains, specialized at
  `ctorParams` and the earlier fields, in the rule's own prefix context. -/
  ctor_doms : ∀ ctorUvars ctorDoms ctorBody,
    env.constants ctorName = some ⟨ctorUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ →
    ctorDoms.length = cnparams + nfields →
    ∀ i, i < nfields → ∀ (hd : nparams + nmotives + nminors + i < doms.length)
      (hc : cnparams + i < ctorDoms.length),
    env.IsDefEqU recUvars ((doms.take (nparams + nmotives + nminors + i)).reverse)
      doms[nparams + nmotives + nminors + i]
      ((ctorDoms[cnparams + i].instL ctorLevels).instOuter
        ((ctorParams.map fun p => p.liftN (nmotives + nminors + i)) ++ VExpr.bvarRange i i))

namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Definitionally equal telescopes of the same length have pointwise definitionally equal
domains, each in the context of the earlier domains of the first telescope. -/
theorem IsDefEqU.wrapForalls_doms (henv : VEnv.WF env) :
    ∀ {Γ ds ds' : List VExpr} {b b' : VExpr}, OnCtx Γ (env.IsType U) →
      ds.length = ds'.length →
      env.IsDefEqU U Γ (VExpr.wrapForalls ds b) (VExpr.wrapForalls ds' b') →
      ∀ k (hk : k < ds.length) (hk' : k < ds'.length),
        env.IsDefEqU U ((ds.take k).reverse ++ Γ) ds[k] ds'[k]
  | _, [], _, _, _, _, _, _, k, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _, _ :: _, [], _, _, _, hl, _, _, _, _ => by simp at hl
  | Γ, d :: ds, d' :: ds', b, b', hΓ, hl, H, k, hk, hk' => by
    obtain ⟨⟨u, hd⟩, _, hrest⟩ := IsDefEqU.forallE_inv henv hΓ H
    cases k with
    | zero => exact ⟨_, hd⟩
    | succ k =>
      have := IsDefEqU.wrapForalls_doms henv (Γ := d :: Γ) ⟨hΓ, _, hd.hasType.1⟩
        (by simpa using hl) ⟨_, hrest⟩ k (by simpa using hk) (by simpa using hk')
      simpa [List.take_succ_cons] using this

/-- A recursor application spine types its arguments along the recursor telescope; in particular
the major premise is typed at the inductive type applied to the parameters and indices. -/
theorem _root_.Lean4Lean.VRecursorShape.spine_typing (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams)
    (hls : ∀ l ∈ ls, l.WF U) (hlsl : ls.length = recUvars)
    {pre : List VExpr} (hpre : pre.length = nparams + nmotives + nminors + nindices)
    {major : VExpr}
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ [major]))) :
    (∀ j (hj : j < pre.length) (hj' : j < (H.doms.map (VExpr.instL ls)).length),
      env.HasType U Γ pre[j] ((H.doms.map (VExpr.instL ls))[j].instOuter (pre.take j))) ∧
    env.HasType U Γ major (VExpr.mkApps (.const indName (indLevels.map (VLevel.inst ls)))
      ((ctorParams.map fun p => (p.instL ls).instOuter (pre.take nparams)) ++
        pre.drop (nparams + nmotives + nminors))) ∧
    env.HasType U Γ major
      (((H.doms.map (VExpr.instL ls))[pre.length]'(by simp [hpre, H.doms_length])).instOuter
        pre) := by

  have hc := HasType.const (Γ := Γ) H.const hls (by simpa using hlsl)
  rw [H.type_eq, VExpr.instL_wrapForalls] at hc
  have hlen : (pre ++ [major]).length = (H.doms.map (VExpr.instL ls)).length := by
    simp [hpre, H.doms_length]
  have ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hc hwf hlen
  have hmaj0 := hargs pre.length (by simp) (by simp [hpre, H.doms_length])
  rw [List.getElem_append_right (Nat.le_refl _), List.take_left] at hmaj0
  simp only [Nat.sub_self, List.getElem_singleton] at hmaj0
  refine ⟨fun j hj hj' => ?_, ?_, hmaj0⟩
  · have := hargs j (by simp; omega) hj'
    rwa [List.getElem_append_left hj, List.take_append_of_le_length (by omega)] at this
  · have := hmaj0
    rw [List.getElem_map] at this
    have hmaj : H.doms[pre.length]'(by simp [hpre, H.doms_length]) =
        VExpr.mkApps (.const indName indLevels)
          ((ctorParams.map fun p => p.liftN (nmotives + nminors + nindices)) ++
            VExpr.bvarRange nindices nindices) := by
      rw [List.getElem_eq_iff, ← H.major_eq, hpre]
    rw [hmaj] at this
    simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, VExpr.instL_bvarRange,
      VExpr.instOuter_mkApps, VExpr.instOuter_const] at this
    have hparams :
        ((ctorParams.map fun p => p.liftN (nmotives + nminors + nindices)).map
          (VExpr.instL ls)).map (fun p => p.instOuter pre) =
        ctorParams.map (fun p => (p.instL ls).instOuter (pre.take nparams)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp_def, VExpr.instL_liftN]
      exact VExpr.instOuter_lift_prefix (H.ctorParams_closed p hp).instL pre
        (by omega)
    rw [hparams,
      VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by omega)] at this
    rw [hpre] at this
    rw [show nparams + nmotives + nminors + nindices - nindices = nparams + nmotives + nminors by
      omega] at this
    rwa [List.take_of_length_le (l := pre.drop (nparams + nmotives + nminors)) (i := nindices)
      (by simp; omega)] at this


/-- A constructor application spine types its arguments along the constructor telescope and has
the inductive type at the instantiated indices. -/
theorem _root_.Lean4Lean.VConstructorShape.spine_typing (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : VConstructorShape env ctorName ctorUvars nparams nfields nindices indName)
    (hls : ∀ l ∈ cls, l.WF U) (hlsl : cls.length = ctorUvars)
    {P fields : List VExpr} (hP : P.length = nparams) (hf : fields.length = nfields)
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const ctorName cls) (P ++ fields))) :
    (∀ j (hj : j < (P ++ fields).length) (hj' : j < (H.doms.map (VExpr.instL cls)).length),
      env.HasType U Γ (P ++ fields)[j]
        ((H.doms.map (VExpr.instL cls))[j].instOuter ((P ++ fields).take j))) ∧
    env.HasType U Γ (VExpr.mkApps (.const ctorName cls) (P ++ fields))
      (VExpr.mkApps (.const indName cls)
        (P ++ H.indices.map fun e => (e.instL cls).instOuter (P ++ fields))) := by
  have hc := HasType.const (Γ := Γ) H.const hls (by simpa using hlsl)
  rw [H.type_eq, VExpr.instL_wrapForalls] at hc
  have hlen : (P ++ fields).length = (H.doms.map (VExpr.instL cls)).length := by
    simp [hP, hf, H.doms_length]
  have ⟨hargs, hres⟩ := HasType.mkApps_wrapForalls henv hΓ hc hwf hlen
  refine ⟨hargs, ?_⟩
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, VExpr.instL_bvarRange,
    VExpr.instOuter_mkApps, VExpr.instOuter_const, List.map_map, Function.comp_def,
    VLevel.params_map_inst cls hlsl] at hres
  rw [VExpr.instOuter_bvarRange _ _ _ (by omega) (by simp; omega)] at hres
  simp only [List.length_append, hP, hf, Nat.sub_self, List.drop_zero] at hres
  rwa [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at hres

/-- The bodies of a stored iota rule are typed under its telescope, at any universe levels. -/
theorem _root_.Lean4Lean.VIotaRuleShape.body_typing (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : VIotaRuleShape env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df ctorParams)
    (hls : ∀ l ∈ ls, l.WF U) :
    OnCtx ((H.doms.map (VExpr.instL ls)).reverse ++ Γ) (env.IsType U) ∧
    env.HasType U ((H.doms.map (VExpr.instL ls)).reverse ++ Γ) (H.lhsBody.instL ls)
      (H.typeBody.instL ls) ∧
    env.HasType U ((H.doms.map (VExpr.instL ls)).reverse ++ Γ) (H.rhsBody.instL ls)
      (H.typeBody.instL ls) := by
  have ⟨hl, hr⟩ := henv.ordered.defEqWF H.defeq
  rw [H.lhs_eq, H.type_eq] at hl
  rw [H.rhs_eq, H.type_eq] at hr
  have hl' := (hl.instL hls).weak0 henv.ordered (Γ := Γ)
  have hr' := (hr.instL hls).weak0 henv.ordered (Γ := Γ)
  simp only [VExpr.instL_wrapLams, VExpr.instL_wrapForalls] at hl' hr'
  have ⟨h1, h2⟩ := HasType.wrapLams_inv henv hΓ hl'
  exact ⟨h1, h2, (HasType.wrapLams_inv henv hΓ hr').2⟩

/-- Closedness of the domains of a closed constant's telescope type. -/
theorem VEnv.constant_doms_closed (henv : VEnv.WF env)
    (hc : env.constants c = some ⟨uvars, VExpr.wrapForalls doms body⟩)
    (hls : ∀ l ∈ ls, l.WF U) :
    (∀ j (hj : j < (doms.map (VExpr.instL ls)).length),
      (doms.map (VExpr.instL ls))[j].ClosedN j) ∧
    (body.instL ls).ClosedN doms.length := by
  have h := (henv.ordered.constWF hc).instL hls
  simp only [VExpr.instL_wrapForalls] at h
  have ⟨h1, h2⟩ := IsType.wrapForalls_inv henv (by trivial) h
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h1.reverse_getElem_closedN henv j hj
    simpa using this
  · have ⟨_, h2⟩ := h2
    have := h2.closedN henv.ordered (CtxWF.closed henv.ordered h1)
    simpa using this

/-- The arguments a recursor application supplies to a stored iota rule are typed along the rule's
telescope: the pattern variables of the left-hand side are typed at the recursor and constructor
telescopes, so unique typing carries the actual arguments over. -/
theorem _root_.Lean4Lean.VIotaRuleShape.args_typing (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (Hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams)
    (Hctor : VConstructorShape env ctorName ctorUvars cnparams nfields nindices indName)
    (Hrule : VIotaRuleShape env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      indLevels nfields df ctorParams)
    (hrigid : env.Rigid indName) (hIL : indLevels.length = ctorUvars)
    (hls : ∀ l ∈ ls, l.WF U) (hlsl : ls.length = recUvars)
    {pre : List VExpr} (hpre : pre.length = nparams + nmotives + nminors + nindices)
    {major : VExpr}
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ [major])))
    {cls : List VLevel} {P' fields : List VExpr}
    (hcls : cls.length = ctorUvars) (hclsw : ∀ l ∈ cls, l.WF U)
    (hP' : P'.length = cnparams) (hf : fields.length = nfields)
    (hmajor : env.IsDefEqU U Γ major (VExpr.mkApps (.const ctorName cls) (P' ++ fields))) :
    ∀ j (hj : j < (pre.take (nparams + nmotives + nminors) ++ fields).length)
      (hj' : j < (Hrule.doms.map (VExpr.instL ls)).length),
      env.HasType U Γ (pre.take (nparams + nmotives + nminors) ++ fields)[j]
        ((Hrule.doms.map (VExpr.instL ls))[j].instOuter
          ((pre.take (nparams + nmotives + nminors) ++ fields).take j)) := by
  -- Notation
  generalize hm : nparams + nmotives + nminors = m at *
  generalize hA : pre.take m ++ fields = A
  generalize hdoms : Hrule.doms.map (VExpr.instL ls) = doms'
  generalize hL' : indLevels.map (VLevel.inst ls) = L'
  have hn : doms'.length = m + nfields := by simp [← hdoms, Hrule.doms_length, hm]
  have hAlen : A.length = m + nfields := by simp [← hA, hf]; omega
  have hL'len : L'.length = ctorUvars := by simp [← hL', hIL]
  have hL'w : ∀ l ∈ L', l.WF U := by
    rw [← hL']; intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hls
  -- (S1) The actual recursor spine.
  have ⟨hpreT, hmajT, _⟩ := Hrec.spine_typing henv hΓ hls hlsl (by rw [hpre, hm]) hwf
  rw [hL', hm] at hmajT
  -- (S2) The actual constructor spine.
  have hctorWF : VExpr.WF env U Γ (VExpr.mkApps (.const ctorName cls) (P' ++ fields)) :=
    let ⟨_, h⟩ := hmajor; ⟨_, h.hasType.2⟩
  have ⟨hcargs, hcres⟩ := Hctor.spine_typing henv hΓ hclsw hcls hP' hf hctorWF
  -- (S3, S4) Injectivity at the major premise's type.
  have hMTCT : env.IsDefEqU U Γ
      (VExpr.mkApps (.const indName L') ((ctorParams.map fun p => (p.instL ls).instOuter (pre.take nparams)) ++ pre.drop m))
      (VExpr.mkApps (.const indName cls)
        (P' ++ Hctor.indices.map fun e => (e.instL cls).instOuter (P' ++ fields))) := by
    have h1 := (hmajor.of_l henv hΓ hmajT).hasType.2
    exact h1.uniqU henv hΓ hcres
  have ⟨_, hsort⟩ := hmajT.isType henv.ordered hΓ
  have ⟨hLcls, hargsE⟩ := IsDefEqU.rigidApp_inv henv hΓ hrigid hMTCT hsort
  have ⟨hPE, _⟩ := List.forall₂_append_split hargsE (by simp [hP', Hrec.ctorParams_length])
  -- (S5) The rule's telescope is a well-formed context.
  obtain ⟨hΓ₀, -, -⟩ := Hrule.body_typing henv hΓ hls (Γ := Γ)
  rw [hdoms] at hΓ₀
  -- (S6) Closedness of the constructor's domains.
  have ⟨hctorC, _⟩ := VEnv.constant_doms_closed henv (Hctor.type_eq ▸ Hctor.const) hL'w
  -- Main induction.
  suffices ∀ j, j ≤ doms'.length → ∀ i (hi : i < j) (hiA : i < A.length) (hi' : i < doms'.length),
      env.HasType U Γ A[i] (doms'[i].instOuter (A.take i)) by
    intro j hj hj'
    exact this doms'.length (Nat.le_refl _) j (by omega) hj hj'
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi hiA hi'
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | hij
    · exact ih (by omega) i hij hiA hi'
    subst i
    have hjn : j < doms'.length := hi'
    -- The typed prefix.
    have hA_j : ∀ i (hi : i < (A.take j).length) (hi' : i < (doms'.take j).length),
        env.HasType U Γ (A.take j)[i] ((doms'.take j)[i].instOuter ((A.take j).take i)) := by
      intro i hi hi'
      simp only [List.length_take] at hi hi'
      have hij : i < j := by omega
      simp only [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
      exact ih (by omega) i hij (by omega) (by omega)
    have hAjlen : (A.take j).length = (doms'.take j).length := by simp; omega
    -- The pattern variable and its declared type.
    rcases Nat.lt_or_ge j m with hjm | hjm
    · -- A parameter, motive, or minor position.
      -- The declared rule domain is the recursor's domain.
      have hjr : j < Hrule.doms.length := by rw [Hrule.doms_length]; omega
      have hjc : j < Hrec.doms.length := by rw [Hrec.doms_length]; omega
      have hag := Hrule.rec_doms Hrec.doms Hrec.result (Hrec.type_eq ▸ Hrec.const)
        Hrec.doms_length j (by omega)
      rw [List.getElem?_eq_getElem hjr, List.getElem?_eq_getElem hjc] at hag
      have hdj : doms'[j] = (Hrec.doms.map (VExpr.instL ls))[j]'(by simpa using hjc) := by
        simp only [← hdoms, List.getElem_map, Option.some.inj hag]
      have hΓj : OnCtx (doms'[j] :: ((doms'.take j).reverse ++ Γ)) (env.IsType U) := by
        have h := hΓ₀
        rw [← List.take_append_drop (j + 1) doms', List.reverse_append, List.append_assoc] at h
        have h' := OnCtx.of_append h
        have hT : (doms'.take (j + 1)).reverse = doms'[j] :: (doms'.take j).reverse := by
          rw [List.take_add_one, List.getElem?_eq_getElem hjn]; simp
        rw [hT] at h'; exact h'
      have hU' : env.IsDefEqU U ((doms'.take j).reverse ++ Γ) doms'[j]
          ((Hrec.doms.map (VExpr.instL ls))[j]'(by simpa using hjc)) := by
        rw [← hdj]; have ⟨_, h⟩ := hΓj.2; exact IsDefEqU.refl ⟨_, h⟩
      have hI := IsDefEqU.instOuter_telescope henv hU' hAjlen hA_j
      have hAj : A.take j = pre.take j := by
        rw [← hA, List.take_append_of_le_length (by simp; omega), List.take_take,
          Nat.min_eq_left (Nat.le_of_lt hjm)]
      have hAjj : A[j] = pre[j]'(by omega) := by
        subst hA
        rw [List.getElem_append_left (by simp; omega), List.getElem_take]
      rw [hAj] at hI ⊢
      rw [hAjj]
      exact (hpreT j (by omega) (by simp [Hrec.doms_length]; omega)).defeqU_r henv hΓ hI.symm
    · -- A field position.
      obtain ⟨i, rfl⟩ : ∃ i, j = m + i := ⟨j - m, by omega⟩
      have hi : i < nfields := by omega
      have hcdl : (Hctor.doms.map (VExpr.instL L')).length = cnparams + nfields := by
        simp [Hctor.doms_length]
      have hcdl' : (Hctor.doms.map (VExpr.instL cls)).length = cnparams + nfields := by
        simp [Hctor.doms_length]
      have hcC := hctorC (cnparams + i) (by omega)
      -- The declared rule domain agrees with the constructor's field domain.
      have hU' : env.IsDefEqU U ((doms'.take (m + i)).reverse ++ Γ) (doms'[m + i]'hjn)
          (((Hctor.doms.map (VExpr.instL L'))[cnparams + i]'(by omega)).instOuter
            ((ctorParams.map fun p => (p.instL ls).liftN (nmotives + nminors + i)) ++
              VExpr.bvarRange i i)) := by
        have hjr : m + i < Hrule.doms.length := by rw [Hrule.doms_length]; omega
        have hag := Hrule.ctor_doms _ Hctor.doms _ (Hctor.type_eq ▸ Hctor.const)
          Hctor.doms_length i hi (by rw [hm]; exact hjr) (by rw [Hctor.doms_length]; omega)
        simp only [hm] at hag
        have ⟨_, h1⟩ := hag.instL hls
        obtain ⟨hΓe, -, -⟩ := Hrule.body_typing henv (Γ := []) trivial hls
        have hΓp : OnCtx ((Hrule.doms.take (m + i)).reverse.map (VExpr.instL ls)) (env.IsType U) := by
          have h := hΓe
          rw [List.append_nil, ← List.take_append_drop (m + i) (Hrule.doms.map (VExpr.instL ls)),
            List.reverse_append] at h
          simpa [List.map_reverse, List.map_take] using OnCtx.of_append h
        have h2 := h1.weakR henv.ordered (CtxWF.closed henv.ordered hΓp) Γ
        have e1 : (Hrule.doms.take (m + i)).reverse.map (VExpr.instL ls) =
            (doms'.take (m + i)).reverse := by
          simp [← hdoms, List.map_reverse, List.map_take]
        have e2 : (Hrule.doms[m + i]'hjr).instL ls = doms'[m + i]'hjn := by simp [← hdoms]
        have e3 : ((ctorParams.map fun p => p.liftN (nmotives + nminors + i)) ++
              VExpr.bvarRange i i).map (VExpr.instL ls) =
            (ctorParams.map fun p => (p.instL ls).liftN (nmotives + nminors + i)) ++
              VExpr.bvarRange i i := by
          simp [List.map_append, List.map_map, Function.comp_def, VExpr.instL_liftN]
        rw [e1, e2, VExpr.instL_instOuter, VExpr.instL_instL, hL', e3] at h2
        rw [List.getElem_map]
        exact ⟨_, h2⟩
      have hI := IsDefEqU.instOuter_telescope henv hU' hAjlen hA_j
      -- The instantiated pattern type.
      have hAj : A.take (m + i) = pre.take m ++ fields.take i := by
        rw [← hA, List.take_append, List.take_of_length_le (by simp; omega)]
        simp only [List.length_take, Nat.min_eq_left (show m ≤ pre.length by omega),
          Nat.add_sub_cancel_left]
      have hY0 : ((Hctor.doms.map (VExpr.instL L'))[cnparams + i].instOuter
            ((ctorParams.map fun p => (p.instL ls).liftN (nmotives + nminors + i)) ++ VExpr.bvarRange i i)).instOuter (A.take (m + i)) =
          (Hctor.doms.map (VExpr.instL L'))[cnparams + i].instOuter
            ((ctorParams.map fun p => (p.instL ls).instOuter (pre.take nparams)) ++ fields.take i) := by
        rw [VExpr.instOuter_instOuter _ _ _ (by simpa [Hrec.ctorParams_length] using hcC), List.map_append,
          VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by simp; omega)]
        rw [hAj]
        have hlen' : (pre.take m ++ fields.take i).length = m + i := by simp; omega
        rw [hlen', show m + i - i = m by omega,
          List.drop_left' (by simp; omega), List.take_take, Nat.min_self]
        congr 1
        simp only [List.map_map, Function.comp_def]
        apply congrArg (fun params => params ++ fields.take i)
        apply List.map_congr_left
        intro p hp
        rw [VExpr.instOuter_lift_prefix ((Hrec.ctorParams_closed p hp).instL) _ (by rw [hlen']; omega),
          List.take_append_of_le_length (by simp; omega), List.take_take,
          Nat.min_eq_left (by omega)]
      rw [hY0] at hI
      -- The actual field, typed along the constructor telescope at the actual levels.
      have hfield := hcargs (cnparams + i) (by simp; omega) (by simp [Hctor.doms_length]; omega)
      rw [List.getElem_append_right (as := P') (i := cnparams + i) (by omega), List.take_append,
        List.take_of_length_le (l := P') (by omega)] at hfield
      simp only [hP', Nat.add_sub_cancel_left] at hfield
      -- Domain agreement between the two level instantiations.
      have hcT := HasType.const (Γ := Γ) Hctor.const hclsw (by simpa using hcls)
      rw [Hctor.type_eq, VExpr.instL_wrapForalls] at hcT
      obtain ⟨res, Hw, _⟩ := HasType.mkApps_telescope henv hΓ hcT hctorWF
        (doms := Hctor.doms.map (VExpr.instL cls)) (rest := _)
        (by rw [show (P' ++ fields).length = (Hctor.doms.map (VExpr.instL cls)).length by
              simp [hP', hf, Hctor.doms_length]]
            exact VExpr.takeForalls_wrapForalls _ _)
      have hT : env.IsDefEqU U Γ
          (VExpr.wrapForalls (Hctor.doms.map (VExpr.instL L'))
            ((VExpr.mkApps (.const indName (VLevel.params ctorUvars))
              (VExpr.bvarRange cnparams (cnparams + nfields) ++ Hctor.indices)).instL L'))
          (VExpr.wrapForalls (Hctor.doms.map (VExpr.instL cls))
            ((VExpr.mkApps (.const indName (VLevel.params ctorUvars))
              (VExpr.bvarRange cnparams (cnparams + nfields) ++ Hctor.indices)).instL cls)) := by
        have := IsType.instL_defeq (Γ := Γ) henv.ordered (henv.ordered.constWF Hctor.const) hL'w hclsw hLcls
        simp only [Hctor.type_eq, VExpr.instL_wrapForalls] at this
        exact this
      have hbsE : List.Forall₂ (env.IsDefEqU U Γ) ((ctorParams.map fun p => (p.instL ls).instOuter (pre.take nparams)) ++ fields.take i)
          ((P' ++ fields).take (cnparams + i)) := by
        rw [List.take_append, List.take_of_length_le (l := P') (by omega), hP',
          Nat.add_sub_cancel_left]
        refine hPE.append' ?_
        refine List.forall₂_of_getElem rfl fun k hk _ => IsDefEqU.refl ?_
        simp only [List.length_take] at hk
        rw [List.getElem_take]
        have := hcargs (cnparams + k) (by simp; omega) (by simp [Hctor.doms_length]; omega)
        rw [List.getElem_append_right (as := P') (i := cnparams + k) (by omega)] at this
        simp only [hP', Nat.add_sub_cancel_left] at this
        exact ⟨_, this⟩
      have hD := InstForallsC.domain_defeq henv hΓ Hw (by simp [hP', hf, Hctor.doms_length])
        (hcdl.trans hcdl'.symm) (by simp [Hctor.doms_length]; omega) hT (by simp [Hrec.ctorParams_length]; omega) hbsE
      rw [List.take_append, List.take_of_length_le (l := P') (by omega), hP',
        Nat.add_sub_cancel_left] at hD
      -- Assemble.
      have hAjj : A[m + i] = fields[i] := by
        subst hA
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_take, Nat.min_eq_left (show m ≤ pre.length by omega),
          Nat.add_sub_cancel_left]
      rw [hAjj]
      exact ((hfield.defeqU_r henv hΓ hD.symm).defeqU_r henv hΓ hI.symm)



theorem _root_.Lean4Lean.List.forall₂_symm {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {l₁ l₂ : List α} (h : List.Forall₂ R l₁ l₂) : List.Forall₂ R l₂ l₁ := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hR _ _ h) ih

/-- Iota reduction from a supplied typing of the rule arguments along the rule telescope.
This form does not use context strengthening. -/
theorem _root_.Lean4Lean.VIotaRuleShape.iota_of_args (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (Hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams)
    (Hctor : VConstructorShape env ctorName ctorUvars cnparams nfields nindices indName)
    (Hrule : VIotaRuleShape env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      indLevels nfields df ctorParams)
    (hrigid : env.Rigid indName) (hIL : indLevels.length = ctorUvars)
    (hls : ∀ l ∈ ls, l.WF U) (hlsl : ls.length = recUvars)
    {pre : List VExpr} (hpre : pre.length = nparams + nmotives + nminors + nindices)
    {major : VExpr} {extra : List VExpr}
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ major :: extra)))
    {cls : List VLevel} {P' fields : List VExpr}
    (hcls : cls.length = ctorUvars) (hclsw : ∀ l ∈ cls, l.WF U)
    (hP' : P'.length = cnparams) (hf : fields.length = nfields)
    (hmajor : env.IsDefEqU U Γ major (VExpr.mkApps (.const ctorName cls) (P' ++ fields)))
    (hA : ∀ j (hj : j < (pre.take (nparams + nmotives + nminors) ++ fields).length)
      (hj' : j < (Hrule.doms.map (VExpr.instL ls)).length),
      env.HasType U Γ (pre.take (nparams + nmotives + nminors) ++ fields)[j]
        ((Hrule.doms.map (VExpr.instL ls))[j].instOuter
          ((pre.take (nparams + nmotives + nminors) ++ fields).take j))) :
    env.IsDefEqU U Γ (VExpr.mkApps (.const recName ls) (pre ++ major :: extra))
      (VExpr.mkApps (df.rhs.instL ls)
        (pre.take (nparams + nmotives + nminors) ++ fields ++ extra)) := by
  have hsplit : pre ++ major :: extra = (pre ++ [major]) ++ extra := by simp
  rw [hsplit, VExpr.mkApps_append (l₁ := pre ++ [major])] at hwf ⊢
  rw [VExpr.mkApps_append (l₁ := pre.take (nparams + nmotives + nminors) ++ fields)]
  have hwf1 : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ [major])) :=
    VExpr.WF.of_mkApps henv.ordered hΓ hwf
  refine IsDefEqU.mkApps_congr_left henv hΓ ?_ hwf
  -- Notation
  generalize hm : nparams + nmotives + nminors = m at *
  generalize hAe : pre.take m ++ fields = A at *
  generalize hdoms : Hrule.doms.map (VExpr.instL ls) = doms' at *
  generalize hL' : indLevels.map (VLevel.inst ls) = L' at *
  have hn : doms'.length = m + nfields := by simp [← hdoms, Hrule.doms_length, hm]
  have hAlen : A.length = m + nfields := by simp [← hAe, hf]; omega
  have hL'len : L'.length = ctorUvars := by simp [← hL', hIL]
  have hL'w : ∀ l ∈ L', l.WF U := by
    rw [← hL']; intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hls
  have hdf : ls.length = df.uvars := hlsl.trans Hrule.uvars.symm
  let params := ctorParams.map fun p => (p.instL ls).instOuter (pre.take nparams)
  let patternParams := ctorParams.map fun p => (p.instL ls).liftN (nmotives + nminors + nfields)
  have hparamsLen : params.length = cnparams := by simp [params, Hrec.ctorParams_length]
  have hpatternLen : patternParams.length = cnparams := by simp [patternParams, Hrec.ctorParams_length]
  have hpatternInst : patternParams.map (·.instOuter A) = params := by
    simp only [patternParams, params, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_def]
    rw [VExpr.instOuter_lift_prefix (Hrec.ctorParams_closed p hp).instL A (by omega)]
    congr 1
    rw [← hAe, List.take_append_of_le_length (by simp; omega), List.take_take,
      Nat.min_eq_left (by omega)]
  have hrawPatternInst :
      ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)).map (VExpr.instL ls)).map
        (·.instOuter A) = params := by
    simpa only [patternParams, List.map_map, Function.comp_def, VExpr.instL_liftN] using hpatternInst
  -- (S1) The actual recursor spine.
  have ⟨hpreT, hmajT, hmajT'⟩ := Hrec.spine_typing henv hΓ hls hlsl (by rw [hpre, hm]) hwf1
  rw [hL', hm] at hmajT
  -- (S2) The actual constructor spine.
  have hctorWF : VExpr.WF env U Γ (VExpr.mkApps (.const ctorName cls) (P' ++ fields)) :=
    let ⟨_, h⟩ := hmajor; ⟨_, h.hasType.2⟩
  have ⟨hcargs, hcres⟩ := Hctor.spine_typing henv hΓ hclsw hcls hP' hf hctorWF
  -- (S3, S4) Injectivity at the major premise's type.
  have hMTCT : env.IsDefEqU U Γ
      (VExpr.mkApps (.const indName L') (params ++ pre.drop m))
      (VExpr.mkApps (.const indName cls)
        (P' ++ Hctor.indices.map fun e => (e.instL cls).instOuter (P' ++ fields))) := by
    have h1 := (hmajor.of_l henv hΓ hmajT).hasType.2
    exact h1.uniqU henv hΓ hcres
  have ⟨_, hsort⟩ := hmajT.isType henv.ordered hΓ
  have ⟨hLcls, hargsE⟩ := IsDefEqU.rigidApp_inv henv hΓ hrigid hMTCT hsort
  have ⟨hPE, _⟩ := List.forall₂_append_split hargsE (by simp [hP']; omega)
  -- (S5) The rule's left-hand side under its telescope.
  have ⟨hΓ₀, hL, hR⟩ := Hrule.body_typing henv hΓ hls (Γ := Γ)
  rw [hdoms] at hΓ₀ hL hR
  rw [Hrule.lhs_pattern] at hL
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_cons, List.map_nil,
    VExpr.instL_bvarRange, VLevel.params_map_inst ls hlsl, hL', hm, List.map_map, Function.comp_def, VExpr.instL_liftN] at hL
  rw [show Hrule.doms.length = doms'.length by simp [← hdoms]] at hL
  have hLwf : VExpr.WF env U (doms'.reverse ++ Γ) (VExpr.mkApps (.const recName ls)
      ((VExpr.bvarRange m doms'.length ++ Hrule.indexArgs.map (VExpr.instL ls)) ++
        [VExpr.mkApps (.const ctorName L')
          (patternParams ++ VExpr.bvarRange nfields nfields)])) :=
    ⟨_, hL⟩
  have ⟨_, hctorT', _⟩ := Hrec.spine_typing henv hΓ₀ hls hlsl
    (pre := VExpr.bvarRange m doms'.length ++ Hrule.indexArgs.map (VExpr.instL ls))
    (by simp [Hrule.indexArgs_length, hm]) hLwf
  -- (S6) The pattern constructor application under the telescope.
  have ⟨_, hcres'⟩ := Hctor.spine_typing henv hΓ₀ hL'w hL'len
    (P := patternParams) (fields := VExpr.bvarRange nfields nfields)
    hpatternLen (by simp) ⟨_, hctorT'⟩
  -- (S7) Closedness of the constructor's index expressions.
  have ⟨_, hresC⟩ := VEnv.constant_doms_closed henv (Hctor.type_eq ▸ Hctor.const) hL'w
  -- (T) The constructor application at the recursor's universe levels and parameters.
  have hcT : env.HasType U Γ (.const ctorName cls)
      (VExpr.wrapForalls (Hctor.doms.map (VExpr.instL cls))
        ((VExpr.mkApps (.const indName (VLevel.params ctorUvars))
          (VExpr.bvarRange cnparams (cnparams + nfields) ++ Hctor.indices)).instL cls)) := by
    have := HasType.const (Γ := Γ) Hctor.const hclsw (by simpa using hcls)
    rwa [Hctor.type_eq, VExpr.instL_wrapForalls] at this
  have hcDF : env.IsDefEq U Γ (.const ctorName cls) (.const ctorName L')
      (VExpr.wrapForalls (Hctor.doms.map (VExpr.instL cls))
        ((VExpr.mkApps (.const indName (VLevel.params ctorUvars))
          (VExpr.bvarRange cnparams (cnparams + nfields) ++ Hctor.indices)).instL cls)) := by
    have := IsDefEq.constDF (Γ := Γ) Hctor.const hclsw hL'w (by simpa using hcls)
      (List.forall₂_symm (fun _ _ h => (VLevel.equiv_def'.1 h).symm) hLcls)
    rwa [Hctor.type_eq, VExpr.instL_wrapForalls] at this
  have hcongr := IsDefEq.mkApps_congr (args := P' ++ fields)
    (args' := params ++ fields) hcDF (by simp [hP', hf, Hctor.doms_length])
    (by simp [hP']; omega) (by
      intro j hj hj' hj''
      rcases Nat.lt_or_ge j cnparams with hjp | hjp
      · have h1 := hcargs j hj hj'
        rw [List.getElem_append_left (by omega)] at h1 ⊢
        rw [List.getElem_append_left (by omega)]
        have h2 := List.forall₂_getElem hPE j (by simpa [params, Hrec.ctorParams_length] using hjp) (by omega)
        exact h2.symm.of_l henv hΓ h1
      · have h1 := hcargs j hj hj'
        rw [List.getElem_append_right (by omega)] at h1 ⊢
        rw [List.getElem_append_right (by omega)]
        simp only [hparamsLen, hP']
        simp only [hP'] at h1
        exact h1)
  have hctorLWF : VExpr.WF env U Γ
      (VExpr.mkApps (.const ctorName L') (params ++ fields)) := ⟨_, hcongr.hasType.2⟩
  have ⟨_, hcresL⟩ := Hctor.spine_typing henv hΓ hL'w hL'len (P := params)
    hparamsLen hf hctorLWF
  have hmajL : env.IsDefEqU U Γ major
      (VExpr.mkApps (.const ctorName L') (params ++ fields)) :=
    hmajor.trans henv hΓ ⟨_, hcongr⟩
  have hMTL : env.IsDefEqU U Γ
      (VExpr.mkApps (.const indName L') (params ++ pre.drop m))
      (VExpr.mkApps (.const indName L')
        (params ++ Hctor.indices.map fun e =>
          (e.instL L').instOuter (params ++ fields))) :=
    (hmajL.of_l henv hΓ hmajT).hasType.2.uniqU henv hΓ hcresL
  have ⟨_, hargsL⟩ := IsDefEqU.rigidApp_inv henv hΓ hrigid hMTL hsort
  have ⟨_, hidxA⟩ := List.forall₂_append_split hargsL rfl
  -- (E) Index agreement: the pattern's index arguments, instantiated at the actual arguments, are
  -- the indices of the actual constructor application.
  have hidx : ∀ k (hk : k < nindices),
      env.IsDefEqU U Γ (pre[m + k]'(by omega))
        ((Hrule.indexArgs.map (VExpr.instL ls))[k]'(by simp [Hrule.indexArgs_length]; omega)
          |>.instOuter A) := by
    intro k hk
    -- Under the telescope, the pattern indices are the constructor's indices at the pattern
    -- variables.
    have hctorT'' := hctorT'
    rw [List.take_append_of_le_length (by simp; omega), VExpr.bvarRange_take _ _ _ (by omega),
      List.drop_left' (by simp; omega), hL'] at hctorT''
    have hE0 := hctorT''.uniqU henv hΓ₀ hcres'
    have ⟨_, hsort'⟩ := hctorT''.isType henv.ordered hΓ₀
    have ⟨_, hE1⟩ := IsDefEqU.rigidApp_inv henv hΓ₀ hrigid hE0 hsort'
    have ⟨_, hidxE⟩ := List.forall₂_append_split hE1 (by simpa only [List.length_map, Hrec.ctorParams_length] using hpatternLen.symm)
    have hk' := List.forall₂_getElem hidxE k (by simp [Hrule.indexArgs_length]; omega)
      (by simp [Hctor.indices_length]; omega)
    have hI := IsDefEqU.instOuter_telescope henv hk' (hAlen.trans hn.symm) hA
    simp only [List.getElem_map] at hI
    have hV : (patternParams ++ VExpr.bvarRange nfields nfields).map
        (·.instOuter A) = params ++ fields := by
      rw [List.map_append, hpatternInst,
        VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by omega)]
      rw [show A.length - nfields = m by omega, ← hAe,
        List.drop_left' (by simp; omega), List.take_of_length_le (l := fields) (by omega)]
    have hcl : ((Hctor.indices[k]'(by rw [Hctor.indices_length]; exact hk)).instL L').ClosedN
        (patternParams ++ VExpr.bvarRange nfields nfields).length := by
      have := hresC
      simp only [VExpr.instL_mkApps, List.map_append] at this
      have hk2 : k < Hctor.indices.length := by rw [Hctor.indices_length]; exact hk
      have := VExpr.ClosedN.of_mkApps_arg this ((Hctor.indices[k]'hk2).instL L')
        (List.mem_append_right _ (List.mem_map.2 ⟨Hctor.indices[k]'hk2, List.getElem_mem hk2, rfl⟩))
      simpa [Hctor.doms_length, hpatternLen] using this
    rw [VExpr.instOuter_instOuter _ _ _ hcl, hV] at hI
    have hk'' := List.forall₂_getElem hidxA k (by simp; omega) (by simp [Hctor.indices_length]; omega)
    rw [List.getElem_drop, List.getElem_map] at hk''
    simp only [List.getElem_map]
    exact hk''.trans henv hΓ hI.symm
  -- (F) The recursor application is the instantiated left-hand side.
  have hX2 : (Hrule.lhsBody.instL ls).instOuter A =
      VExpr.mkApps (.const recName ls)
        ((pre.take m ++ (Hrule.indexArgs.map (VExpr.instL ls)).map (·.instOuter A)) ++
          [VExpr.mkApps (.const ctorName L') (params ++ fields)]) := by
    rw [Hrule.lhs_pattern]
    simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_cons, List.map_nil,
      VExpr.instL_bvarRange, VLevel.params_map_inst ls hlsl, hL', hm, VExpr.instOuter_mkApps,
      VExpr.instOuter_const]
    rw [show Hrule.doms.length = doms'.length by simp [← hdoms]]
    rw [hrawPatternInst,
      VExpr.instOuter_bvarRange _ _ _ (by omega) (by omega),
      VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by omega)]
    rw [show A.length - doms'.length = 0 by omega, List.drop_zero,
      show A.length - nfields = m by omega, ← hAe,
      List.take_append_of_le_length (l₁ := pre.take m) (i := m) (by simp; omega),
      List.take_take, Nat.min_self,
      List.drop_left' (by simp; omega), List.take_of_length_le (l := fields) (by omega)]
  have hrecT : env.HasType U Γ (.const recName ls)
      (VExpr.wrapForalls (Hrec.doms.map (VExpr.instL ls)) (Hrec.result.instL ls)) := by
    have := HasType.const (Γ := Γ) Hrec.const hls (by simpa using hlsl)
    rwa [Hrec.type_eq, VExpr.instL_wrapForalls] at this
  have hX1X2 := IsDefEq.mkApps_congr (args := pre ++ [major])
    (args' := (pre.take m ++ (Hrule.indexArgs.map (VExpr.instL ls)).map (·.instOuter A)) ++
      [VExpr.mkApps (.const ctorName L') (params ++ fields)]) hrecT
    (by simp [hpre, Hrec.doms_length]; omega) (by simp [Hrule.indexArgs_length]; omega) (by
      intro j hj hj' hj''
      rcases Nat.lt_or_ge j pre.length with hjp | hjp
      · rw [List.getElem_append_left hjp, List.take_append_of_le_length (by omega),
          List.getElem_append_left (by simp [Hrule.indexArgs_length]; omega)]
        rcases Nat.lt_or_ge j m with hjm | hjm
        · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
          exact hpreT j hjp hj'
        · rw [List.getElem_append_right (by simp; omega), List.getElem_map]
          simp only [List.length_take, Nat.min_eq_left (show m ≤ pre.length by omega)]
          obtain ⟨k, rfl⟩ : ∃ k, j = m + k := ⟨j - m, by omega⟩
          simp only [Nat.add_sub_cancel_left]
          exact (hidx k (by omega)).of_l henv hΓ (hpreT _ hjp hj')
      · have hjp' : j = pre.length := by simp at hj; omega
        subst hjp'
        rw [List.getElem_append_right (Nat.le_refl _), List.take_left,
          List.getElem_append_right (by simp [Hrule.indexArgs_length]; omega)]
        simp only [Nat.sub_self, List.getElem_singleton, List.length_append, List.length_take,
          List.length_map, Hrule.indexArgs_length,
          hpre, List.getElem_singleton]
        simp only [hpre] at hmajT'
        exact hmajL.of_l henv hΓ hmajT')
  have hty : ∀ j (hj : j < A.length) (hj' : j < Hrule.doms.length),
      env.HasType U Γ A[j] (((Hrule.doms[j]).instL ls).instOuter (A.take j)) := by
    intro j hj hj'
    subst hdoms
    have := hA j hj (by simp; omega)
    rwa [List.getElem_map] at this
  have hbeta := IsDefEq.extra_instOuter henv hΓ Hrule.defeq hls hdf Hrule.lhs_eq Hrule.rhs_eq
    Hrule.type_eq (hAlen.trans (by simp [Hrule.doms_length, hm])) hty
  have hrhs : env.HasType U Γ (VExpr.wrapLams doms' (Hrule.rhsBody.instL ls))
      (VExpr.wrapForalls doms' (Hrule.typeBody.instL ls)) := by
    have ⟨_, hr⟩ := henv.ordered.defEqWF Hrule.defeq
    rw [Hrule.rhs_eq, Hrule.type_eq] at hr
    have := (hr.instL hls).weak0 henv.ordered (Γ := Γ)
    simpa [VExpr.instL_wrapLams, VExpr.instL_wrapForalls, hdoms] using this
  have hlam := IsDefEq.mkApps_wrapLams henv hΓ hrhs (hAlen.trans hn.symm) hA
  have hrhs_eq : df.rhs.instL ls = VExpr.wrapLams doms' (Hrule.rhsBody.instL ls) := by
    rw [Hrule.rhs_eq, VExpr.instL_wrapLams, hdoms]
  rw [hrhs_eq]
  refine IsDefEqU.trans henv hΓ ⟨_, hX1X2⟩ (IsDefEqU.trans henv hΓ ?_ ⟨_, hlam.symm⟩)
  rw [← hX2]
  exact ⟨_, hbeta⟩


/-- Iota reduction: a recursor application whose major premise is definitionally a constructor
application is definitionally equal to the stored rule's right-hand side applied to the
parameters, motives, minors, and constructor fields, followed by the remaining arguments. -/
theorem _root_.Lean4Lean.VIotaRuleShape.iota (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (Hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams)
    (Hctor : VConstructorShape env ctorName ctorUvars cnparams nfields nindices indName)
    (Hrule : VIotaRuleShape env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      indLevels nfields df ctorParams)
    (hrigid : env.Rigid indName) (hIL : indLevels.length = ctorUvars)
    (hls : ∀ l ∈ ls, l.WF U) (hlsl : ls.length = recUvars)
    {pre : List VExpr} (hpre : pre.length = nparams + nmotives + nminors + nindices)
    {major : VExpr} {extra : List VExpr}
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ major :: extra)))
    {cls : List VLevel} {P' fields : List VExpr}
    (hcls : cls.length = ctorUvars) (hclsw : ∀ l ∈ cls, l.WF U)
    (hP' : P'.length = cnparams) (hf : fields.length = nfields)
    (hmajor : env.IsDefEqU U Γ major (VExpr.mkApps (.const ctorName cls) (P' ++ fields))) :
    env.IsDefEqU U Γ (VExpr.mkApps (.const recName ls) (pre ++ major :: extra))
      (VExpr.mkApps (df.rhs.instL ls)
        (pre.take (nparams + nmotives + nminors) ++ fields ++ extra)) := by
  have hwf1 : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ [major])) := by
    have : pre ++ major :: extra = (pre ++ [major]) ++ extra := by simp
    rw [this, VExpr.mkApps_append] at hwf
    exact VExpr.WF.of_mkApps henv.ordered hΓ hwf
  exact Hrule.iota_of_args henv hΓ Hrec Hctor hrigid hIL hls hlsl hpre hwf hcls hclsw hP' hf hmajor
    (Hrule.args_typing henv hΓ Hrec Hctor hrigid hIL hls hlsl hpre hwf1 hcls hclsw hP' hf hmajor)

/-- `iota` with the right-hand side beta-reduced: the instantiated rule body applied to the
remaining arguments. -/
theorem _root_.Lean4Lean.VIotaRuleShape.iota_body (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (Hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams)
    (Hctor : VConstructorShape env ctorName ctorUvars cnparams nfields nindices indName)
    (Hrule : VIotaRuleShape env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      indLevels nfields df ctorParams)
    (hrigid : env.Rigid indName) (hIL : indLevels.length = ctorUvars)
    (hls : ∀ l ∈ ls, l.WF U) (hlsl : ls.length = recUvars)
    {pre : List VExpr} (hpre : pre.length = nparams + nmotives + nminors + nindices)
    {major : VExpr} {extra : List VExpr}
    (hwf : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ major :: extra)))
    {cls : List VLevel} {P' fields : List VExpr}
    (hcls : cls.length = ctorUvars) (hclsw : ∀ l ∈ cls, l.WF U)
    (hP' : P'.length = cnparams) (hf : fields.length = nfields)
    (hmajor : env.IsDefEqU U Γ major (VExpr.mkApps (.const ctorName cls) (P' ++ fields))) :
    env.IsDefEqU U Γ (VExpr.mkApps (.const recName ls) (pre ++ major :: extra))
      (VExpr.mkApps ((Hrule.rhsBody.instL ls).instOuter
        (pre.take (nparams + nmotives + nminors) ++ fields)) extra) := by
  have h1 := Hrule.iota henv hΓ Hrec Hctor hrigid hIL hls hlsl hpre hwf hcls hclsw hP' hf hmajor
  have hwf1 : VExpr.WF env U Γ (VExpr.mkApps (.const recName ls) (pre ++ [major])) := by
    have : pre ++ major :: extra = (pre ++ [major]) ++ extra := by simp
    rw [this, VExpr.mkApps_append] at hwf
    exact VExpr.WF.of_mkApps henv.ordered hΓ hwf
  have hA := Hrule.args_typing henv hΓ Hrec Hctor hrigid hIL hls hlsl hpre hwf1 hcls hclsw hP'
    hf hmajor
  have hrhs : env.HasType U Γ (VExpr.wrapLams (Hrule.doms.map (VExpr.instL ls))
      (Hrule.rhsBody.instL ls))
      (VExpr.wrapForalls (Hrule.doms.map (VExpr.instL ls)) (Hrule.typeBody.instL ls)) := by
    have ⟨_, hr⟩ := henv.ordered.defEqWF Hrule.defeq
    rw [Hrule.rhs_eq, Hrule.type_eq] at hr
    have := (hr.instL hls).weak0 henv.ordered (Γ := Γ)
    simpa [VExpr.instL_wrapLams, VExpr.instL_wrapForalls] using this
  have hlam := IsDefEq.mkApps_wrapLams henv hΓ hrhs
    (by simp [hf, Hrule.doms_length]; omega) hA
  rw [VExpr.mkApps_append (l₁ := pre.take (nparams + nmotives + nminors) ++ fields)] at h1
  refine h1.trans henv hΓ (IsDefEqU.mkApps_congr_left henv hΓ ?_ ?_)
  · rw [Hrule.rhs_eq, VExpr.instL_wrapLams]
    exact ⟨_, hlam⟩
  · have ⟨_, h⟩ := h1
    exact ⟨_, h.hasType.2⟩

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_sort (u : VLevel) (args : List VExpr) :
    (VExpr.sort u).instOuter args = .sort u := by
  rw [VExpr.instOuter_eq_subst, VExpr.subst_sort]

/-- Forward telescope typing: a function typed at a syntactic telescope, applied to arguments typed
along that telescope, has the instantiated residual type. -/
theorem HasType.mkApps_of_telescope :
    ∀ {args : List VExpr} {f : VExpr} {doms : List VExpr} {body : VExpr},
      env.HasType U Γ f (VExpr.wrapForalls doms body) → args.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length),
        env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) →
      env.HasType U Γ (VExpr.mkApps f args) (body.instOuter args) := by
  intro args
  induction args with
  | nil =>
    intro f doms body hf hlen _
    cases doms with
    | nil => exact hf
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro f doms body hf hlen hty
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons] at hlen
      have ha : env.HasType U Γ a d := by
        have := hty 0 (by simp) (by simp)
        simpa only [List.getElem_cons_zero, List.take_zero, VExpr.instOuter_nil] using this
      have hfa : env.HasType U Γ (.app f a) ((VExpr.wrapForalls ds body).inst a) := hf.app ha
      rw [VExpr.wrapForalls_inst] at hfa
      simp only [VExpr.mkApps, List.foldl_cons, VExpr.instOuter_cons]
      rw [show as.length = 0 + ds.length by omega]
      refine ih (doms := VExpr.instDomains ds a 0) hfa (by simpa using hlen) ?_
      intro j hj hj'
      have := hty (j + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
        List.length_take] at this
      rw [VExpr.instDomains_getElem ds a 0 j (by simpa using hj')]
      rwa [show min j as.length = 0 + j by omega] at this

/-- The entries of a reversed telescope context are types in their prefix contexts. -/
theorem _root_.Lean4Lean.OnCtx.reverse_getElem {doms Γ : List VExpr} {P : List VExpr → VExpr → Prop}
    (hΓ : OnCtx (doms.reverse ++ Γ) P) (j : Nat) (hj : j < doms.length) :
    P ((doms.take j).reverse ++ Γ) doms[j] := by
  induction doms generalizing Γ j with
  | nil => simp at hj
  | cons d ds ih =>
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hΓ
    cases j with
    | zero => exact (hΓ.of_append (Γ' := ds.reverse)).2
    | succ j =>
      have := ih (Γ := d :: Γ) hΓ j (by simpa using hj)
      simpa [List.reverse_cons, List.append_assoc] using this

/-- A typed defeq under a telescope, instantiated at arguments typed along the telescope. -/
theorem IsDefEq.instOuter_telescope (henv : VEnv.WF env) :
    ∀ {doms args : List VExpr} {Γ : List VExpr} {X Y T : VExpr},
      env.IsDefEq U (doms.reverse ++ Γ) X Y T → args.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length),
        env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) →
      env.IsDefEq U Γ (X.instOuter args) (Y.instOuter args) (T.instOuter args) := by
  intro doms args
  induction args generalizing doms with
  | nil =>
    intro Γ X Y T H hlen _
    cases doms with
    | nil => simpa using H
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro Γ X Y T H hlen hty
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons] at hlen
      have ha : env.HasType U Γ a d := by
        have := hty 0 (by simp) (by simp)
        simpa only [List.getElem_cons_zero, List.take_zero, VExpr.instOuter_nil] using this
      have W : Ctx.InstN Γ a d (ds.length + 0) (ds.reverse ++ d :: Γ)
          ((VExpr.instDomains ds a 0).reverse ++ Γ) := Ctx.InstN.reverse ds .zero
      have H' : env.IsDefEq U (ds.reverse ++ d :: Γ) X Y T := by
        simpa [List.reverse_cons, List.append_assoc] using H
      have H'' := H'.instN henv.ordered ha W
      simp only [VExpr.instOuter_cons]
      rw [show as.length = ds.length + 0 by omega]
      refine ih (doms := VExpr.instDomains ds a 0) H'' (by simpa using hlen) ?_
      intro j hj hj'
      have := hty (j + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
        List.length_take] at this
      rw [VExpr.instDomains_getElem ds a 0 j (by simpa using hj')]
      rwa [show min j as.length = 0 + j by omega] at this

/-- A telescope domain is a type after instantiation at arguments typed along the telescope. -/
theorem IsType.instOuter_telescope (henv : VEnv.WF env) {doms args : List VExpr} {Γ : List VExpr}
    {A : VExpr} (H : env.IsType U (doms.reverse ++ Γ) A) (hlen : args.length = doms.length)
    (hty : ∀ j (hj : j < args.length) (hj' : j < doms.length),
      env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) :
    env.IsType U Γ (A.instOuter args) :=
  let ⟨u, h⟩ := H
  ⟨u, by have := IsDefEq.instOuter_telescope henv h hlen hty; rwa [VExpr.instOuter_sort] at this⟩

/-- A defeq between closed telescope domains, instantiated at universe levels and at arguments typed
along the telescope. The domains live in the closed context of the binders before them. -/
theorem IsDefEqU.closed_telescope_instOuter (henv : VEnv.WF env)
    {Δ₀ : List VExpr} {X Y : VExpr} (hΓ₀ : OnCtx Δ₀ (env.IsType U₀))
    (H : env.IsDefEqU U₀ Δ₀ X Y) (hls : ∀ l ∈ ls, l.WF U)
    {args : List VExpr} (hargs : args.length = Δ₀.length)
    (hty : ∀ k (hk : k < args.length) (hk' : k < (Δ₀.reverse.map (VExpr.instL ls)).length),
      env.HasType U Γ args[k] ((Δ₀.reverse.map (VExpr.instL ls))[k].instOuter (args.take k))) :
    env.IsDefEqU U Γ ((X.instL ls).instOuter args) ((Y.instL ls).instOuter args) := by
  have H' := H.instL hls
  have hΓ₀' : OnCtx (Δ₀.map (VExpr.instL ls)) (env.IsType U) := hΓ₀.instL hls
  have hclosed := CtxWF.closed henv.ordered hΓ₀'
  have ⟨_, h⟩ := H
  have hX : (X.instL ls).ClosedN Δ₀.length :=
    (VExpr.WF.closedN henv.ordered ⟨_, h.hasType.1⟩ (CtxWF.closed henv.ordered hΓ₀)).instL
  have hY : (Y.instL ls).ClosedN Δ₀.length :=
    (VExpr.WF.closedN henv.ordered ⟨_, h.hasType.2⟩ (CtxWF.closed henv.ordered hΓ₀)).instL
  have W := Ctx.LiftN.right hclosed Γ
  have H'' := H'.weakN henv W
  simp only [List.length_map] at H''
  rw [hX.liftN_eq (Nat.le_refl _), hY.liftN_eq (Nat.le_refl _)] at H''
  have := IsDefEqU.instOuter_telescope henv (doms := Δ₀.reverse.map (VExpr.instL ls)) (args := args)
    (by rwa [List.map_reverse, List.reverse_reverse]) (by simpa using hargs) hty
  exact this

theorem _root_.Lean4Lean.VExpr.eq_wrapForalls_of_takeForalls :
    ∀ {n : Nat} {e : VExpr} {ds : List VExpr} {r : VExpr},
      e.takeForalls n = some (ds, r) → e = VExpr.wrapForalls ds r
  | 0, e, ds, r, H => by
    change some ([], e) = some (ds, r) at H
    cases Option.some.inj H
    rfl
  | n + 1, e, ds, r, H => by
    cases e <;> simp [VExpr.takeForalls] at H
    case forallE dom body =>
      rcases H with ⟨tail, htail, hd⟩
      rw [← hd]
      exact congrArg (VExpr.forallE dom) (VExpr.eq_wrapForalls_of_takeForalls htail)

/-- The entries of two definitionally equal closed contexts are definitionally equal in their
common prefix. -/
theorem IsDefEqCtx.getElem_empty {Γ₁ Γ₂ : List VExpr} (H : IsDefEqCtx env U [] Γ₁ Γ₂) :
    ∀ (i : Nat) (h : i < Γ₁.length) (h' : i < Γ₂.length),
      ∃ u, env.IsDefEq U (Γ₁.drop (i + 1)) Γ₁[i] Γ₂[i] (.sort u) := by
  induction H with
  | zero => intro i h; simp at h
  | @succ Γ₁ Γ₂ A₁ A₂ u _ hd ih =>
    intro i h h'
    cases i with
    | zero => exact ⟨u, hd⟩
    | succ i => exact ih i (by simpa using h) (by simpa using h')

/-- `getElem_empty` for reversed telescopes: the `k`-th binders agree under the binders before
them. -/
theorem IsDefEqCtx.reverse_getElem {l₁ l₂ : List VExpr}
    (H : IsDefEqCtx env U [] l₁.reverse l₂.reverse) (k : Nat) (hk : k < l₁.length)
    (hk' : k < l₂.length) :
    ∃ u, env.IsDefEq U ((l₁.take k).reverse) l₁[k] l₂[k] (.sort u) := by
  have hlen := H.length_eq
  simp only [List.length_reverse] at hlen
  have ⟨u, h⟩ := H.getElem_empty (l₁.length - 1 - k) (by simp; omega) (by simp; omega)
  refine ⟨u, ?_⟩
  rw [List.getElem_reverse, List.getElem_reverse, List.drop_reverse] at h
  have e1 : l₁.length - 1 - (l₁.length - 1 - k) = k := by omega
  have e2 : l₂.length - 1 - (l₁.length - 1 - k) = k := by omega
  have e3 : l₁.length - (l₁.length - 1 - k + 1) = k := by omega
  simp only [e1, e2, e3] at h
  exact h

/-- A closed term typed at a telescope, applied to the telescope's own
variables in the telescope's context, has the telescope's body type. -/
theorem HasType.mkApps_bvarRange {env : VEnv} {U : Nat} (henv : env.WF)
    {f B : VExpr} {doms : List VExpr}
    (hf : env.HasType U [] f (VExpr.wrapForalls doms B))
    (hctx : OnCtx doms.reverse (env.IsType U))
    (hB : B.ClosedN doms.length) :
    env.HasType U doms.reverse
      (VExpr.mkApps f (VExpr.bvarRange doms.length doms.length)) B := by
  have hf' : env.HasType U doms.reverse f (VExpr.wrapForalls doms B) :=
    hf.weak0 henv.ordered
  have h := HasType.mkApps_of_telescope
    (args := VExpr.bvarRange doms.length doms.length) hf' (by simp) ?_
  · rwa [VExpr.instOuter_range_bvar' B _ _ hB (Nat.le_refl _), Nat.sub_self,
      VExpr.liftN_zero] at h
  · intro j hj hj'
    simp only [VExpr.bvarRange_length] at hj
    rw [VExpr.bvarRange_getElem _ _ _ hj, VExpr.bvarRange_take _ _ _ (Nat.le_of_lt hj)]
    have hclosed : doms[j].ClosedN j := by
      have := OnCtx.reverse_getElem_closedN henv (Γ := []) (by simpa using hctx) j hj'
      simpa using this
    rw [VExpr.instOuter_range_bvar' _ _ _ hclosed (by omega)]
    have hl := Lookup.reverse_append doms [] j hj'
    simp only [List.append_nil] at hl
    exact .bvar hl

end VEnv

end Lean4Lean
