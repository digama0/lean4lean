import Lean4Lean.Theory.VExpr

/-! Pure telescope and application-spine syntax, below environments and typing. -/

namespace Lean4Lean

/-- Split exactly `n` leading forall binders, retaining domains in outermost to
innermost order. -/
def VExpr.takeForalls : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE dom body => do
    let (doms, result) ← body.takeForalls n
    return (dom :: doms, result)
  | _ + 1, _ => none

theorem VExpr.takeForalls_domains_length
    {e : VExpr} {n : Nat} {domains : List VExpr} {result : VExpr}
    (H : e.takeForalls n = some (domains, result)) :
    domains.length = n := by
  induction n generalizing e domains result with
  | zero =>
    change some ([], e) = some (domains, result) at H
    cases Option.some.inj H
    rfl
  | succ n ih =>
    cases e <;> simp [VExpr.takeForalls] at H
    case forallE dom body =>
      rcases H with ⟨tailDomains, htail, hd⟩
      rw [← hd]
      simp [ih htail]

/-- Head and left-to-right arguments of an application spine. -/
def VExpr.getAppFnArgs (e : VExpr) : VExpr × List VExpr :=
  go e []
where
  go : VExpr → List VExpr → VExpr × List VExpr
    | .app fn arg, args => go fn (arg :: args)
    | fn, args => (fn, args)

def VExpr.wrapLams (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .lam body

def VExpr.wrapForalls (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .forallE body

@[simp] theorem VExpr.instL_wrapForalls (ds : List VExpr) (body : VExpr) (ls : List VLevel) :
    (VExpr.wrapForalls ds body).instL ls =
      VExpr.wrapForalls (ds.map (·.instL ls)) (body.instL ls) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.instL, List.map_cons] at ih ⊢
    rw [ih]

theorem VExpr.takeForalls_eq_wrapForalls :
    ∀ {n : Nat} {type result : VExpr} {domains : List VExpr},
      type.takeForalls n = some (domains, result) →
      type = VExpr.wrapForalls domains result ∧ domains.length = n
  | 0, type, result, domains, H => by
    cases Option.some.inj H
    exact ⟨rfl, rfl⟩
  | n + 1, type, result, domains, H => by
    cases type with
    | forallE domain body =>
      cases htail : body.takeForalls n with
      | none => simp [VExpr.takeForalls, htail] at H
      | some out =>
        rw [VExpr.takeForalls, htail] at H
        cases Option.some.inj H
        have ih := VExpr.takeForalls_eq_wrapForalls htail
        exact ⟨congrArg (VExpr.forallE domain) ih.1, by simp [ih.2]⟩
    | bvar | sort | const | elim | app | lam | proj => simp [VExpr.takeForalls] at H

/-- Telescopes of the same length are equal only if their domains and bodies are. -/
theorem VExpr.wrapForalls_inj_of_length :
    ∀ {ds ds' : List VExpr} {b b' : VExpr}, ds.length = ds'.length →
      VExpr.wrapForalls ds b = VExpr.wrapForalls ds' b' → ds = ds' ∧ b = b'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | _ :: _, _ :: _, _, _, hl, h => by
    injection h with h1 h2
    have := VExpr.wrapForalls_inj_of_length (by simpa using hl) h2
    exact ⟨by rw [h1, this.1], this.2⟩

theorem VExpr.mkApps_append (f : VExpr) (l₁ l₂ : List VExpr) :
    VExpr.mkApps f (l₁ ++ l₂) = VExpr.mkApps (VExpr.mkApps f l₁) l₂ := by
  simp [VExpr.mkApps, List.foldl_append]

theorem VExpr.mkApps_snoc (f : VExpr) (l : List VExpr) (b : VExpr) :
    VExpr.mkApps f (l ++ [b]) = .app (VExpr.mkApps f l) b := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => exact ih (.app f a)

theorem VExpr.lift'_mkApps (fn : VExpr) (args : List VExpr) (ρ : Lift) :
    (VExpr.mkApps fn args).lift' ρ = VExpr.mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => exact ih (.app fn a)

theorem VExpr.getAppFnArgs_go_mkApps (f : VExpr) :
    ∀ (args acc : List VExpr), VExpr.getAppFnArgs.go (VExpr.mkApps f args) acc =
      VExpr.getAppFnArgs.go f (args ++ acc)
  | [], _ => rfl
  | a :: as, acc => by
    rw [show VExpr.mkApps f (a :: as) = VExpr.mkApps (.app f a) as from rfl,
      VExpr.getAppFnArgs_go_mkApps _ as acc]
    rfl

theorem VExpr.mkApps_const_inj
    (H : VExpr.mkApps (.const n ls) as = VExpr.mkApps (.const n' ls') as') :
    n = n' ∧ ls = ls' ∧ as = as' := by
  have h := congrArg (VExpr.getAppFnArgs.go · []) H
  simp only [VExpr.getAppFnArgs_go_mkApps, List.append_nil, VExpr.getAppFnArgs.go] at h
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem VExpr.mkApps_const_ne_forallE : VExpr.mkApps (.const n ls) args ≠ .forallE A t :=
  VExpr.mkApps_ne_forallE (fun _ _ h => by cases h) args

theorem VExpr.liftN_wrapForalls_sort (domains : List VExpr) (level : VLevel) (n k : Nat) :
    ∃ domains', (VExpr.wrapForalls domains (.sort level)).liftN n k =
      VExpr.wrapForalls domains' (.sort level) := by
  induction domains generalizing k with
  | nil => exact ⟨[], rfl⟩
  | cons domain domains ih =>
    obtain ⟨domains', hd⟩ := ih (k + 1)
    exact ⟨domain.liftN n k :: domains', congrArg (VExpr.forallE (domain.liftN n k)) hd⟩


private theorem VExpr.getAppFnArgs.go_append
    (e : VExpr) (pre suffix : List VExpr) :
    getAppFnArgs.go e (pre ++ suffix) =
      let (fn, args) := getAppFnArgs.go e pre
      (fn, args ++ suffix) := by
  induction e generalizing pre with
  | app fn arg ihFn _ =>
    simpa only [getAppFnArgs.go, List.cons_append] using
      ihFn (arg :: pre)
  | _ => simp [getAppFnArgs.go]

@[simp] theorem VExpr.getAppFnArgs_app :
    getAppFnArgs (.app fn arg) =
      let (head, args) := fn.getAppFnArgs
      (head, args ++ [arg]) := by
  change getAppFnArgs.go fn [arg] =
    let (head, args) := getAppFnArgs.go fn []
    (head, args ++ [arg])
  simpa using getAppFnArgs.go_append fn [] [arg]

theorem VExpr.mkApps_getAppFnArgs (e : VExpr) :
    VExpr.mkApps e.getAppFnArgs.1 e.getAppFnArgs.2 = e := by
  suffices ∀ args, VExpr.mkApps (VExpr.getAppFnArgs.go e args).1
      (VExpr.getAppFnArgs.go e args).2 = VExpr.mkApps e args from this []
  induction e with
  | app fn arg ih _ => intro args; exact ih (arg :: args)
  | _ => intro args; rfl

theorem VExpr.stripLams_wrapLams (ds : List VExpr) (e : VExpr) :
    (VExpr.wrapLams ds e).stripLams = e.stripLams := by
  induction ds with
  | nil => rfl
  | cons d ds ih => exact ih
@[simp] theorem VExpr.wrapForalls_append
    (left right : List VExpr) (body : VExpr) :
    VExpr.wrapForalls (left ++ right) body =
      VExpr.wrapForalls left (VExpr.wrapForalls right body) := by
  simp [wrapForalls, List.foldr_append]

@[simp] theorem VExpr.takeForalls_wrapForalls_append
    (pre suff : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls (pre ++ suff) body).takeForalls pre.length =
      some (pre, VExpr.wrapForalls suff body) := by
  induction pre with
  | nil => rfl
  | cons dom pre ih =>
    change (do
      let (domains, result) ←
        (VExpr.wrapForalls (pre ++ suff) body).takeForalls pre.length
      return (dom :: domains, result)) = _
    rw [ih]
    rfl

@[simp] theorem VExpr.takeForalls_wrapForalls
    (domains : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls domains body).takeForalls domains.length =
      some (domains, body) := by
  simpa [wrapForalls] using
    VExpr.takeForalls_wrapForalls_append domains [] body

end Lean4Lean
