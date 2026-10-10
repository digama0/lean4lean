import Lean4Lean.Theory.Typing.Injectivity

/-!
# Instantiating constructor telescopes

`VProjectionInfo.fieldType` walks a constructor type one binder at a time, instantiating
each binder with a parameter or with the primitive projection of the preceding field.
`InstForalls` is the typed counterpart of that walk; it is what the checker's projection
inference and projection reduction refine, and it is congruent under definitional equality of
its inputs.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- `InstForalls env U Γ T args res`: instantiating the leading binders of `T` by `args`, one
at a time, yields `res`. Each argument is either typed at its binder, or the remaining body does
not depend on the binder (in which case nothing is required of the argument). -/
inductive InstForalls (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → VExpr → Prop
  | nil : InstForalls env U Γ T [] T
  | cons : env.HasType U Γ a A → InstForalls env U Γ (B.inst a) args res →
      InstForalls env U Γ (.forallE A B) (a :: args) res
  | vacuous : InstForalls env U Γ B args res →
      InstForalls env U Γ (.forallE A B.lift) (a :: args) res

/-- The typed-only walk: every argument is typed at its binder. -/
inductive InstForallsC (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → VExpr → Prop
  | nil : InstForallsC env U Γ T [] T
  | cons : env.HasType U Γ a A → InstForallsC env U Γ (B.inst a) args res →
      InstForallsC env U Γ (.forallE A B) (a :: args) res

theorem InstForallsC.toInstForalls (H : InstForallsC env U Γ T args res) :
    InstForalls env U Γ T args res := by
  induction H with
  | nil => exact .nil
  | cons ha _ ih => exact .cons ha ih

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

theorem _root_.Lean4Lean.VExpr.takeForalls_inst {T : VExpr}
    (H : T.takeForalls n = some (doms, rest)) :
    ∃ doms', (T.inst a k).takeForalls n = some (doms', rest.inst a (k + n)) := by
  induction n generalizing T doms rest k with
  | zero =>
    simp [VExpr.takeForalls] at H
    obtain ⟨rfl, rfl⟩ := H
    exact ⟨[], by simp [VExpr.takeForalls]⟩
  | succ n ih =>
    cases T <;> simp [VExpr.takeForalls] at H
    case forallE A B =>
      obtain ⟨doms', h, rfl, rfl⟩ := H
      obtain ⟨doms'', h'⟩ := ih (k := k + 1) h
      exact ⟨A.inst a k :: doms'', by
        simp [VExpr.inst, VExpr.takeForalls, h', Nat.add_assoc, Nat.add_comm 1]⟩

theorem _root_.Lean4Lean.VExpr.WF.of_mkApps (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (VExpr.mkApps f args)) : VExpr.WF env U Γ f := by
  induction args generalizing f with
  | nil => simpa [VExpr.mkApps] using H
  | cons a args ih =>
    have ⟨_, _, hf, _⟩ := (ih (f := .app f a) H).app_inv henv hΓ
    exact ⟨_, hf⟩

theorem _root_.Lean4Lean.VExpr.WF.args_of_mkApps (henv : env.OrderedStrong)
    (hΓ : OnCtx Γ (env.IsType U)) (H : VExpr.WF env U Γ (VExpr.mkApps f args)) :
    ∀ arg ∈ args, VExpr.WF env U Γ arg := by
  induction args generalizing f with
  | nil => simp
  | cons a args ih =>
    have hf := VExpr.WF.of_mkApps (f := f.app a) (args := args) henv hΓ H
    obtain ⟨_, _, _, ha⟩ := hf.app_inv henv hΓ
    intro arg hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ha⟩
    · exact ih H arg hm

/-- An application spine typed against a syntactic forall telescope instantiates that telescope:
every argument is typed at its binder, and the whole application has the residual type. -/
theorem HasType.mkApps_telescope (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ f T) (H : VExpr.WF env U Γ (VExpr.mkApps f args))
    (hT : T.takeForalls args.length = some (doms, rest)) :
    ∃ res, InstForallsC env U Γ T args res ∧ env.HasType U Γ (VExpr.mkApps f args) res := by
  induction args generalizing f T doms rest with
  | nil => exact ⟨_, .nil, by simpa [VExpr.mkApps] using hf⟩
  | cons a args ih =>
    cases T <;> simp [VExpr.takeForalls] at hT
    case forallE A B =>
      obtain ⟨doms', hB, rfl, rfl⟩ := hT
      have hfa : VExpr.WF env U Γ (.app f a) :=
        VExpr.WF.of_mkApps henv hΓ (f := .app f a) (by simpa [VExpr.mkApps] using H)
      have ⟨A', B', hf', ha'⟩ := hfa.app_inv henv hΓ
      have ⟨⟨_, hA⟩, _, hB'⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
      have ha : env.HasType U Γ a A := ha'.defeqU_r henv hΓ ⟨_, hA.symm⟩
      have hfa' : env.HasType U Γ (.app f a) (B.inst a) := hf.app ha
      obtain ⟨_, hB''⟩ := VExpr.takeForalls_inst (a := a) (k := 0) hB
      have ⟨res, H1, H2⟩ := ih hfa' (by simpa [VExpr.mkApps] using H) hB''
      exact ⟨res, .cons ha H1, by simpa [VExpr.mkApps] using H2⟩

/-- Instantiate the outermost binders of a telescope body one at a time: the first argument replaces
the outermost variable (de Bruijn index `args.length - 1`), and so on. -/
def _root_.Lean4Lean.VExpr.instOuter : VExpr → List VExpr → VExpr
  | body, [] => body
  | body, a :: as => VExpr.instOuter (body.inst a as.length) as

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_nil (body : VExpr) : body.instOuter [] = body := rfl

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_cons (body a : VExpr) (as : List VExpr) :
    body.instOuter (a :: as) = (body.inst a as.length).instOuter as := rfl

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_mkApps (fn : VExpr) (xs args : List VExpr) :
    (VExpr.mkApps fn xs).instOuter args =
      VExpr.mkApps (fn.instOuter args) (xs.map fun x => x.instOuter args) := by
  induction args generalizing fn xs with
  | nil => simp
  | cons a as ih => simp [ih, List.map_map, Function.comp_def]

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_const (args : List VExpr) :
    (VExpr.const c ls).instOuter args = .const c ls := by
  induction args <;> simp [VExpr.inst, *]

theorem _root_.Lean4Lean.VExpr.instOuter_liftN (a : VExpr) (args : List VExpr) :
    (a.liftN args.length).instOuter args = a := by
  induction args with
  | nil => simp
  | cons b as ih =>
    simp only [List.length_cons, VExpr.instOuter_cons]
    rw [← VExpr.liftN'_liftN' (n1 := as.length) (n2 := 1) (Nat.zero_le _) (Nat.le_refl _)]
    simp only [Nat.add_zero]
    rw [VExpr.inst_liftN]
    exact ih

theorem _root_.Lean4Lean.VExpr.instOuter_bvar (args : List VExpr) (h : k < args.length) :
    (VExpr.bvar k).instOuter args = args[args.length - 1 - k] := by
  induction args generalizing k with
  | nil => simp at h
  | cons a as ih =>
    simp only [VExpr.instOuter_cons, VExpr.inst, VExpr.instVar]
    by_cases hk : k < as.length
    · rw [if_pos hk, ih hk, List.getElem_cons, dif_neg (by simp; omega)]
      congr 1
      simp
      omega
    · have hk' : k = as.length := by simp at h; omega
      subst hk'
      rw [if_neg hk, if_pos rfl, VExpr.instOuter_liftN]
      simp

/-- Instantiate the domains of a telescope, the `k`-th domain sitting under `k` binders. -/
def _root_.Lean4Lean.VExpr.instDomains : List VExpr → VExpr → Nat → List VExpr
  | [], _, _ => []
  | d :: ds, a, k => d.inst a k :: VExpr.instDomains ds a (k + 1)

@[simp] theorem _root_.Lean4Lean.VExpr.instDomains_length (doms : List VExpr) :
    (VExpr.instDomains doms a k).length = doms.length := by
  induction doms generalizing k <;> simp [VExpr.instDomains, *]

theorem _root_.Lean4Lean.VExpr.wrapForalls_inst (doms : List VExpr) (body a : VExpr) (k : Nat) :
    (VExpr.wrapForalls doms body).inst a k =
      VExpr.wrapForalls (VExpr.instDomains doms a k) (body.inst a (k + doms.length)) := by
  induction doms generalizing k with
  | nil => rfl
  | cons d ds ih =>
    show (VExpr.forallE d (VExpr.wrapForalls ds body)).inst a k =
      VExpr.forallE (d.inst a k) (VExpr.wrapForalls (VExpr.instDomains ds a (k + 1))
        (body.inst a (k + (ds.length + 1))))
    simp only [VExpr.inst]
    rw [ih, Nat.add_assoc, Nat.add_comm 1]

/-- A typed walk through a complete wrapped telescope instantiates its body. -/
theorem InstForalls.wrapForalls_eq (H : InstForalls env U Γ (VExpr.wrapForalls doms body) args res)
    (hlen : args.length = doms.length) : res = body.instOuter args := by
  induction args generalizing doms body res with
  | nil =>
    cases doms with
    | nil => cases H; rfl
    | cons => simp at hlen
  | cons a as ih =>
    cases doms with
    | nil => simp at hlen
    | cons dom doms =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have H' : InstForalls env U Γ ((VExpr.wrapForalls doms body).inst a 0) as res := by
        generalize hT : VExpr.wrapForalls (dom :: doms) body = T at H
        simp only [VExpr.wrapForalls, List.foldr_cons] at hT
        cases H with
        | cons _ H' => cases hT; exact H'
        | vacuous H' =>
          injection hT with _ h2
          rw [show VExpr.wrapForalls doms body = _ from h2, VExpr.inst_lift]; exact H'
      rw [VExpr.wrapForalls_inst] at H'
      have := ih H' (by simpa using hlen)
      simpa [hlen] using this

theorem _root_.Lean4Lean.VInductDecl.paramVars_instOuter (decl : VInductDecl)
    (args : List VExpr) (h : args.length = depth + decl.nparams) :
    (decl.paramVars depth).map (·.instOuter args) = args.take decl.nparams := by
  apply List.ext_getElem
  · simp [VInductDecl.paramVars]; omega
  · intro j h1 h2
    simp only [VInductDecl.paramVars, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.getElem_take, List.length_range]
    simp only [VInductDecl.paramVars, List.length_map, List.length_reverse, List.length_range,
      List.length_take] at h1 h2
    rw [VExpr.instOuter_bvar args (by omega)]
    congr 1
    omega

theorem _root_.Lean4Lean.VExpr.mkApps_getAppFnArgs_eq (e : VExpr) :
    VExpr.mkApps (VExpr.getAppFnArgs.go e []).1 (VExpr.getAppFnArgs.go e []).2 = e := by
  have go : ∀ (e : VExpr) (suffix : List VExpr),
      VExpr.mkApps (VExpr.getAppFnArgs.go e suffix).1 (VExpr.getAppFnArgs.go e suffix).2 =
        VExpr.mkApps e suffix := by
    intro e
    induction e with
    | app fn arg ihFn _ =>
      intro suffix
      simpa [VExpr.getAppFnArgs.go, VExpr.mkApps] using ihFn (arg :: suffix)
    | bvar | sort | const | proj | lam | forallE => intro suffix; rfl
  simpa [VExpr.mkApps] using go e []


theorem _root_.Lean4Lean.VInductDecl.RawIndAppAt.instOuter {decl : VInductDecl}
    (H : decl.RawIndAppAt (some typeName) depth result)
    (hfn : result.getAppFnArgs.1 = .const typeName levels)
    (args : List VExpr) (h : args.length = depth + decl.nparams) :
    ∃ indices, result.instOuter args =
        VExpr.mkApps (.const typeName levels) (args.take decl.nparams ++ indices) ∧
      ∃ type ∈ decl.types, type.name = typeName ∧ indices.length = type.numIndices := by
  obtain ⟨type, htype, hname, levels', hfn', hlevels, hlen, hparams⟩ := H
  rcases hname with hname | hname
  · cases hname
  cases Option.some.inj hname
  have hfn'' : (VExpr.getAppFnArgs.go result []).1 = .const type.name levels := hfn
  rw [hfn'] at hfn''
  cases hfn''
  have hresult := VExpr.mkApps_getAppFnArgs_eq result
  rw [hfn'] at hresult
  generalize hxs : (VExpr.getAppFnArgs.go result []).2 = xs at hlen hparams hresult
  refine ⟨(xs.drop decl.nparams).map (·.instOuter args), ?_, type, htype, rfl, ?_⟩
  · have e1 : result.instOuter args = ((VExpr.const type.name levels).mkApps xs).instOuter args := by
      rw [hresult]
    rw [e1, VExpr.instOuter_mkApps, VExpr.instOuter_const]
    congr 1
    conv => lhs; rw [← List.take_append_drop decl.nparams xs]
    rw [List.map_append, hparams, decl.paramVars_instOuter args h]
  · simp [hlen]

/-- `Occurs a e d`: the term `a`, lifted over the `d` binders enclosing the position, occurs as a
subterm of `e`. -/
inductive _root_.Lean4Lean.VExpr.Occurs (a : VExpr) : VExpr → Nat → Prop
  | refl : VExpr.Occurs a (a.liftN d) d
  | appL : VExpr.Occurs a f d → VExpr.Occurs a (.app f x) d
  | appR : VExpr.Occurs a x d → VExpr.Occurs a (.app f x) d
  | lamA : VExpr.Occurs a A d → VExpr.Occurs a (.lam A b) d
  | lamB : VExpr.Occurs a b (d + 1) → VExpr.Occurs a (.lam A b) d
  | forallA : VExpr.Occurs a A d → VExpr.Occurs a (.forallE A b) d
  | forallB : VExpr.Occurs a b (d + 1) → VExpr.Occurs a (.forallE A b) d
  | proj : VExpr.Occurs a e d → VExpr.Occurs a (.proj n i e) d

/-- Instantiation acts on the occurring subterm. -/
theorem _root_.Lean4Lean.VExpr.Occurs.inst (H : VExpr.Occurs b E d) (x : VExpr) (j : Nat) :
    VExpr.Occurs (b.inst x j) (E.inst x (j + d)) d := by
  induction H with
  | @refl d' =>
    have := VExpr.liftN_instN_lo d' b x j 0 (Nat.zero_le _)
    rw [Nat.add_comm] at this
    rw [← this]
    exact .refl
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | lamA _ ih => exact .lamA ih
  | lamB _ ih => exact .lamB (by simpa [Nat.add_assoc] using ih)
  | forallA _ ih => exact .forallA ih
  | forallB _ ih => exact .forallB (by simpa [Nat.add_assoc] using ih)
  | proj _ ih => exact .proj ih

theorem _root_.Lean4Lean.VExpr.Occurs.instOuter (H : VExpr.Occurs b E 0) (args : List VExpr) :
    VExpr.Occurs (b.instOuter args) (E.instOuter args) 0 := by
  induction args generalizing b E with
  | nil => exact H
  | cons a as ih =>
    simp only [VExpr.instOuter_cons]
    exact ih (by simpa using H.inst a as.length)

/-- A free variable occurs. -/
theorem _root_.Lean4Lean.VExpr.Occurs.of_not_skips :
    ∀ (E : VExpr) (d : Nat), ¬ E.Skips' 1 (k + d) → VExpr.Occurs (.bvar k) E d := by
  intro E
  induction E with
  | bvar i =>
    intro d h
    simp only [VExpr.Skips', Classical.not_imp, Nat.not_lt] at h
    obtain rfl : i = k + d := by omega
    have : VExpr.bvar (k + d) = (VExpr.bvar k).liftN d := by
      simp [VExpr.liftN, liftVar, Nat.add_comm]
    rw [this]; exact .refl
  | sort | const => intro _ h; exact (h trivial).elim
  | app f x ihf ihx =>
    intro d h
    simp only [VExpr.Skips', not_and] at h
    by_cases hf : f.Skips' 1 (k + d)
    · exact .appR (ihx d (h hf))
    · exact .appL (ihf d hf)
  | lam A b ihA ihb =>
    intro d h
    simp only [VExpr.Skips', not_and] at h
    by_cases hA : A.Skips' 1 (k + d)
    · exact .lamB (ihb (d + 1) (by simpa [Nat.add_assoc] using h hA))
    · exact .lamA (ihA d hA)
  | forallE A b ihA ihb =>
    intro d h
    simp only [VExpr.Skips', not_and] at h
    by_cases hA : A.Skips' 1 (k + d)
    · exact .forallB (ihb (d + 1) (by simpa [Nat.add_assoc] using h hA))
    · exact .forallA (ihA d hA)
  | proj _ _ e ih => intro d h; exact .proj (ih d h)

/-- A subterm of a well-formed term is well formed, lifted over the binders enclosing it: the
binders `Δ'` above the occurrence stay in the context. -/
theorem _root_.Lean4Lean.VExpr.WF.of_occurs_lift (henv : VEnv.WF env) {a : VExpr} :
    ∀ {e : VExpr} (Δ : List VExpr), VExpr.Occurs a e Δ.length →
      OnCtx (Δ ++ Γ) (env.IsType U) → VExpr.WF env U (Δ ++ Γ) e →
      ∃ Δ' : List VExpr, OnCtx (Δ' ++ Γ) (env.IsType U) ∧
        VExpr.WF env U (Δ' ++ Γ) (a.liftN Δ'.length) := by
  intro e Δ H
  generalize hd : Δ.length = d at H
  induction H generalizing Δ with
  | refl =>
    intro hΓ' H
    subst hd
    exact ⟨Δ, hΓ', H⟩
  | appL _ ih =>
    intro hΓ' H
    have ⟨_, _, hf, _⟩ := H.app_inv henv hΓ'
    exact ih Δ hd hΓ' ⟨_, hf⟩
  | appR _ ih =>
    intro hΓ' H
    have ⟨_, _, _, hx⟩ := H.app_inv henv hΓ'
    exact ih Δ hd hΓ' ⟨_, hx⟩
  | lamA _ ih =>
    intro hΓ' H
    have ⟨⟨_, hA⟩, _⟩ := H.lam_inv henv hΓ'
    exact ih Δ hd hΓ' ⟨_, hA⟩
  | @lamB _ _ A _ ih =>
    intro hΓ' H
    have ⟨⟨_, hA⟩, hb⟩ := H.lam_inv henv hΓ'
    exact ih (A :: Δ) (by simp [hd]) ⟨hΓ', _, hA⟩ hb
  | forallA _ ih =>
    intro hΓ' H
    have ⟨_, H⟩ := H
    have ⟨⟨_, hA⟩, _⟩ := HasType.forallE_inv henv.ordered H
    exact ih Δ hd hΓ' ⟨_, hA⟩
  | @forallB _ _ A _ ih =>
    intro hΓ' H
    have ⟨_, H⟩ := H
    have ⟨⟨_, hA⟩, _, hb⟩ := HasType.forallE_inv henv.ordered H
    exact ih (A :: Δ) (by simp [hd]) ⟨hΓ', _, hA⟩ ⟨_, hb⟩
  | proj _ ih =>
    intro hΓ' H
    have ⟨_, H⟩ := H
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      HasType.proj_inv henv hΓ' H
    exact ih Δ hd hΓ' ⟨_, hmajor.hasType.2⟩

/-- `instOuter` at an offset: the first argument replaces the variable `k + args.length - 1`. -/
def _root_.Lean4Lean.VExpr.instOuterAt : VExpr → List VExpr → Nat → VExpr
  | body, [], _ => body
  | body, a :: as, k => VExpr.instOuterAt (body.inst a (k + as.length)) as k

@[simp] theorem _root_.Lean4Lean.VExpr.instOuterAt_nil (body : VExpr) (k : Nat) :
    body.instOuterAt [] k = body := rfl

@[simp] theorem _root_.Lean4Lean.VExpr.instOuterAt_cons (body a : VExpr) (as : List VExpr) (k : Nat) :
    body.instOuterAt (a :: as) k = (body.inst a (k + as.length)).instOuterAt as k := rfl

theorem _root_.Lean4Lean.VExpr.instOuter_eq_instOuterAt (body : VExpr) (args : List VExpr) :
    body.instOuter args = body.instOuterAt args 0 := by
  induction args generalizing body with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem _root_.Lean4Lean.VExpr.instOuterAt_append (body : VExpr) (xs ys : List VExpr) (k : Nat) :
    body.instOuterAt (xs ++ ys) k = (body.instOuterAt xs (k + ys.length)).instOuterAt ys k := by
  induction xs generalizing body with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, VExpr.instOuterAt_cons, List.length_append, ih]
    congr 3
    omega

/-- Instantiate the domains of a telescope suffix by the arguments consumed before it; the domain
at position `k` (counted from the start of the suffix) sits under `k` further binders. -/
def _root_.Lean4Lean.VExpr.instDomsAt : List VExpr → List VExpr → Nat → List VExpr
  | [], _, _ => []
  | d :: ds, args, k => d.instOuterAt args k :: VExpr.instDomsAt ds args (k + 1)

@[simp] theorem _root_.Lean4Lean.VExpr.instDomsAt_length (ds args : List VExpr) (k : Nat) :
    (VExpr.instDomsAt ds args k).length = ds.length := by
  induction ds generalizing k <;> simp [VExpr.instDomsAt, *]

theorem _root_.Lean4Lean.VExpr.instDomsAt_getElem (ds args : List VExpr) (k j : Nat)
    (h : j < ds.length) :
    (VExpr.instDomsAt ds args k)[j]'(by simpa using h) = ds[j].instOuterAt args (k + j) := by
  induction ds generalizing k j with
  | nil => simp at h
  | cons d ds ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [VExpr.instDomsAt, List.getElem_cons_succ]
      rw [ih _ _ (by simp at h; omega)]
      simp [Nat.add_assoc, Nat.add_comm 1]

@[simp] theorem _root_.Lean4Lean.VExpr.instDomsAt_nil_args (ds : List VExpr) (k : Nat) :
    VExpr.instDomsAt ds [] k = ds := by
  induction ds generalizing k <;> simp [VExpr.instDomsAt, *]

theorem _root_.Lean4Lean.VExpr.instDomains_getElem (ds : List VExpr) (a : VExpr) (k j : Nat)
    (h : j < ds.length) :
    (VExpr.instDomains ds a k)[j]'(by simpa using h) = ds[j].inst a (k + j) := by
  induction ds generalizing k j with
  | nil => simp at h
  | cons d ds ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [VExpr.instDomains, List.getElem_cons_succ]
      rw [ih _ _ (by simp at h; omega)]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem _root_.Lean4Lean.VExpr.instDomsAt_cons_arg (ds : List VExpr) (a : VExpr) (as : List VExpr)
    (k : Nat) :
    VExpr.instDomsAt ds (a :: as) k = VExpr.instDomsAt (VExpr.instDomains ds a (k + as.length)) as k := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    simp only [VExpr.instDomsAt, VExpr.instDomains, VExpr.instOuterAt_cons]
    rw [ih, Nat.add_right_comm]

theorem _root_.Lean4Lean.VExpr.instDomains_drop (ds : List VExpr) (a : VExpr) (k m : Nat) :
    (VExpr.instDomains ds a k).drop m = VExpr.instDomains (ds.drop m) a (k + m) := by
  induction ds generalizing k m with
  | nil => simp [VExpr.instDomains]
  | cons d ds ih =>
    cases m with
    | zero => simp
    | succ m => simp [VExpr.instDomains, ih, Nat.add_assoc, Nat.add_comm 1]

/-- Instantiating a prefix of a wrapped telescope. -/
theorem _root_.Lean4Lean.VProjectionInfo.instantiateProjectionParameters_wrapForalls
    (doms : List VExpr) (body : VExpr) (args : List VExpr) (h : args.length ≤ doms.length) :
    VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls doms body) args =
      some (VExpr.wrapForalls (VExpr.instDomsAt (doms.drop args.length) args 0)
        (body.instOuterAt args (doms.length - args.length))) := by
  induction args generalizing doms body with
  | nil => simp [VProjectionInfo.instantiateProjectionParameters]
  | cons a as ih =>
    cases doms with
    | nil => simp at h
    | cons d ds =>
      simp only [List.length_cons] at h
      have h' : as.length ≤ ds.length := Nat.le_of_succ_le_succ h
      show VProjectionInfo.instantiateProjectionParameters
        (VExpr.forallE d (VExpr.wrapForalls ds body)) (a :: as) = _
      simp only [VProjectionInfo.instantiateProjectionParameters]
      rw [VExpr.wrapForalls_inst, ih _ _ (by simpa using h')]
      simp only [Nat.zero_add, List.length_cons, List.drop_succ_cons, VExpr.instDomains_length,
        VExpr.instOuterAt_cons, Option.some.injEq, VExpr.instDomains_drop,
        VExpr.instDomsAt_cons_arg, Nat.add_sub_add_right]
      congr 2
      rw [Nat.sub_add_cancel h']

/-- Walking the field binders of a wrapped telescope selects the instantiated domain. -/
theorem _root_.Lean4Lean.VProjectionInfo.instantiateProjectionFields_wrapForalls
    (ds : List VExpr) (body : VExpr) (k current : Nat) (hk : k < ds.length) :
    VProjectionInfo.instantiateProjectionFields typeName major (current + k) current (k + 1)
        (VExpr.wrapForalls ds body) =
      some (ds[k].instOuterAt ((List.range k).map fun j => .proj typeName (current + j) major) 0) := by
  induction k generalizing ds current body with
  | zero =>
    cases ds with
    | nil => simp at hk
    | cons d ds =>
      show VProjectionInfo.instantiateProjectionFields typeName major (current + 0) current 1
        (VExpr.forallE d (VExpr.wrapForalls ds body)) = _
      simp [VProjectionInfo.instantiateProjectionFields]
  | succ k ih =>
    cases ds with
    | nil => simp at hk
    | cons d ds =>
      simp only [List.length_cons] at hk
      show VProjectionInfo.instantiateProjectionFields typeName major (current + (k + 1)) current
        (k + 2) (VExpr.forallE d (VExpr.wrapForalls ds body)) = _
      simp only [VProjectionInfo.instantiateProjectionFields]
      rw [if_neg (by omega), VExpr.wrapForalls_inst]
      have := ih (ds := VExpr.instDomains ds (.proj typeName current major) 0) (current := current + 1)
        (body := body.inst (.proj typeName current major) (0 + ds.length))
        (by simpa using Nat.lt_of_succ_lt_succ hk)
      rw [show current + (k + 1) = current + 1 + k by omega, this]
      congr 1
      simp only [List.getElem_cons_succ, Nat.zero_add,
        List.range_succ_eq_map, List.map_cons, List.map_map, VExpr.instOuterAt_cons,
        List.length_map, List.length_range]
      congr 2
      · simpa using VExpr.instDomains_getElem ds _ 0 k (Nat.lt_of_succ_lt_succ hk)
      · funext j
        simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

/-- `fieldType` is the fully instantiated field domain. -/
theorem _root_.Lean4Lean.VProjectionInfo.fieldType_eq_instOuter (info : VProjectionInfo)
    (hshape : info.ctorType = VExpr.wrapForalls doms result)
    (hlevels : levels.length = info.uvars) (hparams : params.length = info.nparams)
    (hlt : info.nparams + index < doms.length) :
    info.fieldType typeName levels params index major =
      some ((doms[info.nparams + index].instL levels).instOuter
        (params ++ (List.range index).map fun j => .proj typeName j major)) := by
  have hle : params.length ≤ (doms.map (·.instL levels)).length := by simp; omega
  have hfields := VProjectionInfo.instantiateProjectionFields_wrapForalls (typeName := typeName)
    (major := major) (VExpr.instDomsAt ((doms.map (·.instL levels)).drop params.length) params 0)
    (result.instL levels |>.instOuterAt params ((doms.map (·.instL levels)).length - params.length))
    index 0 (by simp; omega)
  simp only [Nat.zero_add] at hfields
  unfold VProjectionInfo.fieldType
  rw [if_neg (by simp [hlevels, hparams]), hshape, VExpr.instL_wrapForalls,
    VProjectionInfo.instantiateProjectionParameters_wrapForalls _ _ params hle]
  simp only [bind, Option.bind]
  rw [hfields]
  congr 1
  rw [VExpr.instDomsAt_getElem _ _ _ _ (by simp; omega), List.getElem_drop, List.getElem_map,
    VExpr.instOuter_eq_instOuterAt, VExpr.instOuterAt_append]
  simp [hparams]

theorem _root_.Lean4Lean.VLevel.params_map_inst (ls : List VLevel) (h : ls.length = n) :
    (VLevel.params n).map (·.inst ls) = ls := by
  apply List.ext_getElem
  · simp [h]
  · intro j h1 h2
    simp [VLevel.params, VLevel.inst, List.getD_eq_getElem?_getD, h2]

@[simp] theorem _root_.Lean4Lean.VExpr.instOuterAt_forallE (A B : VExpr) (args : List VExpr) (k : Nat) :
    (VExpr.forallE A B).instOuterAt args k =
      .forallE (A.instOuterAt args k) (B.instOuterAt args (k + 1)) := by
  induction args generalizing A B with
  | nil => rfl
  | cons a as ih => simp [VExpr.inst, ih, Nat.add_right_comm]

theorem _root_.Lean4Lean.VExpr.instOuter_forallE (A B : VExpr) (args : List VExpr) :
    (VExpr.forallE A B).instOuter args = .forallE (A.instOuter args) (B.instOuterAt args 1) := by
  simp [VExpr.instOuter_eq_instOuterAt]

theorem _root_.Lean4Lean.List.forall₂_append_split {R : α → β → Prop} :
    ∀ {a : List α} {c : List β} {b : List α} {d : List β}, List.Forall₂ R (a ++ b) (c ++ d) →
      a.length = c.length → List.Forall₂ R a c ∧ List.Forall₂ R b d
  | [], [], _, _, H, _ => ⟨.nil, H⟩
  | _ :: _, [], _, _, _, h => by simp at h
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: a, _ :: c, b, d, .cons h H, hl => by
    have ⟨h1, h2⟩ := List.forall₂_append_split H (by simpa using hl)
    exact ⟨.cons h h1, h2⟩

/-- Universe-level congruence for a closed type. -/
theorem IsType.instL_defeq (henv : env.OrderedStrong)
    (H : env.IsType U' [] e)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    env.IsDefEqU U Γ (e.instL ls) (e.instL ls') := by
  have ⟨s, H⟩ := H
  have Hs := H.strong henv (by trivial)
  have H1 : env.IsDefEqStrong U [] (e.instL ls) (e.instL ls) ((VExpr.sort s).instL ls) :=
    Hs.instL hls
  have H2 := (EqUpToLevels.instL hls hls' heq Hs).2
  have H3 := (EqUpToLevels.refl (by trivial) H1).1
  have := EqUpToLevels.defeq henv henv.strong (by trivial) H1 H3 H2
  exact ⟨_, this.defeq.weak0 henv⟩

/-- An application spine typed against a wrapped telescope: every argument is typed at its
instantiated domain, and the application at the instantiated body. -/
theorem HasType.mkApps_wrapForalls (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {f : VExpr} {doms : List VExpr} {body : VExpr},
      env.HasType U Γ f (VExpr.wrapForalls doms body) →
      VExpr.WF env U Γ (VExpr.mkApps f args) → args.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length),
        env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) ∧
      env.HasType U Γ (VExpr.mkApps f args) (body.instOuter args) := by
  intro args
  induction args with
  | nil =>
    intro f doms body hf H hlen
    cases doms with
    | nil => exact ⟨fun _ h => by simp at h, by simpa [VExpr.mkApps, VExpr.wrapForalls] using hf⟩
    | cons => simp at hlen
  | cons a as ih =>
    intro f doms body hf H hlen
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hf' : env.HasType U Γ f (.forallE d (VExpr.wrapForalls ds body)) := hf
      have hfa : VExpr.WF env U Γ (.app f a) :=
        VExpr.WF.of_mkApps henv hΓ (f := .app f a) (by simpa [VExpr.mkApps] using H)
      have ⟨A', B', hf'', ha'⟩ := hfa.app_inv henv hΓ
      have ⟨⟨_, hA⟩, _, hB'⟩ := (hf'.uniqU henv hΓ hf'').forallE_inv henv hΓ
      have ha : env.HasType U Γ a d := ha'.defeqU_r henv hΓ ⟨_, hA.symm⟩
      have hfa' : env.HasType U Γ (.app f a) ((VExpr.wrapForalls ds body).inst a) := hf'.app ha
      rw [VExpr.wrapForalls_inst] at hfa'
      have ⟨ih1, ih2⟩ := ih hfa' (by simpa [VExpr.mkApps] using H) (by simpa using hlen)
      refine ⟨fun j hj hj' => ?_, by simpa [VExpr.mkApps, hlen] using ih2⟩
      cases j with
      | zero => simpa using ha
      | succ j =>
        have := ih1 j (by simpa using hj) (by simpa using hj')
        simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
          List.length_take]
        have hj' : j < as.length := by simpa using hj
        rw [Nat.min_eq_left (Nat.le_of_lt hj')]
        simpa [VExpr.instDomains_getElem ds a 0 j (by omega)] using this

/-- Rebuild a typed walk from a typed walk over pointwise definitionally equal arguments, provided
the telescope is syntactically long enough. -/
theorem InstForallsC.of_defeq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args args' : List VExpr} {T T' res' : VExpr} {domsRest : List VExpr × VExpr},
      InstForallsC env U Γ T' args' res' → env.IsDefEqU U Γ T T' →
      List.Forall₂ (env.IsDefEqU U Γ) args args' →
      T.takeForalls args.length = some domsRest →
      ∃ res, InstForallsC env U Γ T args res ∧ env.IsDefEqU U Γ res res' := by
  intro args
  induction args with
  | nil =>
    intro args' T T' res' _ H' hT hargs _
    cases hargs; cases H'; exact ⟨_, .nil, hT⟩
  | cons a as ih =>
    intro args' T T' res' domsRest H' hT hargs hdoms
    cases hargs with | cons haa hargs
    cases T <;> simp [VExpr.takeForalls] at hdoms
    case forallE A B =>
      obtain ⟨doms', rest', hB, -⟩ := hdoms
      cases H' with
      | cons ha' H' =>
        have ⟨⟨_, hA⟩, _, hBB⟩ := hT.forallE_inv henv hΓ
        have ha : env.HasType U Γ a A :=
          (haa.of_r henv hΓ (ha'.defeqU_r henv hΓ ⟨_, hA.symm⟩)).hasType.1
        have hinst := IsDefEq.instDF henv.ordered hΓ hBB (haa.of_l henv hΓ ha)
        obtain ⟨_, hB'⟩ := VExpr.takeForalls_inst (a := a) (k := 0) hB
        have ⟨res, H1, H2⟩ := ih H' ⟨_, hinst⟩ hargs hB'
        exact ⟨res, .cons ha H1, H2⟩

theorem InstForallsC.append_inv (H : InstForallsC env U Γ T (xs ++ ys) res) :
    ∃ mid, InstForallsC env U Γ T xs mid ∧ InstForallsC env U Γ mid ys res := by
  induction xs generalizing T with
  | nil => exact ⟨_, .nil, H⟩
  | cons x xs ih =>
    cases H with
    | cons hx H =>
      have ⟨mid, h1, h2⟩ := ih H
      exact ⟨mid, .cons hx h1, h2⟩

theorem InstForallsC.wrapForalls_eq (H : InstForallsC env U Γ (VExpr.wrapForalls doms body) args res)
    (hlen : args.length = doms.length) : res = body.instOuter args :=
  H.toInstForalls.wrapForalls_eq hlen

/-- Argument lists that differ only at variables the body does not use instantiate it identically. -/
theorem _root_.Lean4Lean.VExpr.instOuter_congr_of_skips :
    ∀ (args args₂ : List VExpr) (E : VExpr), args.length = args₂.length →
      (∀ k (hk : k < args.length) (hk₂ : k < args₂.length), args[k] ≠ args₂[k] →
        E.Skips 1 (args.length - 1 - k)) →
      E.instOuter args = E.instOuter args₂ := by
  intro args
  induction args with
  | nil => intro args₂ E hlen _; cases args₂ <;> simp_all
  | cons a as ih =>
    intro args₂ E hlen hdiff
    cases args₂ with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [VExpr.instOuter_cons]
      have hstep : E.inst a as.length = E.inst b bs.length := by
        by_cases hab : a = b
        · rw [hab, hlen]
        · have := hdiff 0 (by simp) (by simp) (by simpa using hab)
          simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at this
          obtain ⟨E', rfl⟩ := VExpr.skips_iff_exists.1 this
          rw [VExpr.inst_liftN, ← hlen, VExpr.inst_liftN]
      rw [hstep]
      refine ih bs (E.inst b bs.length) hlen fun k hk hk₂ hne => ?_
      have := hdiff (k + 1) (by simpa using hk) (by simpa using hk₂) (by simpa using hne)
      simp only [List.length_cons] at this
      have hk' : k < bs.length := hk₂
      rw [show as.length + 1 - 1 - (k + 1) = bs.length - 1 - k by omega] at this
      obtain ⟨E', hE⟩ := VExpr.skips_iff_exists.1 this
      rw [hE]
      have := VExpr.liftN_instN_lo 1 E' b (bs.length - 1) (bs.length - 1 - k) (by omega)
      rw [show 1 + (bs.length - 1) = bs.length by omega] at this
      rw [← this, hlen]
      exact .liftN

theorem _root_.Lean4Lean.VExpr.wrapForalls_split (doms : List VExpr) (body : VExpr) (m : Nat)
    (hm : m < doms.length) :
    VExpr.wrapForalls doms body =
      VExpr.wrapForalls (doms.take m)
        (.forallE doms[m] (VExpr.wrapForalls (doms.drop (m + 1)) body)) := by
  calc VExpr.wrapForalls doms body
      = VExpr.wrapForalls (doms.take m ++ doms.drop m) body := by rw [List.take_append_drop]
    _ = _ := by rw [List.drop_eq_getElem_cons hm, VExpr.wrapForalls_append]; rfl

/-- The typing data of a fully applied registered constructor: its universe levels, the typing of
its arguments along the constructor telescope, and its type as an application of the structure. -/
theorem VProjectionInfo.ctorApp_typing {info : VProjectionInfo} {decl : VInductDecl}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩)
    (hshape : info.ctorType = VExpr.wrapForalls doms result)
    (hvalid : decl.RawIndAppAt (some S) (doms.length - decl.nparams) result)
    (hhead : result.getAppFnArgs.1 = .const S (VLevel.params decl.uvars))
    (hdn : decl.nparams = info.nparams) (hdu : decl.uvars = info.uvars)
    (hle : info.nparams ≤ doms.length)
    (hc' : env.HasType U Γ (VExpr.mkApps (.const info.ctorName ls') args') T)
    (hlen : args'.length = doms.length) :
    (∀ l ∈ ls', l.WF U) ∧ ls'.length = info.uvars ∧
    (∀ j (hj : j < args'.length), env.HasType U Γ args'[j]
      (((doms[j]'(by omega)).instL ls').instOuter (args'.take j))) ∧
    (∃ res, InstForallsC env U Γ (info.ctorType.instL ls') args' res) ∧
    ∃ idx', env.HasType U Γ (VExpr.mkApps (.const info.ctorName ls') args')
      (VExpr.mkApps (.const S ls') (args'.take info.nparams ++ idx')) := by
  have ⟨ci, hci, hls', hlen'⟩ :=
    (VExpr.WF.of_mkApps henv hΓ ⟨_, hc'⟩).elim fun _ h => HasType.const_inv henv hΓ h
  rw [hctor] at hci
  cases Option.some.inj hci
  have hconst : env.HasType U Γ (.const info.ctorName ls') (info.ctorType.instL ls') :=
    HasType.const hctor hls' hlen'
  have hT : (info.ctorType.instL ls').takeForalls args'.length =
      some (doms.map (·.instL ls'), result.instL ls') := by
    rw [hshape, VExpr.instL_wrapForalls,
      show args'.length = (doms.map (·.instL ls')).length by simp [hlen]]
    exact VExpr.takeForalls_wrapForalls _ _
  obtain ⟨res, Hw, hres⟩ := HasType.mkApps_telescope henv hΓ hconst ⟨_, hc'⟩ hT
  have hresEq : res = (result.instL ls').instOuter args' := by
    have := Hw
    rw [hshape, VExpr.instL_wrapForalls] at this
    exact this.wrapForalls_eq (by simp [hlen])
  have hhead' : (result.instL ls').getAppFnArgs.1 = .const S ls' := by
    rw [VExpr.getAppFnArgs_instL]
    show (result.getAppFnArgs.1.instL ls') = _
    rw [hhead]
    simp [VExpr.instL, VLevel.params_map_inst ls' (hlen'.trans hdu.symm)]
  obtain ⟨idx', hresEq', -⟩ := (hvalid.instL ls').instOuter hhead' args' (by omega)
  have hf' : env.HasType U Γ (.const info.ctorName ls')
      (VExpr.wrapForalls (doms.map (·.instL ls')) (result.instL ls')) := by
    rwa [hshape, VExpr.instL_wrapForalls] at hconst
  have ⟨hargsTy, _⟩ := HasType.mkApps_wrapForalls henv hΓ hf' ⟨_, hc'⟩ (by simp [hlen])
  refine ⟨hls', hlen', fun j hj => ?_, ⟨_, Hw⟩, idx', ?_⟩
  · have := hargsTy j hj (by simp; omega)
    simpa only [List.getElem_map] using this
  · rw [hresEq, hresEq', hdn] at hres; exact hres

open Classical in
/-- **The field walk.** Instantiating the telescope of a constructor field with arguments that are
pointwise definitionally equal to the constructor's arguments, at every position the field's domain
actually uses, gives a type definitionally equal to the field's declared type at the constructor's
arguments. -/
theorem VProjectionInfo.field_walk {info : VProjectionInfo} {decl : VInductDecl}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hwf : env.IsType info.uvars [] info.ctorType)
    (hctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩)
    (hshape : info.ctorType = VExpr.wrapForalls doms result)
    (hvalid : decl.RawIndAppAt (some S) (doms.length - decl.nparams) result)
    (hhead : result.getAppFnArgs.1 = .const S (VLevel.params decl.uvars))
    (hdn : decl.nparams = info.nparams) (hdu : decl.uvars = info.uvars)
    (hle : info.nparams ≤ doms.length)
    (hc' : env.HasType U Γ (VExpr.mkApps (.const info.ctorName ls') args') T)
    (hlen : args'.length = doms.length)
    {lsA : List VLevel} (hlsA : ∀ l ∈ lsA, l.WF U) (hlsE : List.Forall₂ (· ≈ ·) lsA ls')
    {PA : List VExpr} (hPA : List.Forall₂ (env.IsDefEqU U Γ) PA (args'.take info.nparams))
    {index : Nat} (hmd : info.nparams + index < doms.length)
    {qs : List VExpr} (hqs : qs.length = index)
    (hpt : ∀ k (hk : k < index),
      ((doms[info.nparams + index]'hmd).instL lsA).Skips 1 (index - 1 - k) ∨
      env.IsDefEqU U Γ (qs[k]'(by omega)) (args'[info.nparams + k]'(by omega))) :
    env.IsDefEqU U Γ (((doms[info.nparams + index]'hmd).instL lsA).instOuter (PA ++ qs))
      (((doms[info.nparams + index]'hmd).instL ls').instOuter
        (args'.take (info.nparams + index))) := by
  generalize hD : doms[info.nparams + index]'hmd = D at *
  obtain ⟨hls', hlen', -, ⟨res, Hw⟩, -⟩ :=
    VProjectionInfo.ctorApp_typing henv hΓ hctor hshape hvalid hhead hdn hdu hle hc' hlen
  have hPAlen : PA.length = info.nparams := by
    rw [List.Forall₂.length_eq hPA]; simp; omega
  -- the argument list, with unused positions replaced by the constructor's arguments
  let ps' : List VExpr := (List.range index).map fun j =>
    if (D.instL lsA).Skips 1 (index - 1 - j) then args'.getD (info.nparams + j) default else qs.getD j default
  have hps'Len : ps'.length = index := by simp [ps']
  have hpoint : ∀ j (hj : j < index), env.IsDefEqU U Γ ps'[j] args'[info.nparams + j] := by
    intro j hj
    have hnj : info.nparams + j < args'.length := by omega
    simp only [ps', List.getElem_map, List.getElem_range]
    split
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnj]
      have := VProjectionInfo.ctorApp_typing henv hΓ hctor hshape hvalid hhead hdn hdu hle hc' hlen
      exact ⟨_, this.2.2.1 (info.nparams + j) hnj⟩
    · rename_i hsk
      rcases hpt j hj with h | h
      · exact absurd h hsk
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact h
  -- the two telescopes, split at the field position
  have hmd' : info.nparams + index < (doms.map (·.instL ls')).length := by simp; omega
  have hmd₀ : info.nparams + index < (doms.map (·.instL lsA)).length := by simp; omega
  have hsplit' := VExpr.wrapForalls_split (doms.map (·.instL ls')) (result.instL ls') (info.nparams + index) hmd'
  have hsplit₀ := VExpr.wrapForalls_split (doms.map (·.instL lsA)) (result.instL lsA) (info.nparams + index) hmd₀
  simp only [List.getElem_map, hD] at hsplit' hsplit₀
  -- constructor side: the walk up to the field position
  have Hw' := Hw
  rw [hshape, VExpr.instL_wrapForalls, hsplit', ← List.take_append_drop (info.nparams + index) args'] at Hw'
  obtain ⟨midR, HwR, _⟩ := Hw'.append_inv
  have hmidR := HwR.wrapForalls_eq (by simp; omega)
  rw [VExpr.instOuter_forallE] at hmidR
  -- the other side: rebuild the walk over the pointwise equal arguments
  have hTeq' := IsType.instL_defeq (Γ := Γ) henv hwf hlsA hls' hlsE
  rw [hshape, VExpr.instL_wrapForalls, VExpr.instL_wrapForalls, hsplit₀, hsplit'] at hTeq'
  have hbs : List.Forall₂ (env.IsDefEqU U Γ) (PA ++ ps') (args'.take (info.nparams + index)) := by
    rw [List.take_add]
    refine hPA.append' (List.forall₂_of_getElem (by
      simp only [ps', List.length_map, List.length_range, List.length_take, List.length_drop]
      omega) fun j hj hj' => ?_)
    have hj0 : j < index := by simpa [ps'] using hj
    have := hpoint j hj0
    simpa [List.getElem_take, List.getElem_drop] using this
  obtain ⟨midL, HwL, hmid⟩ := InstForallsC.of_defeq henv hΓ HwR hTeq' hbs (by
    rw [show (PA ++ ps').length = ((doms.map (·.instL lsA)).take (info.nparams + index)).length by
      simp [hps'Len, hPAlen]; omega]
    exact VExpr.takeForalls_wrapForalls _ _)
  have hmidL := HwL.wrapForalls_eq (by simp [hps'Len, hPAlen]; omega)
  rw [VExpr.instOuter_forallE] at hmidL
  subst hmidL hmidR
  have ⟨⟨_, hDeq⟩, _⟩ := hmid.forallE_inv henv hΓ
  -- unused positions may carry either argument
  have hirr : (D.instL lsA).instOuter (PA ++ ps') = (D.instL lsA).instOuter (PA ++ qs) := by
    refine VExpr.instOuter_congr_of_skips _ _ _ (by simp [hps'Len, hqs]) fun k hk hk₂ hne => ?_
    simp only [List.getElem_append] at hne
    split at hne
    · exact absurd rfl hne
    · rename_i hkn
      simp only [ps', List.getElem_map, List.getElem_range] at hne
      split at hne
      · rename_i hsk
        have : (PA ++ ps').length - 1 - k = index - 1 - (k - PA.length) := by
          simp [hps'Len, hPAlen]; omega
        rw [this]; exact hsk
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hk₂; omega)] at hne
        exact absurd rfl hne
  rw [← hirr]
  exact ⟨_, hDeq⟩

/-- A projection of a major convertible to a constructor application is definitionally equal to
the corresponding constructor argument, once the projection is well formed and the field typing
holds at that index. -/
theorem VProjectionInfo.proj_ctorApp_defeq
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections S info)
    (hR : ∀ {F field}, env.HasType U Γ (.proj S j (VExpr.mkApps (.const info.ctorName ls') args')) F →
      args'[info.nparams + j]? = some field → env.HasType U Γ field F)
    (hnj : info.nparams + j < args'.length)
    (hM : env.IsDefEq U Γ M (VExpr.mkApps (.const info.ctorName ls') args') T)
    (hwfj : VExpr.WF env U Γ (.proj S j M)) :
    env.IsDefEqU U Γ (.proj S j M) args'[info.nparams + j] := by
  obtain ⟨_, hpj⟩ := hwfj
  obtain ⟨infoj, lsj, Pj, idxj, smj, Fj, flj, hinfoj, hlsj, huvj, hPj, hidxj, hfieldj, hFtyj,
    hsmj, hclosedj, hguardj⟩ := HasType.proj_inv henv hΓ hpj
  obtain rfl := henv.ordered.projections_unique hinfo hinfoj
  have hTT : env.IsDefEqU U Γ _ _ := hM.hasType.1.uniqU henv hΓ hsmj.hasType.2
  have hsmc := IsDefEqU.defeqDF henv hΓ hTT hM
  have hprojj := IsDefEq.projDF hinfo hlsj huvj hPj hidxj hfieldj hFtyj hsmj (hsmj.trans hsmc)
    hclosedj hguardj
  have hkj : args'[info.nparams + j]? = some args'[info.nparams + j] :=
    List.getElem?_eq_getElem hnj
  have hIH := hR hprojj.hasType.2 hkj
  exact ⟨_, hprojj.trans (.projIota hinfo hprojj.hasType.2 hkj hIH)⟩

/-- Universe instantiation preserves a skipped variable. -/
theorem _root_.Lean4Lean.VExpr.Skips.instL {e : VExpr} (self : e.Skips n k) :
    (e.instL ls).Skips n k := by
  obtain ⟨e', rfl⟩ := VExpr.skips_iff_exists.1 self
  rw [VExpr.instL_liftN]; exact .liftN

open Classical in
/-- The two halves of the projection-of-a-constructor argument, proved together by strong induction
on the field index:
* **field typing**: if `.proj S index (c args)` has type `F` then the field argument has type `F`;
* **projection transfer**: if a projection of a term convertible to `M`, lifted over binders `Δ`, is
  well formed in `Δ ++ Γ`, where `M` is convertible to the constructor application in `Γ`, then the
  projection of `M` is well formed in `Γ` and equal to the field argument there.

The transfer half is what lets an earlier field's projection, occurring under binders inside a later
field's type, be typed in the smaller context: it is rebuilt in `Γ` from the projection typing rule,
with the field type obtained by the field walk and the universe guard transported along the unique
sort of that field type; nothing is strengthened. -/
theorem VProjectionInfo.field_typing_aux {decl : VInductDecl}
    (henv : VEnv.WF env)
    (hinfo : env.projections S info)
    (hwf : env.IsType info.uvars [] info.ctorType)
    (hctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩)
    (hshape : info.ctorType = VExpr.wrapForalls doms result)
    (hvalid : decl.RawIndAppAt (some S) (doms.length - decl.nparams) result)
    (hhead : result.getAppFnArgs.1 = .const S (VLevel.params decl.uvars))
    (hdn : decl.nparams = info.nparams) (hdu : decl.uvars = info.uvars)
    (hle : info.nparams ≤ doms.length) (index : Nat) :
    (∀ {Γ : List VExpr} {ls' : List VLevel} {args' : List VExpr} {F field : VExpr},
      OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.proj S index (VExpr.mkApps (.const info.ctorName ls') args')) F →
      args'.length = doms.length → args'[info.nparams + index]? = some field →
      env.HasType U Γ field F) ∧
    (∀ {Γ : List VExpr} {ls' : List VLevel} {args' : List VExpr} {M T : VExpr}
      (Δ : List VExpr) {X : VExpr}, OnCtx Γ (env.IsType U) → OnCtx (Δ ++ Γ) (env.IsType U) →
      (hmd : info.nparams + index < doms.length) → (hlen : args'.length = doms.length) →
      env.IsDefEq U Γ M (VExpr.mkApps (.const info.ctorName ls') args') T →
      env.IsDefEqU U (Δ ++ Γ) X (M.liftN Δ.length) →
      VExpr.WF env U (Δ ++ Γ) (.proj S index X) →
      env.IsDefEqU U Γ (.proj S index M) (args'[info.nparams + index]'(by omega))) := by
  induction index using WellFounded.induction Nat.lt_wfRel.2 with
  | _ index IH =>
  -- field typing at `index`, from the transfer half below `index`
  have hR : ∀ {Γ : List VExpr} {ls' : List VLevel} {args' : List VExpr} {F field : VExpr},
      OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.proj S index (VExpr.mkApps (.const info.ctorName ls') args')) F →
      args'.length = doms.length → args'[info.nparams + index]? = some field →
      env.HasType U Γ field F := by
    intro Γ ls' args' F field hΓ H hlen hk
    obtain ⟨info', ls₀, P₀, idx₀, sm, F', fl, hinfo', hls₀, huv₀, hP₀, hidx₀, hfield, hFty, hsm,
      hclosed, hguard⟩ := HasType.proj_inv henv hΓ H
    obtain rfl := henv.ordered.projections_unique hinfo hinfo'
    have hproj' : env.HasType U Γ
        (.proj S index (VExpr.mkApps (.const info.ctorName ls') args')) F' :=
      .projDF hinfo hls₀ huv₀ hP₀ hidx₀ hfield hFty hsm hsm hclosed hguard
    have hFF : env.IsDefEqU U Γ F' F := hproj'.uniqU henv hΓ H
    suffices env.HasType U Γ field F' from this.defeqU_r henv hΓ hFF
    have hc' := hsm.hasType.2
    obtain ⟨hls', hlen', hargsTy, -, idx', hres⟩ :=
      VProjectionInfo.ctorApp_typing henv hΓ hctor hshape hvalid hhead hdn hdu hle hc' hlen
    have hTeq := hc'.uniqU henv hΓ hres
    have ⟨u, hu⟩ := IsDefEq.isType henv.ordered hΓ hsm
    have ⟨hlsE, hargsE⟩ := IsDefEqU.structApp_inv henv hΓ hinfo hTeq hu
    have ⟨hPE, _⟩ := List.forall₂_append_split hargsE (by
      rw [hP₀, List.length_take]; exact (Nat.min_eq_left (by omega)).symm)
    obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.1 hk
    have hmd : info.nparams + index < doms.length := by omega
    have hF' := VProjectionInfo.fieldType_eq_instOuter info hshape huv₀ hP₀ hmd
      (typeName := S) (major := sm)
    rw [hfield] at hF'
    cases Option.some.inj hF'
    have hW := VProjectionInfo.field_walk henv hΓ hwf hctor hshape hvalid hhead hdn hdu hle hc' hlen
      hls₀ hlsE hPE hmd (qs := (List.range index).map fun j => .proj S j sm) (by simp)
      fun k hk => by
        by_cases hsk : ((doms[info.nparams + index]'hmd).instL ls₀).Skips 1 (index - 1 - k)
        · exact .inl hsk
        refine .inr ?_
        -- the projection occurs in the field type, hence is well formed under some binders
        have hocc' : VExpr.Occurs (.bvar (index - 1 - k))
            ((doms[info.nparams + index]'hmd).instL ls₀) 0 :=
          VExpr.Occurs.of_not_skips _ 0 (by simpa [← VExpr.skips_iff] using hsk)
        have hocc'' := hocc'.instOuter
          (P₀ ++ (List.range index).map fun j => VExpr.proj S j sm)
        have hb : (VExpr.bvar (index - 1 - k)).instOuter
            (P₀ ++ (List.range index).map fun j => VExpr.proj S j sm) = .proj S k sm := by
          rw [VExpr.instOuter_bvar _ (by simp [hP₀]; omega)]
          apply (List.getElem_eq_iff _).2
          have hidx : (P₀ ++ (List.range index).map fun j => VExpr.proj S j sm).length - 1 -
              (index - 1 - k) = info.nparams + k := by
            simp [hP₀]; omega
          rw [hidx, List.getElem?_append_right (by omega), hP₀, Nat.add_sub_cancel_left]
          simp [List.getElem?_range hk]
        rw [hb] at hocc''
        obtain ⟨Δ, hΓΔ, hwfΔ⟩ := VExpr.WF.of_occurs_lift henv [] hocc'' hΓ ⟨_, hFty⟩
        have hsmΔ := hsm.hasType.1.weakN henv.ordered (Ctx.LiftN.zero (Γ := Γ) Δ rfl)
        have := (IH k hk).2 Δ hΓ hΓΔ (by omega) hlen hsm (IsDefEqU.refl ⟨_, hsmΔ⟩)
          hwfΔ
        simpa using this
    exact (hargsTy (info.nparams + index) hm).defeqU_r henv hΓ hW.symm
  refine ⟨hR, ?_⟩
  -- projection transfer at `index`
  intro Γ ls' args' M T Δ X hΓ hΓΔ hmd hlen hM hX hwfX
  obtain ⟨_, hpX⟩ := hwfX
  obtain ⟨info', L, P, I, N, Fs, fl, hinfo', hL, hLlen, hP, hI, hfield, hFty, hN, hclosed,
    hguard⟩ := HasType.proj_inv henv hΓΔ hpX
  obtain rfl := henv.ordered.projections_unique hinfo hinfo'
  have hc' := hM.hasType.2
  obtain ⟨hls', hlen', hargsTy, -, idx', hres⟩ :=
    VProjectionInfo.ctorApp_typing henv hΓ hctor hshape hvalid hhead hdn hdu hle hc' hlen
  have hMS := IsDefEqU.defeqDF henv hΓ (hc'.uniqU henv hΓ hres) hM
  have W : Ctx.LiftN Δ.length 0 Γ (Δ ++ Γ) := .zero Δ rfl
  have hMS' := hMS.weakN henv.ordered W
  simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append] at hMS'
  -- the source major is convertible to the lifted constructor application
  have hNM : env.IsDefEqU U (Δ ++ Γ) N (M.liftN Δ.length) := (IsDefEq.toU hN).trans henv hΓΔ hX
  have hNc := hNM.trans henv hΓΔ (IsDefEq.toU hMS')
  have hNS := (hNc.symm.of_l henv hΓΔ hMS'.hasType.2).hasType.2
  have ⟨u₀, hu₀⟩ := IsDefEq.isType henv.ordered hΓΔ hN
  have ⟨hLE, hargsE⟩ := IsDefEqU.structApp_inv henv hΓΔ hinfo (hN.hasType.1.uniqU henv hΓΔ hNS) hu₀
  have hidx' : idx'.length = info.nindices := by
    have := List.Forall₂.length_eq hargsE
    simp only [List.length_append, List.length_map, List.length_take, hP, hI] at this
    omega
  -- the field type in the smaller context, by the field walk
  have hmd' := hmd
  have hW := VProjectionInfo.field_walk henv hΓ hwf hctor hshape hvalid hhead hdn hdu hle hc' hlen
    hls' (List.forall₂_of_getElem rfl fun _ _ _ => rfl)
    (PA := args'.take info.nparams)
    (List.forall₂_of_getElem rfl fun j hj _ => by
      have := hargsTy j (by simp at hj; omega)
      rw [List.getElem_take]; exact IsDefEqU.refl ⟨_, this⟩)
    hmd (qs := (List.range index).map fun j => .proj S j M) (by simp)
    fun k hk => by
      by_cases hsk : ((doms[info.nparams + index]'hmd).instL ls').Skips 1 (index - 1 - k)
      · exact .inl hsk
      refine .inr ?_
      have hsk' : ¬ ((doms[info.nparams + index]'hmd).instL L).Skips 1 (index - 1 - k) :=
        fun h => hsk h.of_instL.instL
      have hocc' : VExpr.Occurs (.bvar (index - 1 - k))
          ((doms[info.nparams + index]'hmd).instL L) 0 :=
        VExpr.Occurs.of_not_skips _ 0 (by simpa [← VExpr.skips_iff] using hsk')
      have hFs := VProjectionInfo.fieldType_eq_instOuter info hshape hLlen hP hmd
        (typeName := S) (major := N)
      rw [hfield] at hFs
      cases Option.some.inj hFs
      have hocc'' := hocc'.instOuter (P ++ (List.range index).map fun j => VExpr.proj S j N)
      have hb : (VExpr.bvar (index - 1 - k)).instOuter
          (P ++ (List.range index).map fun j => VExpr.proj S j N) = .proj S k N := by
        rw [VExpr.instOuter_bvar _ (by simp [hP]; omega)]
        apply (List.getElem_eq_iff _).2
        have hidx : (P ++ (List.range index).map fun j => VExpr.proj S j N).length - 1 -
            (index - 1 - k) = info.nparams + k := by
          simp [hP]; omega
        rw [hidx, List.getElem?_append_right (by omega), hP, Nat.add_sub_cancel_left]
        simp [List.getElem?_range hk]
      rw [hb] at hocc''
      obtain ⟨Δ', hΓΔ', hwfΔ'⟩ := VExpr.WF.of_occurs_lift henv [] hocc'' hΓΔ ⟨_, hFty⟩
      have hX' : env.IsDefEqU U ((Δ' ++ Δ) ++ Γ) (N.liftN Δ'.length)
          (M.liftN (Δ' ++ Δ).length) := by
        have := hNM.weakN henv.ordered (Ctx.LiftN.zero (Γ := Δ ++ Γ) Δ' rfl)
        rw [List.append_assoc]
        simpa [VExpr.liftN_liftN, Nat.add_comm] using this
      have := (IH k hk).2 (Δ' ++ Δ) hΓ (by rwa [List.append_assoc]) (by omega) hlen hM hX'
        (by rw [List.append_assoc]; exact hwfΔ')
      simpa using this
  have hCty := hargsTy (info.nparams + index) (by omega)
  have ⟨u, hCu⟩ := hCty.isType henv.ordered hΓ
  have hFj := hCu.defeqU_l henv hΓ hW.symm
  -- the sort of the field type agrees with the one in the larger context
  have hR' := hR hΓΔ (F := Fs) (ls' := ls') (args' := args'.map (VExpr.liftN Δ.length))
    (field := (args'[info.nparams + index]'(by omega)).liftN Δ.length)
    (by
      have := IsDefEq.projDF hinfo hL hLlen hP hI hfield hFty hN
        (hNc.of_l henv hΓΔ hN.hasType.1) hclosed hguard
      simpa [VExpr.liftN_mkApps, VExpr.liftN] using this.hasType.2)
    (by simp [hlen]) (by simp [List.getElem?_map, List.getElem?_eq_getElem (show
      info.nparams + index < args'.length by omega)])
  have hFsC := hR'.uniqU henv hΓΔ (hCty.weakN henv.ordered W)
  have hFjFs := (hW.weakN henv.ordered W).trans henv hΓΔ hFsC.symm
  have hFsu := (hFj.weakN henv.ordered W).defeqU_l henv hΓΔ hFjFs
  have hufl : u ≈ fl := IsDefEqU.sort_inv henv hΓΔ
    (by simpa [VExpr.liftN] using hFsu.uniqU henv hΓΔ hFty)
  have hguard' : (info.resultLevel.inst ls').IsNeverZero ∨ u ≈ .zero := by
    rcases hguard with h | h
    · exact .inl (h.of_equiv (VLevel.inst_congr (VLevel.equiv_def'.2 rfl) hLE))
    · exact .inr ((VLevel.equiv_congr_left hufl).2 h)
  have hfieldΓ := VProjectionInfo.fieldType_eq_instOuter info hshape hlen'
    (params := args'.take info.nparams) (by simp; omega) hmd (typeName := S) (major := M)
  have hpM := IsDefEq.projDF hinfo hls' hlen' (by simp; omega) hidx' hfieldΓ hFj
    hMS.hasType.1 hMS.hasType.1 hclosed hguard'
  exact VProjectionInfo.proj_ctorApp_defeq henv hΓ hinfo
    (fun h hk => hR hΓ h hlen hk) (by omega) hM ⟨_, hpM.hasType.1⟩

/-- **Projection of a constructor application.** If `.proj S i (c args)` is well typed at `F`,
where `c` is the registered constructor of `S` with the recorded telescope shape, then the `i`-th
field argument has type `F`. This is the premise `projIota` needs, and the reason the checker's
`reduceProjCore` refines the abstract rule. -/
theorem VProjectionInfo.field_typing_of_ctorApp {decl : VInductDecl}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections S info)
    (hwf : env.IsType info.uvars [] info.ctorType)
    (hctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩)
    (hshape : info.ctorType = VExpr.wrapForalls doms result)
    (hvalid : decl.RawIndAppAt (some S) (doms.length - decl.nparams) result)
    (hhead : result.getAppFnArgs.1 = .const S (VLevel.params decl.uvars))
    (hdn : decl.nparams = info.nparams) (hdu : decl.uvars = info.uvars)
    (hle : info.nparams ≤ doms.length) :
    ∀ (index : Nat) {F field : VExpr},
      env.HasType U Γ (.proj S index (VExpr.mkApps (.const info.ctorName ls') args')) F →
      args'.length = doms.length → args'[info.nparams + index]? = some field →
      env.HasType U Γ field F := fun index =>
  (VProjectionInfo.field_typing_aux henv hinfo hwf hctor hshape hvalid hhead hdn hdu hle
    index).1 hΓ

/-- Congruence along an application spine typed against a wrapped telescope. -/
theorem IsDefEq.mkApps_congr :
    ∀ {args args' : List VExpr} {f f' : VExpr} {doms : List VExpr} {body : VExpr},
      env.IsDefEq U Γ f f' (VExpr.wrapForalls doms body) → args.length = doms.length →
      args.length = args'.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length) (hj'' : j < args'.length),
        env.IsDefEq U Γ args[j] args'[j] (doms[j].instOuter (args.take j))) →
      env.IsDefEq U Γ (VExpr.mkApps f args) (VExpr.mkApps f' args') (body.instOuter args) := by
  intro args
  induction args with
  | nil =>
    intro args' f f' doms body hf hlen hlen' _
    cases doms with
    | nil =>
      cases args' with
      | nil => simpa [VExpr.mkApps, VExpr.wrapForalls] using hf
      | cons => simp at hlen'
    | cons => simp at hlen
  | cons a as ih =>
    intro args' f f' doms body hf hlen hlen' hargs
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      cases args' with
      | nil => simp at hlen'
      | cons a' as' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen hlen'
        have hf' : env.IsDefEq U Γ f f' (.forallE d (VExpr.wrapForalls ds body)) := hf
        have ha : env.IsDefEq U Γ a a' d := hargs 0 (by simp) (by simp) (by simp)
        have hfa := hf'.appDF ha
        rw [VExpr.wrapForalls_inst] at hfa
        have := ih (args' := as') hfa (by simpa using hlen) hlen' fun j hj hj' hj'' => by
          have := hargs (j + 1) (by simpa using hj) (by simpa using hj') (by simpa using hj'')
          simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
            List.length_take] at this
          have hj0 : j < as.length := by simpa using hj
          rw [Nat.min_eq_left (Nat.le_of_lt hj0)] at this
          simpa [VExpr.instDomains_getElem ds a 0 j (by simpa using hj')] using this
        simpa [VExpr.mkApps, hlen] using this

/-- Domains at the same position of two definitionally equal telescopes, instantiated by
pointwise definitionally equal arguments, are definitionally equal. -/
theorem InstForallsC.domain_defeq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {dl dl₀ : List VExpr} {body body₀ : VExpr} {args' bs : List VExpr} {m : Nat}
    (Hw : InstForallsC env U Γ (VExpr.wrapForalls dl body) args' res)
    (hlen : args'.length = dl.length) (hlen₀ : dl₀.length = dl.length) (hm : m < dl.length)
    (hT : env.IsDefEqU U Γ (VExpr.wrapForalls dl₀ body₀) (VExpr.wrapForalls dl body))
    (hbs : bs.length = m) (hbsE : List.Forall₂ (env.IsDefEqU U Γ) bs (args'.take m)) :
    env.IsDefEqU U Γ ((dl₀[m]'(by omega)).instOuter bs) (dl[m].instOuter (args'.take m)) := by
  rw [VExpr.wrapForalls_split dl body m hm, ← List.take_append_drop m args'] at Hw
  obtain ⟨midR, HwR, _⟩ := Hw.append_inv
  have hmidR := HwR.wrapForalls_eq (by simp; omega)
  rw [VExpr.instOuter_forallE] at hmidR
  rw [VExpr.wrapForalls_split dl₀ body₀ m (by omega), VExpr.wrapForalls_split dl body m hm] at hT
  obtain ⟨midL, HwL, hmid⟩ := InstForallsC.of_defeq henv hΓ HwR hT hbsE (by
    rw [show bs.length = (dl₀.take m).length by simp; omega]
    exact VExpr.takeForalls_wrapForalls _ _)
  have hmidL := HwL.wrapForalls_eq (by simp; omega)
  rw [VExpr.instOuter_forallE] at hmidL
  subst hmidL hmidR
  have ⟨⟨_, hDeq⟩, _⟩ := hmid.forallE_inv henv hΓ
  exact ⟨_, hDeq⟩

end VEnv
end Lean4Lean
