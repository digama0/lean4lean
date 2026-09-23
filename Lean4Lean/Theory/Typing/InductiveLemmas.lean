import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
namespace VEnv

/-!
# Environment-extension lemmas for `VEnv.addInduct`

`addInduct_le` (adding an inductive only grows the environment) and `addInduct_pat` (every
recursor rule's ι rule ends up in `pats`), threaded through the stages `addTypes`/`addCtors`/
`addRecs`/`addRules` (`addInduct_stages`); `addInduct_WF` (adding a well-formed inductive
keeps the environment `Ordered`), proved stage by stage from `VInductDecl.WF`; and the
population lemmas saying what each stage binds in `constants` and registers in `pats`.
Subject reduction of the registered ι rules is the open `VEnv.WF.patsStrong` (`EnvLemmas.lean`).
-/

/-- Monotonicity of a monadic left fold in the `Option` monad: if each successful
step only grows the environment, then so does the whole fold. -/
theorem foldlM_le {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e x e'}, f e x = some e' → e ≤ e') :
    ∀ {l : List α} {init r}, l.foldlM f init = some r → init ≤ r
  | [], init, r, h => by simp [List.foldlM] at h; exact h ▸ .rfl
  | _ :: _, init, r, h => by
    simp only [List.foldlM] at h
    obtain ⟨_, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (hf h1).trans (foldlM_le hf h2)

/-- Registering one ι rule only grows the environment. -/
theorem addRecRule_le {env env' : VEnv} {r ru}
    (h : env.addRecRule r ru = some env') : env ≤ env' := by
  unfold addRecRule at h
  split at h
  · cases h; exact addPat_le
  · cases h

/-- Registering the ι rule of recursor rule `ru` (of recursor `r`) makes exactly
that rule present in the resulting environment's `pats`. -/
theorem addRecRule_pats {env env' : VEnv} {r ru} (hclosed : ru.rhs.Closed)
    (h : env.addRecRule r ru = some env') :
    env'.pats
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hclosed,
        .true) := by
  unfold addRecRule at h
  rw [dif_pos hclosed] at h
  cases h
  exact addPat_self

/-! ### The stages -/

/-- Adding the type formers only grows the environment. -/
theorem addTypes_le {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addTypes env = some env') : env ≤ env' :=
  foldlM_le (fun hh => addConst_le hh) h

/-- Adding the constructors only grows the environment. -/
theorem addCtors_le {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addCtors env = some env') : env ≤ env' :=
  foldlM_le (fun hh => addConst_le hh) h

/-- Adding the recursors only grows the environment. -/
theorem addRecs_le {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRecs env = some env') : env ≤ env' :=
  foldlM_le (fun hh => addConst_le hh) h

/-- Registering the ι rules only grows the environment. -/
theorem addRules_le {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRules env = some env') : env ≤ env' :=
  foldlM_le (fun hh => foldlM_le (fun hh2 => addRecRule_le hh2) hh) h

/-- A successful `addInduct` decomposes into its four successful stages. -/
theorem addInduct_stages {env env' : VEnv} {decl : VInductDecl}
    (h : env.addInduct decl = some env') :
    ∃ envT envC envR, decl.addTypes env = some envT ∧ decl.addCtors envT = some envC ∧
      decl.addRecs envC = some envR ∧ decl.addRules envR = some env' := by
  unfold addInduct at h
  obtain ⟨envR, hR, hP⟩ := Option.bind_eq_some_iff.1 h
  unfold VInductDecl.addTypesCtorsRecs at hR
  obtain ⟨envC, hC', hRec⟩ := Option.bind_eq_some_iff.1 hR
  unfold VInductDecl.addTypesCtors at hC'
  obtain ⟨envT, hT, hC⟩ := Option.bind_eq_some_iff.1 hC'
  exact ⟨envT, envC, envR, hT, hC, hRec, hP⟩

/-- Adding an inductive declaration only grows the environment. -/
theorem addInduct_le {env env' : VEnv} {decl} (h : env.addInduct decl = some env') :
    env ≤ env' := by
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := addInduct_stages h
  exact (addTypes_le hT).trans <| (addCtors_le hC).trans <| (addRecs_le hR).trans (addRules_le hP)

/-- If some `x ∈ l` yields a `P` under a successful step, `P` is `≤`-monotone, and
every step only grows the environment, then the fold result satisfies `P`. Used to
carry a freshly-registered `pat` through the rest of a `foldlM`. -/
theorem foldlM_mono_of_mem {α} {f : VEnv → α → Option VEnv} {P : VEnv → Prop} {x : α}
    (hf : ∀ {e a e'}, f e a = some e' → e ≤ e')
    (hmono : ∀ {e e'}, e ≤ e' → P e → P e')
    (hstep : ∀ {e e'}, f e x = some e' → P e')
    {l : List α} (hx : x ∈ l) {init final} (hfold : l.foldlM f init = some final) : P final := by
  induction l generalizing init with
  | nil => nomatch hx
  | cons a as ih =>
    simp only [List.foldlM] at hfold
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 hfold
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact hmono (foldlM_le hf h2) (hstep h1)
    · exact ih hx' h2

/-- After `addRules`, the ι-reduction rule for every recursor rule `ru ∈ r.rules`
(with `r ∈ decl.recs` and `ru.rhs` closed) is present in `env'.pats`. -/
theorem addRules_pat {env env' : VEnv} {decl : VInductDecl} {r ru}
    (hr : r ∈ decl.recs) (hru : ru ∈ r.rules) (hclosed : ru.rhs.Closed)
    (h : decl.addRules env = some env') :
    env'.pats
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hclosed,
        .true) := by
  unfold VInductDecl.addRules at h
  refine foldlM_mono_of_mem (x := r)
    (f := fun e r => List.foldlM (fun e ru => e.addRecRule r ru) e r.rules)
    (fun hh => foldlM_le (fun hh2 => addRecRule_le hh2) hh)
    (fun le hp => le.pats hp)
    (fun {e e'} hh => ?_)
    hr h
  exact foldlM_mono_of_mem (x := ru) (f := fun e u => e.addRecRule r u)
    (fun hh2 => addRecRule_le hh2)
    (fun le hp => le.pats hp)
    (fun hh2 => addRecRule_pats hclosed hh2)
    hru hh

/-- After `addInduct`, the ι-reduction rule for every recursor rule `ru ∈ r.rules`
(with `r ∈ decl.recs` and `ru.rhs` closed) is present in `env'.pats`. -/
theorem addInduct_pat {env env' : VEnv} {decl : VInductDecl} {r ru}
    (hr : r ∈ decl.recs) (hru : ru ∈ r.rules) (hclosed : ru.rhs.Closed)
    (h : env.addInduct decl = some env') :
    env'.pats
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hclosed,
        .true) := by
  obtain ⟨_, _, _, _, _, _, hP⟩ := addInduct_stages h
  exact addRules_pat hr hru hclosed hP

/-! ### Orderedness of the stages -/

/-- A predicate preserved by every successful step of a monadic left fold in the
`Option` monad is preserved by the whole fold. -/
theorem foldlM_inv {α} {f : VEnv → α → Option VEnv} {P : VEnv → Prop} :
    ∀ {l : List α} {init final}, (∀ a ∈ l, ∀ {e e'}, P e → f e a = some e' → P e') →
      P init → l.foldlM f init = some final → P final
  | [], _, _, _, hinit, h => by simp [List.foldlM] at h; exact h ▸ hinit
  | a :: as, _, _, hstep, hinit, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact foldlM_inv (fun a ha => hstep a (.tail _ ha)) (hstep a (.head _) hinit h1) h2

/-- Adding a list of constants, each well-formed in the initial environment, keeps the
environment `Ordered`. Generalises `addConsts_ordered` to any fold over `addConst`. -/
theorem foldlM_addConst_ordered {α} {nm : α → Name} {ci : α → VConstant}
    {l : List α} {init final : VEnv} (hord : Ordered init) (hwf : ∀ a ∈ l, (ci a).WF init)
    (h : l.foldlM (fun e a => e.addConst (nm a) (ci a)) init = some final) : Ordered final :=
  (foldlM_inv (P := fun e => Ordered e ∧ init ≤ e)
    (fun a ha _ _ ⟨hord, hle⟩ hstep =>
      ⟨.const hord ((hwf a ha).mono hle) hstep, hle.trans (addConst_le hstep)⟩)
    ⟨hord, .rfl⟩ h).1

/-- Stage 0 keeps the environment `Ordered` (`types_wf`). -/
theorem addTypes_ordered {env envT : VEnv} {decl : VInductDecl}
    (henv : Ordered env) (hdecl : decl.WF env) (h : decl.addTypes env = some envT) :
    Ordered envT :=
  foldlM_addConst_ordered henv hdecl.types_wf h

/-- Stage 1 keeps the environment `Ordered` (`ctors_wf`, in the stage-0 environment). -/
theorem addCtors_ordered {env envT envC : VEnv} {decl : VInductDecl}
    (hdecl : decl.WF env) (hT : decl.addTypes env = some envT) (hordT : Ordered envT)
    (hC : decl.addCtors envT = some envC) : Ordered envC :=
  foldlM_addConst_ordered hordT (fun c hc => by
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
    exact hdecl.ctors_wf envT hT t ht c hc) hC

/-- Stage 2 keeps the environment `Ordered` (`recs_wf`, in the stage-1 environment). -/
theorem addRecs_ordered {env envC envR : VEnv} {decl : VInductDecl}
    (hdecl : decl.WF env) (hC : decl.addTypesCtors env = some envC) (hordC : Ordered envC)
    (hR : decl.addRecs envC = some envR) : Ordered envR :=
  foldlM_addConst_ordered hordC (hdecl.recs_wf envC hC) hR

/-- Stages 0–1 keep the environment `Ordered`. -/
theorem addTypesCtors_ordered {env envC : VEnv} {decl : VInductDecl}
    (henv : Ordered env) (hdecl : decl.WF env) (h : decl.addTypesCtors env = some envC) :
    Ordered envC := by
  obtain ⟨envT, hT, hC⟩ := Option.bind_eq_some_iff.1 h
  exact addCtors_ordered hdecl hT (addTypes_ordered henv hdecl hT) hC

/-- Stages 0–2 keep the environment `Ordered`. -/
theorem addTypesCtorsRecs_ordered {env envR : VEnv} {decl : VInductDecl}
    (henv : Ordered env) (hdecl : decl.WF env) (h : decl.addTypesCtorsRecs env = some envR) :
    Ordered envR := by
  obtain ⟨envC, hC, hR⟩ := Option.bind_eq_some_iff.1 h
  exact addRecs_ordered hdecl hC (addTypesCtors_ordered henv hdecl hC) hR

/-- Stage 3 keeps the environment `Ordered`: every registration is an `Ordered.pat`
step, whose `VEnv.PatWF` is `VInductDecl.WF.rules_wf` (the typing, stated at `envR` and
carried to the environment reached so far by `PatTyped.mono`) together with the template
shape of the reduct (`rule_shape`: the template is a λ-abstraction, so `iotaRHS` is
`TemplateHeaded`). -/
theorem addRules_ordered {env envR env' : VEnv} {decl : VInductDecl}
    (hdecl : decl.WF env) (hR : decl.addTypesCtorsRecs env = some envR) (hordR : Ordered envR)
    (hP : decl.addRules envR = some env') : Ordered env' := by
  unfold VInductDecl.addRules at hP
  refine (foldlM_inv (P := fun e => Ordered e ∧ envR ≤ e) (fun r hr _ _ hPe hfold => ?_)
    ⟨hordR, .rfl⟩ hP).1
  refine foldlM_inv (P := fun e => Ordered e ∧ envR ≤ e) (fun ru hru _ _ ⟨hord, hle⟩ h => ?_)
    hPe hfold
  unfold addRecRule at h
  split at h
  · cases h
    obtain ⟨j, hj, _, _, _, _, hshape⟩ := hdecl.rule_shape r hr ru hru
    exact ⟨.pat hord ⟨(hdecl.rules_wf envR hR r hr ru hru ‹_›).mono hle,
      SimplePattern.iotaRHS_templateHeaded (hshape.lam hj) _⟩, hle.trans addPat_le⟩
  · cases h

/-- Soundness of `addInduct`: extending an `Ordered` environment with a well-formed
inductive declaration keeps it `Ordered`. The constant stages follow from the staged
`VInductDecl.WF` (`types_wf`/`ctors_wf`/`recs_wf`); the ι-rule stage from `Ordered.pat`
and `rules_wf`. -/
theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' := by
  obtain ⟨envR, hR, hP⟩ := Option.bind_eq_some_iff.1 henv'
  exact addRules_ordered hdecl hR (addTypesCtorsRecs_ordered henv hdecl hR) hP

/-! ## Environment-population lemmas

The stage-by-stage bookkeeping of `addInduct` seen through `constants` and `pats`:
what each stage leaves untouched (`env.pats` is populated only by `addRecRule`, which
installs `SimplePattern.iota`-shaped patterns; the other extensions leave it
untouched), which names it binds (fresh, to exactly the declared constant, without
duplicates), and the origin of every registered pattern entry
(`addInduct_pats_origin'`: an old one, or exactly the ι entry of one recursor rule).
These are the facts the front-end refinement (`Verify/Environment`) derives its
`AddInduct` theorems from, so they live here rather than in `InductiveParams`. -/

/-- `addConst` leaves `pats` unchanged. -/
theorem addConst_pats {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.pats = env.pats := by
  rw [VEnv.addConst] at h; split at h
  · simp at h
  · injection h with h; subst h; rfl

/-- `addConst` leaves `defeqs` unchanged. -/
theorem addConst_defeqs {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.defeqs = env.defeqs := by
  rw [VEnv.addConst] at h; split at h
  · simp at h
  · injection h with h; subst h; rfl

/-- `addDefEq` leaves `pats` unchanged. -/
theorem addDefEq_pats {env : VEnv} {df} : (env.addDefEq df).pats = env.pats := rfl

/-- `addConsts` (a block of `addConst`s) leaves `pats` unchanged. -/
theorem addConsts_pats {env env' : VEnv} : ∀ {cis},
    env.addConsts cis = some env' → env'.pats = env.pats
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConsts_pats h2).trans (addConst_pats h1)

/-- `addConsts` (a block of `addConst`s) leaves `defeqs` unchanged. -/
theorem addConsts_defeqs {env env' : VEnv} : ∀ {cis},
    env.addConsts cis = some env' → env'.defeqs = env.defeqs
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConsts_defeqs h2).trans (addConst_defeqs h1)

/-- `addDefEqs` (a block of `addDefEq`s) leaves `pats` unchanged. -/
theorem addDefEqs_pats : ∀ {cis : List VDefVal} {env : VEnv}, (env.addDefEqs cis).pats = env.pats
  | [], _ => rfl
  | ci :: cis, env => by
    show ((env.addDefEq ci.toDefEq).addDefEqs cis).pats = env.pats
    rw [addDefEqs_pats, addDefEq_pats]

/-- `addDefEqs` (a block of `addDefEq`s) only grows the environment. -/
theorem addDefEqs_le : ∀ {cis : List VDefVal} {env : VEnv}, env ≤ env.addDefEqs cis
  | [], _ => .rfl
  | ci :: cis, env => by
    show env ≤ (env.addDefEq ci.toDefEq).addDefEqs cis
    exact addDefEq_le.trans addDefEqs_le

/-- `addQuot` (a chain of `addConst`s and one `addDefEq`) leaves `pats` unchanged. -/
theorem addQuot_pats {env env' : VEnv} (h : env.addQuot = some env') : env'.pats = env.pats := by
  rw [VEnv.addQuot] at h
  obtain ⟨e1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e3, s3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e4, s4, h⟩ := Option.bind_eq_some_iff.1 h
  injection h with h; subst h
  rw [addDefEq_pats, addConst_pats s4, addConst_pats s3, addConst_pats s2, addConst_pats s1]

/-- A `foldlM` whose every step preserves `pats` preserves `pats`. -/
theorem foldlM_pats_preserved {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e a e'}, f e a = some e' → e'.pats = e.pats) :
    ∀ {l : List α} {init env' : VEnv}, l.foldlM f init = some env' → env'.pats = init.pats
  | [], _, _, h => by simp [List.foldlM] at h; exact h ▸ rfl
  | _ :: _, _, _, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h; rw [foldlM_pats_preserved hf h2, hf h1]

/-- A `foldlM` whose every step preserves `defeqs` preserves `defeqs`. -/
theorem foldlM_defeqs_preserved {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e a e'}, f e a = some e' → e'.defeqs = e.defeqs) :
    ∀ {l : List α} {init env' : VEnv}, l.foldlM f init = some env' → env'.defeqs = init.defeqs
  | [], _, _, h => by simp [List.foldlM] at h; exact h ▸ rfl
  | _ :: _, _, _, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [foldlM_defeqs_preserved hf h2, hf h1]

/-- Full specification of a successful `addConst`: the name was fresh, is now bound
to `ci`, and no other name changed. -/
theorem addConst_eq {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env.constants n = none ∧ env'.constants n = some ci ∧
    ∀ m, n ≠ m → env'.constants m = env.constants m := by
  rw [VEnv.addConst] at h; split at h
  · simp at h
  · rename_i hnone; injection h with h; subst h; exact ⟨hnone, by simp, fun m hm => by simp [hm]⟩

/-- In a successful `addConst` fold, every registered name was fresh w.r.t. the
starting environment. -/
theorem addConst_foldlM_fresh {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ a ∈ l, init.constants (nm a) = none
  | [], _, _, _, _, ha => by cases ha
  | b :: bs, init, final, h, a, ha => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hfresh_b, hspec_b, hother_b⟩ := addConst_eq h1
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact hfresh_b
    · have hrec := addConst_foldlM_fresh h2 a ha'
      by_cases hnn : nm b = nm a
      · rw [← hnn, hspec_b] at hrec; simp at hrec
      · rwa [hother_b (nm a) hnn] at hrec

/-- Two `addConst` steps commute: their names are distinct (the second name was fresh
after the first step), and `VEnv.addConst` only sets that name. -/
theorem addConst_comm {env e₁ e₂ : VEnv} {n₁ n₂ : Name} {c₁ c₂ : VConstant}
    (h₁ : env.addConst n₁ c₁ = some e₁) (h₂ : e₁.addConst n₂ c₂ = some e₂) :
    ∃ e₁', env.addConst n₂ c₂ = some e₁' ∧ e₁'.addConst n₁ c₁ = some e₂ := by
  obtain ⟨hf₁, hs₁, ho₁⟩ := addConst_eq h₁
  obtain ⟨hf₂, hs₂, ho₂⟩ := addConst_eq h₂
  have hne : n₁ ≠ n₂ := fun h => by subst h; rw [hs₁] at hf₂; cases hf₂
  have hf₂' : env.constants n₂ = none := by rw [← ho₁ n₂ hne]; exact hf₂
  unfold VEnv.addConst at h₁ h₂ ⊢
  rw [hf₁] at h₁; injection h₁ with h₁; subst h₁
  rw [hf₂] at h₂; injection h₂ with h₂; subst h₂
  rw [hf₂']
  refine ⟨_, rfl, ?_⟩
  simp only [if_neg hne.symm, hf₁, Option.some.injEq]
  refine VEnv.ext (funext fun n => ?_) rfl rfl
  simp only
  by_cases e₁ : n₁ = n <;> by_cases e₂ : n₂ = n <;> simp [e₁, e₂]
  exact absurd (e₁.trans e₂.symm) hne

/-- The result of a successful `addConst` fold does not depend on the order of the list. -/
theorem addConst_foldlM_perm {α} {nm : α → Name} {ci : α → VConstant} {l l' : List α}
    (hp : l.Perm l') : ∀ {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      l'.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final := by
  induction hp with
  | nil => exact id
  | cons x _ ih =>
    intro init final h
    simp only [List.foldlM] at h ⊢
    obtain ⟨e, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2 ⟨e, h1, ih h2⟩
  | swap x y l =>
    intro init final h
    simp only [List.foldlM] at h ⊢
    obtain ⟨e₁, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e₂, h2, h3⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e₁', h1', h2'⟩ := addConst_comm h1 h2
    exact Option.bind_eq_some_iff.2 ⟨e₁', h1', Option.bind_eq_some_iff.2 ⟨e₂, h2', h3⟩⟩
  | trans _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)

/-- A constant bound after a successful `addConst` fold was bound before, or is one of the
fold's constants under its own name. -/
theorem addConst_foldlM_constants_inv {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ {n c}, final.constants n = some c →
        init.constants n = some c ∨ ∃ a ∈ l, nm a = n ∧ ci a = c
  | [], _, _, h, _, _, hc => by simp [List.foldlM] at h; exact .inl (h ▸ hc)
  | b :: bs, init, final, h, n, c, hc => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rcases addConst_foldlM_constants_inv h2 hc with hc1 | ⟨a, ha, hn, hca⟩
    · obtain ⟨_, hs, ho⟩ := addConst_eq h1
      by_cases hnb : nm b = n
      · subst hnb; rw [hs] at hc1; cases hc1; exact .inr ⟨b, .head _, rfl, rfl⟩
      · rw [ho n hnb] at hc1; exact .inl hc1
    · exact .inr ⟨a, .tail _ ha, hn, hca⟩

/-- Stages 0–2 are one `addConst` fold over `VInductDecl.consts`. -/
theorem _root_.Lean4Lean.VInductDecl.addTypesCtorsRecs_eq (decl : VInductDecl) (env : VEnv) :
    decl.addTypesCtorsRecs env =
      decl.consts.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) env := by
  simp only [VInductDecl.addTypesCtorsRecs, VInductDecl.addTypesCtors, VInductDecl.addTypes,
    VInductDecl.consts, List.foldlM_append, List.foldlM_map]
  rfl

/-- In a successful `addConst` fold, every registered name is bound, in the result,
to exactly the constant it was registered with. -/
theorem addConst_foldlM_find {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ a ∈ l, final.constants (nm a) = some (ci a)
  | [], _, _, _, _, ha => by cases ha
  | b :: bs, init, final, h, a, ha => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, hspec_b, _⟩ := addConst_eq h1
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact (foldlM_le (fun hh => addConst_le hh) h2).constants hspec_b
    · exact addConst_foldlM_find h2 a ha'

/-- In a successful `addConst` fold, the naming function is injective on the list:
two elements with the same name coincide. -/
theorem addConst_foldlM_inj {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ a ∈ l, ∀ b ∈ l, nm a = nm b → a = b
  | [], _, _, _, _, ha, _, _, _ => by cases ha
  | c :: cs, init, final, h, a, ha, b, hb, hab => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, hspec_c, _⟩ := addConst_eq h1
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exfalso; have := addConst_foldlM_fresh h2 b hb'; rw [← hab, hspec_c] at this; simp at this
    · exfalso; have := addConst_foldlM_fresh h2 a ha'; rw [hab, hspec_c] at this; simp at this
    · exact addConst_foldlM_inj h2 a ha' b hb' hab

/-- A `Nodup` image determines its preimage: `f` is injective on a list whose `f`-image
has no duplicates. -/
theorem nodup_map_inj_on {α β} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, _, ha, _, _, _ => by cases ha
  | c :: cs, h, a, ha, b, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hnot, hcs⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (hab ▸ List.mem_map_of_mem hb') hnot
    · exact absurd (hab.symm ▸ List.mem_map_of_mem ha') hnot
    · exact nodup_map_inj_on hcs a ha' b hb' hab

/-- Adding quotient constants only grows the environment. -/
theorem addQuot_le {env env' : VEnv} (h : env.addQuot = some env') : env ≤ env' := by
  rw [VEnv.addQuot] at h
  obtain ⟨e1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e3, s3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e4, s4, h⟩ := Option.bind_eq_some_iff.1 h
  injection h with h; subst h
  exact (addConst_le s1).trans <| (addConst_le s2).trans <| (addConst_le s3).trans <|
    (addConst_le s4).trans addDefEq_le

/-! ### The stages of `addInduct`, seen through `pats` and `constants` -/

/-- `addTypes` leaves `pats` unchanged. -/
theorem addTypes_pats {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addTypes env = some env') : env'.pats = env.pats := by
  unfold VInductDecl.addTypes at h; exact foldlM_pats_preserved (fun hh => addConst_pats hh) h

/-- `addCtors` leaves `pats` unchanged. -/
theorem addCtors_pats {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addCtors env = some env') : env'.pats = env.pats := by
  unfold VInductDecl.addCtors at h; exact foldlM_pats_preserved (fun hh => addConst_pats hh) h

/-- `addRecs` leaves `pats` unchanged. -/
theorem addRecs_pats {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRecs env = some env') : env'.pats = env.pats := by
  unfold VInductDecl.addRecs at h; exact foldlM_pats_preserved (fun hh => addConst_pats hh) h

/-- `addTypes` leaves `defeqs` unchanged. -/
theorem addTypes_defeqs {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addTypes env = some env') : env'.defeqs = env.defeqs := by
  unfold VInductDecl.addTypes at h
  exact foldlM_defeqs_preserved (fun hh => addConst_defeqs hh) h

/-- `addCtors` leaves `defeqs` unchanged. -/
theorem addCtors_defeqs {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addCtors env = some env') : env'.defeqs = env.defeqs := by
  unfold VInductDecl.addCtors at h
  exact foldlM_defeqs_preserved (fun hh => addConst_defeqs hh) h

/-- `addRecs` leaves `defeqs` unchanged. -/
theorem addRecs_defeqs {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRecs env = some env') : env'.defeqs = env.defeqs := by
  unfold VInductDecl.addRecs at h
  exact foldlM_defeqs_preserved (fun hh => addConst_defeqs hh) h

/-- Registering one ι rule leaves `defeqs` unchanged. -/
theorem addRecRule_defeqs {env env' : VEnv} {r ru}
    (h : env.addRecRule r ru = some env') : env'.defeqs = env.defeqs := by
  unfold addRecRule at h
  split at h
  · cases h; rfl
  · cases h

/-- `addRules` leaves `defeqs` unchanged. -/
theorem addRules_defeqs {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRules env = some env') : env'.defeqs = env.defeqs := by
  unfold VInductDecl.addRules at h
  exact foldlM_defeqs_preserved
    (fun hh => foldlM_defeqs_preserved (fun hh2 => addRecRule_defeqs hh2) hh) h

/-- `addInduct` leaves `defeqs` unchanged: an inductive block contributes constants and ι
rules, never a definitional axiom. -/
theorem addInduct_defeqs {env env' : VEnv} {decl : VInductDecl}
    (h : env.addInduct decl = some env') : env'.defeqs = env.defeqs := by
  obtain ⟨_, _, _, hT, hC, hR, hP⟩ := addInduct_stages h
  rw [addRules_defeqs hP, addRecs_defeqs hR, addCtors_defeqs hC, addTypes_defeqs hT]

/-- After `addTypes`, every type former of `decl` is bound to its constant. -/
theorem addTypes_find {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addTypes env = some env') :
    ∀ t ∈ decl.types, env'.constants t.name = some t.toVConstVal.toVConstant := by
  unfold VInductDecl.addTypes at h; exact addConst_foldlM_find h

/-- Every constructor of `decl` is fresh w.r.t. the environment `addCtors` starts from. -/
theorem addCtors_fresh {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addCtors env = some env') :
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env.constants c.name = none := by
  unfold VInductDecl.addCtors at h
  exact fun t ht c hc => addConst_foldlM_fresh h c (List.mem_flatMap.2 ⟨t, ht, hc⟩)

/-- After `addCtors`, every constructor of `decl` is bound to its constant. -/
theorem addCtors_find {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addCtors env = some env') :
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env'.constants c.name = some c.toVConstant := by
  unfold VInductDecl.addCtors at h
  exact fun t ht c hc => addConst_foldlM_find h c (List.mem_flatMap.2 ⟨t, ht, hc⟩)

/-- Every recursor of `decl` is fresh w.r.t. the environment `addRecs` starts from. -/
theorem addRecs_fresh {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRecs env = some env') : ∀ r ∈ decl.recs, env.constants r.name = none := by
  unfold VInductDecl.addRecs at h; exact addConst_foldlM_fresh h

/-- After `addRecs`, every recursor of `decl` is bound to its constant. -/
theorem addRecs_find {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRecs env = some env') :
    ∀ r ∈ decl.recs, env'.constants r.name = some r.toVConstVal.toVConstant := by
  unfold VInductDecl.addRecs at h; exact addConst_foldlM_find h

/-- Recursor names within one `decl` are distinct. -/
theorem addRecs_name_inj {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRecs env = some env') :
    ∀ ra ∈ decl.recs, ∀ rb ∈ decl.recs, ra.name = rb.name → ra = rb := by
  unfold VInductDecl.addRecs at h; exact addConst_foldlM_inj h

/-! ### Origin of a registered pattern

A pattern present after `addRecRule`/`addInduct` is either an old one or exactly the
ι entry of one recursor rule: the `∃ hc e, e ▸ rr = …` witness is the entry form of
`VEnv.addPat` itself, so the reduct `rr` is pinned to `SimplePattern.iotaRHS` and not
only the key to `SimplePattern.iota`. -/

/-- A pattern entry present after one `addRecRule` is either an old one or exactly this
rule's ι entry. -/
theorem addRecRule_pats_inv' {env env' : VEnv} {r ru p rr}
    (h : env.addRecRule r ru = some env') (hp : env'.pats p rr) :
    env.pats p rr ∨
    ∃ (hc : ru.rhs.Closed)
      (e : p = (SimplePattern.iota r.name r.getMajorIdx ru.ctor
        (ru.ctorParams + ru.nfields)).toPattern),
      e ▸ rr = (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true) := by
  unfold addRecRule at h; split at h
  · cases h; rcases hp with ⟨e, he⟩ | hp
    · exact .inr ⟨‹_›, e, he⟩
    · exact .inl hp
  · cases h

/-- Membership-tracking pattern inversion for a `foldlM`: a pattern entry present after
the fold is either present at the start or produced (with witness `a ∈ l`) by some step. -/
theorem foldlM_pats_inv_mem {α} {f : VEnv → α → Option VEnv}
    {motive : α → (p : Pattern) → p.RHS × p.Check → Prop} {p rr} :
    ∀ {l : List α} {init final : VEnv},
      (∀ {e a e'}, a ∈ l → f e a = some e' → e'.pats p rr → e.pats p rr ∨ motive a p rr) →
      l.foldlM f init = some final → final.pats p rr → init.pats p rr ∨ ∃ a ∈ l, motive a p rr
  | [], _, _, _, h, hp => by simp [List.foldlM] at h; exact .inl (h ▸ hp)
  | a :: as, init, final, hf, h, hp => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rcases foldlM_pats_inv_mem (f := f) (motive := motive) (l := as)
        (fun {e a' e'} hm => hf (List.mem_cons_of_mem _ hm)) h2 hp with hp1 | ⟨a', ha', hm⟩
    · rcases hf (List.mem_cons_self ..) h1 hp1 with hp0 | hm0
      · exact .inl hp0
      · exact .inr ⟨a, List.mem_cons_self .., hm0⟩
    · exact .inr ⟨a', List.mem_cons_of_mem _ ha', hm⟩

/-- Origin of a pattern entry after `addInduct`: it is either old, or exactly the ι
entry of some recursor rule `ru ∈ rec.rules` with `rec ∈ decl.recs` — key
`SimplePattern.iota` and reduct `SimplePattern.iotaRHS`, both read off `rec`/`ru`. -/
theorem addInduct_pats_origin' {env env' : VEnv} {decl : VInductDecl} {p rr}
    (h : env.addInduct decl = some env') (hp : env'.pats p rr) :
    env.pats p rr ∨ ∃ rec ∈ decl.recs, ∃ ru ∈ rec.rules, ∃ (hc : ru.rhs.Closed)
      (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
        (ru.ctorParams + ru.nfields)).toPattern),
      e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
        rec.numParams rec.numMotives rec.numMinors rec.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true) := by
  obtain ⟨env1, env2, env3, s1, s2, s3, s4⟩ := addInduct_stages h
  unfold VInductDecl.addRules at s4
  rcases foldlM_pats_inv_mem
      (motive := fun (rec : VRecursor) (p : Pattern) (rr : p.RHS × p.Check) => ∃ ru ∈ rec.rules,
        ∃ (hc : ru.rhs.Closed)
          (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
            (ru.ctorParams + ru.nfields)).toPattern),
          e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
            rec.numParams rec.numMotives rec.numMinors rec.numIndices
            ru.ctorParams ru.nfields ru.rhs hc, .true))
      (fun {e rec e'} _ hstep hpp =>
        foldlM_pats_inv_mem
          (motive := fun (ru : VRecRule) (p : Pattern) (rr : p.RHS × p.Check) =>
            ∃ (hc : ru.rhs.Closed)
              (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
                (ru.ctorParams + ru.nfields)).toPattern),
              e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
                rec.numParams rec.numMotives rec.numMinors rec.numIndices
                ru.ctorParams ru.nfields ru.rhs hc, .true))
          (fun {e2 ru e2'} _ hstep2 hpp2 => addRecRule_pats_inv' hstep2 hpp2) hstep hpp)
      s4 hp with hk | horigin
  · rw [addRecs_pats s3, addCtors_pats s2, addTypes_pats s1] at hk; exact .inl hk
  · exact .inr horigin

/-- Origin of a pattern after `addInduct`: it is either old, or the ι redex of some
recursor rule `ru ∈ rec.rules` with `rec ∈ decl.recs`, with recursor name/arity and
constructor pinned to that rule. -/
theorem addInduct_pats_origin {env env' : VEnv} {decl : VInductDecl} {p rr}
    (h : env.addInduct decl = some env') (hp : env'.pats p rr) :
    env.pats p rr ∨ ∃ rec ∈ decl.recs, ∃ ru ∈ rec.rules,
      p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
            (ru.ctorParams + ru.nfields)).toPattern := by
  rcases addInduct_pats_origin' h hp with hold | ⟨rec, hrec, ru, hru, _, e, _⟩
  · exact .inl hold
  · exact .inr ⟨rec, hrec, ru, hru, e⟩

/-! ### The constants of `addInduct`, threaded through the stages -/

/-- A recursor of `decl` is fresh w.r.t. `env` (its name is not already registered). -/
theorem addInduct_rec_fresh {env env' : VEnv} {decl : VInductDecl} {rec}
    (h : env.addInduct decl = some env') (hrec : rec ∈ decl.recs) :
    env.constants rec.name = none := by
  obtain ⟨env1, env2, env3, s1, s2, s3, s4⟩ := addInduct_stages h
  have hfresh : env2.constants rec.name = none := addRecs_fresh s3 rec hrec
  have hle : env ≤ env2 := (addTypes_le s1).trans (addCtors_le s2)
  cases hnn : env.constants rec.name with
  | none => rfl
  | some c => rw [hle.constants hnn] at hfresh; simp at hfresh

/-- A recursor of `decl` is bound to its constant in the resulting environment. -/
theorem addInduct_rec_find {env env' : VEnv} {decl : VInductDecl} {rec}
    (h : env.addInduct decl = some env') (hrec : rec ∈ decl.recs) :
    env'.constants rec.name = some rec.toVConstVal.toVConstant := by
  obtain ⟨env1, env2, env3, s1, s2, s3, s4⟩ := addInduct_stages h
  exact (addRules_le s4).constants (addRecs_find s3 rec hrec)

/-- Recursor names within one `decl` are distinct: two recursors sharing a name coincide. -/
theorem addInduct_recs_name_inj {env env' : VEnv} {decl : VInductDecl} {ra rb}
    (h : env.addInduct decl = some env') (hra : ra ∈ decl.recs) (hrb : rb ∈ decl.recs)
    (hname : ra.name = rb.name) : ra = rb := by
  obtain ⟨env1, env2, env3, s1, s2, s3, s4⟩ := addInduct_stages h
  exact addRecs_name_inj s3 ra hra rb hrb hname

/-- The constructor a rule of a well-formed `decl` fires on is one of the block's own
(`VInductDecl.WF.rules_ctor`), hence registered in the stage-1 environment with a type of
`CtorShape (ru.ctorParams + ru.nfields)`. -/
theorem _root_.Lean4Lean.VInductDecl.WF.rules_ctor_shape {env : VEnv} {decl : VInductDecl}
    (hwf : decl.WF env) : ∀ envC, decl.addTypesCtors env = some envC →
      ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ ci, envC.constants ru.ctor = some ci ∧
        ci.type.CtorShape (ru.ctorParams + ru.nfields) := by
  intro envC hC r hr ru hru
  obtain ⟨env1, s1, s2⟩ := Option.bind_eq_some_iff.1 hC
  obtain ⟨t, ht, -, c, hc, hname, hnp, hres⟩ := hwf.rules_ctor r hr ru hru
  refine ⟨c.toVConstant, ?_, ?_⟩
  · rw [hname]; exact addCtors_find s2 t ht c hc
  · rw [hnp]; exact hres.ctorShape

/-- The constructor a rule of a well-formed `decl` fires on is registered in the
resulting environment, with a type of `CtorShape (ru.ctorParams + ru.nfields)`
(`VInductDecl.WF.rules_ctor_shape`, carried forward from the stage-1 environment). -/
theorem addInduct_rule_ctor {env env' : VEnv} {decl : VInductDecl} {rec ru}
    (hwf : decl.WF env) (h : env.addInduct decl = some env')
    (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules) :
    ∃ ci, env'.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields) := by
  obtain ⟨env1, env2, env3, s1, s2, s3, s4⟩ := addInduct_stages h
  have hC : decl.addTypesCtors env = some env2 := Option.bind_eq_some_iff.2 ⟨env1, s1, s2⟩
  obtain ⟨ci, hci, hcs⟩ := hwf.rules_ctor_shape env2 hC rec hrec ru hru
  exact ⟨ci, ((addRecs_le s3).trans (addRules_le s4)).constants hci, hcs⟩

/-! ### Combinatorics of ι redexes -/

/-- `SimplePattern.iota` is injective through `toPattern`. -/
theorem iota_toPattern_inj {r1 m1 c1 n1 r2 m2 c2 n2}
    (h : (SimplePattern.iota r1 m1 c1 n1).toPattern = (SimplePattern.iota r2 m2 c2 n2).toPattern) :
    r1 = r2 ∧ m1 = m2 ∧ c1 = c2 ∧ n1 = n2 := by
  simp only [SimplePattern.toPattern] at h
  injection h with hl hr
  obtain ⟨rfl, rfl⟩ := Pattern.varN_const_inj hl
  obtain ⟨rfl, rfl⟩ := Pattern.varN_const_inj hr
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### Success of every step, and duplicate-freedom of the bound names -/

/-- Every element of a successful `foldlM` had a successful step. -/
theorem foldlM_step_success {α} {f : VEnv → α → Option VEnv} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM f init = some final → ∀ a ∈ l, ∃ e e', f e a = some e'
  | [], _, _, _, _, ha => by cases ha
  | b :: bs, init, final, h, a, ha => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, _, h1⟩
    · exact foldlM_step_success h2 a ha'

/-- A successful `addRecRule` registered a closed reduct. -/
theorem addRecRule_closed {env env' : VEnv} {r ru} (h : env.addRecRule r ru = some env') :
    ru.rhs.Closed := by
  unfold addRecRule at h; split at h
  · assumption
  · cases h

/-- After a successful `addRules`, every rule reduct of the declaration is closed. -/
theorem addRules_closed {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRules env = some env') : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ru.rhs.Closed := by
  unfold VInductDecl.addRules at h
  intro r hr ru hru
  obtain ⟨_, _, h1⟩ := foldlM_step_success h r hr
  obtain ⟨_, _, h2⟩ := foldlM_step_success h1 ru hru
  exact addRecRule_closed h2

/-- In a successful `addConst` fold, the registered names have no duplicates. -/
theorem addConst_foldlM_nodup {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      (l.map nm).Nodup
  | [], _, _, _ => List.nodup_nil
  | b :: bs, init, final, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, hspec_b, _⟩ := addConst_eq h1
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, addConst_foldlM_nodup h2⟩
    obtain ⟨a, ha, hab⟩ := List.mem_map.1 hmem
    have := addConst_foldlM_fresh h2 a ha
    rw [hab, hspec_b] at this; cases this

/-- Type-former names within one `decl` have no duplicates. -/
theorem addTypes_nodup {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addTypes env = some env') : (decl.types.map (·.name)).Nodup := by
  unfold VInductDecl.addTypes at h; exact addConst_foldlM_nodup h

/-- Constructor names within one `decl` (across all its type formers) have no
duplicates. -/
theorem addCtors_nodup {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addCtors env = some env') : ((decl.types.flatMap (·.ctors)).map (·.name)).Nodup := by
  unfold VInductDecl.addCtors at h; exact addConst_foldlM_nodup h

/-- Recursor names within one `decl` have no duplicates. -/
theorem addRecs_nodup {decl : VInductDecl} {env env' : VEnv}
    (h : decl.addRecs env = some env') : (decl.recs.map (·.name)).Nodup := by
  unfold VInductDecl.addRecs at h; exact addConst_foldlM_nodup h

end VEnv
end Lean4Lean
