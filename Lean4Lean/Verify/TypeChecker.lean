import Lean4Lean.Verify.TypeChecker.InferType
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Verify.TypeChecker.IsDefEq

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

structure VEnvs where
  venv : DefinitionSafety → VEnv

structure VEnvs.WF (env : Environment) (ves : VEnvs) where
  tr : TrEnv safety env (ves.venv safety)
  hasPrimitives : VEnv.HasPrimitives (ves.venv safety)
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  mono : safety ≤ safety' → ves.venv safety' ≤ ves.venv safety

/-- Assemble a `VEnvs` from a pointwise existential. `DefinitionSafety` has three elements, so
this is a finite case split rather than an appeal to choice -- the name records what it replaces. -/
theorem VEnvs.axiom_of_choice {P : DefinitionSafety → VEnv → Prop} (H : ∀ sf, ∃ x, P sf x) :
    ∃ x : VEnvs, ∀ sf, P sf (x.venv sf) := by
  have ⟨x1, _⟩ := H .safe; have ⟨x2, _⟩ := H .partial; have ⟨x3, _⟩ := H .unsafe
  exact ⟨⟨fun | .safe => x1 | .partial => x2 | .unsafe => x3⟩, by rintro ⟨⟩ <;> assumption⟩

/-- A model of `env` at a *single* safety level, which is all the type checker consumes.

`VEnvs.WF` bundles one of these at every level, but not every environment the checker runs
against admits that: while a `partial` mutual block is being checked its members are present
as axioms tagged `safe` (an `AxiomVal` cannot be tagged `partial`), and their types were only
checked at `partial`, so there is no `safe`-level model of that environment. -/
structure VEnvAt (env : Environment) (safety : DefinitionSafety) (venv : VEnv) : Prop where
  tr : TrEnv safety env venv
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []

theorem VEnvs.WF.toVEnvAt {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) : VEnvAt env safety (ves.venv safety) where
  tr := wf.tr
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives

namespace TypeChecker
open Inner

theorem Methods.withFuel.WF : ∀ {n}, (withFuel n).WF
  | 0 =>
    { isDefEqCore _ _ := .throw
      whnfCore _ := .throw
      whnf _ := .throw
      inferType _ _ := .throw }
  | n + 1 =>
    have := withFuel.WF (n := n)
    { isDefEqCore h1 h2 := isDefEqCore'.WF h1 h2 _ this
      whnfCore h1 := whnfCore'.WF h1 _ this
      whnf h1 := whnf'.WF h1 _ this
      inferType h1 h2 := inferType'.WF h1 h2 _ this }

theorem RecM.WF.run {x : RecM α} (H : x.WF c s Q) : (RecM.run x).WF c s Q :=
  H _ Methods.withFuel.WF

def VContext.mk1 {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    (wf : VEnvAt env safety venv) (lparams : List Name := [])
    (fuel : FuelConfig := {}) : VContext where
  env; safety; lparams; fuel; venv
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  trenv := wf.tr
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl

def VContext.mk' {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety := .safe) (lparams : List Name := [])
    (fuel : FuelConfig := {}) : VContext := .mk1 (wf.toVEnvAt safety) lparams fuel

theorem VState.WF.empty1 {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    {wf : VEnvAt env safety venv} {lparams : List Name} {fuel : FuelConfig} :
    VState.WF (.mk1 wf lparams fuel) {} where
  trctx := .nil
  ngen_wf := nofun
  ectx := ⟨[], .refl, trivial, .refl, .empty, nofun⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

theorem VState.WF.empty {env : Environment} {ves : VEnvs} {wf : ves.WF env}
    {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig} :
    VState.WF (.mk' wf safety lparams fuel) {} := by
  unfold VContext.mk'; exact .empty1

theorem M.WF.run1 {env : Environment} {venv : VEnv} (wf : VEnvAt env safety venv)
    {x : M α} {Q} (H : x.WF (.mk1 wf lparams fuel) {} fun a _ => Q a) :
    (M.run env safety {} lparams fuel x).WF Q := by
  intro a eq
  simp [M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  let ⟨_, _, _, _, H⟩ := H .empty1 _ _ eq
  exact H

theorem M.WF.run {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {x : M α} {Q} (H : x.WF (.mk' wf safety lparams fuel) {} fun a _ => Q a) :
    (M.run env safety {} lparams fuel x).WF Q := by
  unfold VContext.mk' at H; exact M.WF.run1 _ H

/-- Loop invariant rule for `for x in xs do ...`. `Inv` is indexed by the list still to be
processed, so the conclusion `Inv []` records that every element was handled. The body must
`yield`; a loop that can `break` is out of scope (none of the kernel's loops do). -/
theorem M.WF.forIn {c : VContext} {f : α → β → M (ForInStep β)}
    {Inv : List α → β → VState → Prop}
    (H : ∀ v vs b s, Inv (v :: vs) b s →
      (f v b).WF c s fun r s' => ∃ b', r = .yield b' ∧ Inv vs b' s') :
    ∀ {vs : List α} {b : β} {s : VState}, Inv vs b s →
      (forIn vs b f).WF c s fun b' s' => Inv [] b' s'
  | [], _, _, h => .pure h
  | v :: vs, b, s, h => by
    rw [List.forIn_cons]
    refine (H v vs b s h).bind fun r s' _ hr => ?_
    obtain ⟨b', rfl, hinv⟩ := hr
    exact M.WF.forIn H hinv

theorem M.WF.bindThrow {c : VContext} {s : VState} {x : M α} {f : α → M β} {Q}
    (h : x.WF c s fun _ _ => False) : (x >>= f).WF c s Q :=
  h.bind fun _ _ _ hf => hf.elim

/-- Loop rule for `addMutual`'s header loop, whose accumulator is the set of names seen so
far: each iteration rejects a name already in the set, so the whole block is duplicate-free. -/
theorem M.WF.forInFresh {c : VContext} {Q : Lean.DefinitionVal → β → Prop}
    {f : Lean.DefinitionVal → NameSet → M (ForInStep NameSet)}
    (H : ∀ v found s, (f v found).WF c s fun r _ =>
      found.contains v.name = false ∧ (∃ b, Q v b) ∧ r = .yield (found.insert v.name)) :
    ∀ {vs : List Lean.DefinitionVal} {found : NameSet} {s : VState},
      (ForIn.forIn vs found f).WF c s fun _ _ =>
        (∃ bs, List.Forall₂ Q vs bs) ∧ (vs.map (·.name)).Nodup ∧
          ∀ v ∈ vs, found.contains v.name = false
  | [], _, _ => .pure ⟨⟨[], .nil⟩, by simp, by simp⟩
  | v :: vs, found, s => by
    rw [List.forIn_cons]
    refine (H v found s).bind fun r s' _ h => ?_
    obtain ⟨hfresh, ⟨b, hb⟩, rfl⟩ := h
    refine (M.WF.forInFresh H (vs := vs) (found := found.insert v.name)).mono
      fun _ _ _ h => ?_
    obtain ⟨⟨bs, hbs⟩, hnd, hmem⟩ := h
    refine ⟨⟨b :: bs, .cons hb hbs⟩, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hnd⟩
      obtain ⟨w, hw, hwn⟩ := List.mem_map.1 hm
      have := hmem w hw
      rw [NameSet.contains_insert, hwn] at this
      simp at this
    · intro w hw
      cases hw with
      | head => exact hfresh
      | tail _ hw =>
        have := hmem w hw
        rw [NameSet.contains_insert] at this
        exact (by simpa using this : _ ∧ _).2

/-- Loop rule for a loop whose elements are already related to a list `cis`, so each iteration
may use the datum paired with the element it processes; each refines its `ci` to a `ci'`
related by `R`. -/
theorem M.WF.forInForall₂ {c : VContext} {f : α → Unit → M (ForInStep Unit)}
    {P : α → β → Prop} {R : β → β → Prop} {Q : α → β → Prop}
    (H : ∀ v ci s, P v ci → (f v ()).WF c s fun r _ =>
      (∃ ci', R ci ci' ∧ Q v ci') ∧ r = .yield ()) :
    ∀ {vs : List α} {cis : List β} {s : VState}, List.Forall₂ P vs cis →
      (ForIn.forIn vs () f).WF c s fun _ _ =>
        ∃ cis', List.Forall₂ R cis cis' ∧ List.Forall₂ Q vs cis' := by
  intro vs cis s h
  induction h generalizing s with
  | nil => exact .pure ⟨[], .nil, .nil⟩
  | @cons v ci vs cis hd tl ih =>
    rw [List.forIn_cons]
    refine (H v ci s hd).bind fun r s' _ h => ?_
    obtain ⟨⟨ci', hR, hQ⟩, rfl⟩ := h
    refine (ih (s := s')).mono fun _ _ _ h => ?_
    obtain ⟨cis', h1, h2⟩ := h
    exact ⟨ci' :: cis', .cons hR h1, .cons hQ h2⟩

nonrec theorem whnf.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (whnf e) fun e₁ _ => c.TrExpr e₁ e' :=
  (whnf.WF he).run.mono fun _ _ _ h => h.2

nonrec theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (inferType e) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' :=
  (inferType.WF he).run

nonrec theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (checkType e) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  (checkType.WF h1).run

nonrec theorem isDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    M.WF c s (isDefEq e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  (isDefEq.WF he₁ he₂).run

nonrec theorem isProp.WF {c : VContext} {s : VState}
    (he : c.TrExprS e e') : (isProp e).WF c s fun b _ => b → c.HasType e' (.sort .zero) :=
  (isProp.WF he).run

nonrec theorem ensureSort.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (ensureSort e e₀) fun e1 _ => c.TrExpr e1 e' ∧ ∃ u, e1 = .sort u :=
  (ensureSortCore.WF he).run.mono fun _ _ _ h => ⟨h.2.1, h.1⟩

nonrec theorem ensureForall.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (ensureForall e) fun e1 _ =>
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  (ensureForallCore.WF he).run.mono fun _ _ _ h => h.2

nonrec theorem ensureType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (ensureType e) fun e1 _ => ∃ e', c.TrExprS e e' ∧ ∃ u u', e1 = .sort u ∧
      VLevel.ofLevel c.lparams u = some u' ∧ c.HasType e' (.sort u') := by
  refine (inferType.WF he).bind fun _ _ _ ⟨_, _, a1, a2, a3⟩ => ?_
  refine (ensureSort.WF a2).mono fun _ _ _ ⟨⟨_, b1, b2⟩, b3⟩ => ?_
  obtain ⟨_, rfl⟩ := b3; let .sort b1 := b1
  exact ⟨_, a1, _, _, rfl, b1, a3.defeqU_r c.Ewf c.Δwf b2.symm⟩
