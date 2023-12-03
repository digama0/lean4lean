import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean

open Lean (Name FVarId)
open VExpr

namespace VEnv

theorem with_addConst {P : Prop} {env env' : VEnv} {cis : List (Name × VConstant)}
    (henv : Ordered env)
    (hci : (cis.All fun ci => env.constants ci.1 = ci.2) → ci.WF env)
    (IH : ∀ {env1}, Ordered env1 →
      (((n, ci) :: cis).All fun ci => env1.constants ci.1 = ci.2) → f env1 = some env' → P)
    (hcis : cis.All fun ci => env.constants ci.1 = ci.2)
    (H : (env.addConst n (some ci) >>= f) = some env') : P := by
  let ⟨env1, h1, henv1⟩ := Option.bind_eq_some.1 H
  refine IH (.const henv (by rintro _ ⟨⟩; exact hci hcis) h1) ?_ henv1
  exact ⟨addConst_self h1, hcis.imp fun _ => (addConst_le h1).1 _ _⟩

theorem Lookup.zero' (eq : A.lift = ty') :
    Lookup (A::Γ) 0 ty' := eq ▸ .zero
theorem Lookup.succ' (h : Lookup Γ n ty) (eq : ty.lift = ty') :
    Lookup (A::Γ) (n+1) ty' := eq ▸ .succ h

syntax "lookup_tac" : tactic
macro_rules | `(tactic| lookup_tac) => `(tactic|
  first
  | refine Lookup.zero' ?a (ty' := ?_); case a => exact rfl
  | refine Lookup.succ' ?a ?b (ty := ?_) (ty' := ?_); (case a => lookup_tac); case b => exact rfl
)

theorem IsDefEq.app' (h1 : HasType env U Γ f (.forallE A B)) (h2 : HasType env U Γ a A)
    (eq : B.inst a = B') : HasType env U Γ (.app f a) B' := eq ▸ .appDF h1 h2
theorem IsDefEq.const'
  (h1 : constants env c = some (some ci))
  (h2 : ∀ (l : VLevel), l ∈ ls → VLevel.WF uvars l)
  (h3 : List.length ls = ci.uvars)
  (eq : .instL ls ci.type = ty') :
  HasType env uvars Γ (.const c ls) ty' := eq ▸ .const h1 h2 h3

syntax "type_tac" : tactic -- TODO: write an actual tactic
macro_rules | `(tactic| type_tac) => `(tactic|
  first
  | refine IsDefEq.forallE ?a ?b (u := ?_) (v := ?_)
    (case a => type_tac); (case b => type_tac)
  | refine IsDefEq.sort ?a; (case a => decide)
  | refine IsDefEq.bvar ?a; (case a => lookup_tac)
  | refine IsDefEq.app' ?f ?a ?eq (A := ?_) (B := ?_)
    (case f => type_tac); (case a => type_tac); (case eq => exact rfl)
  | refine IsDefEq.const' ?h1 ?h2 ?h3 ?eq (ci := ?_)
    (case h1 => assumption); (case h2 => decide); (case h3 => decide); (case eq => exact rfl)
  | refine IsDefEq.lam ?h1 ?h2 (u := ?_)
    (case h1 => type_tac); (case h2 => type_tac)
)
