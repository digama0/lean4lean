import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean
namespace VEnv

theorem with_addConst {P : Prop} {env env' : VEnv} {cis : List VObject}
    (henv : Ordered env)
    (hci : env.HasObjects cis → ci.WF env)
    (IH : ∀ {env1}, Ordered env1 →
      env1.HasObjects (.const n ci :: cis) → f env1 = some env' → P)
    (hcis : env.HasObjects cis)
    (H : (env.addConst n ci >>= f) = some env') : P := by
  let ⟨env1, h1, henv1⟩ := Option.bind_eq_some_iff.1 H
  refine IH (.const henv (hci hcis) h1) (hcis.const h1) henv1

theorem Lookup.zero' (eq : A.lift = ty') :
    Lookup (A::Γ) 0 ty' := eq ▸ .zero
theorem Lookup.succ' (h : Lookup Γ n ty) (eq : ty.lift = ty') :
    Lookup (A::Γ) (n+1) ty' := eq ▸ .succ h

syntax "lookup_tac" : tactic
macro_rules | `(tactic| lookup_tac) => `(tactic|
  first
  | refine Lookup.zero' ?_; exact rfl
  | refine Lookup.succ' (ty := ?_) ?_ ?_ <;> [skip; lookup_tac; exact rfl]
)

theorem HasType.app' (h1 : HasType env U Γ f (.forallE A B)) (h2 : HasType env U Γ a A)
    (eq : B.inst a = B') : HasType env U Γ (.app f a) B' := eq ▸ .appDF h1 h2
theorem HasType.const'
  (h1 : constants env c = some ci)
  (h2 : ∀ (l : VLevel), l ∈ ls → VLevel.WF uvars l)
  (h3 : List.length ls = ci.uvars)
  (eq : .instL ls ci.type = ty') :
  HasType env uvars Γ (.const c ls) ty' := eq ▸ .const h1 h2 h3

syntax "type_tac" : tactic -- TODO: write an actual tactic
macro_rules | `(tactic| type_tac) => `(tactic|
  first
  | refine HasType.forallE (u := ?_) (v := ?_) ?_ ?_ <;> [skip; skip; type_tac; type_tac]
  | refine HasType.sort ?_; decide
  | refine HasType.bvar ?_; lookup_tac
  | refine HasType.app' (A := ?_) (B := ?_) ?_ ?_ ?_ <;> [skip; skip; type_tac; type_tac; exact rfl]
  | refine HasType.const' (ci := ?_) ?_ ?_ ?_ ?_ <;> [skip; assumption; decide; decide; exact rfl]
  | refine HasType.lam (u := ?_) ?_ ?_ <;> [skip; type_tac; type_tac]
)
