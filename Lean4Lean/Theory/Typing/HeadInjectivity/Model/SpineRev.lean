import Lean4Lean.Theory.Typing.HeadInjectivity.Model.HTS

/-! # The reverse spine lemma

`HTS.spineRev`: for a constant or eliminator spine `mkApps hd args` semantically typed at `T`
and a typed valuation, each argument has a domain type `A` in the typing derivation, and the
observations of `T` (and the domain class and the observations of each `A`) are covered by
chain observations of the head's type at keys whose classes contain the arguments and whose
observations are covered by observations of the arguments (`ChainArgs`). This is the converse of
the observation transfer (P2, P2') of the spine lemma `HTS.spineH`; the key lists are chosen by
compactness, so they differ from observation to observation. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- Keys whose classes contain the arguments (at `σ`) and whose observations are each weaker than
an observation of the argument. -/
def ChainArgs (env : VEnv) (U : Nat) (Δ : List VExpr) (σ : VExpr.Subst) (S : ObSets)
    (keys : List Key) (args : List VExpr) : Prop :=
  List.Forall₂ (fun (k : Key) a => k.2.1 (a.subst σ) ∧
    ∀ y ∈ k.2.2, ∃ y₀, Obs env U Δ σ S a y₀ ∧ y₀ ≼ y) keys args

theorem ChainArgs.append {k : Key} (h : ChainArgs env U Δ σ S keys args)
    (h1 : k.2.1 (a.subst σ)) (h2 : ∀ y ∈ k.2.2, ∃ y₀, Obs' σ S a y₀ ∧ y₀ ≼ y) :
    ChainArgs env U Δ σ S (keys ++ [k]) (args ++ [a]) :=
  forall₂_append_single h ⟨h1, h2⟩

theorem ChainArgs.length (h : ChainArgs env U Δ σ S keys args) : keys.length = args.length :=
  List.Forall₂.length_eq h

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **The reverse spine lemma.** -/
theorem HTS.spineRev (H : HTS env U Δ Γ e T) {hd args} (he : e = .mkApps hd args)
    (hhd : (∃ c ls, hd = .const c ls) ∨ ∃ b o ls, hd = .elim b o ls)
    {σ S} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    ∃ (Th : VExpr) (As : List VExpr), HeadTy env U hd Th ∧ Th.ClosedN ∧ As.length = args.length ∧
      (∀ i A a, As[i]? = some A → args[i]? = some a →
        SD env U Δ Γ a a A ∧
        (∃ keys, ChainArgs env U Δ σ S keys (args.take i) ∧
          Obs' .id .empty Th (piCodChain keys (.piDom (TyCls env U Δ (A.subst σ))))) ∧
        ∀ x, Obs' σ S A x → ∃ keys x', ChainArgs env U Δ σ S keys (args.take i) ∧
          Obs' .id .empty Th (piCodChain keys (.piDomOb x')) ∧ x' ≼ x) ∧
      ∀ y, Obs' σ S T y → ∃ keys y', ChainArgs env U Δ σ S keys args ∧
        Obs' .id .empty Th (piCodChain keys y') ∧ y' ≼ y := by
  induction H generalizing args with
  | bvar =>
    rcases hhd with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact absurd he.symm mkApps_const_ne_bvar
    · exact absurd he.symm mkApps_elim_ne_bvar
  | other h h' =>
    rcases hhd with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact absurd he (h _ _ _)
    · exact absurd he (h' _ _ _ _)
  | lam =>
    rcases hhd with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact absurd he.symm mkApps_const_ne_lam
    · exact absurd he.symm mkApps_elim_ne_lam
  | forallE =>
    rcases hhd with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact absurd he.symm VExpr.mkApps_const_ne_forallE
    · exact absurd he.symm mkApps_elim_ne_forallE
  | proj =>
    rcases hhd with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
      (rcases mkApps_inv he with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h)
  | const hci hls _ hT hsd =>
    rcases mkApps_inv he with ⟨rfl, he'⟩ | ⟨_, _, _, he'⟩
    · subst he'
      refine ⟨_, [], .inl ⟨_, _, _, rfl, hci, hls, rfl⟩, (henv.closedC hci).instL, rfl,
        fun i A a h => by simp at h, fun y hy => ⟨[], y, .nil,
          (Obs.closed_iff_id (henv.closedC hci).instL).1 hy, .refl⟩⟩
    · cases he'
  | elim hb htype hcl0 hls hT hsd =>
    rcases mkApps_inv he with ⟨rfl, he'⟩ | ⟨_, _, _, he'⟩
    · subst he'
      refine ⟨_, [], .inr ⟨_, _, _, _, _, rfl, hb, htype, hcl0, hls, rfl⟩, hcl0.instL, rfl,
        fun i A a h => by simp at h, fun y hy => ⟨[], y, .nil,
          (Obs.closed_iff_id hcl0.instL).1 hy, .refl⟩⟩
    · cases he'
  | @app _ A u B v f a hA hB _ hfty _ hsa ihf _ =>
    rcases mkApps_inv he with ⟨rfl, he'⟩ | ⟨as, a', rfl, he'⟩
    · rcases hhd with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> cases he'
    injection he' with hf ha; subst ha
    obtain ⟨Th, As, hTh, hcl, hlen, hdom, hrev⟩ := ihf hf W tv
    have haσ : env.HasType U Δ (a.subst σ) (A.subst σ) :=
      hsa.1.defeq.hasType.1.substDF henv W.wf hΔ W
    have hc := TypedElCls.of_hasType haσ
    have IHa := hsa.2 σ σ S W tv tv
    refine ⟨Th, As ++ [A], hTh, hcl, by simp [hlen], fun i A' a' hA' ha' => ?_, fun y hy => ?_⟩
    · by_cases hi : i < as.length
      · rw [List.getElem?_append_left (by omega)] at hA'
        rw [List.getElem?_append_left hi] at ha'
        rw [List.take_append_of_le_length (by omega)]
        exact hdom i A' a' hA' ha'
      · have hi' : i = as.length := by
          have := (List.getElem?_eq_some_iff.1 ha').1; simp at this; omega
        subst hi'
        rw [List.getElem?_append_right (by omega), hlen] at hA'
        simp at hA'
        rw [List.getElem?_append_right (by omega)] at ha'
        simp at ha'
        subst hA' ha'
        rw [List.take_left' rfl]
        refine ⟨hsa, ?_, fun x hx => ?_⟩
        · obtain ⟨keys, y', hk, hy', l⟩ := hrev _ (Obs.piDom (A := A) (B := B))
          cases l.piDom_inv
          exact ⟨keys, hk, hy'⟩
        · obtain ⟨keys, y', hk, hy', l⟩ := hrev _ (Obs.piDomOb (B := B) hx)
          obtain ⟨x', rfl, l'⟩ := l.piDomOb_inv
          exact ⟨keys, x', hk, hy', l'⟩
    · have hy' : Obs' (σ.cons (a.subst σ)) (S.cons (Obs' σ S a)) B y := Obs.inst_iff.1 hy
      obtain ⟨K, hK, hbK, hyK⟩ := hy'.compact0B fun o h => Obs.backed h tv.1
      obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge fun k hk => IHa.2.2.1 k (hK k hk)
      have hpi : Obs' σ S (.forallE A B) (.piCodOb _ K y) := .piCodOb hc hτk hkk hbK .self hyK
      obtain ⟨keys, y₁, hk, hy₁, l⟩ := hrev _ hpi
      obtain ⟨K₀, y₂, rfl, hKK₀, l₂⟩ := l.piCodOb_inv
      refine ⟨keys ++ [(TyCls env U Δ (A.subst σ), ElCls env U Δ (TyCls env U Δ (A.subst σ))
        (a.subst σ), K₀)], y₂, hk.append .self fun z hz => ?_, ?_, l₂⟩
      · obtain ⟨z₀, hz₀, l₀⟩ := hKK₀ z hz
        exact ⟨z₀, hK z₀ hz₀, l₀⟩
      · rw [piCodChain_append]; exact hy₁
  | conv _ hAB ih =>
    obtain ⟨Th, As, hTh, hcl, hlen, hdom, hrev⟩ := ih he W tv
    refine ⟨Th, As, hTh, hcl, hlen, hdom, fun y hy => ?_⟩
    obtain ⟨y₁, hy₁, l₁⟩ := (SD.sub hAB W tv).2 y hy
    obtain ⟨keys, y₂, hk, hy₂, l₂⟩ := hrev y₁ hy₁
    exact ⟨keys, y₂, hk, hy₂, l₂.trans l₁⟩

end

end Model
end VEnv
end Lean4Lean
