import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RecursorRule

/-! # Proof binders of singleton eliminators

`proofBinder_of`: a binder of a rule telescope whose type is, in an earlier environment `E`
whose rules are valid in the model of `envF`, typed at `Sort 0` in the telescope's own context,
is a proof binder in the model of `envF` (`ProofBinder`): the soundness of that typing
derivation (by the history induction of `Model/EnvValid.lean`) types every observation of the
binder type at `Sort 0`, and its substitution instance makes the binder type a proposition.

`Ctx.liftN_ins`, `onCtx_wrapForalls` and the prefix restrictions of valuations are the typing
infrastructure used to place the field typings of `InductiveSignature.SingletonElimination`
in the context of a generated equation. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

/-- Inserting `n` binders below a telescope lifts the telescope's domains at their depths. -/
theorem Ctx.liftN_ins {n : Nat} : ∀ (A : List VExpr) (k : Nat) (Γ Γ' : List VExpr),
    Ctx.LiftN n k Γ Γ' →
    Ctx.LiftN n (k + A.length) (A.reverse ++ Γ)
      (((A.zipIdx k).map fun (t, j) => t.liftN n j).reverse ++ Γ')
  | [], k, Γ, Γ', h => by simpa using h
  | a :: A', k, Γ, Γ', h => by
    have := Ctx.liftN_ins A' (k + 1) (a :: Γ) (a.liftN n k :: Γ') (.succ h)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.zipIdx_cons,
      List.map_cons, List.length_cons]
    rw [show k + (A'.length + 1) = k + 1 + A'.length by omega]
    exact this

/-- The domains of a well-typed Pi telescope form a well-formed context. -/
theorem onCtx_wrapForalls {E : VEnv} (henv : E.Ordered) : ∀ {ds Γ : List VExpr} {b : VExpr},
    OnCtx Γ (E.IsType U) → E.IsType U Γ (.wrapForalls ds b) → OnCtx (ds.reverse ++ Γ) (E.IsType U)
  | [], _, _, hΓ, _ => by simpa using hΓ
  | d :: ds, Γ, b, hΓ, h => by
    obtain ⟨h1, h2⟩ := IsType.forallE_inv henv h
    have := onCtx_wrapForalls henv (ds := ds) (Γ := d :: Γ) ⟨hΓ, h1⟩ h2
    simpa [List.reverse_cons, List.append_assoc] using this

theorem Ctx.SubstEq.prefix {E : VEnv} : ∀ {L : List VExpr} {σ σ' : VExpr.Subst},
    OnCtx L (E.IsType U) → Ctx.SubstEq E U Δ σ σ' (L ++ Γ) → Ctx.SubstEq E U Δ σ σ' L
  | [], _, _, _, _ => .nil
  | _ :: L, _, _, ⟨hL, ⟨_, hA⟩⟩, W => by
    cases W with
    | cons W _ hh => exact .cons (Ctx.SubstEq.prefix hL W) hA hh

namespace Model

theorem TV.prefix {L : List VExpr} {σ : VExpr.Subst} {S : ObSets}
    (tv : TV env U Δ (L ++ Γ) σ S) : TV env U Δ L σ S :=
  ⟨tv.1, fun i A hL o h => tv.2 i A (Lookup.append_left hL) o h⟩

/-- **Proof binders** from typings at `Sort 0` in an earlier environment. -/
theorem proofBinder_of {envF E : VEnv} {doms : List VExpr} {u0 x : Nat}
    (henvF : envF.Ordered) (hE : E.Ordered) (hEF : E ≤ envF)
    (V : EnvValid envF E)
    (hdoms : OnCtx doms.reverse (E.IsType u0))
    (hder : E.HasType u0 doms.reverse ((doms.reverse.getD x default).liftN (x + 1))
      (.sort .zero))
    {U : Nat} {Δ Γ : List VExpr} {ls : List VLevel} (hΔ : OnCtx Δ (envF.IsType U))
    (hlw : ∀ l ∈ ls, l.WF U) : ProofBinder envF U Δ doms ls x Γ := by
  intro v vS Wv tvv
  have hL : OnCtx (doms.map (·.instL ls)).reverse (E.IsType U) := by
    rw [← List.map_reverse]; exact hdoms.instL hlw
  have hd' := hder.instL hlw
  rw [List.map_reverse] at hd'
  have S := (V.soundAtH henvF hEF U Δ hΔ (hd'.strong hE hL)).1
  have W := Wv.prefix (hL.mono (IsType.mono hEF))
  have tv := TV.prefix tvv
  refine ⟨⟨_, Or.inl rfl, (hd'.mono hEF).subst henvF W hΔ⟩, fun τ hτ => ?_⟩
  exact ⟨_, typedAt_sort_iff.1 ((S v v vS W tv tv).2.2.1 τ hτ)⟩

end Model

/-- The field typing of a singleton eliminator, placed in the context of the generated
equation: a field that is not determined by an index is a proof in the equation's
telescope. -/
theorem singleton_field_typing {s : InductiveSignature} {g : Instance s} {E envE : VEnv}
    (hE : E.Ordered) (hEE : envE ≤ E) (hsing : s.SingletonElimination envE g.uvars g.levels)
    (index : Fin s.constructors.size) {i : Nat} (hi : i < s.constructors[index].fields.length)
    (hidx : VExpr.bvar (s.constructors[index].fields.length - 1 - i) ∉
      s.constructors[index].indices) :
    E.HasType g.uvars (g.eqDoms index).reverse
      (((g.eqDoms index).reverse.getD (s.constructors[index].fields.length - 1 - i)
        default).liftN (s.constructors[index].fields.length - 1 - i + 1)) (.sort .zero) := by
  have hpf := hsing.2.2 s.constructors[index] (by simp) i hi
  rcases hpf with d0 | h
  case inr => exact absurd h hidx
  simp only [Fin.getElem_fin] at hi hidx d0 ⊢
  obtain ⟨F, hF⟩ : ∃ F, (s.fieldTypes s.constructors[index.1]).map (·.instL g.levels) = F :=
    ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, s.families.size + s.constructors.size = n := ⟨_, rfl⟩
  have hFl : F.length = s.constructors[index.1].fields.length := by
    simp [← hF, fieldTypes]
  have hF1 : ((s.fieldTypes s.constructors[index.1]).take i).map (·.instL g.levels) = F.take i := by
    rw [← hF, List.map_take]
  have hFi : (s.fieldType i s.constructors[index.1].fields[i]).instL g.levels = F[i]'(by omega) := by
    simp [← hF, fieldTypes]
  rw [hF1, hFi] at d0
  obtain ⟨M, hMd⟩ : ∃ M, g.motives ++ g.minors = M := ⟨_, rfl⟩
  have hM : M.length = n := by simp [← hMd, ← hn, Instance.motives, Instance.minors]
  have d1 := (d0.mono hEE).weakN hE (Ctx.liftN_ins (n := n) (F.take i) 0 (g.params.reverse)
    (M.reverse ++ g.params.reverse) (.zero M.reverse (by simp [hM])))
  have hti : (F.take i).length = i := by simp [hFl]; omega
  rw [hti, Nat.zero_add] at d1
  have d2 := d1.weakN hE (.zero (((F.drop i).zipIdx i).map fun (t, j) => t.liftN n j).reverse
    (n := s.constructors[index.1].fields.length - 1 - i + 1) (by simp [hFl]; omega))
  have e1 : (g.eqDoms index).reverse = (((F.drop i).zipIdx i).map fun (t, j) => t.liftN n j).reverse ++
      ((((F.take i).zipIdx 0).map fun (t, j) => t.liftN n j).reverse ++
        (M.reverse ++ g.params.reverse)) := by
    have : insertBinders F n = (((F.take i).zipIdx 0).map fun (t, j) => t.liftN n j) ++
        (((F.drop i).zipIdx i).map fun (t, j) => t.liftN n j) := by
      conv => lhs; rw [← List.take_append_drop i F]
      simp only [insertBinders, List.zipIdx_append, List.map_append, hti, Nat.zero_add]
    simp only [Instance.eqDoms, ← hMd, List.reverse_append, List.append_assoc, Fin.getElem_fin]
    rw [hn, hF, this, List.reverse_append, List.append_assoc]
  have e2 : (g.eqDoms index).reverse.getD (s.constructors[index.1].fields.length - 1 - i) default =
      (F[i]'(by omega)).liftN n i := by
    rw [e1, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hFl]; omega)]
    rw [List.getElem?_reverse (by simp [hFl]; omega)]
    simp only [List.length_map, List.length_zipIdx, List.length_drop, hFl]
    rw [show s.constructors[index.1].fields.length - i - 1 -
      (s.constructors[index.1].fields.length - 1 - i) = 0 by omega]
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_drop, Nat.add_zero]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [e2, e1]
  exact d2

end VEnv
end Lean4Lean
