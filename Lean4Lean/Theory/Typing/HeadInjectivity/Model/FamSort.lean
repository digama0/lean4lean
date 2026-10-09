import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Singleton

/-! # The semantic sort of a family

`Model.famSort_of`: a constant whose type is, in an earlier environment `E` with valid rules,
definitionally a telescope whose body is definitionally `Sort level` has only `level` at the
ends of the chain observations of its type in the model of the final environment
(`FamSort`). -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- If a closed type `T` is soundly equal, through an intermediate type `M`, to a telescope
ending in `Sort l`, every sort at the end of a codomain chain observation of `T` is `l`. -/
theorem family_sort₂ {T M X₁ X₂ : VExpr} {ds : List VExpr} {ks : List Key}
    (H1 : SoundAt env U Δ [] T M X₁) (H2 : SoundAt env U Δ [] M (.wrapForalls ds (.sort l)) X₂)
    (h : Obs' .id .empty T (piCodChain ks (.sort z))) : z = l.eval := by
  obtain ⟨o', h1, h2⟩ := (H1 .id .id .empty .nil TV.empty TV.empty).1 _ h
  obtain ⟨o'', h3, h4⟩ := (H2 .id .id .empty .nil TV.empty TV.empty).1 _ h1
  obtain ⟨ks', -, rfl⟩ := (h4.trans h2).piCodChain_sort_inv
  exact obs_wrapForalls_sort h3

end Model

/-- Congruence of a Pi telescope in its codomain. -/
theorem wrapForalls_congr {E : VEnv} (henv : E.Ordered) : ∀ {ds Γ : List VExpr} {b b' A : VExpr}
    {l : VLevel}, E.HasType U Γ (.wrapForalls ds b) A →
    E.IsDefEq U (ds.reverse ++ Γ) b b' (.sort l) →
    ∃ v, E.IsDefEq U Γ (.wrapForalls ds b) (.wrapForalls ds b') (.sort v)
  | [], _, _, _, _, _, _, h2 => ⟨_, by simpa [VExpr.wrapForalls] using h2⟩
  | d :: ds, Γ, b, b', A, l, h1, h2 => by
    obtain ⟨⟨u, hd⟩, ⟨w, hw⟩⟩ := HasType.forallE_inv henv h1
    obtain ⟨v, hv⟩ := wrapForalls_congr henv hw (by simpa using h2)
    exact ⟨_, .forallEDF hd hv⟩

theorem install_parts {env installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install env block = some installed) :
    ∃ types, env.addConstVals block.types = some types ∧ types ≤ installed := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := H
  exact ⟨types, ht, (VEnv.addConstVals_le hc).trans <| VEnv.addEliminators_addProjections_le.trans <|
    (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le⟩

/-- **`FamSort` from a family's declared shape** in an earlier environment with valid
rules. -/
theorem Model.famSort_of {envF E : VEnv} {I : Name} {c : VConstant} {domains : List VExpr}
    {body A : VExpr} {level l : VLevel} {u0 : Nat}
    (henvF : envF.Ordered) (hE : E.Ordered) (hEF : E ≤ envF)
    (V : Model.EnvValid envF E)
    (hc : envF.constants I = some c)
    (h1 : E.IsDefEq u0 [] c.type (.wrapForalls domains body) A)
    (h2 : E.IsDefEq u0 domains.reverse body (.sort level) (.sort level.succ)) (hlev : level ≈ l) :
    Model.FamSort envF I l := by
  intro U Δ ci lsI ks z hΔ hci hls h
  rw [hc] at hci; cases hci
  obtain ⟨v, h3⟩ := wrapForalls_congr hE h1.hasType.2 (by rw [List.append_nil]; exact h2)
  have i1 := h1.instL hls
  have i3 := h3.instL hls
  simp only [List.map_nil] at i1 i3
  have s1 := IsDefEq.strong hE (show OnCtx [] (E.IsType U) from trivial) i1
  have s3 := IsDefEq.strong hE (show OnCtx [] (E.IsType U) from trivial) i3
  have S1 := (V.soundAtH henvF hEF U Δ hΔ s1).1
  have S3 := (V.soundAtH henvF hEF U Δ hΔ s3).1
  rw [VExpr.instL_wrapForalls domains (.sort level)] at S3
  have := Model.family_sort₂ S1 S3 h
  rw [this]
  exact VLevel.inst_congr_l hlev

end VEnv
end Lean4Lean
