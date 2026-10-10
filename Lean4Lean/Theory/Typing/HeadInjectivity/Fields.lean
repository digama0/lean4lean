import Lean4Lean.Theory.Typing.HeadInjectivity.Uniqueness

/-! # The injectivity fields of head inversion

`ChainHeadInjectivity.toHeadInjectivity`: in a well-formed environment, chain-level head
injectivity yields the four injectivity fields of `VEnv.HeadInversion` (`forallE_forallE`,
the argument part of `rigid_rigid`, `former_args`, `proj_fieldType`), stated in
`HeadInjectivity` exactly as in `HeadInversion.lean`. -/

namespace Lean4Lean
open Lean4Lean
namespace VEnv

theorem ChainHeadInjectivity.toHeadInjectivity {env : VEnv} (henv : env.WF)
    (core : env.ChainHeadInjectivity) : env.HeadInjectivity where
  forallE_forallE {U Γ A B A' B'} hΓ H := by
    have ⟨hA, hB⟩ := core.forallE_chain hΓ H
    have ⟨hAt, hBt⟩ := H.isType_l.forallE_inv henv.ordered
    have ⟨u, hAu⟩ := hAt
    have ⟨v, hBv⟩ := hBt
    have hΓ' : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, hAt⟩
    exact ⟨⟨u, hA.collapse_of_chainHeadInjectivity henv core hΓ hAu⟩, ⟨v, hB.collapse_of_chainHeadInjectivity henv core hΓ' hBv⟩⟩
  rigid_args hΓ hc H := (core.rigid_rigid hΓ hc hc H).2.2
  former_args := core.former_args
  proj_fieldType {U Γ typeName info index
      levels₁ params₁ indexArgs₁ sourceMajor₁ fieldType₁ fieldLevel₁
      levels₂ params₂ indexArgs₂ sourceMajor₂ fieldType₂ fieldLevel₂}
      hΓ hproj _ _ _ hp₁ _ hf₁ hF₁ _ hl₂ _ hp₂ _ hf₂ _ _ hsource hmajor := by
    have hrig := henv.projectionRigid hproj
    obtain ⟨-, hls, hargs⟩ := core.rigid_rigid hΓ hrig hrig hmajor
    have hps := forall₂_append_left (hp₁.trans hp₂.symm) hargs
    have hc := fieldType_congr henv.ordered hproj hls hl₂ hps ⟨_, hsource⟩ hf₁ hf₂
    have s := (hF₁.strong henv hΓ).hasType'.1
    exact .single (s.congrUB_defeq henv core hΓ (.zero []) hc)

end VEnv
end Lean4Lean
