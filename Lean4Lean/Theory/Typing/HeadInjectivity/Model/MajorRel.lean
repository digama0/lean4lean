import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineVal
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RigidRel

/-! # The major of an ι redex: relating the constructor's arguments to the recursor's

For a semantically typed ι redex `rec ls recArgs (ctor lsC ctorArgs)`, the major
`ctor lsC ctorArgs` is typed at a type `Amaj` which is soundly equal both to the recursor's
major domain `I lsI iargs` at the valuation by `recArgs` (`HTS.spineVal_dom` on the recursor
spine) and to the constructor's result `Rc = I lsC' cargs` at the valuation by `ctorArgs`
(`HTS.spineVal` on the constructor spine). The two spines of the rigid family `I`, read at these
valuations of the two generic telescopes, are therefore related (`rigid_spines_rel`): same
arity, equivalent levels, and corresponding arguments with mutually subsuming observations and
definitionally equal values in the target context. This is the typing information of the redex
that lets the ι rule exchange the recursor's parameters and indices for the constructor's
(`redex_major_rel`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- A Pi telescope split at its last domain. -/
theorem wrapForalls_last {ds : List VExpr} {R : VExpr} {n : Nat} (hn : ds.length = n + 1) :
    VExpr.wrapForalls ds R = .wrapForalls (ds.take n ++ [ds[n]'(by omega)]) R := by
  congr 1
  rw [← List.take_succ_eq_append_getElem (by omega), ← hn, List.take_length]

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **The major of an ι redex.** -/
theorem redex_major_rel {Γ : List VExpr} {n ctor I : Name} {m1 lsC lsI lsC' : List VLevel}
    {ci cc : VConstant} {dsH Dc iargs cargs recArgs ctorArgs : List VExpr} {RH A : VExpr}
    {kM : Nat} {uT uC : VLevel} {σ : VExpr.Subst} {S : ObSets}
    (hci : env.constants n = some ci) (eH : ci.type.instL m1 = .wrapForalls dsH RH)
    (hT : HTS env U Δ [] (ci.type.instL m1) (.sort uT))
    (hlenH : dsH.length = kM + 1) (hkH : dsH[kM]? = some (.mkApps (.const I lsI) iargs))
    (hcc : env.constants ctor = some cc)
    (eC : cc.type.instL lsC = .wrapForalls Dc (.mkApps (.const I lsC') cargs))
    (hTc : HTS env U Δ [] (cc.type.instL lsC) (.sort uC))
    (hrigI : env.Rigid I) (hrA : recArgs.length = kM) (hcA : ctorArgs.length = Dc.length)
    (H : HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A)
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    ∃ Amaj, HTS env U Δ Γ (.mkApps (.const ctor lsC) ctorArgs) Amaj ∧
      SD env U Δ Γ (.mkApps (.const ctor lsC) ctorArgs) (.mkApps (.const ctor lsC) ctorArgs) Amaj ∧
      (∃ B, HTS env U Δ Γ (.mkApps (.const n m1) recArgs) (.forallE Amaj B)) ∧
    ∃ uR uI,
      HTS env U Δ (dsH.take kM).reverse (.mkApps (.const I lsI) iargs) (.sort uR) ∧
      HTS env U Δ Dc.reverse (.mkApps (.const I lsC') cargs) (.sort uI) ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst (recArgs.map (·.subst σ)))
        (VExpr.argSubst (recArgs.map (·.subst σ))) (dsH.take kM).reverse ∧
      TV env U Δ (dsH.take kM).reverse (VExpr.argSubst (recArgs.map (·.subst σ)))
        (argSets env U Δ σ S recArgs) ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst (ctorArgs.map (·.subst σ)))
        (VExpr.argSubst (ctorArgs.map (·.subst σ))) Dc.reverse ∧
      TV env U Δ Dc.reverse (VExpr.argSubst (ctorArgs.map (·.subst σ)))
        (argSets env U Δ σ S ctorArgs) ∧
      cargs.length = iargs.length ∧ List.Forall₂ (· ≈ ·) lsC' lsI ∧
      ∀ i (hi : i < cargs.length) (hi' : i < iargs.length),
        Ob.Sub (Obs' (VExpr.argSubst (ctorArgs.map (·.subst σ))) (argSets env U Δ σ S ctorArgs)
            cargs[i])
          (Obs' (VExpr.argSubst (recArgs.map (·.subst σ))) (argSets env U Δ σ S recArgs)
            iargs[i]) ∧
        Ob.Sub (Obs' (VExpr.argSubst (recArgs.map (·.subst σ))) (argSets env U Δ σ S recArgs)
            iargs[i])
          (Obs' (VExpr.argSubst (ctorArgs.map (·.subst σ))) (argSets env U Δ σ S ctorArgs)
            cargs[i]) ∧
        ∃ A₁, HTS env U Δ Dc.reverse cargs[i] A₁ ∧
          SD env U Δ Dc.reverse cargs[i] cargs[i] A₁ ∧
          env.IsDefEq U Δ (cargs[i].subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))
            (iargs[i].subst (VExpr.argSubst (recArgs.map (·.subst σ))))
            (A₁.subst (VExpr.argSubst (ctorArgs.map (·.subst σ)))) := by
  subst hrA
  have hkM : recArgs.length < dsH.length := by omega
  -- the last application: the major and its type
  obtain ⟨Amaj, B, u, v, hf, -, -, -, hmaj, hsmaj, hch⟩ := H.app_const_inv' rfl
  -- the recursor spine prefix
  have hT' : HTS env U Δ [] (.wrapForalls dsH RH) (.sort uT) := by rw [← eH]; exact hT
  have hTc' : HTS env U Δ [] (.wrapForalls Dc (.mkApps (.const I lsC') cargs)) (.sort uC) := by
    rw [← eC]; exact hTc
  have hpiH' : PiSD env U Δ [] dsH RH := hT'.piSD
  have hpiC : PiSD env U Δ [] Dc (.mkApps (.const I lsC') cargs) := hTc'.piSD
  have hTW : Ob.Sub (Obs' .id .empty (ci.type.instL m1))
      (Obs' .id .empty (.wrapForalls dsH RH)) := by rw [eH]; exact Ob.Sub.refl
  have hTWc : Ob.Sub (Obs' .id .empty (cc.type.instL lsC))
      (Obs' .id .empty (.wrapForalls Dc (.mkApps (.const I lsC') cargs))) := by
    rw [eC]; exact Ob.Sub.refl
  obtain ⟨WR, tvR⟩ := spine_tele henv hΔ hf W tv hci hTW hpiH' (by omega)
  obtain ⟨WC, tvC⟩ := spine_tele henv hΔ hmaj W tv hcc hTWc hpiC (Nat.le_of_eq hcA)
  rw [hcA, List.take_length] at WC tvC
  -- the major domain and the constructor's result, at the argument valuations
  have hdom := HTS.spineVal_dom henv hΔ hci eH hpiH' hf W tv (by omega)
  have hdsHk : dsH[recArgs.length] = .mkApps (.const I lsI) iargs := by
    rw [List.getElem?_eq_getElem hkM] at hkH; exact Option.some.inj hkH
  rw [hdsHk] at hdom
  have hres := HTS.spineVal henv hΔ hcc eC hpiC hmaj W tv (Nat.le_of_eq hcA)
  rw [hcA, List.drop_length] at hres
  simp only [VExpr.wrapForalls, List.foldr_nil] at hres
  -- the generic spines are typed
  obtain ⟨uR, hIR, -⟩ := HTS.tele_dom (pre := dsH.take recArgs.length) (post := [])
    (A := dsH[recArgs.length])
    (by rw [← wrapForalls_last hlenH]; exact hT')
  rw [List.append_nil, hdsHk] at hIR
  obtain ⟨uI, hIC⟩ := HTS.wrapForalls_body hTc'
  rw [List.append_nil] at hIC
  -- the two spines of `I` subsume each other
  have hsub₁ := hres.2.trans hdom.1
  have hsub₂ := hdom.2.trans hres.1
  obtain ⟨hlen, hls, hrel⟩ := rigid_spines_rel henv hΔ hIC WC tvC hIR WR tvR hrigI hsub₁ hsub₂
  exact ⟨Amaj, hmaj, hsmaj, ⟨B, hf⟩, uR, uI, hIR, hIC, WR, tvR, WC, tvC, hlen, hls, hrel⟩

end

end Model
end VEnv
end Lean4Lean
