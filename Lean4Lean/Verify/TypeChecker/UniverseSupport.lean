import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.Verify.Typing.UniverseSupport

/-! Definition unfolding preserves every universe scope of its input, including when the
unfolded body comes from the `unfold` cache: the cache invariant identifies the installed
declaration and the specialized body, so no extra cache assumption is needed for this part of
weak-head normalization. -/

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem instantiateDeltaValue_levelParams {c : VContext}
    (he : c.TrExprS (.const name levels) target)
    (hlookup : c.env.find? name = some info) (hdelta : info.deltaValue? = some value)
    (hs : (Expr.const name levels).levelParamsIn params = true) :
    (instantiateDeltaValue info levels).levelParamsIn params = true := by
  cases he with
  | const hc hl hn =>
    obtain ⟨rfl, hsafe, hu, _⟩ := c.trenv.find?_uniq hlookup hc
    have hv := c.trenv.of_value hlookup hsafe hdelta
    simp only [instantiateDeltaValue, hdelta, Option.get!_some]
    apply Expr.levelParamsIn_instantiateLevelParams hv.levelParamsIn
    · simpa only [Expr.levelParamsIn, List.all_eq_true] using hs
    · exact hu.trans hn.symm

theorem unfoldDefinitionCore.WF_levelParams {c : VContext} {s : State}
    (he : c.TrExprS e target) (hs : e.levelParamsIn params = true) :
    RecM.WF c s (unfoldDefinitionCore e) fun result _ =>
      ∀ e', result = some e' → e'.levelParamsIn params = true := by
  dsimp [unfoldDefinitionCore]
  split <;> [refine .getEnv ?_; exact .pure nofun]
  split
  · rename_i name levels optInfo info hdelta
    obtain ⟨_, hlookup, ⟨_, hv⟩, _, ⟨⟩, hlen⟩ := isDelta_is_some.mp hdelta
    have hscope := instantiateDeltaValue_levelParams he hlookup hv hs
    split
    · refine .get ?_
      split
      · rename_i hcache
        refine .stateWF fun wf => .pure ?_
        obtain ⟨_, _, _, ⟨⟩, hc, rfl⟩ := wf.unfold_wf hcache
        cases hlookup.symm.trans hc
        exact fun _ h => Option.some.inj h ▸ hscope
      · refine .bind (Q := fun _ _ => True) ?_ fun _ _ _ _ =>
          .pure fun _ h => Option.some.inj h ▸ hscope
        rintro _ mwf wf _ _ ⟨⟩
        refine ⟨_, rfl, .rfl, { wf with unfold_wf := ?_ }, ⟨⟩⟩
        intro e e'
        simp only [Std.HashMap.getElem?_insert]
        split <;> [rintro ⟨⟩; exact (wf.unfold_wf ·)]
        rename_i eq
        rw [BEq.comm, Expr.eqv_const] at eq
        exact ⟨_, _, _, eq, hlookup, rfl⟩
    · exact .pure fun _ h => Option.some.inj h ▸ hscope
  · exact .pure nofun
theorem unfoldDefinition.WF_levelParams {c : VContext} {s : State}
    (he : c.TrExprS e target) (hs : e.levelParamsIn params = true) :
    RecM.WF c s (unfoldDefinition e) fun result _ =>
      ∀ e', result = some e' → e'.levelParamsIn params = true := by
  simp [unfoldDefinition]
  split
  · have ⟨fn', stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
    refine (unfoldDefinitionCore.WF_levelParams stk.tr (Expr.levelParamsIn_getAppFn hs)).bind
      fun result _ _ hresult => ?_
    cases result with
    | none => exact .pure nofun
    | some body =>
      refine .pure ?_
      intro out hout
      cases Option.some.inj hout
      rw [Expr.mkAppRevRange_eq (l₁ := []) (l₂ := e.getAppArgsRevList) (l₃ := [])
        (by simp [Expr.getAppRevArgs_toList]) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
      simpa only [Expr.mkAppList_reverse] using
        Expr.levelParamsIn_mkAppRevList (hresult _ rfl) (Expr.levelParamsIn_getAppArgsRevList hs)
  · exact unfoldDefinitionCore.WF_levelParams he hs
end Lean4Lean.TypeChecker.Inner
