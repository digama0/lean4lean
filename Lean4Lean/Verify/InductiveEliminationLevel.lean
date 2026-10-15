import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem freshElimName.loop.spec (names : List Name) (index : Nat) :
    ∃ selected, index ≤ selected ∧ loop names index = candidate selected ∧
      candidate selected ∉ names ∧
      ∀ earlier, index ≤ earlier → earlier < selected → candidate earlier ∈ names := by
  induction index using loop.induct names with
  | case1 index member induction =>
    obtain ⟨selected, bound, result, fresh, earlier⟩ := induction
    refine ⟨selected, by omega, ?_, fresh, ?_⟩
    · rw [loop.eq_def, dif_pos member]
      exact result
    · intro previous lower upper
      by_cases same : previous = index
      · exact same ▸ member
      · exact earlier previous (by omega) upper
  | case2 index fresh =>
    exact ⟨index, Nat.le_refl _, by rw [loop, dif_neg fresh], fresh,
      fun earlier lower upper => by omega⟩

theorem freshElimName.not_mem (names : List Name) : freshElimName names ∉ names := by
  unfold freshElimName
  split
  · obtain ⟨selected, _, result, fresh, _⟩ := loop.spec names 1
    exact result ▸ fresh
  · assumption

theorem freshElimName.first (names : List Name) :
    (freshElimName names = `u ∧ `u ∉ names) ∨
      (`u ∈ names ∧ ∃ selected, 0 < selected ∧
        freshElimName names = candidate selected ∧ candidate selected ∉ names ∧
        ∀ earlier, 0 < earlier → earlier < selected → candidate earlier ∈ names) := by
  unfold freshElimName
  split
  · rename_i member
    obtain ⟨selected, bound, result, fresh, earlier⟩ := loop.spec names 1
    exact .inr ⟨member, selected, by omega, result, fresh,
      fun previous positive upper => earlier previous (by omega) upper⟩
  · exact .inl ⟨rfl, by assumption⟩

theorem getElimLevel.eq_map (stats : InductiveStats) (types : Array InductiveType)
    (reader : Context) :
    getElimLevel stats types reader = (isLargeEliminator stats types reader).map
      (fun large => if large then .param (freshElimName reader.lparams) else .zero) := by
  change Except.bind (isLargeEliminator stats types reader) _ = _
  cases isLargeEliminator stats types reader with
  | error error => rfl
  | ok large => cases large <;> cases reader <;> rfl

theorem getElimLevel.fresh (stats : InductiveStats) (types : Array InductiveType)
    (reader : Context) :
    (getElimLevel stats types reader).WF fun level =>
      level = .zero ∨ ∃ name, level = .param name ∧ name ∉ reader.lparams := by
  rw [getElimLevel.eq_map]
  cases isLargeEliminator stats types reader with
  | error error => intro level success; cases success
  | ok large =>
    cases large
    · exact .pure (.inl rfl)
    · exact .pure (.inr ⟨_, rfl, freshElimName.not_mem _⟩)

theorem getElimLevel.recLevelParams (stats : InductiveStats) (types : Array InductiveType)
    (reader : Context) (distinct : reader.lparams.Nodup) :
    (getElimLevel stats types reader).WF fun level =>
      (getRecLevelParams level reader.lparams).Nodup ∧
      VLevel.ofLevel (getRecLevelParams level reader.lparams) level =
        some (if level.isParam then .param 0 else .zero) := by
  refine (getElimLevel.fresh stats types reader).mono fun level fresh => ?_
  rcases fresh with rfl | ⟨name, rfl, fresh⟩
  · exact ⟨distinct, rfl⟩
  · refine ⟨List.nodup_cons.mpr ⟨fresh, distinct⟩, ?_⟩
    simp [getRecLevelParams, VLevel.ofLevel, Level.isParam]

end Lean4Lean.AddInductive
