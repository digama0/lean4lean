import Lean4Lean.Theory.Typing.EnvLemmas

/-! # A well-formed history with its stages

`VEnv.WFH ds hs env` is a well-formedness derivation `VEnv.WF' ds env` that records, in `hs`
(latest first), the environment every declaration step starts from. A chosen such history of an
environment (`VEnv.stages`) pins the recursor registry of the confluence engine to one
installation order: its stages are well-formed prefixes of the environment, totally ordered by
extension (`VEnv.WFH.chain`). The coverage of the registered ι rules is proved by induction along
it. -/

namespace Lean4Lean

/-- A well-formedness derivation recording the environment each declaration step starts from. -/
inductive VEnv.WFH : List VDecl → List VEnv → VEnv → Prop where
  | empty : VEnv.WFH [] [] .empty
  | decl {env env' : VEnv} {d : VDecl} {ds : List VDecl} {hs : List VEnv} :
    VDecl.WF env d env' → env.WF' ds → VEnv.WFH ds hs env → VEnv.WFH (d :: ds) (env :: hs) env'
  | projs {env : VEnv} {ds : List VDecl} {hs : List VEnv} {entries : List VProjectionEntry} :
    VEnv.WFH ds hs env → (env.addProjections entries).WF' ds →
    VEnv.WFH ds hs (env.addProjections entries)

namespace VEnv

theorem WFH.wf' {ds : List VDecl} {hs : List VEnv} {env : VEnv} (H : env.WFH ds hs) :
    env.WF' ds := by
  induction H with
  | empty => exact .empty
  | decl hd hds _ _ => exact .decl hd hds
  | projs _ h _ => exact h

theorem WF'.wfh {ds : List VDecl} {env : VEnv} (H : env.WF' ds) : ∃ hs, env.WFH ds hs := by
  induction H with
  | empty => exact ⟨[], .empty⟩
  | decl hd hds ih => obtain ⟨hs, h⟩ := ih; exact ⟨_, .decl hd hds h⟩
  | inductProjections h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 ih1 ih2 =>
    obtain ⟨hs, h⟩ := ih2
    exact ⟨hs, .projs h (.inductProjections h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)⟩

/-- The stages of a well-formed history are well-formed prefixes of the environment. -/
theorem WFH.stage {ds : List VDecl} {hs : List VEnv} {env : VEnv} (H : env.WFH ds hs)
    {e : VEnv} (he : e ∈ hs) : e.WF ∧ env.WFPrefix e := by
  induction H with
  | empty => cases he
  | decl hd hds _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨⟨_, hds⟩, .decl hd .rfl⟩
    · obtain ⟨h1, h2⟩ := ih he; exact ⟨h1, .decl hd h2⟩
  | projs _ _ ih =>
    obtain ⟨h1, h2⟩ := ih he; exact ⟨h1, .projs h2⟩

/-- The stages of a history are below the environment. -/
theorem WFH.stage_le {ds : List VDecl} {hs : List VEnv} {env : VEnv} (H : env.WFH ds hs)
    {e : VEnv} (he : e ∈ hs) : e ≤ env := (H.stage he).2.le

/-- **The stages of a history are totally ordered by extension**: a later stage (smaller index)
extends an earlier one. -/
theorem WFH.chain {ds : List VDecl} {hs : List VEnv} {env : VEnv} (H : env.WFH ds hs) :
    ∀ {i j : Nat} (hi : i < hs.length) (hj : j < hs.length), i ≤ j → hs[j] ≤ hs[i] := by
  induction H with
  | empty => intro i j hi; simp at hi
  | decl hd hds H ih =>
    intro i j hi hj hij
    cases i with
    | zero =>
      cases j with
      | zero => exact .rfl
      | succ j => exact H.stage_le (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih (by simpa using hi) (by simpa using hj) (by omega)
  | projs _ _ ih => exact ih

open Classical in
/-- A chosen history of an environment: its stages, latest first (empty if the environment is
not well-formed). -/
noncomputable def stages (env : VEnv) : List VEnv :=
  if h : ∃ p : List VDecl × List VEnv, env.WFH p.1 p.2 then (Classical.choose h).2 else []

theorem WF.stagesH {env : VEnv} (henv : env.WF) : ∃ ds, env.WFH ds env.stages := by
  have h : ∃ p : List VDecl × List VEnv, env.WFH p.1 p.2 := by
    obtain ⟨ds, H⟩ := henv
    obtain ⟨hs, h⟩ := H.wfh
    exact ⟨(ds, hs), h⟩
  unfold stages
  rw [dif_pos h]
  exact ⟨_, Classical.choose_spec h⟩

end VEnv
end Lean4Lean
