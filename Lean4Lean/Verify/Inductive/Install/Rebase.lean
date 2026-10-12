import Lean4Lean.Verify.Inductive.Basic

/-! # Rebasing a certified block onto a larger model

`AddInduct.rebase`: a block certified at one safety level is installed in the models of the
other safety levels (the facts behind `BlockCertificate.rebase`). The model-side replay of
`VEnv.addInduct` over a larger environment is in `Theory/Inductive/AddInduct.lean` (the stages)
and `Theory/Typing/InductiveLemmas.lean` (`VEnv.addInduct_rebase`, `VEnv.addInduct_mono`);
this file adds the facts that need the checker's side: the primitive invariant
(`HasPrimitives.addInduct_rebase`), `VInductDecl.WF.rebase`, and the kernel-side alignment. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VEnv

/-- The primitive invariant of a replayed installation: the declaration's names are looked up
as in the original installation, every other name as in the larger base. -/
theorem HasPrimitives.addInduct_rebase {decl : VInductDecl} {env env' out out' : VEnv}
    (hbase : env'.HasPrimitives) (hout : out.HasPrimitives)
    (h : env.addInduct decl = some out) (h' : env'.addInduct decl = some out')
    (hle : out ≤ out') : out'.HasPrimitives := by
  intro p hp
  by_cases hmem : ∃ b ∈ decl.consts, b.1 = p.1
  · obtain ⟨b, hb, hbn⟩ := hmem
    refine (hout p hp).extend hle ?_
    have h1 := addInduct_constants_mem h hb
    rw [hbn] at h1; rw [h1, hle.constants h1]
  · exact (hbase p hp).extend (addInduct_le h')
      (addInduct_constants_of_not_mem h' fun b hb e => hmem ⟨b, hb, e⟩)

end VEnv

/-- A well-formed declaration with a well-formed compiled block stays well formed over a larger
environment in which its stages replay. -/
theorem VInductDecl.WF.rebase {decl : VInductDecl} {block : VInductBlock}
    {env env' envT envC envR envT' envC' envR' : VEnv}
    (H : decl.WF env) (hcomp : decl.CompilesTo env block) (hrecs : decl.RecsOf block)
    (hblock : block.WF env) (hle : env ≤ env')
    (stT : decl.addTypes env = some envT) (stC : decl.addCtors envT = some envC)
    (stR : decl.addRecs (decl.addProjs envC) = some envR)
    (stT' : decl.addTypes env' = some envT') (stC' : decl.addCtors envT' = some envC')
    (stR' : decl.addRecs (decl.addProjs envC') = some envR') :
    decl.WF env' ∧ block.WF env' := by
  obtain ⟨hT, hC, hR⟩ := VEnv.addStages_mono hle stT stC stR stT' stC' stR'
  have htypes' := stT'; rw [VInductDecl.addTypes_eq_addConstVals] at htypes'
  have hctors' := stC'; rw [VInductDecl.addCtors_eq_addConstVals] at hctors'
  have hrecs' := stR'
  rw [VInductDecl.addRecs_eq_addConstVals] at hrecs'
  have hblock' : block.WF env' := by
    refine hblock.rebase (envR' := envR') hle (by rw [hcomp.types]; exact htypes')
      (by rw [hcomp.ctors]; exact hctors') ?_
    rw [hcomp.projections, ← hrecs.recursors]; exact hrecs'
  have hCeq : ∀ {x}, decl.addTypesCtors env' = some x → x = envC' := by
    intro x hx
    rw [VInductDecl.addTypesCtors, stT'] at hx
    exact Option.some.inj (hx.symm.trans stC')
  have hCeq₀ : decl.addTypesCtors env = some envC := by
    rw [VInductDecl.addTypesCtors, stT]; exact stC
  have hPeq : ∀ {x}, decl.addTypesCtorsProjs env' = some x → x = decl.addProjs envC' := by
    intro x hx
    rw [VInductDecl.addTypesCtorsProjs] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    rw [hCeq hy]
  have hPeq₀ : decl.addTypesCtorsProjs env = some (decl.addProjs envC) :=
    VEnv.addTypesCtorsProjs_eq_some hCeq₀
  have hReq₀ : decl.addTypesCtorsProjsRecs env = some envR :=
    VEnv.addTypesCtorsProjsRecs_of_stages stT stC stR
  have hReq : ∀ {x}, decl.addTypesCtorsProjsRecs env' = some x → x = envR' := by
    intro x hx
    rw [VEnv.addTypesCtorsProjsRecs_of_stages stT' stC' stR'] at hx
    exact (Option.some.inj hx).symm
  have hP : decl.addProjs envC ≤ decl.addProjs envC' := VEnv.addProjections_mono hC
  refine ⟨?_, hblock'⟩
  refine ⟨H.source.mono_of_addConstVals hle htypes' hctors', ?_,
    ⟨block, hcomp.mono hle hblock', hrecs, hblock'⟩, ?_, H.rec_shape, H.rules_nodup, ?_, ?_,
    H.rule_shape, ?_⟩  -- `RecsCompiled` carries `block.WF`
  · cases H.formation with
    | ordinary h => exact .ordinary (h.mono_of_addConstVals hle htypes')
    | nested h hb => exact .nested h (hb.trans hle)
  · intro envP hP' r hr
    rw [hPeq hP']
    exact (H.recs_wf _ hPeq₀ r hr).mono hP
  · intro envC'' hC'' r hr ru hru
    rw [hCeq hC'']
    obtain ⟨ci, hci, hshape⟩ := H.rules_ctor _ hCeq₀ r hr ru hru
    exact ⟨ci, hC.constants hci, hshape⟩
  · -- `rules_ctorParams` is monotone in the environment.
    intro r hr ru hru
    rcases H.rules_ctorParams r hr ru hru with h | ⟨D, hD, h⟩
    · exact .inl h
    · exact .inr ⟨D, VEnv.InstalledBelow.mono hle hD, h⟩
  · intro envR'' hR'' r hr ru hru hc
    rw [hReq hR'']
    exact (H.rules_wf _ hReq₀ r hr ru hru hc).mono hR

/-- The names `addInduct` binds are the names of the kernel constants of an `AddInduct`. -/
theorem AddInduct.consts_fst {safety : DefinitionSafety} {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {decl : VInductDecl} (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    decl.consts.map Prod.fst = (AddInduct.consts H.ivals H.rvals).map (·.name) := by
  rw [H.consts_names]
  simp [VInductDecl.consts, List.map_append, List.map_map, Function.comp_def, List.map_flatMap]

/-- The declaration's names are fresh in every model aligned with the source constant map. -/
theorem AddInduct.fresh_of_aligned {safety safety' : DefinitionSafety} {m₁ m₂ : ConstMap}
    {env₁ env₂ env' : VEnv} {decl : VInductDecl} (H : AddInduct safety m₁ env₁ decl m₂ env₂)
    (hA : Aligned safety' m₁ env') : ∀ b ∈ decl.consts, env'.constants b.1 = none := by
  intro b hb
  have hmem : b.1 ∈ (AddInduct.consts H.ivals H.rvals).map (·.name) := by
    rw [← H.consts_fst]; exact List.mem_map_of_mem hb
  obtain ⟨ci, hci, hname⟩ := List.mem_map.1 hmem
  cases hc : env'.constants b.1 with
  | none => rfl
  | some c =>
    obtain ⟨ci', hci', -⟩ := hA.find?_iff.2 ⟨c, hc⟩
    have := H.fresh ci hci
    rw [hname, hci'] at this; cases this

/-- Replay an `AddInduct` at a lower safety level over a larger model in which the
declaration's names are fresh: the kernel side is unchanged, the stages replay above the
original ones (`VEnv.addInduct_rebase`) and the translations are monotone. -/
theorem AddInduct.rebase {s safety : DefinitionSafety} {m₁ m₂ : ConstMap}
    {env env' out : VEnv} {decl : VInductDecl}
    (H : AddInduct s m₁ env decl m₂ out) (hs : safety ≤ s) (hle : env ≤ env')
    (hfresh : ∀ b ∈ decl.consts, env'.constants b.1 = none) :
    ∃ out', ∃ H' : AddInduct safety m₁ env' decl m₂ out',
      H'.ivals = H.ivals ∧ H'.rvals = H.rvals ∧ out ≤ out' := by
  obtain ⟨envT', envC', envR', out', stT', stC', stR', stP', hT, hC, hR, hout⟩ :=
    VEnv.addInduct_rebase H.stT H.stC H.stR H.stP hle hfresh
  refine ⟨out', {
    ivals := H.ivals
    rvals := H.rvals
    envT := envT'
    envC := envC'
    envR := envR'
    stT := stT'
    stC := stC'
    stR := stR'
    stP := stP'
    types := Lean4Lean.List.Forall₂.imp (fun _ _ h =>
      ⟨⟨(h.tr.1.sf_mono hs).mono hle, h.tr.2⟩, h.ctor_names,
        Lean4Lean.List.Forall₂.imp (fun _ _ hc => ⟨⟨(hc.1.1.sf_mono hs).mono hT, hc.1.2⟩, hc.2⟩)
          h.ctors⟩) H.types
    recs := Lean4Lean.List.Forall₂.imp (fun _ _ h =>
      { tr := ⟨(h.tr.1.sf_mono hs).mono (VEnv.addProjections_mono hC), h.tr.2⟩
        all := h.all
        numParams := h.numParams
        numMotives := h.numMotives
        numMinors := h.numMinors
        numIndices := h.numIndices
        k := h.k
        rules := Lean4Lean.List.Forall₂.imp
          (fun _ _ hr => ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.mono hR⟩) h.rules }) H.recs
    order := H.order
    order_perm := H.order_perm
    fresh := H.fresh
    map_eq := H.map_eq }, rfl, rfl, hout⟩

/-- A block of constants that is invisible at `safety` extends the constant map without
touching the model, one `TrEnv'.ignore` per member. -/
theorem TrEnv'.ignoreConsts {safety : DefinitionSafety} {Q : Bool} {venv : VEnv} :
    ∀ {cis : List ConstantInfo} {C : ConstMap},
    (∀ ci ∈ cis, ¬ safety ≤ ci.safety) →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup →
    TrEnv' safety C Q venv → TrEnv' safety (insertConsts C cis) Q venv
  | [], _, _, _, _, H => H
  | d :: ds, C, hvis, hfr, hnd, H => by
    have H' := TrEnv'.ignore (ci := d) (hfr _ (.head _)) (hvis _ (.head _)) H
    rw [insertConsts_cons]
    refine TrEnv'.ignoreConsts (fun e he => hvis e (.tail _ he))
      (insertConsts_fresh_tail H.map_wf.map₂ hfr hnd) ?_ H'
    rw [List.map_cons, List.nodup_cons] at hnd; exact hnd.2

theorem ConstantInfo.not_le_safety_of_isUnsafe {ci : ConstantInfo} (h : ci.isUnsafe = true)
    {safety : DefinitionSafety} (hs : safety ≠ .unsafe) : ¬ safety ≤ ci.safety := by
  have : ci.safety = .unsafe := by simp [ConstantInfo.safety, h]
  rw [this]; intro hle
  exact hs (DefinitionSafety.le_antisymm hle DefinitionSafety.unsafe_le)

theorem VEnv.HasPrimitives.addRules {decl : VInductDecl} {env env' : VEnv}
    (H : env.HasPrimitives) (h : decl.addRules env = some env') : env'.HasPrimitives :=
  VEnv.foldlM_inv (P := VEnv.HasPrimitives)
    (fun _ _ _ _ hP hstep => VEnv.foldlM_inv (P := VEnv.HasPrimitives)
      (fun _ _ _ _ hP' hs => by
        unfold VEnv.addRecRule at hs; split at hs
        · cases hs; exact hP'.addPat
        · cases hs) hP hstep) H h

/-- Registering ι rules keeps a valid checking environment valid, given that the new
environment is well formed and every new pattern is headed by a recursor of the map. -/
theorem CheckingEnv.Valid.addRules {safety : DefinitionSafety} {env : Environment}
    {venv venv' : VEnv} {decl : VInductDecl} (H : CheckingEnv.Valid safety env venv)
    (hP : decl.addRules venv = some venv') (hwf : venv'.WF)
    (hheads : ∀ p r, venv'.pats p r →
      venv.pats p r ∨ ∃ rec, env.constants.find? p.headConst = some (.recInfo rec)) :
    CheckingEnv.Valid safety env venv' := by
  have hle : venv ≤ venv' := VEnv.addRules_le hP
  have heads : EquationHeadsCoherent env.constants venv' :=
    H.equationHeads.extend id (fun df hdf => .inl (by rwa [VEnv.addRules_defeqs hP] at hdf))
      hheads
  exact {
    tr := {
      aligned := H.tr.aligned.addRules hP
      wf := hwf
      of_value := fun h1 h2 h3 => (H.tr.of_value h1 h2 h3).mono hle }
    hasPrimitives := H.hasPrimitives.addRules hP
    safePrimitives := H.safePrimitives
    blocks := H.blocks.extend id id (fun _ _ h => h) hle (InstallStage.le_refl _)
      (fun h1 h2 => by rw [h2] at h1; cases h1) (fun h1 h2 => by rw [h2] at h1; cases h1)
      (fun h1 h2 => by rw [h2] at h1; cases h1)
      (fun hp => .inl (by rwa [VEnv.addRules_projections hP] at hp))
    equationHeads := heads
    quot := fun hq => (H.quot hq).extend id hle heads }

/-- `InductInfoAlignment` reads only the source fields of the declaration. -/
theorem InductInfoAlignment.withRecs {C : ConstMap} {decl : VInductDecl} {i : Nat}
    {info : InductiveVal} (A : InductInfoAlignment C decl i info) (recs : List VRecursor) :
    InductInfoAlignment C (decl.withRecs recs) i info :=
  { A with constructor := fun k hk => let ⟨B⟩ := A.constructor k hk; ⟨{ B with }⟩ }

theorem InductInfosFromDecl.withRecs {C C' : ConstMap} {decl : VInductDecl}
    (H : InductInfosFromDecl C C' decl) (recs : List VRecursor) :
    InductInfosFromDecl C C' (decl.withRecs recs) := by
  intro n v h
  rcases H n v h with hold | ⟨i, hn, ⟨A⟩⟩
  · exact .inl hold
  · exact .inr ⟨i, hn, ⟨A.withRecs recs⟩⟩

end Lean4Lean
