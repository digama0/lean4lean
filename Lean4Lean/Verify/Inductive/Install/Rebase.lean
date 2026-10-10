import Lean4Lean.Verify.Inductive.Basic

/-! # Replaying `addInduct` over a larger environment

A successful `VEnv.addInduct` of a declaration replays over any larger environment in which the
declaration's names are fresh, stage by stage above the original stages
(`VEnv.addInduct_rebase`), and two successful installations of the same declaration are ordered
like their bases (`VEnv.addInduct_mono`). These are the model-side facts behind
`BlockCertificate.rebase`: a block certified at one safety level is installed in the models of
the other safety levels. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VEnv

theorem addPat_mono {env₁ env₂ : VEnv} {p : Pattern} {r : p.RHS × p.Check} (H : env₁ ≤ env₂) :
    env₁.addPat p r ≤ env₂.addPat p r where
  constants := H.constants
  defeqs := H.defeqs
  pats h := h.elim .inl (.inr ∘ H.pats)
  projections := H.projections

/-- A successful `addConst` fold replays over a larger environment in which its names are
fresh, above the original result. -/
theorem addConst_foldlM_rebase {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final init' : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      init ≤ init' → (∀ a ∈ l, init'.constants (nm a) = none) →
      ∃ final', l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init' = some final' ∧
        final ≤ final'
  | [], init, final, init', h, hle, _ => by
    simp [List.foldlM] at h; subst h; exact ⟨init', rfl, hle⟩
  | b :: bs, init, final, init', h, hle, hfr => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨-, hs1, -⟩ := addConst_eq h1
    cases h1' : init'.addConst (nm b) (ci b) with
    | none =>
      unfold VEnv.addConst at h1'; rw [hfr b (.head _)] at h1'; cases h1'
    | some e1' =>
      obtain ⟨-, -, ho1'⟩ := addConst_eq h1'
      have hfr' : ∀ a ∈ bs, e1'.constants (nm a) = none := by
        intro a ha
        have hne : nm b ≠ nm a := by
          intro e
          have := addConst_foldlM_fresh h2 a ha
          rw [← e, hs1] at this; cases this
        rw [ho1' _ hne]; exact hfr a (.tail _ ha)
      obtain ⟨final', hf', hle'⟩ := addConst_foldlM_rebase h2 (addConstVal_mono hle h1 h1') hfr'
      exact ⟨final', by simp only [List.foldlM, h1']; exact hf', hle'⟩

/-- A fold whose steps replay over larger environments replays as a whole. -/
theorem foldlM_rebase {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e₁ e₂ e₁' : VEnv} {x}, e₁ ≤ e₂ → f e₁ x = some e₁' →
      ∃ e₂', f e₂ x = some e₂' ∧ e₁' ≤ e₂') :
    ∀ {l : List α} {i₁ i₂ o₁ : VEnv}, i₁ ≤ i₂ → l.foldlM f i₁ = some o₁ →
      ∃ o₂, l.foldlM f i₂ = some o₂ ∧ o₁ ≤ o₂
  | [], i₁, i₂, o₁, hle, h => by simp [List.foldlM] at h; subst h; exact ⟨i₂, rfl, hle⟩
  | x :: xs, i₁, i₂, o₁, hle, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e2, h1', hle'⟩ := hf hle h1
    obtain ⟨o₂, h2', hle''⟩ := foldlM_rebase (f := f) hf hle' h2
    exact ⟨o₂, by simp only [List.foldlM, h1']; exact h2', hle''⟩

/-- A fold whose successful steps are monotone in the environment is monotone. -/
theorem foldlM_mono {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e₁ e₂ e₁' e₂' : VEnv} {x}, e₁ ≤ e₂ → f e₁ x = some e₁' → f e₂ x = some e₂' →
      e₁' ≤ e₂') :
    ∀ {l : List α} {i₁ i₂ o₁ o₂ : VEnv}, i₁ ≤ i₂ → l.foldlM f i₁ = some o₁ →
      l.foldlM f i₂ = some o₂ → o₁ ≤ o₂
  | [], _, _, _, _, hle, h, h' => by
    simp [List.foldlM] at h h'; subst h h'; exact hle
  | x :: xs, _, _, _, _, hle, h, h' => by
    simp only [List.foldlM] at h h'
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e1', h1', h2'⟩ := Option.bind_eq_some_iff.1 h'
    exact foldlM_mono (f := f) hf (hf hle h1 h1') h2 h2'

theorem addRecRule_rebase {e₁ e₂ e₁' : VEnv} {r : VRecursor} {ru : VRecRule} (hle : e₁ ≤ e₂)
    (h : e₁.addRecRule r ru = some e₁') :
    ∃ e₂', e₂.addRecRule r ru = some e₂' ∧ e₁' ≤ e₂' := by
  unfold VEnv.addRecRule at h ⊢
  split at h
  · cases h; rw [dif_pos ‹_›]; exact ⟨_, rfl, addPat_mono hle⟩
  · cases h

theorem addRules_rebase {decl : VInductDecl} {e₁ e₂ e₁' : VEnv} (hle : e₁ ≤ e₂)
    (h : decl.addRules e₁ = some e₁') :
    ∃ e₂', decl.addRules e₂ = some e₂' ∧ e₁' ≤ e₂' := by
  unfold VInductDecl.addRules at h ⊢
  exact foldlM_rebase (f := fun e r => r.rules.foldlM (fun e ru => e.addRecRule r ru) e)
    (fun {_ _ _ r} hle h => foldlM_rebase (f := fun e ru => VEnv.addRecRule e r ru)
      (fun hle h => addRecRule_rebase hle h) hle h) hle h

theorem addRules_mono {decl : VInductDecl} {e₁ e₂ e₁' e₂' : VEnv} (hle : e₁ ≤ e₂)
    (h : decl.addRules e₁ = some e₁') (h' : decl.addRules e₂ = some e₂') : e₁' ≤ e₂' := by
  obtain ⟨e₂'', h'', hle'⟩ := addRules_rebase hle h
  rw [h'] at h''; cases h''; exact hle'

/-- The ι-rule stage adds no constant. -/
theorem addRules_constants {decl : VInductDecl} {e e' : VEnv}
    (h : decl.addRules e = some e') : e'.constants = e.constants :=
  foldlM_inv (P := fun x => x.constants = e.constants)
    (fun _ _ _ _ hP hstep => foldlM_inv (P := fun x => x.constants = e.constants)
      (fun _ _ _ _ hP' hstep' => by
        unfold VEnv.addRecRule at hstep'; split at hstep'
        · cases hstep'; exact hP'
        · cases hstep') hP hstep) rfl h

/-- The constant stages of `addInduct`, as the one fold over `VInductDecl.consts`. -/
theorem addTypesCtorsProjsRecs_of_stages {decl : VInductDecl} {env envT envC envR : VEnv}
    (stT : decl.addTypes env = some envT) (stC : decl.addCtors envT = some envC)
    (stR : decl.addRecs (decl.addProjs envC) = some envR) :
    decl.addTypesCtorsProjsRecs env = some envR := by
  simp [VInductDecl.addTypesCtorsProjsRecs, VInductDecl.addTypesCtorsProjs,
    VInductDecl.addTypesCtors, stT, stC, stR]

theorem stages_of_addTypesCtorsProjsRecs {decl : VInductDecl} {env envR : VEnv}
    (h : decl.addTypesCtorsProjsRecs env = some envR) :
    ∃ envT envC, decl.addTypes env = some envT ∧ decl.addCtors envT = some envC ∧
      decl.addRecs (decl.addProjs envC) = some envR := by
  unfold VInductDecl.addTypesCtorsProjsRecs at h
  obtain ⟨envP, hP', hRec⟩ := Option.bind_eq_some_iff.1 h
  unfold VInductDecl.addTypesCtorsProjs at hP'
  obtain ⟨envC, hC', rfl⟩ := Option.map_eq_some_iff.1 hP'
  unfold VInductDecl.addTypesCtors at hC'
  obtain ⟨envT, hT, hC⟩ := Option.bind_eq_some_iff.1 hC'
  exact ⟨envT, envC, hT, hC, hRec⟩

/-- The stages of a successful installation are ordered like their bases. -/
theorem addStages_mono {decl : VInductDecl} {env env' envT envC envR envT' envC' envR' : VEnv}
    (hle : env ≤ env')
    (stT : decl.addTypes env = some envT) (stC : decl.addCtors envT = some envC)
    (stR : decl.addRecs (decl.addProjs envC) = some envR)
    (stT' : decl.addTypes env' = some envT') (stC' : decl.addCtors envT' = some envC')
    (stR' : decl.addRecs (decl.addProjs envC') = some envR') :
    envT ≤ envT' ∧ envC ≤ envC' ∧ envR ≤ envR' := by
  rw [VInductDecl.addTypes_eq_addConstVals] at stT stT'
  rw [VInductDecl.addCtors_eq_addConstVals] at stC stC'
  rw [VInductDecl.addRecs_eq_addConstVals] at stR stR'
  have hT := addConstVals_mono hle stT stT'
  have hC := addConstVals_mono hT stC stC'
  exact ⟨hT, hC, addConstVals_mono (addProjections_mono hC) stR stR'⟩

/-- Two successful installations of the same declaration are ordered like their bases. -/
theorem addInduct_mono {decl : VInductDecl} {env env' out out' : VEnv} (hle : env ≤ env')
    (h : env.addInduct decl = some out) (h' : env'.addInduct decl = some out') : out ≤ out' := by
  obtain ⟨envT, envC, envR, stT, stC, stR, stP⟩ := addInduct_stages h
  obtain ⟨envT', envC', envR', stT', stC', stR', stP'⟩ := addInduct_stages h'
  exact addRules_mono (addStages_mono hle stT stC stR stT' stC' stR').2.2 stP stP'

/-- The stages of a successful installation replay over a larger environment in which the
declaration's names are fresh. -/
theorem addInduct_rebase {decl : VInductDecl} {env env' envT envC envR out : VEnv}
    (stT : decl.addTypes env = some envT) (stC : decl.addCtors envT = some envC)
    (stR : decl.addRecs (decl.addProjs envC) = some envR) (stP : decl.addRules envR = some out)
    (hle : env ≤ env') (hfresh : ∀ b ∈ decl.consts, env'.constants b.1 = none) :
    ∃ envT' envC' envR' out', decl.addTypes env' = some envT' ∧
      decl.addCtors envT' = some envC' ∧ decl.addRecs (decl.addProjs envC') = some envR' ∧
      decl.addRules envR' = some out' ∧
      envT ≤ envT' ∧ envC ≤ envC' ∧ envR ≤ envR' ∧ out ≤ out' := by
  have hR := addTypesCtorsProjsRecs_of_stages stT stC stR
  rw [VInductDecl.addTypesCtorsProjsRecs_eq] at hR
  obtain ⟨envF, hF, -⟩ := Option.map_eq_some_iff.1 hR
  obtain ⟨envF', hF', -⟩ := addConst_foldlM_rebase (nm := Prod.fst) (ci := Prod.snd) hF hle hfresh
  have hR' : decl.addTypesCtorsProjsRecs env' = some (decl.addProjs envF') := by
    rw [VInductDecl.addTypesCtorsProjsRecs_eq, hF']; rfl
  obtain ⟨envT', envC', stT', stC', stR'⟩ := stages_of_addTypesCtorsProjsRecs hR'
  obtain ⟨hT, hC, hRle⟩ := addStages_mono hle stT stC stR stT' stC' stR'
  obtain ⟨out', stP', hout⟩ := addRules_rebase hRle stP
  exact ⟨envT', envC', _, out', stT', stC', stR', stP', hT, hC, hRle, hout⟩

theorem addConst_foldlM_constants_of_not_mem {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ {n}, (∀ a ∈ l, nm a ≠ n) → final.constants n = init.constants n
  | [], _, _, h, _, _ => by simp [List.foldlM] at h; rw [h]
  | b :: bs, init, final, h, n, hn => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [addConst_foldlM_constants_of_not_mem h2 (fun a ha => hn a (.tail _ ha)),
      (addConst_eq h1).2.2 n (hn b (.head _))]

/-- `addInduct` binds no name outside the declaration's constants. -/
theorem addInduct_constants_of_not_mem {decl : VInductDecl} {env out : VEnv}
    (h : env.addInduct decl = some out) {n : Name} (hn : ∀ b ∈ decl.consts, b.1 ≠ n) :
    out.constants n = env.constants n := by
  unfold VEnv.addInduct at h
  obtain ⟨envR, hR, hP⟩ := Option.bind_eq_some_iff.1 h
  rw [VInductDecl.addTypesCtorsProjsRecs_eq] at hR
  obtain ⟨envF, hF, rfl⟩ := Option.map_eq_some_iff.1 hR
  rw [addRules_constants hP, VInductDecl.addProjs, addProjections_constants]
  exact addConst_foldlM_constants_of_not_mem (nm := Prod.fst) (ci := Prod.snd) hF hn

/-- `addInduct` binds each of the declaration's constants. -/
theorem addInduct_constants_mem {decl : VInductDecl} {env out : VEnv}
    (h : env.addInduct decl = some out) {b : Name × VConstant} (hb : b ∈ decl.consts) :
    out.constants b.1 = some b.2 := by
  unfold VEnv.addInduct at h
  obtain ⟨envR, hR, hP⟩ := Option.bind_eq_some_iff.1 h
  rw [VInductDecl.addTypesCtorsProjsRecs_eq] at hR
  obtain ⟨envF, hF, rfl⟩ := Option.map_eq_some_iff.1 hR
  rw [addRules_constants hP, VInductDecl.addProjs, addProjections_constants]
  exact addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hF b hb

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

theorem foldlM_exists {α} {f : VEnv → α → Option VEnv} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ e, ∃ e', f e x = some e') → ∀ init, ∃ r, l.foldlM f init = some r
  | [], _, init => ⟨init, rfl⟩
  | x :: xs, hf, init => by
    obtain ⟨e1, h1⟩ := hf x (.head _) init
    obtain ⟨r, hr⟩ := foldlM_exists (fun y hy => hf y (.tail _ hy)) e1
    exact ⟨r, by simp only [List.foldlM, h1]; exact hr⟩

/-- The ι-rule stage succeeds once every reduct is closed. -/
theorem addRules_exists {decl : VInductDecl} (env : VEnv)
    (h : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ru.rhs.Closed) : ∃ env', decl.addRules env = some env' := by
  unfold VInductDecl.addRules
  exact foldlM_exists (fun r hr e => foldlM_exists (f := fun e ru => VEnv.addRecRule e r ru)
    (fun ru hru e => ⟨_, by unfold VEnv.addRecRule; rw [dif_pos (h r hr ru hru)]⟩) e) env

end VEnv

/-- A well-formed block stays well formed over a larger environment in which it installs. -/
theorem VInductBlock.WF.rebase {block : VInductBlock} {env env' envT' envC' envR' : VEnv}
    (H : block.WF env) (hle : env ≤ env')
    (ht : env'.addConstVals block.types = some envT')
    (hc : envT'.addConstVals block.ctors = some envC')
    (hr : (envC'.addProjections block.projections).addConstVals block.recursors = some envR') :
    block.WF env' := by
  obtain ⟨envT, envC, envR, ht₀, hc₀, hr₀, htw, hcw, hrw, hdw⟩ := H
  have hT := VEnv.addConstVals_mono hle ht₀ ht
  have hC := VEnv.addConstVals_mono hT hc₀ hc
  have hR := VEnv.addConstVals_mono (VEnv.addProjections_mono hC) hr₀ hr
  exact ⟨envT', envC', envR', ht, hc, hr, fun ci h => (htw ci h).mono hle,
    fun ci h => (hcw ci h).mono hT, fun ci h => (hrw ci h).mono (VEnv.addProjections_mono hC),
    fun df h => (hdw df h).mono hR⟩

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
    ⟨block, hcomp.mono hle hblock', hrecs⟩, ?_, H.rec_shape, H.rules_nodup, ?_, H.rule_shape, ?_⟩
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
      { tr := ⟨(h.tr.1.sf_mono hs).mono (VEnv.addProjections_mono hC), h.tr.2⟩  -- WAVE 2 rec COMPAT
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
