import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Typing.SingletonExtraction.TelescopeTyping
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Std.List
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.UniqueTyping

/-! Soundness of generated iota patterns.

A generated iota pattern is generated from an actual restored recursor equation.
Its soundness is the iota theorem `VIotaRuleShape.iota` for the restored
recursor, constructor and rule shapes. The shapes are read off the finite
compilation that registered the recursor; the restoration lemmas for nested
specializations are shared with the executable verification. -/

namespace Lean4Lean
open InductiveSignature

namespace InductiveSignature

theorem mem_familyNames {types : List VInductiveType} {n : Name} :
    n ∈ familyNames types ↔
      (∃ t ∈ types, t.name = n) ∨ ∃ t ∈ types, ∃ c ∈ t.ctors, c.name = n := by
  unfold familyNames
  simp only [List.mem_flatMap, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨t, ht, h | ⟨c, hc, rfl⟩⟩
    · exact .inl ⟨t, ht, h.symm⟩
    · exact .inr ⟨t, ht, c, hc, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, c, hc, rfl⟩)
    · exact ⟨t, ht, .inl rfl⟩
    · exact ⟨t, ht, .inr ⟨c, hc, rfl⟩⟩

theorem familyNames_append (l₁ l₂ : List VInductiveType) :
    familyNames (l₁ ++ l₂) = familyNames l₁ ++ familyNames l₂ := by
  simp [familyNames, List.flatMap_append]

/-- Restoration-only names are absent from the environment holding the source
types and constructors. Auxiliary heads are lowered family and constructor
names, fresh by the expanded formation; auxiliary recursor names are fresh
generated recursors. -/
theorem CompilationData.restorableNames_fresh
    {base envTypes envCtors : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (H : CompilationData base source expanded s g auxiliaries block)
    (hadded : base.addConstVals source.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals source.constructorConstants = some envCtors) :
    ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none := by
  intro n hn
  -- every name of the source block
  have hsrc : ∀ v, envCtors.constants n = some v → base.constants n = some v ∨
      n ∈ familyNames source.types := by
    intro v hv
    rcases VEnv.addConstVals_lookup_cases hctors hv with h | ⟨e, he, hname, _⟩
    · rcases VEnv.addConstVals_lookup_cases hadded h with h | ⟨e, he, hname, _⟩
      · exact .inl h
      · right
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
        exact mem_familyNames.mpr (.inl ⟨t, ht, hname⟩)
    · right
      obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp he
      exact mem_familyNames.mpr (.inr ⟨t, ht, e, hc, hname⟩)
  -- expanded names
  obtain ⟨envT, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  have hexpNames : familyNames expanded.types = familyNames source.types ++ familyNames direct := by
    rw [← H.model.familyNames, RestoresFamily.familyNames hfamilies, familyNames_append]
  obtain ⟨envExpT, envExpC, _, hexpT, hexpC, _⟩ := H.generatedIHsWellTyped
  have hfreshExp : ∀ m ∈ familyNames expanded.types, base.constants m = none := by
    intro m hm
    rcases mem_familyNames.mp hm with ⟨t, ht, rfl⟩ | ⟨t, ht, c, hc, rfl⟩
    · exact VEnv.addConstVals_names_fresh hexpT t.toVConstVal (List.mem_map.mpr ⟨t, ht, rfl⟩)
    · have h := VEnv.addConstVals_names_fresh hexpC c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)
      cases hb : base.constants c.name with
      | none => rfl
      | some v => rw [(VEnv.addConstVals_le hexpT).constants hb] at h; cases h
  cases hv : envCtors.constants n with
  | none => rfl
  | some v =>
  rcases List.mem_append.mp hn with hhead | hrec
  · have hdir : n ∈ familyNames direct := by
      rw [← compilationRestoration_heads_names (H.model.nparams.trans H.nparams) hdirect]
      exact hhead
    rcases hsrc v hv with hb | hs
    · rw [hfreshExp n (by rw [hexpNames]; exact List.mem_append_right _ hdir)] at hb
      cases hb
    · exact (H.source_head_disjoint hs hhead).elim
  · obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hrec
    have hg := H.recursor_source_mem hpair
    rcases hsrc v hv with hb | hs
    · obtain ⟨rc, hrc, hname⟩ := List.mem_map.mp hg
      rw [← hname, H.recursorsFresh rc hrc] at hb
      cases hb
    · exfalso
      have hnd := H.generatedNames
      simp only [List.map_append, List.nodup_append] at hnd
      have hin : pair.1 ∈ (expanded.typeConstants.map (·.name) ++
          expanded.constructorConstants.map (·.name)) := by
        have he : pair.1 ∈ familyNames expanded.types := by
          rw [hexpNames]; exact List.mem_append_left _ hs
        rcases mem_familyNames.mp he with ⟨t, ht, h⟩ | ⟨t, ht, c, hc, h⟩
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨t.toVConstVal,
            List.mem_map.mpr ⟨t, ht, rfl⟩, h⟩)
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨c,
            List.mem_flatMap.mpr ⟨t, ht, hc⟩, h⟩)
      exact hnd.2.2 _ hin _ hg rfl

end InductiveSignature

namespace VEnv

/-! ### Telescope instantiation without strengthening -/

theorem InstForallsC.det (H : InstForallsC env U Γ T args res)
    (H' : InstForallsC env U Γ T args res') : res = res' := by
  induction H with
  | nil => cases H'; rfl
  | cons _ _ ih => cases H' with | cons _ H' => exact ih H'

theorem InstForallsC.typed (H : InstForallsC env U Γ T args res) :
    ∀ x ∈ args, ∃ A, env.HasType U Γ x A := by
  induction H with
  | nil => intro _ h; cases h
  | cons ha _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, ha⟩
    · exact ih x hx

theorem InstForallsC.append (H : InstForallsC env U Γ T xs mid)
    (H' : InstForallsC env U Γ mid ys res) : InstForallsC env U Γ T (xs ++ ys) res := by
  induction H with
  | nil => exact H'
  | cons ha _ ih => exact .cons ha (ih H')

theorem _root_.Lean4Lean.VExpr.takeForalls_wrapForalls_le (dl : List VExpr) (body : VExpr)
    (hk : k ≤ dl.length) :
    (VExpr.wrapForalls dl body).takeForalls k =
      some (dl.take k, VExpr.wrapForalls (dl.drop k) body) := by
  have h := VExpr.takeForalls_wrapForalls_append (dl.take k) (dl.drop k) body
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hk] at h
  exact h

/-- Arguments typed along a prefix of a telescope instantiate it. -/
theorem InstForallsC.of_prefix :
    ∀ {xs dl : List VExpr} {body : VExpr}, xs.length ≤ dl.length →
      (∀ k (hk : k < xs.length) (hk' : k < dl.length),
        env.HasType U Γ xs[k] (dl[k].instOuter (xs.take k))) →
      ∃ res, InstForallsC env U Γ (VExpr.wrapForalls dl body) xs res
  | [], _, _, _, _ => ⟨_, .nil⟩
  | x :: xs, [], _, h, _ => by simp at h
  | x :: xs, d :: dl, body, h, hty => by
    have hx : env.HasType U Γ x d := hty 0 (by simp) (by simp)
    have ⟨res, H⟩ := InstForallsC.of_prefix (env := env) (U := U) (Γ := Γ) (xs := xs)
      (dl := VExpr.instDomains dl x 0)
      (body := body.inst x dl.length) (by simp at h ⊢; omega) (by
        intro k hk hk'
        have := hty (k + 1) (by simp; omega) (by simp at hk' ⊢; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
          List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
        rwa [VExpr.instDomains_getElem dl x 0 k (by simpa using hk'), Nat.zero_add])
    refine ⟨res, .cons hx ?_⟩
    change InstForallsC env U Γ ((VExpr.wrapForalls dl body).inst x 0) xs _
    rw [VExpr.wrapForalls_inst, Nat.zero_add]
    exact H

theorem _root_.Lean4Lean.VExpr.takeForalls_instOuter :
    ∀ {xs : List VExpr} {T : VExpr}, T.takeForalls n = some (doms, rest) →
      ∃ dr, (T.instOuter xs).takeForalls n = some dr
  | [], _, h => ⟨_, h⟩
  | x :: xs, T, h => by
    obtain ⟨_, h'⟩ := VExpr.takeForalls_inst (a := x) (k := xs.length) h
    exact VExpr.takeForalls_instOuter (xs := xs) h'

/-- Domain alignment after instantiating two telescopes at different
prefixes whose remainders are definitionally equal. Only Pi injectivity in the
current context is used. -/
theorem InstForallsC.domain_defeq_mid (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {dl dl₀ : List VExpr} {body body₀ : VExpr} {xs ys args bs : List VExpr} {m : Nat}
    (Hw : InstForallsC env U Γ (VExpr.wrapForalls dl body) (ys ++ args) res)
    (Hy₀ : InstForallsC env U Γ (VExpr.wrapForalls dl₀ body₀) xs mid₀)
    (Hy : InstForallsC env U Γ (VExpr.wrapForalls dl body) ys mid)
    (hT : env.IsDefEqU U Γ mid₀ mid)
    (hm : ys.length + m < dl.length) (hma : m < args.length)
    (hm₀ : xs.length + m < dl₀.length)
    (hbs : bs.length = m) (hbsE : List.Forall₂ (env.IsDefEqU U Γ) bs (args.take m)) :
    env.IsDefEqU U Γ ((dl₀[xs.length + m]'hm₀).instOuter (xs ++ bs))
      ((dl[ys.length + m]'hm).instOuter (ys ++ args.take m)) ∧
    env.HasType U Γ (args[m]'hma) ((dl[ys.length + m]'hm).instOuter (ys ++ args.take m)) := by
  -- the right telescope, split at the selected domain
  have hsplit := VExpr.wrapForalls_split dl body (ys.length + m) hm
  have hargs : ys ++ args = (ys ++ args.take m) ++ args.drop m := by
    rw [List.append_assoc, List.take_append_drop]
  rw [hargs] at Hw
  obtain ⟨midR, HwR, Hrest⟩ := Hw.append_inv
  obtain ⟨mid', Hy', Hm⟩ := HwR.append_inv
  cases Hy'.det Hy
  have hlenR : (ys ++ args.take m).length = (dl.take (ys.length + m)).length := by
    simp; omega
  rw [hsplit] at HwR
  have hmidR := HwR.wrapForalls_eq hlenR
  rw [VExpr.instOuter_forallE] at hmidR
  subst hmidR
  have hdrop : args.drop m = args[m] :: args.drop (m + 1) := List.drop_eq_getElem_cons hma
  rw [hdrop] at Hrest
  cases Hrest with
  | cons harg _ =>
  refine ⟨?_, harg⟩
  -- the left telescope, transported along the same arguments
  have hx : xs.length ≤ dl₀.length := by omega
  have Hy₀' := Hy₀
  rw [← List.take_append_drop xs.length dl₀, VExpr.wrapForalls_append] at Hy₀'
  have hmid₀ := Hy₀'.wrapForalls_eq (by simp; omega)
  have htf : ∃ dr, mid₀.takeForalls bs.length = some dr := by
    rw [hmid₀]
    exact VExpr.takeForalls_instOuter
      (VExpr.takeForalls_wrapForalls_le _ body₀ (by simp; omega))
  obtain ⟨dr, htf⟩ := htf
  obtain ⟨res₀, H₀, hres₀⟩ := InstForallsC.of_defeq henv hΓ Hm hT hbsE htf
  have Hfull := Hy₀.append H₀
  rw [VExpr.wrapForalls_split dl₀ body₀ (xs.length + m) hm₀] at Hfull
  have hres := Hfull.wrapForalls_eq (by simp; omega)
  rw [VExpr.instOuter_forallE] at hres
  subst hres
  have ⟨⟨_, hD⟩, _⟩ := hres₀.forallE_inv henv hΓ
  exact ⟨_, hD⟩

theorem _root_.List.mapM_some_getElem {f : α → Option β} :
    ∀ {l : List α} {out : List β}, l.mapM f = some out →
      ∀ k (hk : k < l.length) (hk' : k < out.length), f l[k] = some out[k] := by
  intro l out h k hk hk'
  exact Lean4Lean.List.forall₂_getElem (List.mapM_eq_some.mp h) k hk hk'

theorem _root_.List.mapM_some_length {f : α → Option β} {l : List α} {out : List β}
    (h : l.mapM f = some out) : out.length = l.length :=
  (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp h)).symm

theorem _root_.Lean4Lean.VExpr.wrapLams_inj :
    ∀ {d d' : List VExpr} {b b' : VExpr}, VExpr.wrapLams d b = VExpr.wrapLams d' b' →
      d.length = d'.length → d = d'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: d, y :: d', b, b', h, hl => by
    have h' : VExpr.lam x (VExpr.wrapLams d b) = VExpr.lam y (VExpr.wrapLams d' b') := h
    simp only [VExpr.lam.injEq] at h'
    rw [h'.1, VExpr.wrapLams_inj h'.2 (by simpa using hl)]

theorem _root_.Lean4Lean.VExpr.ClosedN.wrapForalls_inv_getElem :
    ∀ {ds : List VExpr} {b : VExpr} {k : Nat}, (VExpr.wrapForalls ds b).ClosedN k →
      ∀ i (hi : i < ds.length), ds[i].ClosedN (k + i)
  | [], _, _, _, i, hi => by simp at hi
  | d :: ds, b, k, h, i, hi => by
    have h' : d.ClosedN k ∧ (VExpr.wrapForalls ds b).ClosedN (k + 1) := h
    cases i with
    | zero => simpa using h'.1
    | succ i =>
      have := VExpr.ClosedN.wrapForalls_inv_getElem h'.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem _root_.Lean4Lean.VExpr.ClosedN.wrapForalls_body :
    ∀ {ds : List VExpr} {b : VExpr} {k : Nat}, (VExpr.wrapForalls ds b).ClosedN k →
      b.ClosedN (k + ds.length)
  | [], _, _, h => h
  | d :: ds, b, k, h => by
    have h' : d.ClosedN k ∧ (VExpr.wrapForalls ds b).ClosedN (k + 1) := h
    have := VExpr.ClosedN.wrapForalls_body h'.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Instantiating a term lifted past a middle block of binders ignores that block. -/
theorem _root_.Lean4Lean.VExpr.instOuter_liftN_mid {X : VExpr} {p mid f : List VExpr}
    (hX : X.ClosedN (p.length + f.length)) :
    (X.liftN mid.length f.length).instOuter (p ++ mid ++ f) = X.instOuter (p ++ f) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, ← VExpr.lift'_consN_skipN,
    VExpr.subst_lift']
  apply VExpr.subst_congr_closedN hX
  intro x hx
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN, liftVar, VExpr.Subst.ofList,
    List.length_append]
  by_cases hxf : x < f.length
  · simp only [hxf, ↓reduceIte, show x < p.length + mid.length + f.length by omega,
      show x < p.length + f.length by omega, ↓reduceDIte]
    rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
    congr 1; simp; omega
  · simp only [hxf, ↓reduceIte, show mid.length + x < p.length + mid.length + f.length by omega,
      hx, ↓reduceDIte]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega),
      List.getElem_append_left (by omega)]
    congr 1; omega

/-- The constructor field alignment of a recursor rule, after the recursor
parameters `P` and the actual constructor parameters `ys` are supplied. The
restored constructor type `R` is related to a source type `Q`, whose remainder
after `P` is the actual constructor telescope's remainder after `ys`. -/
theorem field_alignment (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {R Q T Rb Tb : VExpr} {Rd Td P ys fields : List VExpr} {L₀ L₁ : List VLevel}
    (hR : R = VExpr.wrapForalls Rd Rb) (hT : T = VExpr.wrapForalls Td Tb)
    (hRQ : env.IsDefEqU U Γ (R.instL L₀) (Q.instL L₀))
    (hP : P.length + fields.length = Rd.length)
    (hPty : ∀ k (hk : k < P.length) (hk' : k < Rd.length),
      env.HasType U Γ P[k] ((Rd[k].instL L₀).instOuter (P.take k)))
    (hQ : ∃ dr, (Q.instL L₀).takeForalls P.length = some dr)
    (Hw : InstForallsC env U Γ (T.instL L₁) (ys ++ fields) res)
    (hys : ys.length + fields.length = Td.length)
    (hmid : ∀ {midQ mid}, InstForallsC env U Γ (Q.instL L₀) P midQ →
      InstForallsC env U Γ (T.instL L₁) ys mid → midQ = mid)
    (i : Nat) (hi : i < fields.length) :
    env.HasType U Γ fields[i]
      (((Rd[P.length + i]'(by omega)).instL L₀).instOuter (P ++ fields.take i)) := by
  have Hy₀ : ∃ mid₀, InstForallsC env U Γ (R.instL L₀) P mid₀ := by
    rw [hR, VExpr.instL_wrapForalls]
    exact InstForallsC.of_prefix (by simp; omega) fun k hk hk' => by
      rw [List.getElem_map]; exact hPty k hk (by simpa using hk')
  obtain ⟨mid₀, Hy₀⟩ := Hy₀
  obtain ⟨dr, hQ⟩ := hQ
  have hPrefl : List.Forall₂ (env.IsDefEqU U Γ) P P :=
    List.forall₂_of_getElem rfl fun k hk _ => IsDefEqU.refl ⟨_, hPty k hk (by omega)⟩
  obtain ⟨midQ, HyQ, hQ₀⟩ := InstForallsC.of_defeq henv hΓ Hy₀ hRQ.symm hPrefl hQ
  obtain ⟨mid, Hy, Hf⟩ := Hw.append_inv
  cases hmid HyQ Hy
  have hfty := Hf.typed
  rw [hR, VExpr.instL_wrapForalls] at Hy₀
  rw [hT, VExpr.instL_wrapForalls] at Hw Hy
  have hfrefl : List.Forall₂ (env.IsDefEqU U Γ) (fields.take i) (fields.take i) :=
    List.forall₂_of_getElem rfl fun k hk _ => by
      obtain ⟨_, h⟩ := hfty _ (List.mem_of_mem_take (List.getElem_mem hk))
      exact IsDefEqU.refl ⟨_, h⟩
  obtain ⟨hdef, hty⟩ := InstForallsC.domain_defeq_mid henv hΓ Hw Hy₀ Hy hQ₀.symm
    (m := i) (bs := fields.take i) (by simp; omega) hi (by simp; omega) (by simp; omega) hfrefl
  simp only [List.getElem_map] at hdef hty
  exact hty.defeqU_r henv hΓ hdef.symm

end VEnv

namespace VEnv

private theorem stripLams_wrap' (domains : List VExpr) (e : VExpr) :
    (VExpr.wrapLams domains e).stripLams = e.stripLams := by
  induction domains with
  | nil => rfl
  | cons d ds ih => exact ih

private theorem map_liftN_inj {K : Nat} :
    ∀ {xs ys : List VExpr}, xs.map (·.liftN K) = ys.map (·.liftN K) → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [VExpr.liftN_inj.mp h.1, map_liftN_inj h.2]

/-- The restored major family application determines the restored family head. -/
private theorem head_of_major (head : RestoredFamilyHead) {n : Name} {lv : List VLevel}
    {xs tail : List VExpr} {K : Nat}
    (h : VExpr.mkApps (.const head.name head.levels) (head.arguments.map (·.liftN K) ++ tail) =
      VExpr.mkApps (.const n lv) (xs.map (·.liftN K) ++ tail)) :
    head.name = n ∧ head.levels = lv ∧ head.arguments = xs := by
  have h1 := congrArg VExpr.getAppFnArgs h
  rw [VerifyInductive.VExpr.getAppFnArgs_mkApps, VerifyInductive.VExpr.getAppFnArgs_mkApps] at h1
  simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, List.nil_append, Prod.mk.injEq,
    VExpr.const.injEq] at h1
  obtain ⟨⟨hn, hl⟩, ha⟩ := h1
  exact ⟨hn, hl, map_liftN_inj (List.append_cancel_right ha)⟩

theorem _root_.Lean4Lean.VExpr.ClosedN.wrapForalls_drop {A B : List VExpr} {b : VExpr}
    (h : (VExpr.wrapForalls (A ++ B) b).ClosedN k) :
    (VExpr.wrapForalls B b).ClosedN (k + A.length) := by
  rw [VExpr.wrapForalls_append] at h
  exact VExpr.ClosedN.wrapForalls_body h

set_option maxHeartbeats 4000000 in
/-- The restored recursor, constructor and rule shapes of an installed recursor
rule, at the restored head of its owner family. -/
theorem RecursorRegistered.iota_core {data : RecursorData} (henv : env.WF)
    (hr : RecursorRegistered env data)
    {index : Fin data.schema.signature.constructors.size}
    (ho : data.schema.signature.constructors[index].owner = data.owner)
    (hg : data.equation index = some equation) :
    ∃ (head : RestoredFamilyHead)
      (Hrec : VRecursorShape env data.name data.uvars data.schema.signature.params.length
        head.arguments.length data.schema.signature.families.size
        data.schema.signature.constructors.size data.numIndices head.name head.levels
        head.arguments)
      (Hctor : VConstructorShape env (data.ruleConstructor index) head.levels.length
        head.arguments.length data.schema.signature.constructors[index].fields.length
        data.numIndices head.name)
      (I : VIotaRuleShape env data.name data.uvars data.schema.signature.params.length
        head.arguments.length data.schema.signature.families.size
        data.schema.signature.constructors.size data.numIndices (data.ruleConstructor index)
        head.levels data.schema.signature.constructors[index].fields.length equation
        head.arguments),
      env.Rigid head.name ∧
      (∀ j (h1 : j < I.doms.length) (h2 : j < Hrec.doms.length),
        j < data.schema.signature.params.length + data.schema.signature.families.size +
          data.schema.signature.constructors.size → I.doms[j] = Hrec.doms[j]) ∧
      ∀ {U : Nat} {Γ : List VExpr} {ls : List VLevel} {P fields Mid : List VExpr} {res : VExpr},
        OnCtx Γ (env.IsType U) → (∀ l ∈ ls, l.WF U) → ls.length = data.uvars →
        P.length = data.schema.signature.params.length →
        fields.length = data.schema.signature.constructors[index].fields.length →
        Mid.length = data.schema.signature.families.size + data.schema.signature.constructors.size →
        (∀ k (hk : k < P.length) (hk' : k < I.doms.length),
          env.HasType U Γ P[k] ((I.doms[k].instL ls).instOuter (P.take k))) →
        InstForallsC env U Γ (Hctor.type.instL (head.levels.map (·.inst ls)))
          (head.arguments.map (fun p => (p.instL ls).instOuter P) ++ fields) res →
        ∀ i (hi : i < fields.length) (hi' : data.schema.signature.params.length +
            data.schema.signature.families.size + data.schema.signature.constructors.size + i <
            I.doms.length),
          env.HasType U Γ fields[i] ((I.doms[data.schema.signature.params.length +
            data.schema.signature.families.size + data.schema.signature.constructors.size + i].instL
              ls).instOuter (P ++ Mid ++ fields.take i)) := by
  have hr₀ := hr
  have hdef := hr.equation_present hg
  have hmajor₀ := hr.equation_major hg
  obtain ⟨base, installBase, source, expanded, g, aux, block, installed,
    hdata, hprior, hbase, hres, _, hu, hlv, htg, hi, he⟩ := hr
  have hinst : data.recursorInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [RecursorData.recursorInstance, Instance.mk.injEq]
      exact ⟨hu, hlv, htg, funext fun owner => (hdata.recursorNames owner).symm⟩
  let r := compilationRestoration source aux
  have heq : r.equation (g.equation index) = some equation := by
    have := hg
    unfold RecursorData.equation at this
    rwa [hres, hinst] at this
  obtain ⟨-, -, -, -, envTypes, envCtors, hadded, hctorsAdded, -, -⟩ := hdata.sourceWF
  have hfreshC := hdata.restorableNames_fresh hadded hctorsAdded
  have hfreshT : ∀ n ∈ r.restorableNames, envTypes.constants n = none := by
    intro n hn
    cases h : envTypes.constants n with
    | none => rfl
    | some v =>
      have := (VEnv.addConstVals_le hctorsAdded).constants h
      rw [hfreshC n hn] at this; cases this
  have hbaseEnv : base ≤ env := hbase.trans ((VInductBlock.install_le hi).trans he)
  have hinstalled := VInductBlock.install_constants hi
  have hle : envCtors ≤ env := by
    apply VEnv.addConstVals_le_target (VEnv.addConstVals_le_target hbaseEnv hadded ?_) hctorsAdded
    · intro v hv
      exact he.constants (hinstalled v (List.mem_append_right _ (by rw [hdata.ctors]; exact hv)))
    · intro v hv
      exact he.constants (hinstalled v (List.mem_append_left _ (by rw [hdata.types]; exact hv)))
  obtain ⟨head, hhead, _, _, hargs, happ, Hctors⟩ :=
    hdata.restoredFamilyHead_spec hadded hctorsAdded hfreshT hfreshC data.owner
  obtain ⟨-, happC⟩ := Hctors index ho
  have hindices := hdata.model.constructorArity _
    (Array.getElem_mem_toList (xs := data.schema.signature.constructors) index.isLt)
  have hnotHead : r.heads.find? (fun h => h.auxiliary ==
      g.recursorName data.schema.signature.constructors[index].owner) = none := by
    apply Restoration.heads_find?_eq_none
    intro hm
    obtain ⟨h, hh, he'⟩ := List.mem_map.mp hm
    exact hdata.heads_not_recursors _ h hh he'
  -- the recursor type
  obtain ⟨type, htype⟩ := hr₀.recursorType_exists
  have hcst := hr₀.recursorType htype
  have htype' : r.expr (g.recursorType data.owner) = some type := by
    unfold RecursorData.recursorType at htype
    rwa [hres, hinst] at htype
  have hrecType : ∃ type, r.expr (g.recursorType
      data.schema.signature.constructors[index].owner) = some type ∧
      env.constants (r.recursorName (g.recursorName
        data.schema.signature.constructors[index].owner)) = some ⟨g.uvars, type⟩ := by
    refine ⟨type, by rw [ho]; exact htype', ?_⟩
    have hn : data.name = r.recursorName (g.recursorName data.owner) := by
      unfold RecursorData.name; rw [hres, hdata.recursorNames]
    rw [ho, ← hn, ← hu]; exact hcst
  obtain ⟨_, -, Hadm⟩ := hdata.admissible
  obtain ⟨head3, hhead3, RP, RF, hRP, hRF, Hfd⟩ :=
    hdata.restoredConstructorFieldDomains hprior hadded hctorsAdded hfreshT hfreshC hle henv
      Hadm.levels_wf index data.owner ho
  have h33 : head3 = head := Option.some.inj (hhead3.symm.trans hhead)
  rw [h33] at Hfd
  obtain ⟨I⟩ := Restoration.restored_iota_shape g r index heq hdef henv VEnv.LE.rfl
    (fun _ => rfl) hrecType hindices hnotHead happC
    (fun h hh => (hdata.restorationScoped.2.2.1 h hh).2) ⟨RP, RF, hRP, hRF, Hfd⟩
  obtain ⟨head2, hhead2, fields, ⟨hctorShape⟩⟩ := hdata.restoredConstructorShape hprior
    hadded hctorsAdded hfreshT hfreshC hle index data.owner ho
  cases Option.some.inj (hhead2.symm.trans hhead)
  -- names and counts
  have hname : data.name = r.recursorName (g.recursorName data.owner) := by
    unfold RecursorData.name
    rw [hres, hdata.recursorNames]
  have I : VIotaRuleShape env data.name data.uvars data.schema.signature.params.length
      head.arguments.length data.schema.signature.families.size
      data.schema.signature.constructors.size data.numIndices
      (r.restoredHeadName data.schema.signature.constructors[index].name)
      head.levels data.schema.signature.constructors[index].fields.length equation
      head.arguments := by
    have := I
    simp only [ho] at this
    rw [hname, hu]
    exact this
  -- the constructor name
  have hctorName : data.ruleConstructor index =
      r.restoredHeadName data.schema.signature.constructors[index].name := by
    obtain ⟨fn, lv, args, hfn⟩ := hmajor₀
    have hl := I.lhs_eq
    have hb := I.lhs_pattern
    have hs : equation.lhs.stripLams = I.lhsBody := by
      rw [hl, stripLams_wrap', hb]
      exact VExpr.stripLams_of_head_const (VExpr.getAppFnArgs_mkApps_head _ _)
    rw [hs, hb, VExpr.mkApps_append, VExpr.mkApps] at hfn
    simp only [List.foldl_cons, List.foldl_nil, VExpr.app.injEq] at hfn
    have h2 := congrArg (fun e : VExpr => e.getAppFnArgs.1) hfn.2
    rw [VExpr.getAppFnArgs_mkApps_head, VExpr.getAppFnArgs_mkApps_head] at h2
    unfold RecursorData.ruleConstructor
    exact (VExpr.const.inj h2).1.symm
  rw [← hctorName] at I hctorShape
  -- the recursor shape
  obtain ⟨pre, major, hpre, hm, rfl⟩ := r.expr_recursorType_eq_some htype'
  have hprelen : pre.length = data.schema.signature.params.length +
      data.schema.signature.families.size + data.schema.signature.constructors.size +
      data.numIndices := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)),
      g.recursorPrefix_length data.owner]
    rfl
  have hmaj := Option.some.inj (hm.symm.trans happ)
  let Hrec : VRecursorShape env data.name data.uvars data.schema.signature.params.length
      head.arguments.length data.schema.signature.families.size
      data.schema.signature.constructors.size data.numIndices head.name head.levels
      head.arguments := {
    ctorParams_length := rfl
    ctorParams_closed := hargs
    type := _
    const := hcst
    doms := pre ++ [major]
    result := g.recursorBody data.owner
    type_eq := rfl
    doms_length := by simp [hprelen]
    major_eq := by
      rw [← hprelen, List.getElem?_concat_length, hmaj, vars_eq_bvarRange, Nat.add_zero]
      rfl }
  -- rigidity of the major family
  have hrigid : env.Rigid head.name := by
    have hm' : equation.HasConstructorMajor (data.ruleConstructor index) := by
      unfold RecursorData.ruleConstructor; exact hmajor₀
    obtain ⟨ci, hci, F, ls, hF, _, hFr⟩ := henv.installed_constructor_result_rigid hdef hm'
    rw [hctorShape.const] at hci
    cases hci
    rw [hctorShape.type_eq, VExpr.forallResult_wrapForalls,
      VExpr.forallResult_of_head (VExpr.getAppFnArgs_mkApps_head _ _),
      VExpr.getAppFnArgs_mkApps_head] at hF
    cases hF
    exact hFr
  have hfields := VIotaRuleShape.fieldCount henv I (henv.ordered.defEqWF hdef) Hrec hctorShape hrigid
  subst hfields
  -- the restored rule telescope
  have hlhsGen : ∃ body, (g.equation index).lhs = VExpr.wrapLams (g.params ++ g.motives ++
      g.minors ++ insertBinders ((data.schema.signature.fieldTypes
        data.schema.signature.constructors[index]).map (·.instL g.levels))
        (data.schema.signature.families.size + data.schema.signature.constructors.size)) body :=
    ⟨_, rfl⟩
  obtain ⟨bodyGen, hlhsGen⟩ := hlhsGen
  have hl := (Restoration.equation_parts heq).1
  rw [hlhsGen, r.expr_wrapLams_eq] at hl
  generalize hdomsGen : g.params ++ g.motives ++ g.minors ++ insertBinders
    ((data.schema.signature.fieldTypes data.schema.signature.constructors[index]).map
      (·.instL g.levels))
    (data.schema.signature.families.size + data.schema.signature.constructors.size) = domsGen at hl
  cases hD : domsGen.mapM r.expr with
  | none => rw [hD] at hl; cases hl
  | some D' =>
  cases hb : r.expr bodyGen with
  | none => rw [hD, hb] at hl; cases hl
  | some lb =>
  rw [hD, hb] at hl
  simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hl
  have hDlen := List.mapM_some_length hD
  have hdomsLen : domsGen.length = data.schema.signature.params.length +
      data.schema.signature.families.size + data.schema.signature.constructors.size +
      data.schema.signature.constructors[index].fields.length := by
    rw [← hdomsGen]
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders, fieldTypes,
      Nat.add_assoc]
  have hID : I.doms = D' := VExpr.wrapLams_inj (I.lhs_eq.symm.trans hl.symm) (by
    rw [I.doms_length, hDlen, hdomsLen])
  have hpreFirst : (g.params ++ g.motives ++ g.minors).length =
      data.schema.signature.params.length + data.schema.signature.families.size +
        data.schema.signature.constructors.size := by
    simp [Instance.params, Instance.motives, Instance.minors]; omega
  have hpreLen' := List.mapM_some_length hpre
  refine ⟨head, Hrec, hctorShape, I, hrigid, ?_, ?_⟩
  · intro j h1 h2 hj
    have hjD : j < D'.length := hID ▸ h1
    have hjp : j < pre.length := by rw [hprelen]; omega
    have e1 := List.mapM_some_getElem hD j (by omega) hjD
    have e2 := List.mapM_some_getElem hpre j (by omega) hjp
    have hg1 : domsGen[j]'(by omega) = (g.params ++ g.motives ++ g.minors)[j]'(by omega) := by
      subst hdomsGen
      exact List.getElem_append_left (by omega)
    have hg2 : (g.recursorPrefix data.owner)[j]'(by omega) =
        (g.params ++ g.motives ++ g.minors)[j]'(by omega) := by
      unfold Instance.recursorPrefix
      exact List.getElem_append_left (by omega)
    rw [hg1] at e1
    rw [hg2] at e2
    have : D'[j] = pre[j] := Option.some.inj (e1.symm.trans e2)
    have h3 : (pre ++ [major])[j]'(by simp; omega) = pre[j] := List.getElem_append_left hjp
    simp only [hID]
    exact this.trans h3.symm
  · intro U Γ ls P fields Mid res hΓ hls hlsl hPl hfl hMid hPty Hw i hi hi'
    obtain ⟨envTypes', direct, hadded', hdirect, hwellFormed, Hfam⟩ := hdata.correspondence
    cases Option.some.inj (hadded.symm.trans hadded')
    obtain ⟨_, -, Hadm⟩ := hdata.admissible
    have hlevelsLen : g.levels.length = source.uvars :=
      Hadm.levels_length.trans (hdata.model.uvars.trans hdata.uvars)
    have hnp : data.schema.signature.params.length = source.nparams :=
      hdata.model.nparams.trans hdata.nparams
    have hlsg : ls.length = g.uvars := hlsl.trans hu
    have hL₀ : ∀ l ∈ g.levels.map (·.inst ls), l.WF U := by
      intro l hl
      obtain ⟨l', -, rfl⟩ := List.mem_map.mp hl
      exact VLevel.WF.inst hls
    -- the normalized constructor and its restoration
    have hdeclLen : data.schema.signature.declaration.types.length =
        data.schema.signature.families.size := by simp [InductiveSignature.declaration]
    have hown : data.schema.signature.constructors[index].owner.val <
        data.schema.signature.declaration.types.length := by
      rw [hdeclLen]; exact data.schema.signature.constructors[index].owner.isLt
    have hlenF := Lean4Lean.List.Forall₂.length_eq Hfam
    have hown' : data.schema.signature.constructors[index].owner.val <
        (source.types ++ direct).length := hlenF ▸ hown
    have Hat := Lean4Lean.List.forall₂_getElem Hfam _ hown hown'
    obtain ⟨src, hsrc, hsrcName, -, R, hR, hRQ₀⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l Hat.constructors _ (declaration_ctor_mem _ index hown)
    have hcty : data.schema.signature.constructorType data.schema.signature.constructors[index] =
        VExpr.wrapForalls (data.schema.signature.params ++ data.schema.signature.fieldTypes
          data.schema.signature.constructors[index]) (data.schema.signature.familyApp
          data.schema.signature.constructors[index].owner (VLevel.params data.schema.signature.uvars)
          (vars data.schema.signature.params.length
            data.schema.signature.constructors[index].fields.length)
          data.schema.signature.constructors[index].indices) := rfl
    rw [hcty, r.expr_wrapForalls] at hR
    cases hRd : (data.schema.signature.params ++ data.schema.signature.fieldTypes
        data.schema.signature.constructors[index]).mapM r.expr with
    | none => rw [hRd] at hR; cases hR
    | some Rd =>
    rw [hRd] at hR
    cases hRb : r.expr (data.schema.signature.familyApp
          data.schema.signature.constructors[index].owner (VLevel.params data.schema.signature.uvars)
          (vars data.schema.signature.params.length
            data.schema.signature.constructors[index].fields.length)
          data.schema.signature.constructors[index].indices) with
    | none => rw [hRb] at hR; cases hR
    | some Rb =>
    rw [hRb] at hR
    simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hR
    subst hR
    have hRdLen : Rd.length = data.schema.signature.params.length +
        data.schema.signature.constructors[index].fields.length := by
      rw [List.mapM_some_length hRd]; simp [fieldTypes]
    obtain ⟨_, hRQ⟩ := hRQ₀
    have hTypesLe : envTypes ≤ env := (VEnv.addConstVals_le hctorsAdded).trans hle
    have hRQe := hRQ.mono hTypesLe
    have hRC : (VExpr.wrapForalls Rd Rb).ClosedN 0 := by
      have := VExpr.WF.closedN henv.ordered (Γ := []) ⟨_, hRQe.hasType.1⟩ trivial
      simpa using this
    have hRQΓ : env.IsDefEqU U Γ ((VExpr.wrapForalls Rd Rb).instL (g.levels.map (·.inst ls)))
        (src.type.instL (g.levels.map (·.inst ls))) :=
      ⟨_, (hRQe.instL hL₀).weak0 henv.ordered⟩
    -- the rule domains in terms of the restored constructor type
    have hft : (data.schema.signature.fieldTypes data.schema.signature.constructors[index]).length =
        data.schema.signature.constructors[index].fields.length := by simp [fieldTypes]
    have hgp : g.params.length = data.schema.signature.params.length := by simp [Instance.params]
    have hgm : g.motives.length = data.schema.signature.families.size := by
      simp [Instance.motives]
    have hgn : g.minors.length = data.schema.signature.constructors.size := by
      simp [Instance.minors]
    have hDk : ∀ k (hk : k < data.schema.signature.params.length) (h1 : k < D'.length)
        (h2 : k < Rd.length), D'[k] = Rd[k].instL g.levels := by
      intro k hk h1 h2
      have e1 := List.mapM_some_getElem hD k (by omega) h1
      have e2 := List.mapM_some_getElem hRd k (by rw [List.length_append, hft]; omega) h2
      have hgk : domsGen[k]'(by omega) =
          (data.schema.signature.params[k]'hk).instL g.levels := by
        subst hdomsGen
        have h₁ : k < (g.params ++ g.motives ++ g.minors).length := by
          simp only [List.length_append, hgp, hgm, hgn]; omega
        have h₂ : k < (g.params ++ g.motives).length := by
          simp only [List.length_append, hgp, hgm]; omega
        have h₃ : k < g.params.length := by rw [hgp]; exact hk
        rw [List.getElem_append_left h₁, List.getElem_append_left h₂,
          List.getElem_append_left h₃]
        simp [Instance.params]
      rw [List.getElem_append_left hk] at e2
      rw [hgk, ← Restoration.expr_instL, e2] at e1
      exact (Option.some.inj e1).symm
    have hscoped : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams :=
      fun h hh => (hdata.restorationScoped.2.2.1 h hh).2
    have hDf : ∀ (h1 : data.schema.signature.params.length + data.schema.signature.families.size +
          data.schema.signature.constructors.size + i < D'.length)
        (h2 : data.schema.signature.params.length + i < Rd.length),
        D'[data.schema.signature.params.length + data.schema.signature.families.size +
          data.schema.signature.constructors.size + i] =
        ((Rd[data.schema.signature.params.length + i]).instL g.levels).liftN
          (data.schema.signature.families.size + data.schema.signature.constructors.size) i := by
      intro h1 h2
      have e1 := List.mapM_some_getElem hD _ (by omega) h1
      have e2 := List.mapM_some_getElem hRd _ (by rw [List.length_append, hft]; omega) h2
      have hgi : domsGen[data.schema.signature.params.length + data.schema.signature.families.size +
          data.schema.signature.constructors.size + i]'(by omega) =
          (((data.schema.signature.fieldTypes data.schema.signature.constructors[index])[i]'(by
            rw [hft]; omega)).instL g.levels).liftN
            (data.schema.signature.families.size + data.schema.signature.constructors.size) i := by
        subst hdomsGen
        have h₁ : (g.params ++ g.motives ++ g.minors).length ≤
            data.schema.signature.params.length + data.schema.signature.families.size +
              data.schema.signature.constructors.size + i := by
          simp only [List.length_append, hgp, hgm, hgn]; omega
        rw [List.getElem_append_right h₁]
        have hidx : data.schema.signature.params.length + data.schema.signature.families.size +
            data.schema.signature.constructors.size + i - (g.params ++ g.motives ++ g.minors).length =
            i := by simp only [List.length_append, hgp, hgm, hgn]; omega
        simp only [hidx, insertBinders, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      rw [List.getElem_append_right (Nat.le_add_right _ _)] at e2
      simp only [Nat.add_sub_cancel_left] at e2
      rw [hgi, ← Restoration.expr_liftN r hscoped, ← Restoration.expr_instL, e2] at e1
      exact (Option.some.inj e1).symm
    have hPty' : ∀ k (hk : k < P.length) (hk' : k < Rd.length),
        env.HasType U Γ P[k] ((Rd[k].instL (g.levels.map (·.inst ls))).instOuter (P.take k)) := by
      intro k hk hk'
      have h1 : k < I.doms.length := by
        have := I.doms_length; omega
      have h1' : k < D'.length := by rw [hDlen, hdomsLen]; omega
      have := hPty k hk h1
      rwa [List.getElem_of_eq hID h1, hDk k (by omega) h1' hk', VExpr.instL_instL] at this
    have key : (∃ dr, (src.type.instL (g.levels.map (·.inst ls))).takeForalls P.length = some dr) ∧
        (∀ {midQ mid}, InstForallsC env U Γ (src.type.instL (g.levels.map (·.inst ls))) P midQ →
          InstForallsC env U Γ (hctorShape.type.instL (head.levels.map (·.inst ls)))
            (head.arguments.map (fun p => (p.instL ls).instOuter P)) mid → midQ = mid) := by
      have hKeq : VExpr.mkApps (.const head.name head.levels)
          (head.arguments.map (·.liftN (data.schema.signature.families.size +
            data.schema.signature.constructors.size + data.numIndices)) ++
            vars data.numIndices 0) = _ := hmaj.symm.trans rfl
      have hfamName : data.schema.signature.families[data.owner].name =
          ((source.types ++ direct)[data.schema.signature.constructors[index].owner.val]'hown').name := by
        have := Hat.name
        simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx,
          Array.getElem_toList] at this
        refine (congrArg (fun o : Fin data.schema.signature.families.size =>
          data.schema.signature.families[o].name) ho).symm.trans ?_
        simpa using this
      have hTc := hctorShape.const
      obtain ⟨Td, Tb, hT, hTlen⟩ : ∃ Td Tb, hctorShape.type = VExpr.wrapForalls Td Tb ∧
          Td.length = head.arguments.length +
            data.schema.signature.constructors[index].fields.length :=
        ⟨_, _, hctorShape.type_eq, hctorShape.doms_length⟩
      generalize hctorShape.type = Tc at hT hTc ⊢
      by_cases hsrcFam : data.schema.signature.constructors[index].owner.val < source.types.length
      · -- a source family
        have hsrcIn : src ∈ (source.types[data.schema.signature.constructors[index].owner.val]'hsrcFam).ctors := by
          have := hsrc
          rwa [List.getElem_append_left hsrcFam] at this
        have hfamSrc : data.schema.signature.families[data.owner].name =
            (source.types[data.schema.signature.constructors[index].owner.val]'hsrcFam).name := by
          rw [hfamName, List.getElem_append_left hsrcFam]
        have hfamMem : data.schema.signature.families[data.owner].name ∈ familyNames source.types :=
          mem_familyNames.mpr (.inl ⟨_, List.getElem_mem hsrcFam, hfamSrc.symm⟩)
        have hfind : r.heads.find? (fun h => h.auxiliary == data.schema.signature.families[data.owner].name) = none :=
          Restoration.heads_find?_eq_none (hdata.source_head_disjoint hfamMem)
        have hconstFam : envTypes.constants data.schema.signature.families[data.owner].name =
            some (source.types[data.schema.signature.constructors[index].owner.val]'hsrcFam).toVConstVal.toVConstant := by
          rw [hfamSrc]
          exact VEnv.addConstVals_get hadded (List.mem_map.mpr ⟨_, List.getElem_mem hsrcFam, rfl⟩)
        have hfreshRecs : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
          fun p hp => hfreshT p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
        have hrecName := Restoration.recursorName_of_constants hfreshRecs hconstFam
        have hmajS := r.expr_recursorMajor_source g data.owner hfind hrecName
        have happ' : r.expr (g.recursorMajor data.owner) = _ := happ
        rw [hmajS] at happ'
        have hmajEq := (Option.some.inj happ').symm
        simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp] at hmajEq
        rw [← vars_map_liftN data.schema.signature.params.length] at hmajEq
        obtain ⟨-, hlev, hargsEq⟩ := head_of_major head hmajEq
        -- the actual constructor is the source constructor
        have hsrcCtor : src ∈ source.constructorConstants :=
          List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrcFam, hsrcIn⟩
        have hconstSrc : env.constants src.name = some src.toVConstant :=
          he.constants (hinstalled src (List.mem_append_right _ (by rw [hdata.ctors]; exact hsrcCtor)))
        have hrc : data.ruleConstructor index = src.name := by
          unfold RecursorData.ruleConstructor
          rw [hres, ← hsrcName]
          apply hdata.headName_source
          exact mem_familyNames.mpr (.inr ⟨_, List.getElem_mem hsrcFam, src, hsrcIn, hsrcName.symm⟩)
        have hTy : Tc = src.type := by
          rw [hrc, hconstSrc] at hTc
          exact (congrArg VConstant.type (Option.some.inj hTc)).symm
        have hys : head.arguments.map (fun p => (p.instL ls).instOuter P) = P := by
          rw [hargsEq, vars_eq_bvarRange, Nat.add_zero]
          have h1 : (VExpr.bvarRange data.schema.signature.params.length
              data.schema.signature.params.length).map (fun p => (p.instL ls).instOuter P) =
              ((VExpr.bvarRange data.schema.signature.params.length
                data.schema.signature.params.length).map (VExpr.instL ls)).map (·.instOuter P) := by
            rw [List.map_map]; rfl
          rw [h1, VExpr.instL_bvarRange, VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by omega),
            hPl, Nat.sub_self, List.drop_zero, List.take_of_length_le (by omega)]
        refine ⟨?_, ?_⟩
        · rw [← hTy, hT, VExpr.instL_wrapForalls]
          exact ⟨_, VExpr.takeForalls_wrapForalls_le _ _ (by
            simp only [List.length_map, hTlen, hargsEq]; simp; omega)⟩
        · intro midQ mid HQ HT
          rw [hys, hlev, hTy] at HT
          exact HQ.det HT
      · -- an auxiliary family
        have hge : source.types.length ≤ data.schema.signature.constructors[index].owner.val :=
          Nat.le_of_not_lt hsrcFam
        have hidx : data.schema.signature.constructors[index].owner.val - source.types.length <
            direct.length := by
          have := hown'; simp only [List.length_append] at this; omega
        have hFdirect := List.mapM_eq_some.mp hdirect
        have hauxLen : aux.length = direct.length := Lean4Lean.List.Forall₂.length_eq hFdirect
        have hidx' : data.schema.signature.constructors[index].owner.val - source.types.length <
            aux.length := hauxLen ▸ hidx
        have hdf : (aux[data.schema.signature.constructors[index].owner.val -
            source.types.length]'hidx').specializedFamily source.uvars data.schema.signature.params =
            some (direct[data.schema.signature.constructors[index].owner.val -
              source.types.length]'hidx) :=
          Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
        generalize hA : aux[data.schema.signature.constructors[index].owner.val -
          source.types.length]'hidx' = A at hdf
        have hA' : A ∈ aux := hA ▸ List.getElem_mem hidx'
        have hfamAux : data.schema.signature.families[data.owner].name = A.auxiliary := by
          rw [hfamName, List.getElem_append_right hge]
          exact ContainerSpecialization.directFamily_name hdf
        have hsrcD : src ∈ (direct[data.schema.signature.constructors[index].owner.val -
            source.types.length]'hidx).ctors := by
          have := hsrc
          rwa [List.getElem_append_right hge] at this
        generalize hDir : direct[data.schema.signature.constructors[index].owner.val -
          source.types.length]'hidx = Dir at hdf hsrcD
        -- the family head
        let h : HeadSpecialization :=
          ⟨A.auxiliary, source.uvars, source.nparams, A.source.name, A.levels, A.arguments⟩
        have hmem : h ∈ r.heads := List.mem_flatMap.mpr ⟨A, hA', List.mem_cons_self⟩
        have hfind : r.heads.find? (fun h => h.auxiliary ==
            data.schema.signature.families[data.owner].name) = some h := by
          rw [hfamAux]
          exact Restoration.find?_of_nodup hdata.restorationScoped.1 hmem
        obtain ⟨hargLen, hargsClosed, hlevLen, -, -⟩ := hwellFormed A hA'
        have hmajA := r.expr_recursorMajor_auxiliary g data.owner hfind hlevelsLen hnp.symm
          hargsClosed
        have happ' : r.expr (g.recursorMajor data.owner) = _ := happ
        rw [hmajA] at happ'
        have hmajEq := (Option.some.inj happ').symm
        have hmapEq : A.arguments.map (fun arg => (arg.instL g.levels).liftN
            (data.schema.signature.families.size + data.schema.signature.constructors.size +
              data.schema.signature.families[data.owner].indices.length)) =
            (A.arguments.map (·.instL g.levels)).map (·.liftN
              (data.schema.signature.families.size + data.schema.signature.constructors.size +
                data.schema.signature.families[data.owner].indices.length)) := by
          rw [List.map_map]; rfl
        rw [hmapEq] at hmajEq
        obtain ⟨-, hlev, hargsEq⟩ := head_of_major head hmajEq
        -- the direct constructor is a specialization of a container constructor
        unfold ContainerSpecialization.specializedFamily at hdf
        simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
          Option.some.injEq] at hdf
        obtain ⟨tyA, -, cs, hcs, hdf⟩ := hdf
        subst hdf
        obtain ⟨cc, hcc, hccSrc⟩ := Lean4Lean.List.Forall₂.forall_exists_r
          (List.mapM_eq_some.mp hcs) src hsrcD
        simp only [Option.bind_eq_some_iff,
          Option.some.injEq] at hccSrc
        obtain ⟨spec, hspec, hccSrc⟩ := hccSrc
        subst hccSrc
        -- the actual constructor constant
        let hc : HeadSpecialization :=
          ⟨A.constructorName cc, source.uvars, source.nparams, cc.name, A.levels, A.arguments⟩
        have hcmem : hc ∈ r.heads := List.mem_flatMap.mpr ⟨A, hA', List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨cc, hcc, rfl⟩)⟩
        have hrc : data.ruleConstructor index = cc.name := by
          unfold RecursorData.ruleConstructor
          have hsn : data.schema.signature.constructors[index].name = A.constructorName cc :=
            hsrcName
          rw [hres, hsn]
          exact Restoration.headName_of_mem hdata.restorationScoped hcmem
        obtain ⟨-, hctorsC⟩ := hprior.containerConstructors A hA'
        obtain ⟨-, hlookup⟩ := hctorsC A.source (List.getElem_mem _) cc hcc
        have hTy : Tc = cc.type := by
          rw [hrc, hbaseEnv.constants hlookup] at hTc
          exact (congrArg VConstant.type (Option.some.inj hTc)).symm
        subst hTy
        have hcnp : head.arguments.length = A.arguments.length := by
          rw [hargsEq, List.length_map]
        have hccC : cc.type.ClosedN 0 := by
          have := henv.ordered.constWF (hbaseEnv.constants hlookup)
          obtain ⟨_, hty⟩ := this
          simpa using VExpr.WF.closedN henv.ordered (Γ := []) ⟨_, hty⟩ trivial
        rw [hT, ← List.take_append_drop A.arguments.length Td] at hccC
        have hWC := VExpr.ClosedN.wrapForalls_drop hccC
        rw [List.length_take, Nat.min_eq_left (by rw [hTlen, hcnp]; omega), Nat.zero_add] at hWC
        unfold specializeType at hspec
        rw [hT, VExpr.instL_wrapForalls, VExpr.takeForalls_wrapForalls_le _ _ (by
          rw [List.length_map, hTlen, hcnp]; omega)] at hspec
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hspec
        refine ⟨?_, ?_⟩
        · show ∃ dr, ((VExpr.wrapForalls data.schema.signature.params spec).instL
            (g.levels.map (·.inst ls))).takeForalls P.length = some dr
          rw [VExpr.instL_wrapForalls]
          exact ⟨_, VExpr.takeForalls_wrapForalls_le _ _ (by rw [List.length_map]; omega)⟩
        · intro midQ mid HQ HT
          have HQ' : InstForallsC env U Γ ((VExpr.wrapForalls data.schema.signature.params spec).instL
              (g.levels.map (·.inst ls))) P midQ := HQ
          rw [VExpr.instL_wrapForalls] at HQ'
          have e1 := HQ'.wrapForalls_eq (by rw [List.length_map]; omega)
          rw [hT, VExpr.instL_wrapForalls,
            ← List.take_append_drop A.arguments.length
              (Td.map (VExpr.instL (head.levels.map (·.inst ls)))),
            VExpr.wrapForalls_append] at HT
          have e2 := HT.wrapForalls_eq (by
            simp only [List.length_map, List.length_take, hTlen, hcnp]; omega)
          rw [e1, e2, ← hspec, instantiateParams_instL, instantiateParams_eq_instOuter,
            VExpr.instOuter_instOuter _ _ _ (by
              rw [List.length_map]
              have := hWC.instL (ls := A.levels)
              have := this.instL (ls := g.levels.map (·.inst ls))
              simpa [VExpr.instL_wrapForalls, List.map_drop] using this),
            hlev, hargsEq]
          simp only [VExpr.instL_wrapForalls, List.map_drop, List.map_map, Function.comp_def,
            VExpr.instL_instL, VLevel.inst_inst]
          rfl
    have hfa := field_alignment henv hΓ (R := VExpr.wrapForalls Rd Rb) (Q := src.type)
      (T := hctorShape.type) rfl hctorShape.type_eq hRQΓ (by omega) hPty' key.1 Hw
      (by simp [hctorShape.doms_length]; omega) key.2 i hi
    have hclosed : ((Rd[data.schema.signature.params.length + i]'(by omega)).instL
        (g.levels.map (·.inst ls))).ClosedN (P.length + (fields.take i).length) := by
      have := VExpr.ClosedN.wrapForalls_inv_getElem hRC (data.schema.signature.params.length + i)
        (by omega)
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), hPl, Nat.zero_add] at this ⊢
      exact this.instL
    have hmidLem := VExpr.instOuter_liftN_mid (mid := Mid) hclosed
    rw [hMid, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hmidLem
    rw [List.getElem_of_eq hID hi', hDf _ (by omega), VExpr.instL_liftN, VExpr.instL_instL,
      hmidLem]
    simpa only [hPl] using hfa

private theorem argumentRHS_var {p : Pattern} :
    ∀ {n} {x : (p.varN n).RHS}, x ∈ p.argumentRHS n → ∃ path, x = .var path
  | 0, _, h => by cases h
  | n + 1, x, h => by
    simp only [Pattern.argumentRHS, List.mem_append, List.mem_map, List.mem_singleton] at h
    rcases h with ⟨y, hy, rfl⟩ | rfl
    · obtain ⟨path, rfl⟩ := argumentRHS_var hy
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

private theorem argumentRHS_apply_levels {p : Pattern} {n : Nat} (l l' : List VLevel)
    (v : (p.varN n).Path → VExpr) :
    (p.argumentRHS n).map (·.apply l v) = (p.argumentRHS n).map (·.apply l' v) := by
  apply List.map_congr_left
  intro x hx
  obtain ⟨path, rfl⟩ := argumentRHS_var hx
  rfl

/-- The major arguments of a restored recursor rule: the specialized parameters
and the field variables. -/
private theorem ruleMajorArguments_eq
    (I : VIotaRuleShape env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df ctorParams) :
    RecursorData.ruleMajorArguments df =
      (ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
        VExpr.bvarRange nfields nfields := by
  unfold RecursorData.ruleMajorArguments
  rw [I.lhs_eq, stripLams_wrap', I.lhs_pattern,
    VExpr.stripLams_of_head_const (VExpr.getAppFnArgs_mkApps_head _ _),
    VerifyInductive.VExpr.getAppFnArgs_mkApps]
  simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, List.nil_append,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]
  have h := VerifyInductive.VExpr.getAppFnArgs_mkApps (.const ctorName ctorLevels)
    ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
      VExpr.bvarRange nfields nfields)
  simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, List.nil_append] at h
  rw [h]

/-- Generated iota patterns are sound: a matched redex is definitionally equal
to the captured instance of the installed recursor equation. -/
theorem GeneratedIotaPattern.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (_hregistry : ∀ name data, registry name = some data →
      RecursorRegistered env data ∧ data.name = name)
    (H : GeneratedIotaPattern env registry p rhs)
    (hm : p.Matches e levels values) (ht : env.HasType U Γ e type) :
    env.IsDefEqU U Γ e (rhs.1.apply levels values) := by
  cases H with
  | @intro data index equation _ hr _ ho hg =>
  obtain ⟨head, Hrec, Hctor, Hrule, hrigid, hF1, hF2⟩ := hr.iota_core henv ho hg
  have hargsEq := ruleMajorArguments_eq Hrule
  simp only [RecursorData.rulePattern, SimplePattern.toPattern] at hm
  cases hm with
  | @app _ F _ g1 _ M lsc g2 hF hM =>
  have hFe := hF.const_arguments
  have hMe := hM.const_arguments
  generalize hpre : ((Pattern.const data.name).argumentRHS data.majorOffset).map
    (·.apply levels g1) = pre at hFe
  generalize hcargs : ((Pattern.const (data.ruleConstructor index)).argumentRHS
    (RecursorData.ruleMajorArguments equation).length).map (·.apply lsc g2) = cargs at hMe
  subst hFe hMe
  have hpreLen : pre.length = data.majorOffset := by
    rw [← hpre]; simp [Pattern.argumentRHS_length]
  have hcLen : cargs.length = head.arguments.length +
      data.schema.signature.constructors[index].fields.length := by
    rw [← hcargs]; simp [Pattern.argumentRHS_length, hargsEq]
  have happ : VExpr.mkApps (.const data.name levels)
      (pre ++ VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs :: []) =
      .app (VExpr.mkApps (.const data.name levels) pre)
        (VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs) := by
    simp [VExpr.mkApps, List.foldl_append]
  have hwf : VExpr.WF env U Γ (VExpr.mkApps (.const data.name levels)
      (pre ++ VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs :: [])) := by
    rw [happ]; exact ⟨_, ht⟩
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ hwf
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.ordered hΓ hc
  rw [Hrec.const] at hci
  cases hci
  have hfa : VExpr.WF env U Γ (.app (VExpr.mkApps (.const data.name levels) pre)
      (VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs)) := ⟨_, ht⟩
  obtain ⟨_, _, _, hMt⟩ := hfa.app_inv henv.ordered hΓ
  obtain ⟨_, hcc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ (⟨_, hMt⟩ :
    VExpr.WF env U Γ (VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs))
  obtain ⟨cci, hcci, hcw, hcl⟩ := HasType.const_inv henv.ordered hΓ hcc
  rw [Hctor.const] at hcci
  cases hcci
  -- notation
  generalize hnp : data.schema.signature.params.length = np at *
  generalize hcnp : head.arguments.length = cnp at *
  have hm : np + data.schema.signature.families.size + data.schema.signature.constructors.size ≤
      pre.length := by
    rw [hpreLen]; unfold RecursorData.majorOffset RecursorData.indexOffset
      RecursorData.numParams; omega
  have hwf1 : VExpr.WF env U Γ (VExpr.mkApps (.const data.name levels)
      (pre ++ [VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs])) := by
    have : pre ++ VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs :: [] =
      pre ++ [VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs] := rfl
    rw [← this]; exact hwf
  have hpreArity : pre.length = np + data.schema.signature.families.size +
      data.schema.signature.constructors.size + data.numIndices := by
    rw [hpreLen]; unfold RecursorData.majorOffset RecursorData.indexOffset
      RecursorData.numParams; omega
  obtain ⟨hpreT, hmajT, -⟩ := Hrec.spine_typing henv hΓ hw hl hpreArity hwf1
  -- the actual constructor telescope and the parameter alignment
  have hcT := HasType.const (Γ := Γ) Hctor.const hcw hcl
  have hTsplit := Hctor.type_eq
  have hctorWF : VExpr.WF env U Γ (VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs) :=
    ⟨_, hMt⟩
  obtain ⟨res0, Hw0, -⟩ := HasType.mkApps_telescope henv hΓ hcT hctorWF
    (doms := Hctor.doms.map (VExpr.instL lsc)) (rest := _) (by
      rw [hTsplit, VExpr.instL_wrapForalls,
        show cargs.length = (Hctor.doms.map (VExpr.instL lsc)).length by
          rw [List.length_map, Hctor.doms_length, hcLen]]
      exact VExpr.takeForalls_wrapForalls _ _)
  have hcargs' : cargs = cargs.take cnp ++ cargs.drop cnp := (List.take_append_drop _ _).symm
  obtain ⟨-, hcres⟩ := Hctor.spine_typing henv hΓ hcw hcl (P := cargs.take cnp)
    (fields := cargs.drop cnp) (by rw [List.length_take, hcLen]; omega)
    (by rw [List.length_drop, hcLen]; omega) (by rw [← hcargs']; exact hctorWF)
  rw [← hcargs'] at hcres
  have hMTCT := (hmajT.uniqU henv hΓ hcres)
  have ⟨_, hsort⟩ := hmajT.isType henv.ordered hΓ
  have ⟨hLcls, hargsE⟩ := IsDefEqU.rigidApp_inv henv hΓ hrigid hMTCT hsort
  obtain ⟨hPE, -⟩ := List.forall₂_append_split hargsE (by
    simp only [List.length_map, List.length_take, hcLen]; omega)
  -- the rule arguments typed along the rule telescope, without strengthening
  have hA : ∀ j (hj : j < (pre.take (np + data.schema.signature.families.size +
        data.schema.signature.constructors.size) ++ cargs.drop cnp).length)
      (hj' : j < (Hrule.doms.map (VExpr.instL levels)).length),
      env.HasType U Γ (pre.take (np + data.schema.signature.families.size +
          data.schema.signature.constructors.size) ++ cargs.drop cnp)[j]
        ((Hrule.doms.map (VExpr.instL levels))[j].instOuter
          ((pre.take (np + data.schema.signature.families.size +
            data.schema.signature.constructors.size) ++ cargs.drop cnp).take j)) := by
    intro j hj hj'
    rw [List.getElem_map]
    generalize hmdef : np + data.schema.signature.families.size +
      data.schema.signature.constructors.size = m at *
    have hmlen : (pre.take m).length = m := by rw [List.length_take]; omega
    have hRdl := Hrule.doms_length
    have hHdl := Hrec.doms_length
    have hPty : ∀ k (hk : k < (pre.take np).length) (hk' : k < Hrule.doms.length),
        env.HasType U Γ (pre.take np)[k] ((Hrule.doms[k].instL levels).instOuter
          ((pre.take np).take k)) := by
      intro k hk hk'
      simp only [List.length_take] at hk
      rw [List.getElem_take, List.take_take, Nat.min_eq_left (by omega),
        hF1 k hk' (by omega) (by omega)]
      have := hpreT k (by omega) (by simp; omega)
      rwa [List.getElem_map] at this
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by rw [hmlen]; exact hjm), List.getElem_take,
        List.take_append_of_le_length (by rw [hmlen]; omega), List.take_take,
        Nat.min_eq_left (Nat.le_of_lt hjm), hF1 j (by simpa using hj') (by omega) hjm]
      have := hpreT j (by omega) (by simp; omega)
      rwa [List.getElem_map] at this
    · obtain ⟨i, rfl⟩ : ∃ i, j = m + i := ⟨j - m, by omega⟩
      have hi : i < (cargs.drop cnp).length := by
        rw [List.length_append, hmlen] at hj; omega
      have e1 : (pre.take m ++ cargs.drop cnp)[m + i]'hj = (cargs.drop cnp)[i] := by
        rw [List.getElem_append_right (by rw [hmlen]; omega)]
        simp only [hmlen, Nat.add_sub_cancel_left]
      have e2 : (pre.take m ++ cargs.drop cnp).take (m + i) =
          pre.take m ++ (cargs.drop cnp).take i := by
        rw [List.take_append, List.take_of_length_le (by rw [hmlen]; omega), hmlen,
          Nat.add_sub_cancel_left]
      rw [e1, e2]
      -- the actual constructor arguments along the parameter-aligned telescope
      have hTdef : env.IsDefEqU U Γ (Hctor.type.instL (head.levels.map (·.inst levels)))
          (Hctor.type.instL lsc) :=
        IsType.instL_defeq (Γ := Γ) henv.ordered (henv.ordered.constWF Hctor.const)
          (fun _ hl' => by obtain ⟨_, -, rfl⟩ := List.mem_map.mp hl'; exact VLevel.WF.inst hw)
          hcw hLcls
      have hfty := Hw0.typed
      have hargsDef : List.Forall₂ (env.IsDefEqU U Γ)
          (head.arguments.map (fun p => (p.instL levels).instOuter (pre.take np)) ++
            cargs.drop cnp) cargs := by
        have hrefl : List.Forall₂ (env.IsDefEqU U Γ) (cargs.drop cnp) (cargs.drop cnp) :=
          List.forall₂_of_getElem rfl fun k hk _ => by
            have hmem : (cargs.drop cnp)[k] ∈ cargs := List.mem_of_mem_drop (List.getElem_mem hk)
            obtain ⟨_, h⟩ := hfty _ hmem
            exact IsDefEqU.refl ⟨_, h⟩
        have := hPE.append' hrefl
        rwa [List.take_append_drop] at this
      obtain ⟨res, Hw, -⟩ := InstForallsC.of_defeq henv hΓ Hw0 hTdef hargsDef (by
        rw [Hctor.type_eq, VExpr.instL_wrapForalls,
          show (head.arguments.map (fun p => (p.instL levels).instOuter (pre.take np)) ++
            cargs.drop cnp).length = (Hctor.doms.map (VExpr.instL (head.levels.map
              (·.inst levels)))).length by
            simp only [List.length_append, List.length_map]
            rw [Hctor.doms_length, hcnp, List.length_drop, hcLen]; omega]
        exact VExpr.takeForalls_wrapForalls _ _)
      have hPm : pre.take np ++ (pre.take m).drop np = pre.take m := by
        conv => rhs; rw [← List.take_append_drop np (pre.take m)]
        rw [List.take_take, Nat.min_eq_left (by omega)]
      have hPl : (pre.take np).length = np := by rw [List.length_take]; omega
      have hfl : (cargs.drop cnp).length = data.schema.signature.constructors[index].fields.length := by
        rw [List.length_drop, hcLen]; omega
      have hMl : ((pre.take m).drop np).length = data.schema.signature.families.size +
          data.schema.signature.constructors.size := by
        rw [List.length_drop, hmlen]; omega
      have := hF2 hΓ hw hl hPl hfl hMl hPty Hw i hi (by omega)
      rwa [hPm] at this
  have key := VIotaRuleShape.iota_of_args henv hΓ Hrec Hctor Hrule hrigid rfl hw hl
    hpreArity hwf hcl hcw
    (P' := cargs.take cnp) (fields := cargs.drop cnp)
    (by rw [List.length_take, hcLen]; omega) (by rw [List.length_drop, hcLen]; omega)
    (by rw [List.take_append_drop]; exact ⟨_, hMt⟩) hA
  rw [happ] at key
  have hrhs : ∀ hcl, @Pattern.RHS.apply (data.rulePattern index equation) levels (Sum.elim g1 g2)
        (data.ruleRHS index equation hcl) =
      VExpr.mkApps (equation.rhs.instL levels)
        (pre.take (np + data.schema.signature.families.size +
          data.schema.signature.constructors.size) ++ cargs.drop cnp ++ []) := by
    intro hcl
    simp only [RecursorData.ruleRHS, RecursorData.ruleCaptures]
    refine (Pattern.RHS.applyArgs_apply (p := data.rulePattern index equation) _ _).trans ?_
    simp only [List.map_append, List.map_map, Function.comp_def, List.append_nil]
    have h1 : ∀ x : ((Pattern.const data.name).varN data.majorOffset).RHS,
        Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2)
          (x.mapPaths Sum.inl) = x.apply levels g1 := fun x =>
      Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inl x
    have h2 : ∀ x : ((Pattern.const (data.ruleConstructor index)).varN
        (RecursorData.ruleMajorArguments equation).length).RHS,
        Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2)
          (x.mapPaths Sum.inr) = x.apply levels g2 := fun x =>
      Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inr x
    simp only [h1, h2]
    show VExpr.mkApps (equation.rhs.instL levels) _ = _
    have hk : (RecursorData.ruleMajorArguments equation).length -
        data.schema.signature.constructors[index].fields.length = cnp := by
      rw [hargsEq]; simp [hcnp]
    rw [hk, List.map_take, List.map_drop, hpre, argumentRHS_apply_levels levels lsc, hcargs]
    have hio : data.indexOffset = np + data.schema.signature.families.size +
        data.schema.signature.constructors.size := by
      unfold RecursorData.indexOffset RecursorData.numParams; omega
    rw [hio]
  exact (hrhs _) ▸ key

end VEnv

end Lean4Lean
