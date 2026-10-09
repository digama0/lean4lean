import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas

/-! Registered eliminator schemas avoid names that are not constants.

`VEnv.WF.eliminatorsAvoidConsts`: in a well-formed environment every
registered case schema's generic type and generic equations mention (in the
sense of `mentionsAnyConst`, i.e. ignoring projection type names) no name that is
absent from the environment. The proof follows the schema's certification
(`VEnv.WF.eliminator_installed`): the normalized signature's pieces are typed in
the expanded header/constructor environments, in which the absent names and
the renamed auxiliary recursor names are fresh; restoration then replaces
every auxiliary head by a certified container target with arguments typed in
the source header environment.

Projection type names are deliberately not covered. Restoration keeps
`.proj n i e` names unchanged, and a normalized family index telescope is
typed only in the expanded environment (`FamilyTypesWF`), whose projection
table may contain the schema's own never-installed auxiliary structure
families. So avoidance in the `containsAnyConst` sense does not follow from
the formation certificate `Certified`; registration certifies projection names
separately (`CaseSchema.ProjNamesRegistered`,
`VEnv.WF.eliminatorsProjNamesRegistered`). An interpretation that keeps projection owners
ignores projection names, so `EliminatorsAvoidConsts` is what it needs to fix a schema
(`VEnv.Interpretation.expr_eq_self_of_mentions`).
-/

namespace Lean4Lean

open InductiveSignature

namespace VExpr

/-- Constant support ignoring projection type names: exactly the support seen by an
interpretation that keeps projection owners. -/
def mentionsAnyConst (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ | .elim .. => false
  | .const name _ => names.contains name
  | .proj _ _ struct => struct.mentionsAnyConst names
  | .app fn arg | .lam fn arg | .forallE fn arg =>
    fn.mentionsAnyConst names || arg.mentionsAnyConst names

theorem mentionsAnyConst_of_containsAnyConst {e : VExpr}
    (h : e.containsAnyConst names = false) : e.mentionsAnyConst names = false := by
  induction e <;> simp_all [containsAnyConst, mentionsAnyConst]

@[simp] theorem mentionsAnyConst_liftN (e : VExpr) (n k : Nat) :
    (e.liftN n k).mentionsAnyConst names = e.mentionsAnyConst names := by
  induction e generalizing k <;> simp [VExpr.liftN, mentionsAnyConst, *]

@[simp] theorem mentionsAnyConst_instL (e : VExpr) (levels : List VLevel) :
    (e.instL levels).mentionsAnyConst names = e.mentionsAnyConst names := by
  induction e <;> simp [VExpr.instL, mentionsAnyConst, *]

theorem mentionsAnyConst_mkApps_eq_false_iff (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).mentionsAnyConst names = false ↔
      fn.mentionsAnyConst names = false ∧
        ∀ arg ∈ args, arg.mentionsAnyConst names = false := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
      rw [show VExpr.mkApps fn (arg :: args) =
        VExpr.mkApps (.app fn arg) args by rfl, ih]
      simp [mentionsAnyConst, and_assoc]

theorem mentionsAnyConst_subst_eq_false {e : VExpr} {σ : Subst}
    (hσ : ∀ i, (σ i).mentionsAnyConst names = false)
    (he : e.mentionsAnyConst names = false) :
    (e.subst σ).mentionsAnyConst names = false := by
  have hlift : ∀ {σ : Subst}, (∀ i, (σ i).mentionsAnyConst names = false) →
      ∀ i, (σ.lift i).mentionsAnyConst names = false := by
    intro σ hσ i
    cases i with
    | zero => rfl
    | succ i => simpa [Subst.lift, VExpr.lift] using hσ i
  induction e generalizing σ <;>
    simp_all [VExpr.subst, mentionsAnyConst]

end VExpr

/-- An interpretation fixes a term none of whose constants (in the `mentionsAnyConst` sense) it
interprets or renames, and whose projection owners it fixes. -/
theorem VEnv.Interpretation.expr_eq_self_of_mentions {I : VEnv.Interpretation}
    {names : List Name} (hc : ∀ c, c ∉ names → I.consts c = none)
    (hr : ∀ c, c ∉ names → I.rename c = c)
    (he : ∀ block owner, I.elim block owner = (block, owner)) :
    ∀ {e : VExpr}, e.mentionsAnyConst names = false → e.ProjNamesFixed I.projOwner →
      I.expr e = e
  | .bvar _, _, _ | .sort _, _, _ => rfl
  | .elim .., _, _ => by simp [VEnv.Interpretation.expr, he]
  | .const c ls, h, _ => by
    have hn : c ∉ names := by simpa [VExpr.mentionsAnyConst] using h
    rw [VEnv.Interpretation.expr_const_none (hc c hn), hr c hn]
  | .app f a, h, h' | .lam f a, h, h' | .forallE f a, h, h' => by
    simp only [VExpr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [VEnv.Interpretation.expr, expr_eq_self_of_mentions hc hr he h.1 h'.1,
      expr_eq_self_of_mentions hc hr he h.2 h'.2]
  | .proj n i e, h, h' => by
    simp only [VExpr.mentionsAnyConst] at h
    simp only [VEnv.Interpretation.expr, expr_eq_self_of_mentions hc hr he h h'.2, h'.1]

namespace VExpr

theorem containsAnyConst_wrapForalls_eq_false_iff {domains : List VExpr} {body : VExpr} :
    (VExpr.wrapForalls domains body).containsAnyConst names = false ↔
      (∀ d ∈ domains, d.containsAnyConst names = false) ∧
        body.containsAnyConst names = false := by
  induction domains with
  | nil => simp [VExpr.wrapForalls]
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at ih ⊢
    simp [containsAnyConst, ih, and_assoc]

theorem containsAnyConst_wrapLams_eq_false_iff {domains : List VExpr} {body : VExpr} :
    (VExpr.wrapLams domains body).containsAnyConst names = false ↔
      (∀ d ∈ domains, d.containsAnyConst names = false) ∧
        body.containsAnyConst names = false := by
  induction domains with
  | nil => simp [VExpr.wrapLams]
  | cons d ds ih =>
    simp only [VExpr.wrapLams, List.foldr_cons] at ih ⊢
    simp [containsAnyConst, ih, and_assoc]

end VExpr

namespace InductiveSignature

/-- Restoration output avoids `N` (in the `mentionsAnyConst` sense) when the
input avoids `L`, every non-head constant outside `L` is renamed outside `N`,
and every head has its target and arguments outside `N`. -/
theorem Restoration.go_mentions {r : Restoration} {N L : List Name}
    (hheads : ∀ h ∈ r.heads, N.contains h.target = false ∧
      ∀ a ∈ h.arguments, a.mentionsAnyConst N = false)
    (hconst : ∀ name, name ∉ r.heads.map (·.auxiliary) → L.contains name = false →
      N.contains (r.recursorName name) = false) :
    ∀ (e : VExpr) (args : List VExpr) (out : VExpr),
      e.containsAnyConst L = false →
      (∀ a ∈ args, a.mentionsAnyConst N = false) →
      Restoration.expr.go r e args = some out → out.mentionsAnyConst N = false := by
  intro e
  induction e with
  | bvar i =>
    intro args out _ hargs h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, hargs⟩
  | sort u =>
    intro args out _ hargs h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, hargs⟩
  | elim b o ls =>
    intro args out _ hargs h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, hargs⟩
  | const name levels =>
    intro args out he hargs h
    simp only [Restoration.expr.go] at h
    split at h
    · rename_i hd hfind
      have hmem := List.mem_of_find?_eq_some hfind
      obtain ⟨htarget, harguments⟩ := hheads hd hmem
      unfold HeadSpecialization.apply at h
      split at h
      · cases h
      · simp only [pure, Option.some.injEq] at h
        subst h
        refine (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr
          ⟨by simpa [VExpr.mentionsAnyConst] using htarget, ?_⟩
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp ha
          unfold instantiateParams
          apply VExpr.mentionsAnyConst_subst_eq_false
          · intro i
            split
            · exact hargs _ (List.mem_of_mem_take (List.getElem_mem _))
            · rfl
          · simpa using harguments arg harg
        · exact hargs a (List.mem_of_mem_drop ha)
    · rename_i hfind
      simp only [Option.some.injEq] at h
      subst h
      have hnot : name ∉ r.heads.map (·.auxiliary) := by
        intro hm
        obtain ⟨hd, hd_mem, rfl⟩ := List.mem_map.mp hm
        have := List.find?_eq_none.mp hfind hd hd_mem
        simp at this
      have hL : L.contains name = false := by simpa [VExpr.containsAnyConst] using he
      exact (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr
        ⟨by simpa [VExpr.mentionsAnyConst] using hconst name hnot hL, hargs⟩
  | app fn arg ihfn iharg =>
    intro args out he hargs h
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at he
    simp only [Restoration.expr.go, bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', harg', h⟩ := h
    have harg'' := iharg [] arg' he.2 (by simp) harg'
    exact ihfn _ out he.1 (by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact harg''
      · exact hargs a ha) h
  | lam dom body ihd ihb =>
    intro args out he hargs h
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at he
    simp only [Restoration.expr.go, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨d', hd', b', hb', rfl⟩ := h
    refine (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨?_, hargs⟩
    simp only [VExpr.mentionsAnyConst, Bool.or_eq_false_iff]
    exact ⟨ihd [] d' he.1 (by simp) hd', ihb [] b' he.2 (by simp) hb'⟩
  | forallE dom body ihd ihb =>
    intro args out he hargs h
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at he
    simp only [Restoration.expr.go, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨d', hd', b', hb', rfl⟩ := h
    refine (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨?_, hargs⟩
    simp only [VExpr.mentionsAnyConst, Bool.or_eq_false_iff]
    exact ⟨ihd [] d' he.1 (by simp) hd', ihb [] b' he.2 (by simp) hb'⟩
  | proj tn i major ih =>
    intro args out he hargs h
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at he
    simp only [Restoration.expr.go, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨m', hm', rfl⟩ := h
    refine (VExpr.mentionsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨?_, hargs⟩
    simpa [VExpr.mentionsAnyConst] using ih [] m' he.2 (by simp) hm'

theorem Restoration.expr_mentions {r : Restoration} {N L : List Name}
    (hheads : ∀ h ∈ r.heads, N.contains h.target = false ∧
      ∀ a ∈ h.arguments, a.mentionsAnyConst N = false)
    (hconst : ∀ name, name ∉ r.heads.map (·.auxiliary) → L.contains name = false →
      N.contains (r.recursorName name) = false)
    {e out : VExpr} (he : e.containsAnyConst L = false) (h : r.expr e = some out) :
    out.mentionsAnyConst N = false :=
  Restoration.go_mentions hheads hconst e [] out he (by simp) h

end InductiveSignature

namespace InductiveSignature

/-- Every piece of a signature with only external fields avoids `L`. -/
structure SigAvoids (L : List Name) (s : InductiveSignature) : Prop where
  params : ∀ p ∈ s.params, p.containsAnyConst L = false
  familyName : ∀ f ∈ s.families.toList, L.contains f.name = false
  familyIndices : ∀ f ∈ s.families.toList, ∀ e ∈ f.indices, e.containsAnyConst L = false
  ctorName : ∀ c ∈ s.constructors.toList, L.contains c.name = false
  ctorFields : ∀ c ∈ s.constructors.toList, ∀ e ∈ s.fieldTypes c,
    e.containsAnyConst L = false
  ctorIndices : ∀ c ∈ s.constructors.toList, ∀ e ∈ c.indices, e.containsAnyConst L = false
  external : ∀ c ∈ s.constructors.toList, Instance.recursiveFields (s := s) c = []

theorem vars_avoids (count below : Nat) :
    ∀ e ∈ vars count below, e.containsAnyConst L = false := by
  intro e he
  simp only [vars, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  rfl

theorem insertBinders_avoids {domains : List VExpr}
    (h : ∀ d ∈ domains, d.containsAnyConst L = false) (count : Nat) :
    ∀ d ∈ insertBinders domains count, d.containsAnyConst L = false := by
  intro d hd
  simp only [insertBinders, List.mem_map] at hd
  obtain ⟨⟨t, i⟩, hti, rfl⟩ := hd
  simpa using h t (List.fst_mem_of_mem_zipIdx hti)

section
variable {s : InductiveSignature} {L : List Name} (S : SigAvoids L s) (g : Instance s)
include S

theorem SigAvoids.instance_params : ∀ p ∈ g.params, p.containsAnyConst L = false := by
  intro p hp
  simp only [Instance.params, List.mem_map] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  simpa using S.params p hp

theorem SigAvoids.motive {f : Family} (hf : f ∈ s.families.toList) (prior : Nat) :
    (g.motive f prior).containsAnyConst L = false := by
  unfold Instance.motive
  refine VExpr.containsAnyConst_wrapForalls_eq_false_iff.mpr ⟨?_, rfl⟩
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact insertBinders_avoids (by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      simpa using S.familyIndices f hf e0 he0) _ d hd
  · simp only [List.mem_singleton] at hd
    subst hd
    refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr
      ⟨by simpa [VExpr.containsAnyConst] using S.familyName f hf, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha <;> exact vars_avoids _ _ a ha

theorem SigAvoids.motives : ∀ m ∈ g.motives, m.containsAnyConst L = false := by
  intro m hm
  simp only [Instance.motives, List.mem_map] at hm
  obtain ⟨⟨f, i⟩, hfi, rfl⟩ := hm
  exact S.motive g (List.fst_mem_of_mem_zipIdx hfi) i

theorem SigAvoids.fields {c : Constructor s.families.size} (hc : c ∈ s.constructors.toList)
    (extra : Nat) :
    ∀ d ∈ insertBinders ((s.fieldTypes c).map (·.instL g.levels)) extra,
      d.containsAnyConst L = false :=
  insertBinders_avoids (by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    simpa using S.ctorFields c hc e0 he0) extra

theorem SigAvoids.constructorApp {c : Constructor s.families.size}
    (hc : c ∈ s.constructors.toList) (extra below : Nat) :
    (g.constructorApp c extra below).containsAnyConst L = false := by
  unfold Instance.constructorApp
  refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr
    ⟨by simpa [VExpr.containsAnyConst] using S.ctorName c hc, ?_⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha <;> exact vars_avoids _ _ a ha

theorem SigAvoids.minor {c : Constructor s.families.size} (hc : c ∈ s.constructors.toList)
    (prior : Nat) : (g.minor c prior).containsAnyConst L = false := by
  unfold Instance.minor
  simp only [S.external c hc, List.zipIdx_nil, List.map_nil, List.length_nil,
    List.append_nil]
  refine VExpr.containsAnyConst_wrapForalls_eq_false_iff.mpr ⟨S.fields g hc _, ?_⟩
  refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, ?_⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    simpa using S.ctorIndices c hc e he
  · simp only [List.mem_singleton] at ha
    subst ha
    exact S.constructorApp g hc _ _

theorem SigAvoids.minors : ∀ m ∈ g.minors, m.containsAnyConst L = false := by
  intro m hm
  simp only [Instance.minors, List.mem_map] at hm
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := hm
  exact S.minor g (List.fst_mem_of_mem_zipIdx hci) i

theorem SigAvoids.recursorType (owner : Fin s.families.size) :
    (g.recursorType owner).containsAnyConst L = false := by
  have hf : s.families[owner] ∈ s.families.toList := by simp
  unfold Instance.recursorType
  refine VExpr.containsAnyConst_wrapForalls_eq_false_iff.mpr ⟨?_, ?_⟩
  · intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with (((hd | hd) | hd) | hd) | rfl
    · exact S.instance_params g d hd
    · exact S.motives g d hd
    · exact S.minors g d hd
    · exact insertBinders_avoids (by
        intro e he
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
        simpa using S.familyIndices _ hf e0 he0) _ d hd
    · unfold Instance.familyApp InductiveSignature.familyApp
      refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr
        ⟨by simpa [VExpr.containsAnyConst] using S.familyName _ hf, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha <;> exact vars_avoids _ _ a ha
  · refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact vars_avoids _ _ a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      rfl

theorem SigAvoids.equation (index : Fin s.constructors.size) (block : Name) (first : Nat) :
    (g.equation index (.elim block first)).lhs.containsAnyConst L = false ∧
    (g.equation index (.elim block first)).rhs.containsAnyConst L = false ∧
    (g.equation index (.elim block first)).type.containsAnyConst L = false := by
  have hc : s.constructors[index] ∈ s.constructors.toList := by simp
  have hdomains : ∀ d ∈ g.params ++ g.motives ++ g.minors ++
      insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + s.constructors.size), d.containsAnyConst L = false := by
    intro d hd
    simp only [List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact S.instance_params g d hd
    · exact S.motives g d hd
    · exact S.minors g d hd
    · exact S.fields g hc _ d hd
  have hindices : ∀ e ∈ s.constructors[index].indices.map fun e =>
      (e.instL g.levels).liftN (s.families.size + s.constructors.size)
        s.constructors[index].fields.length, e.containsAnyConst L = false := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    simpa using S.ctorIndices _ hc e0 he0
  have hmajor := S.constructorApp g hc (s.families.size + s.constructors.size) 0
  unfold Instance.equation
  simp only [S.external _ hc, List.map_nil, List.append_nil]
  refine ⟨?_, ?_, ?_⟩
  · refine VExpr.containsAnyConst_wrapLams_eq_false_iff.mpr ⟨hdomains, ?_⟩
    refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, ?_⟩
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact vars_avoids _ _ a ha
    · exact hindices a ha
    · exact hmajor
  · refine VExpr.containsAnyConst_wrapLams_eq_false_iff.mpr ⟨hdomains, ?_⟩
    refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, ?_⟩
    exact vars_avoids _ _
  · refine VExpr.containsAnyConst_wrapForalls_eq_false_iff.mpr ⟨hdomains, ?_⟩
    refine (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mpr ⟨rfl, ?_⟩
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hindices a ha
    · exact hmajor

end

end InductiveSignature

/-! ### Restoration targets of a certified schema -/



/-- Every restoration target of a certified specialization is a constant of
the environment certifying it. -/
theorem ContainersInstalled.target_present {env : VEnv}
    {auxiliaries : List ContainerSpecialization}
    (H : ContainersInstalled env auxiliaries) :
    ∀ a ∈ auxiliaries, ∀ h ∈ a.heads U n, env.constants h.target ≠ none := by
  induction auxiliaries with
  | nil => intro a ha; cases ha
  | cons a0 rest ih =>
    cases H with
    | cons hcompiled _ hinstall hle hrest =>
    intro a' ha' h hh
    rcases List.mem_cons.mp ha' with rfl | ha'
    · obtain ⟨htypes, hctors⟩ := hcompiled.types_ctors
      have hpresent := VInductBlock.install_constants hinstall
      have hsrc : a'.source ∈ a'.container.types := List.getElem_mem _
      simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
      rcases hh with rfl | ⟨ctor, hctor, rfl⟩
      · have := hle.constants (hpresent a'.source.toVConstVal (List.mem_append_left _ (by
          rw [htypes]; exact List.mem_map.mpr ⟨_, hsrc, rfl⟩)))
        simp [this]
      · have := hle.constants (hpresent ctor (List.mem_append_right _ (by
          rw [hctors]; exact List.mem_flatMap.mpr ⟨_, hsrc, hctor⟩)))
        simp [this]
    · exact ih hrest a' ha' h hh

theorem ContainerSpecialization.directFamily_type
    {a : ContainerSpecialization} {uvars : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.specializedFamily uvars params = some direct) :
    ∃ body, direct.type = VExpr.wrapForalls params body := by
  unfold ContainerSpecialization.specializedFamily at H
  cases htype : specializeType (a.source.type.instL a.levels) a.arguments with
  | none => simp [htype] at H
  | some type =>
    simp [htype] at H
    rcases H with ⟨ctors, _, H⟩
    cases H
    exact ⟨type, rfl⟩

/-- Avoidance of fresh names for derivations in an environment extended by
projection entries over an ordered environment. -/
theorem VEnv.IsDefEq.noFreshConsts_addProjections {env : VEnv}
    {entries : List VProjectionEntry}
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : (env.addProjections entries).IsDefEq U Gamma lhs rhs type) :
    lhs.containsAnyConst names = false ∧
    rhs.containsAnyConst names = false ∧
    type.containsAnyConst names = false := by
  have hon := Henv.onTypes_noFreshConsts Hfresh
  apply H.noConsts ⟨fun h => hon.1 (by simpa using h), fun h => hon.2 (by simpa using h)⟩
  · intro name ci hlookup hname
    simp only [VEnv.addProjections_constants] at hlookup
    rw [Hfresh name hname] at hlookup
    contradiction
  · exact Hctx

theorem VEnv.ctxNoFreshConsts_addProjections {env : VEnv}
    {entries : List VProjectionEntry}
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none) :
    ∀ {Gamma}, OnCtx Gamma ((env.addProjections entries).IsType U) → CtxAvoidsConsts names Gamma
  | [], _ => by
      intro type htype
      simp at htype
  | A :: Gamma, ⟨Htail, _level, Htype⟩ => by
      have HtailFree := VEnv.ctxNoFreshConsts_addProjections Henv Hfresh Htail
      have HA := VEnv.IsDefEq.noFreshConsts_addProjections Henv Hfresh HtailFree Htype
      exact HtailFree.cons HA.1

theorem familyNames_append (left right : List VInductiveType) :
    familyNames (left ++ right) = familyNames left ++ familyNames right := by
  simp [familyNames, List.flatMap_append]

theorem mem_familyNames_of_type {types : List VInductiveType} {t : VInductiveType}
    (ht : t ∈ types) : t.name ∈ familyNames types :=
  List.mem_flatMap.mpr ⟨t, ht, List.mem_cons_self⟩

theorem mem_familyNames_of_ctor {types : List VInductiveType} {t : VInductiveType}
    {c : VConstVal} (ht : t ∈ types) (hc : c ∈ t.ctors) : c.name ∈ familyNames types :=
  List.mem_flatMap.mpr ⟨t, ht, List.mem_cons_of_mem _ (List.mem_map_of_mem hc)⟩

theorem caseConstructor_recursiveFields {schema : CaseSchema}
    (ctor : Constructor schema.signature.families.size)
    (owner : Fin schema.signature.families.size) :
    Instance.recursiveFields (s := schema.view owner) (schema.caseConstructor ctor) = [] := by
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro ⟨field, i⟩ hmem
  have hf := List.fst_mem_of_mem_zipIdx hmem
  change field ∈ (schema.signature.fieldTypes ctor).map Field.external at hf
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
  rfl

theorem caseConstructor_fieldTypes {schema : CaseSchema}
    (ctor : Constructor schema.signature.families.size)
    (owner : Fin schema.signature.families.size) :
    ∀ e ∈ (schema.view owner).fieldTypes (schema.caseConstructor ctor),
      e ∈ schema.signature.fieldTypes ctor := by
  intro e he
  simp only [InductiveSignature.fieldTypes, List.mem_map] at he
  obtain ⟨⟨field, i⟩, hmem, rfl⟩ := he
  have hf := List.fst_mem_of_mem_zipIdx hmem
  change field ∈ (schema.signature.fieldTypes ctor).map Field.external at hf
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
  simpa [InductiveSignature.fieldType, InductiveSignature.fieldTypes] using ht

/-- The registered eliminator schemas avoid `names`, with the constant
support seen by `mentionsAnyConst` (projection type names are not counted). -/
def EliminatorsAvoidConsts (envTypes : VEnv) (names : List Name) : Prop :=
  ∀ block schema, envTypes.eliminators block schema →
    (∀ owner type, schema.genericType owner = some type →
      type.mentionsAnyConst names = false) ∧
    (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
      df.lhs.mentionsAnyConst names = false ∧ df.rhs.mentionsAnyConst names = false ∧
      df.type.mentionsAnyConst names = false)

/-- In a well-formed environment, every registered eliminator schema avoids
(in the `mentionsAnyConst` sense) every name that is not a constant of the
environment. -/
theorem VEnv.WF.eliminatorsAvoidConsts {env : VEnv} {names : List Name}
    (henv : env.WF) (hfresh : ∀ n ∈ names, env.constants n = none) :
    EliminatorsAvoidConsts env names := by
  intro block schema hlookup
  obtain ⟨base, source, blk, hbase, hle, hcert, _, hconst⟩ := henv.eliminator_installed hlookup
  obtain ⟨expanded, auxiliaries, hdata, hprior, hres, _, hrfresh⟩ := hcert
  have hbaseOrd : base.Ordered := hbase.ordered
  have hbaseFresh : ∀ n ∈ names, base.constants n = none :=
    fun n hn => hle.constants_eq_none_left (hfresh n hn)
  have hnotNames : ∀ {n}, env.constants n ≠ none → names.contains n = false := by
    intro n hn
    apply Bool.eq_false_iff.mpr
    intro hc
    exact hn (hfresh n (by simpa using hc))
  -- source family and constructor names are constants of `env`
  have hsrcPresent : ∀ n ∈ familyNames source.types, env.constants n ≠ none := by
    intro n hn
    obtain ⟨t, ht, hn⟩ := List.mem_flatMap.mp hn
    rcases List.mem_cons.mp hn with rfl | hn
    · have := hconst t.toVConstVal (List.mem_append_left _ (by
        rw [hdata.types]; exact List.mem_map_of_mem ht))
      simp [this]
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      have := hconst c (List.mem_append_right _ (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩))
      simp [this]
  have hsrcNot : ∀ n ∈ familyNames source.types, n ∉ names := by
    intro n hn hmem
    exact hsrcPresent n hn (hfresh n hmem)
  -- the expanded environments
  obtain ⟨envET, envEC, es, hET, hEC, -, hfam⟩ := hdata.familyTypesWF
  obtain ⟨_, _, _, _, envET', envEC', hET', hEC', htWF, hcWF⟩ := hdata.expandedWF
  have : envET' = envET := Option.some.inj (hET'.symm.trans hET)
  subst this
  have : envEC' = envEC := Option.some.inj (hEC'.symm.trans hEC)
  subst this
  have hETord : envET'.Ordered := hbaseOrd.addConstVals (by
    intro ci hci
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hci
    exact htWF t ht) hET
  have hECord : envEC'.Ordered := hETord.addConstVals hcWF hEC
  have hETle : envET' ≤ envEC' := VEnv.addConstVals_le hEC
  -- names
  let r := compilationRestoration source auxiliaries
  let H := r.heads.map (·.auxiliary)
  let R := r.recursors.map Prod.fst
  let L := names.filter (fun n => !(H.contains n)) ++ R
  obtain ⟨envTS, direct, hTS, hdirect, hwell, hfamilies⟩ := hdata.correspondence
  have hparamsLen : schema.signature.params.length = source.nparams :=
    hdata.model.nparams.trans hdata.nparams
  have hheadNames : H = familyNames direct :=
    compilationRestoration_heads_names hparamsLen hdirect
  have hexpNames : ∀ n ∈ familyNames expanded.types,
      n ∈ familyNames source.types ∨ n ∈ H := by
    intro n hn
    rw [← hdata.model.familyNames, RestoresFamily.familyNames hfamilies,
      familyNames_append] at hn
    rcases List.mem_append.mp hn with hn | hn
    · exact Or.inl hn
    · exact Or.inr (hheadNames ▸ hn)
  have hexpTC : ∀ n ∈ expanded.typeConstants.map (·.name) ++
      expanded.constructorConstants.map (·.name), n ∈ familyNames expanded.types := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      exact mem_familyNames_of_type ht
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
      obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hv
      exact mem_familyNames_of_ctor ht hc
  have hLfresh : ∀ n ∈ L, envEC'.constants n = none := by
    intro n hn
    cases hlook : envEC'.constants n with
    | none => rfl
    | some ci =>
      exfalso
      have horigin : base.constants n ≠ none ∨
          n ∈ expanded.typeConstants.map (·.name) ++
            expanded.constructorConstants.map (·.name) := by
        rcases VEnv.addConstVals_lookup_cases hEC hlook with h | ⟨e, he, rfl, _⟩
        · rcases VEnv.addConstVals_lookup_cases hET h with h | ⟨e, he, rfl, _⟩
          · exact Or.inl (by simp [h])
          · exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem he))
        · exact Or.inr (List.mem_append_right _ (List.mem_map_of_mem he))
      rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨hnN, hnH⟩ := List.mem_filter.mp hn
        rcases horigin with hb | he
        · exact hb (hbaseFresh n hnN)
        · rcases hexpNames n (hexpTC n he) with hs | hh
          · exact hsrcNot n hs hnN
          · simp [hh] at hnH
      · obtain ⟨hb', -, he'⟩ := hrfresh n hn
        rcases horigin with hb | he
        · exact hb hb'
        · exact he' (by simpa only [VInductDecl.sourceNames, List.map_append] using he)
  have hLconst : ∀ {n}, envEC'.constants n ≠ none → L.contains n = false := by
    intro n hn
    apply Bool.eq_false_iff.mpr
    intro hc
    exact hn (hLfresh n (by simpa using hc))
  have hLfreshET : ∀ n ∈ L, envET'.constants n = none :=
    fun n hn => hETle.constants_eq_none_left (hLfresh n hn)
  -- the pieces of the normalized signature avoid `L`
  have hctorAvoid : ∀ ctor ∈ schema.signature.constructors.toList,
      L.contains ctor.name = false ∧
      (∀ e ∈ schema.signature.fieldTypes ctor, e.containsAnyConst L = false) ∧
      (∀ e ∈ ctor.indices, e.containsAnyConst L = false) := by
    intro ctor hctor
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hctor
    let index : Fin schema.signature.constructors.size := ⟨i, by simpa using hi⟩
    have hidx : schema.signature.constructors[index] = ctor := by
      simpa [index] using hget
    obtain ⟨src, hsrc, hname, _, T, hdef⟩ := hdata.model.constructor index hET
    rw [hidx] at hname hdef
    have hfree := (VEnv.IsDefEq.noFreshConsts hETord hLfreshET
      (by intro t ht; simp at ht) hdef).1
    unfold InductiveSignature.constructorType at hfree
    obtain ⟨hdoms, hbody⟩ := VExpr.containsAnyConst_wrapForalls_eq_false_iff.mp hfree
    unfold InductiveSignature.familyApp at hbody
    obtain ⟨_, hargs⟩ := (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mp hbody
    refine ⟨?_, fun e he => hdoms e (List.mem_append_right _ he),
      fun e he => hargs e (List.mem_append_right _ he)⟩
    rw [hname]
    exact hLconst (by
      rw [VEnv.addConstVals_get hEC hsrc]
      simp)
  have hview : ∀ owner : Fin schema.signature.families.size,
      SigAvoids L (schema.view owner) := by
    intro owner
    have hctx := VEnv.ctxNoFreshConsts_addProjections (env := envEC'.addEliminators es)
      hECord.addEliminators (fun n hn => by simpa using hLfresh n hn) (hfam owner).1
    obtain ⟨src, hsrc, hname, _⟩ := hdata.model.family owner
    have hfamName : L.contains schema.signature.families[owner].name = false := by
      rw [hname]
      exact hLconst (by
        rw [(hETle).constants (VEnv.addConstVals_get hET (List.mem_map_of_mem hsrc))]
        simp)
    have hsingle : ∀ f ∈ (schema.view owner).families.toList,
        f = schema.signature.families[owner] := by
      intro f hf
      simpa [CaseSchema.view] using hf
    have hviewCtor : ∀ c ∈ (schema.view owner).constructors.toList,
        ∃ ctor ∈ schema.signature.constructors.toList, c = schema.caseConstructor ctor := by
      intro c hc
      change c ∈ (schema.signature.constructors.toList.filterMap fun ctor =>
        if ctor.owner == owner then some (schema.caseConstructor ctor) else none) at hc
      obtain ⟨ctor, hctor, hsome⟩ := List.mem_filterMap.mp hc
      split at hsome
      · exact ⟨ctor, hctor, (Option.some.inj hsome).symm⟩
      · cases hsome
    refine
      { params := ?_
        familyName := ?_
        familyIndices := ?_
        ctorName := ?_
        ctorFields := ?_
        ctorIndices := ?_
        external := ?_ }
    · intro p hp
      exact hctx p (List.mem_append_right _ (List.mem_reverse.mpr hp))
    · intro f hf
      rw [hsingle f hf]
      exact hfamName
    · intro f hf e he
      rw [hsingle f hf] at he
      exact hctx e (List.mem_append_left _ (List.mem_reverse.mpr he))
    · intro c hc
      obtain ⟨ctor, hctor, rfl⟩ := hviewCtor c hc
      exact (hctorAvoid ctor hctor).1
    · intro c hc e he
      obtain ⟨ctor, hctor, rfl⟩ := hviewCtor c hc
      exact (hctorAvoid ctor hctor).2.1 e (caseConstructor_fieldTypes ctor owner e he)
    · intro c hc e he
      obtain ⟨ctor, hctor, rfl⟩ := hviewCtor c hc
      exact (hctorAvoid ctor hctor).2.2 e he
    · intro c hc
      obtain ⟨ctor, hctor, rfl⟩ := hviewCtor c hc
      exact caseConstructor_recursiveFields ctor owner
  -- the restoration heads
  obtain ⟨_, _, _, _, envTS', _, hTS', _, hsWF, _⟩ := hdata.sourceWF
  have : envTS' = envTS := Option.some.inj (hTS'.symm.trans hTS)
  subst this
  have hTSord : envTS'.Ordered := hbaseOrd.addConstVals (by
    intro ci hci
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hci
    exact hsWF t ht) hTS
  have hTSfresh : ∀ n ∈ names, envTS'.constants n = none := by
    intro n hn
    cases hlook : envTS'.constants n with
    | none => rfl
    | some ci =>
      exfalso
      rcases VEnv.addConstVals_lookup_cases hTS hlook with h | ⟨e, he, rfl, _⟩
      · rw [hbaseFresh n hn] at h
        cases h
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
        exact hsrcNot _ (mem_familyNames_of_type ht) hn
  have hheads : ∀ h ∈ r.heads, names.contains h.target = false ∧
      ∀ a ∈ h.arguments, a.mentionsAnyConst names = false := by
    intro h hh
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hh
    refine ⟨?_, ?_⟩
    · apply Bool.eq_false_iff.mpr
      intro hc
      exact hprior.target_present a ha h hh (hbaseFresh _ (by simpa using hc))
    · have hargs : h.arguments = a.arguments := by
        simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
        rcases hh with rfl | ⟨_, _, rfl⟩ <;> rfl
      rw [hargs]
      obtain ⟨d, hd, hdirectA⟩ :=
        Lean4Lean.List.Forall₂.forall_exists_l (List.mapM_eq_some.mp hdirect) a ha
      obtain ⟨x, _, hrestores⟩ := Lean4Lean.List.Forall₂.forall_exists_r hfamilies d
        (List.mem_append_right _ hd)
      obtain ⟨_, _, _, _, _, hdef, _⟩ := hrestores.type
      have hdtype := (VEnv.IsDefEq.noFreshConsts hTSord hTSfresh
        (by intro t ht; simp at ht) hdef).1
      obtain ⟨body, hbody⟩ := ContainerSpecialization.directFamily_type hdirectA
      rw [hbody] at hdtype
      have hparams := (VExpr.containsAnyConst_wrapForalls_eq_false_iff.mp hdtype).1
      have hctx : CtxAvoidsConsts names schema.signature.params.reverse := by
        intro t ht
        exact hparams t (List.mem_reverse.mp ht)
      obtain ⟨_, _, _, _, _, type, htyped⟩ := hwell a ha
      have happ := (VEnv.IsDefEq.noFreshConsts hTSord hTSfresh hctx htyped).1
      obtain ⟨_, hargs'⟩ := (VExpr.containsAnyConst_mkApps_eq_false_iff _ _).mp happ
      intro arg harg
      exact VExpr.mentionsAnyConst_of_containsAnyConst (hargs' arg harg)
  have hrename : ∀ name, name ∉ r.heads.map (·.auxiliary) → L.contains name = false →
      names.contains (r.recursorName name) = false := by
    intro name hnotH hnotL
    have hnotR : name ∉ R := by
      intro hR
      have : L.contains name = true := by simp [L, hR]
      rw [hnotL] at this
      cases this
    have hren : r.recursorName name = name := by
      unfold Restoration.recursorName
      rw [List.find?_eq_none.mpr]
      intro pair hpair heq
      exact hnotR (List.mem_map.mpr ⟨pair, hpair, by simpa using heq⟩)
    rw [hren]
    apply Bool.eq_false_iff.mpr
    intro hc
    have : L.contains name = true := by
      simp only [L, H, List.contains_append, Bool.or_eq_true]
      left
      simp only [List.elem_eq_mem, decide_eq_true_eq, List.mem_filter,
        Bool.not_eq_eq_eq_not, Bool.not_true]
      refine ⟨by simpa using hc, ?_⟩
      simpa using hnotH
    rw [hnotL] at this
    cases this
  refine ⟨?_, ?_⟩
  · intro owner type htype
    change schema.restoration.expr _ = some type at htype
    rw [hres] at htype
    exact Restoration.expr_mentions hheads hrename
      ((hview owner).recursorType _ _) htype
  · intro owner rules hrules df hdf
    obtain ⟨index, hrestore⟩ := CaseSchema.equation_of_mem hrules hdf
    rw [hres] at hrestore
    obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
    obtain ⟨al, ar, at'⟩ := (hview owner).equation _ index block owner.val
    exact ⟨Restoration.expr_mentions hheads hrename al hl,
      Restoration.expr_mentions hheads hrename ar hr,
      Restoration.expr_mentions hheads hrename at' ht⟩
