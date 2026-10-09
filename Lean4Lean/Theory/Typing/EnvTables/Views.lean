import Lean4Lean.Theory.Typing.EnvTables.Defs

/-!
# The history invariant of the environment tables

Every `VEnv.WF'` history has tables satisfying `Tables.Inv`. Families are recorded at their
first registration: block installation (families with at least one constructor), structure
registration (`inductProjections`), eliminator registration (family by family, for a family none
of whose names is already recorded) and the quotient.
-/

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

variable {env env' : VEnv}

/-! ## Small syntactic lemmas -/

theorem install_parts {base installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install base block = some installed) :
    ∃ envTypes envCtors envRecursors,
      base.addConstVals block.types = some envTypes ∧
      envTypes.addConstVals block.ctors = some envCtors ∧
      ((envCtors.addEliminators block.eliminators).addProjections block.projections).addConstVals
        block.recursors = some envRecursors ∧
      installed = envRecursors.addDefEqRules block.rules :=
  VInductBlock.install_stages H

theorem install_defeqs {base installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install base block = some installed) :
    installed.defeqs df ↔ df ∈ block.rules ∨ base.defeqs df := by
  obtain ⟨t, c, r, ht, hc, hr, rfl⟩ := install_parts H
  rw [VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
    VEnv.addEliminators_defeqs, VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht]

theorem install_projections {base installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install base block = some installed) :
    installed.projections s info ↔
      (∃ entry ∈ block.projections, s = entry.typeName ∧ info = entry.info) ∨
        base.projections s info := by
  obtain ⟨t, c, r, ht, hc, hr, rfl⟩ := install_parts H
  simp only [VEnv.addDefEqRules_projections]
  rw [VEnv.addConstVals_projections hr, VEnv.addProjections_iff, VEnv.addEliminators_projections,
    VEnv.addConstVals_projections hc, VEnv.addConstVals_projections ht]

theorem install_eliminators {base installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install base block = some installed) :
    installed.eliminators n s ↔ (n, s) ∈ block.eliminators ∨ base.eliminators n s :=
  VInductBlock.install_eliminators_iff H

theorem Mentions.of_stripLams {e : VExpr} (h : Mentions X e.stripLams) : Mentions X e := by
  induction e with
  | lam _ _ _ ih => exact Or.inr (ih h)
  | _ => exact h

theorem Mentions.of_forallResult {e : VExpr}
    (h : e.forallResult.getAppFnArgs.1 = .const X ls) : Mentions X e := by
  have spine : ∀ {e : VExpr}, e.getAppFnArgs.1 = .const X ls → Mentions X e := by
    intro e he
    rw [← VExpr.mkApps_getAppFnArgs e, he]
    exact Mentions.mkApps_head
  induction e with
  | forallE _ _ _ ih => exact Or.inr (ih h)
  | _ => exact spine h

theorem find?_name_some {l : List α} {f : α → Name}
    (h : l.find? (fun x => f x == n) = some x) : x ∈ l ∧ f x = n :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem find?_name_of_mem {l : List α} {f : α → Name} (hnd : (l.map f).Nodup) (hx : x ∈ l) :
    l.find? (fun y => f y == f x) = some x := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : f y ≠ f x := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
      simp [hne, ih hnd.2 hx]

theorem find?_name_none {l : List α} {f : α → Name} (h : ∀ x ∈ l, f x ≠ n) :
    l.find? (fun y => f y == n) = none := by
  apply List.find?_eq_none.mpr
  intro x hx
  simpa using h x hx

/-! ## Generic preservation -/

theorem ViewInv.transport {fam : Name → Option FamData} {ctor : Name → Option CtorData}
    (H : ViewInv env fam ctor) (hle : env ≤ env') (hdf : env'.defeqs = env.defeqs) :
    ViewInv env' fam ctor where
  fam h := by
    obtain ⟨h1, h2⟩ := H.fam h
    exact ⟨h1.mono hle, h2⟩
  ctor h := by
    obtain ⟨h1, h2⟩ := H.ctor h
    exact ⟨h1.mono hle, h2⟩
  fam_ctor := H.fam_ctor
  rigid h := by
    have := H.rigid h
    simpa only [VEnv.Rigid, hdf] using this
  witness h := (H.witness h).mono hle

/-- Add views for names not yet recorded. -/
def addView (old : Name → Option α) (new : Name → Option α) (n : Name) : Option α :=
  match old n with
  | some d => some d
  | none => new n

theorem addView_some {old new : Name → Option α} :
    addView old new n = some d ↔ old n = some d ∨ (old n = none ∧ new n = some d) := by
  simp only [addView]
  cases old n <;> simp

theorem addView_none {old new : Name → Option α} :
    addView old new n = none ↔ old n = none ∧ new n = none := by
  simp only [addView]
  cases old n <;> simp

theorem addView_of_old {old new : Name → Option α} (h : old n = some d) :
    addView old new n = some d := addView_some.mpr (.inl h)

/-- Conditions under which a family of new views is consistent. -/
structure NewViewsWF (env : VEnv) (famT : Name → Option FamData) (ctorT : Name → Option CtorData)
    (fs : Name → Option FamData) (cs : Name → Option CtorData) : Prop where
  fam : fs n = some d → famT n = none ∧ ctorT n = none ∧ cs n = none ∧
    FamShape env n d ∧ d.ctors.Nodup ∧
    (∀ c ∈ d.ctors, ∃ k, cs c = some k ∧ k.family = n ∧ k.uvars = d.uvars ∧
      k.nparams = d.nparams) ∧
    env.Rigid n ∧ MetadataMentions env n
  ctor : cs c = some k → famT c = none ∧ ctorT c = none ∧ fs c = none ∧
    CtorShape env c k ∧ (∃ d, fs k.family = some d ∧ c ∈ d.ctors) ∧
    env.Rigid c ∧ MetadataMentions env c

theorem ViewInv.addViews {fam : Name → Option FamData} {ctor : Name → Option CtorData}
    {fs : Name → Option FamData} {cs : Name → Option CtorData}
    (H : ViewInv env fam ctor) (hok : NewViewsWF env fam ctor fs cs) :
    ViewInv env (addView fam fs) (addView ctor cs) where
  fam {I d} h := by
    rcases addView_some.mp h with h | ⟨_, h⟩
    · obtain ⟨h1, h2, h3⟩ := H.fam h
      exact ⟨h1, h2, fun c hc => by
        obtain ⟨k, hk, hk'⟩ := h3 c hc
        exact ⟨k, addView_of_old hk, hk'⟩⟩
    · obtain ⟨_, _, _, h1, h2, h3, _⟩ := hok.fam h
      refine ⟨h1, h2, fun c hc => ?_⟩
      obtain ⟨k, hk, hk'⟩ := h3 c hc
      exact ⟨k, addView_some.mpr (.inr ⟨(hok.ctor hk).2.1, hk⟩), hk'⟩
  ctor {c k} h := by
    rcases addView_some.mp h with h | ⟨_, h⟩
    · obtain ⟨h1, d, h2, h3⟩ := H.ctor h
      exact ⟨h1, d, addView_of_old h2, h3⟩
    · obtain ⟨_, _, _, h1, ⟨d, h2, h3⟩, _⟩ := hok.ctor h
      exact ⟨h1, d, addView_some.mpr (.inr ⟨(hok.fam h2).1, h2⟩), h3⟩
  fam_ctor {n} h := by
    apply addView_none.mpr
    cases hf : fam n with
    | some d =>
      refine ⟨H.fam_ctor (by simp [hf]), ?_⟩
      cases hc : cs n with
      | none => rfl
      | some k => exact absurd (hok.ctor hc).1 (by simp [hf])
    | none =>
      have hfs : fs n ≠ none := by
        intro hfs; exact h (addView_none.mpr ⟨hf, hfs⟩)
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hfs
      exact ⟨(hok.fam hd).2.1, (hok.fam hd).2.2.1⟩
  rigid {n} h := by
    by_cases hold : fam n ≠ none ∨ ctor n ≠ none
    · exact H.rigid hold
    · simp only [ne_eq, not_or, Classical.not_not] at hold
      rcases h with h | h
      · have hfs : fs n ≠ none := fun hfs => h (addView_none.mpr ⟨hold.1, hfs⟩)
        obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hfs
        exact (hok.fam hd).2.2.2.2.2.2.1
      · have hcs : cs n ≠ none := fun hcs => h (addView_none.mpr ⟨hold.2, hcs⟩)
        obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hcs
        exact (hok.ctor hk).2.2.2.2.2.1
  witness {n} h := by
    by_cases hold : fam n ≠ none ∨ ctor n ≠ none
    · exact H.witness hold
    · simp only [ne_eq, not_or, Classical.not_not] at hold
      rcases h with h | h
      · have hfs : fs n ≠ none := fun hfs => h (addView_none.mpr ⟨hold.1, hfs⟩)
        obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hfs
        exact (hok.fam hd).2.2.2.2.2.2.2
      · have hcs : cs n ≠ none := fun hcs => h (addView_none.mpr ⟨hold.2, hcs⟩)
        obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hcs
        exact (hok.ctor hk).2.2.2.2.2.2

/-- Add views to tables. -/
def Tables.addViews (T : Tables) (fs : Name → Option FamData) (cs : Name → Option CtorData) :
    Tables :=
  { T with fam := addView T.fam fs, ctor := addView T.ctor cs }

theorem Tables.extends_addViews (T : Tables) (fs : Name → Option FamData)
    (cs : Name → Option CtorData) : T.Extends (T.addViews fs cs) where
  defs h := h
  recursors h := h
  quot h := h
  fam h := addView_of_old h
  ctor h := addView_of_old h

namespace Tables.Inv
variable {T T' : Tables}

/-- Growth of the environment that adds no equations and no projections. -/
theorem transport (H : T.Inv env) (hle : env ≤ env') (hdf : env'.defeqs = env.defeqs)
    (hproj : env'.projections = env.projections) : T.Inv env' where
  defs h := by
    obtain ⟨h1, h2, h3⟩ := H.defs h
    exact ⟨h1, hle.constants h2, hle.defeqs h3⟩
  recursors h := by
    obtain ⟨h1, h2⟩ := H.recursors h
    exact ⟨h1, h2.mono hle .rfl⟩
  quot h := by
    obtain ⟨h1, h2⟩ := H.quot h
    exact ⟨h1.mono hle, h2⟩
  defs_recursors := H.defs_recursors
  views := H.views.transport hle hdf
  equations h := H.equations (by rwa [hdf] at h)
  projections h := H.projections (by rwa [hproj] at h)

theorem addViews (H : T.Inv env) (hok : NewViewsWF env T.fam T.ctor fs cs) :
    (T.addViews fs cs).Inv env where
  defs h := H.defs h
  recursors h := by
    obtain ⟨h1, h2⟩ := H.recursors h
    exact ⟨h1, h2.mono .rfl (T.extends_addViews fs cs)⟩
  quot h := by
    obtain ⟨h1, h2, h3, h4⟩ := H.quot h
    exact ⟨h1, addView_of_old h2, addView_of_old h3, h4⟩
  defs_recursors := H.defs_recursors
  views := H.views.addViews hok
  equations h := H.equations h
  projections h := by
    obtain ⟨h1, h2⟩ := H.projections h
    exact ⟨addView_of_old h1, addView_of_old h2⟩

end Tables.Inv

/-! ## Views of a declaration -/

variable {decl : VInductDecl} {sel : VInductiveType → Bool} {t t' type : VInductiveType}
  {c ctor : VConstVal} {params : List VExpr}

def viewFams (decl : VInductDecl) (sel : VInductiveType → Bool) (n : Name) : Option FamData :=
  ((decl.types.filter sel).find? (fun t => t.name == n)).map (famView decl)

def viewPairs (decl : VInductDecl) (sel : VInductiveType → Bool) :
    List (VInductiveType × VConstVal) :=
  (decl.types.filter sel).flatMap fun t => t.ctors.map (t, ·)

def viewCtors (decl : VInductDecl) (sel : VInductiveType → Bool) (n : Name) : Option CtorData :=
  ((viewPairs decl sel).find? (fun p => p.2.name == n)).map fun p => ctorView decl p.1 p.2

theorem find?_exists {l : List α} {f : α → Name} (hx : x ∈ l) (hf : f x = n) :
    ∃ y, l.find? (fun y => f y == n) = some y := by
  cases h : l.find? (fun y => f y == n) with
  | some y => exact ⟨y, rfl⟩
  | none =>
    have := List.find?_eq_none.mp h x hx
    simp [hf] at this

theorem viewFams_some (h : viewFams decl sel n = some d) :
    ∃ t ∈ decl.types, sel t ∧ t.name = n ∧ d = famView decl t := by
  simp only [viewFams, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨hmem, hn⟩ := find?_name_some (f := fun t : VInductiveType => t.name) ht
  obtain ⟨hmem, hsel⟩ := List.mem_filter.mp hmem
  exact ⟨t, hmem, hsel, hn, rfl⟩

theorem viewFams_mem (hnd : decl.sourceNames.Nodup) (ht : t ∈ decl.types) (hs : sel t) :
    viewFams decl sel t.name = some (famView decl t) := by
  obtain ⟨y, hy⟩ := find?_exists (f := fun t : VInductiveType => t.name) (List.mem_filter.mpr ⟨ht, hs⟩) rfl
  obtain ⟨hmem, hn⟩ := find?_name_some (f := fun t : VInductiveType => t.name) hy
  have := VInductDecl.type_eq_of_mem_name hnd (List.mem_filter.mp hmem).1 ht hn
  subst this
  simp only [viewFams, hy, Option.map_some]

theorem viewFams_none (hn : ∀ t ∈ decl.types, sel t → t.name ≠ n) : viewFams decl sel n = none := by
  simp only [viewFams, Option.map_eq_none_iff]
  exact find?_name_none fun t ht => hn t (List.mem_filter.mp ht).1 (List.mem_filter.mp ht).2

theorem mem_viewPairs : p ∈ viewPairs decl sel ↔ p.1 ∈ decl.types ∧ sel p.1 ∧ p.2 ∈ p.1.ctors := by
  obtain ⟨t, c⟩ := p
  simp only [viewPairs, List.mem_flatMap, List.mem_filter, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ⟨ha, hs⟩, c', hc', rfl, rfl⟩
    exact ⟨ha, hs, hc'⟩
  · rintro ⟨ha, hs, hc⟩
    exact ⟨t, ⟨ha, hs⟩, c, hc, rfl, rfl⟩

theorem viewCtors_some (h : viewCtors decl sel n = some k) :
    ∃ t ∈ decl.types, sel t ∧ ∃ c ∈ t.ctors, c.name = n ∧ k = ctorView decl t c := by
  simp only [viewCtors, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨hmem, hn⟩ := find?_name_some (f := fun p : VInductiveType × VConstVal => p.2.name) hp
  obtain ⟨h1, h2, h3⟩ := mem_viewPairs.mp hmem
  exact ⟨p.1, h1, h2, p.2, h3, hn, rfl⟩

theorem viewCtors_mem (ht : t ∈ decl.types) (hs : sel t) (hc : c ∈ t.ctors)
    (huniq : ∀ t' ∈ decl.types, sel t' → ∀ c' ∈ t'.ctors, c'.name = c.name →
      ctorView decl t' c' = ctorView decl t c) :
    viewCtors decl sel c.name = some (ctorView decl t c) := by
  obtain ⟨y, hy⟩ := find?_exists (f := fun p : VInductiveType × VConstVal => p.2.name)
    (x := (t, c)) (mem_viewPairs.mpr ⟨ht, hs, hc⟩) rfl
  obtain ⟨hmem, hn⟩ := find?_name_some (f := fun p : VInductiveType × VConstVal => p.2.name) hy
  obtain ⟨h1, h2, h3⟩ := mem_viewPairs.mp hmem
  simp only [viewCtors, hy, Option.map_some]
  rw [huniq _ h1 h2 _ h3 hn]

theorem viewCtors_none (hn : ∀ t ∈ decl.types, sel t → ∀ c ∈ t.ctors, c.name ≠ n) :
    viewCtors decl sel n = none := by
  simp only [viewCtors, Option.map_eq_none_iff]
  apply find?_name_none
  intro p hp
  obtain ⟨h1, h2, h3⟩ := mem_viewPairs.mp hp
  exact hn _ h1 h2 _ h3

theorem sourceNames_type_ne_ctor (hnd : decl.sourceNames.Nodup) (ht : t ∈ decl.types)
    (ht' : t' ∈ decl.types) (hc : c ∈ t'.ctors) : c.name ≠ t.name := by
  intro heq
  have hdisj := (List.nodup_append.mp hnd).2.2
  have h1 : t.name ∈ decl.typeConstants.map VConstVal.name :=
    List.mem_map.mpr ⟨t.toVConstVal, List.mem_map.mpr ⟨t, ht, rfl⟩, rfl⟩
  have h2 : t.name ∈ decl.constructorConstants.map VConstVal.name :=
    List.mem_map.mpr ⟨c, List.mem_flatMap.mpr ⟨t', ht', hc⟩, heq⟩
  exact hdisj _ h1 _ h2 rfl

theorem nodup_of_flatMap {l : List α} {f : α → List β} (h : (l.flatMap f).Nodup)
    (hx : x ∈ l) : (f x).Nodup := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.flatMap_cons] at h
    have := List.nodup_append.mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact this.1
    · exact ih this.2.1 hx

theorem sourceNames_ctors_nodup (hnd : decl.sourceNames.Nodup) (ht : t ∈ decl.types) :
    (t.ctors.map (·.name)).Nodup := by
  have h := (List.nodup_append.mp hnd).2.1
  simp only [VInductDecl.constructorConstants, List.map_flatMap] at h
  exact nodup_of_flatMap (f := fun a : VInductiveType => a.ctors.map VConstVal.name) h ht

/-- The raw constructor shape is the table's constructor shape. -/
theorem ctorShape_of_raw (hraw : decl.RawCtorShape type ctor) (huv : ctor.uvars = decl.uvars)
    (hc : env.constants ctor.name = some ctor.toVConstant) :
    CtorShape env ctor.name (ctorView decl type ctor) := by
  obtain ⟨doms, result, heq, hle, hraw, hhead, harity⟩ := hraw.forallArity
  obtain ⟨type', _, _, levels, hfn, _, hlen, htake⟩ := hraw
  have hspine := VExpr.mkApps_getAppFnArgs result
  rw [hhead] at hspine
  have htake' : result.getAppFnArgs.2.take decl.nparams =
      decl.paramVars (doms.length - decl.nparams) := htake
  have hres : result = VExpr.mkApps (.const type.name (VLevel.params decl.uvars))
      (decl.paramVars (doms.length - decl.nparams) ++ result.getAppFnArgs.2.drop decl.nparams) := by
    rw [← htake', List.take_append_drop]
    exact hspine.symm
  refine ⟨ctor.toVConstant, doms, result.getAppFnArgs.2.drop decl.nparams, hc, huv, ?_, ?_⟩
  · change ctor.type = _
    rw [heq]
    conv => lhs; rw [hres]
    simp only [ctorView, harity, VInductDecl.paramVars, vars]
  · simp only [ctorView, harity]
    omega

/-- The typed family header is the table's family shape. -/
theorem famShape_of_typeShape (hshape : decl.TypeShape env params type)
    (huv : type.uvars = decl.uvars) (hc : env.constants type.name = some type.toVConstant) :
    FamShape env type.name (famView decl type) := by
  obtain ⟨normalized, ownParams, afterParams, indices, result, exprType, htype, hparams,
    hindices, _, hresult⟩ := hshape
  have split : ∀ {n : Nat} {e r : VExpr} {ds : List VExpr},
      e.takeForalls n = some (ds, r) → e = VExpr.wrapForalls ds r ∧ ds.length = n := by
    intro n
    induction n with
    | zero =>
      intro e r ds h
      cases Option.some.inj h
      exact ⟨rfl, rfl⟩
    | succ n ih =>
      intro e r ds h
      cases e with
      | forallE dom body =>
        cases hb : body.takeForalls n with
        | none => simp [VExpr.takeForalls, hb] at h
        | some out =>
          rw [VExpr.takeForalls, hb] at h
          cases Option.some.inj h
          obtain ⟨h1, h2⟩ := ih hb
          exact ⟨congrArg (VExpr.forallE dom) h1, by simp [h2]⟩
      | _ => simp [VExpr.takeForalls] at h
  obtain ⟨hn, hnl⟩ := split hparams
  obtain ⟨ha, hal⟩ := split hindices
  refine ⟨type.toVConstant, hc, huv, ownParams ++ indices, result, exprType, ?_, ?_, ?_⟩
  · change env.IsDefEq decl.uvars [] type.type _ _
    rw [VExpr.wrapForalls_append, ← ha, ← hn]
    exact htype
  · simp [famView, hnl, hal]
  · simpa [famView, List.reverse_append] using hresult

/-- Two raw constructor shapes of the same constant have the same family. -/
theorem RawCtorShape.family_eq {decl decl' : VInductDecl} {t t' : VInductiveType}
    {c c' : VConstVal} (h : decl.RawCtorShape t c) (h' : decl'.RawCtorShape t' c')
    (htype : c.type = c'.type) : t.name = t'.name := by
  obtain ⟨doms, result, heq, _, _, hhead, harity⟩ := h.forallArity
  obtain ⟨doms', result', heq', _, _, hhead', harity'⟩ := h'.forallArity
  have hlen : doms.length = doms'.length := by rw [← harity, ← harity', htype]
  have hp := VExpr.takeForalls_wrapForalls doms result
  rw [← heq, htype, heq', hlen, VExpr.takeForalls_wrapForalls] at hp
  have hr : result' = result := (Prod.mk.inj (Option.some.inj hp)).2
  rw [hr, hhead] at hhead'
  exact (VExpr.const.inj hhead').1

theorem ctorView_unique
    (hctors : ∀ t ∈ decl.types, sel t → ∀ c ∈ t.ctors,
      env.constants c.name = some c.toVConstant ∧ decl.RawCtorShape t c ∧ c.uvars = decl.uvars) :
    ∀ t ∈ decl.types, sel t → ∀ c ∈ t.ctors,
      ∀ t' ∈ decl.types, sel t' → ∀ c' ∈ t'.ctors, c'.name = c.name →
        ctorView decl t' c' = ctorView decl t c := by
  intro t ht hs c hc t' ht' hs' c' hc' hn
  obtain ⟨h1, h2, _⟩ := hctors t ht hs c hc
  obtain ⟨h1', h2', _⟩ := hctors t' ht' hs' c' hc'
  rw [hn, h1] at h1'
  have htype : c'.type = c.type := congrArg VConstant.type (Option.some.inj h1').symm
  simp only [ctorView, htype, RawCtorShape.family_eq h2' h2 htype]

/-- New views of a declaration are consistent. -/
theorem newViewsWF_decl {famT : Name → Option FamData} {ctorT : Name → Option CtorData}
    (hnd : decl.sourceNames.Nodup)
    (hfresh : ∀ t ∈ decl.types, sel t → famT t.name = none ∧ ctorT t.name = none ∧
      ∀ c ∈ t.ctors, famT c.name = none ∧ ctorT c.name = none)
    (hfam : ∀ t ∈ decl.types, sel t → FamShape env t.name (famView decl t))
    (hctors : ∀ t ∈ decl.types, sel t → ∀ c ∈ t.ctors,
      env.constants c.name = some c.toVConstant ∧ decl.RawCtorShape t c ∧ c.uvars = decl.uvars)
    (hrigid : ∀ t ∈ decl.types, sel t → env.Rigid t.name ∧ ∀ c ∈ t.ctors, env.Rigid c.name)
    (hwit : ∀ t ∈ decl.types, sel t → MetadataMentions env t.name ∧ ∀ c ∈ t.ctors, MetadataMentions env c.name) :
    NewViewsWF env famT ctorT (viewFams decl sel) (viewCtors decl sel) := by
  have huniq := ctorView_unique hctors
  refine ⟨fun {n d} h => ?_, fun {n k} h => ?_⟩
  · obtain ⟨t, ht, hs, rfl, rfl⟩ := viewFams_some h
    obtain ⟨h1, h2, _⟩ := hfresh t ht hs
    refine ⟨h1, h2, viewCtors_none fun t' ht' _ c hc => sourceNames_type_ne_ctor hnd ht ht' hc,
      hfam t ht hs, sourceNames_ctors_nodup hnd ht, ?_, (hrigid t ht hs).1, (hwit t ht hs).1⟩
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    exact ⟨_, viewCtors_mem ht hs hc (huniq t ht hs c hc), rfl, rfl, rfl⟩
  · obtain ⟨t, ht, hs, c, hc, rfl, rfl⟩ := viewCtors_some h
    obtain ⟨h1, h2, h3⟩ := hctors t ht hs c hc
    refine ⟨((hfresh t ht hs).2.2 c hc).1, ((hfresh t ht hs).2.2 c hc).2,
      viewFams_none fun t' ht' _ heq => sourceNames_type_ne_ctor hnd ht' ht hc heq.symm,
      ctorShape_of_raw h2 h3 h1, ⟨_, viewFams_mem hnd ht hs, List.mem_map.mpr ⟨c, hc, rfl⟩⟩,
      (hrigid t ht hs).2 c hc, (hwit t ht hs).2 c hc⟩

end Lean4Lean.EnvTables
