import Lean4Lean.Theory.Typing.EnvTables.Views

/-!
# Preservation of the table invariant by the declaration steps
-/

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

variable {env env' : VEnv} {T : Tables}

/-! ## Entries are declared constants -/

namespace Tables.Inv

theorem fam_const (H : T.Inv env) (h : T.fam n ≠ none) : ∃ ci, env.constants n = some ci := by
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨⟨ci, hci, _⟩, _⟩ := H.views.fam hd
  exact ⟨ci, hci⟩

theorem ctor_const (H : T.Inv env) (h : T.ctor n ≠ none) : ∃ ci, env.constants n = some ci := by
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨⟨ci, _, _, hci, _⟩, _⟩ := H.views.ctor hk
  exact ⟨ci, hci⟩

theorem defs_const (H : T.Inv env) (h : T.defs n ≠ none) : ∃ ci, env.constants n = some ci := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  exact ⟨_, (H.defs hv).2.1⟩

theorem recursors_const (H : T.Inv env) (h : T.recursors n ≠ none) :
    ∃ ci, env.constants n = some ci := by
  obtain ⟨data, hd⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨rfl, he⟩ := H.recursors hd
  exact he.registered.constant_exists

end Tables.Inv

theorem ViewInv.const {famT : Name → Option FamData} {ctorT : Name → Option CtorData}
    (H : ViewInv env famT ctorT) (h : famT n ≠ none ∨ ctorT n ≠ none) :
    ∃ ci, env.constants n = some ci := by
  rcases h with h | h
  · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨⟨ci, hci, _⟩, _⟩ := H.fam hd
    exact ⟨ci, hci⟩
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨⟨ci, _, _, hci, _⟩, _⟩ := H.ctor hk
    exact ⟨ci, hci⟩

/-- Adding equations whose heads are fresh constants preserves the views. -/
theorem ViewInv.addRules {famT : Name → Option FamData} {ctorT : Name → Option CtorData}
    (H : ViewInv env famT ctorT) (hle : env ≤ env')
    (hrules : ∀ df, env'.defeqs df → env.defeqs df ∨
      ∃ h ls, df.lhs.stripLams.getAppFnArgs.1 = .const h ls ∧ env.constants h = none) :
    ViewInv env' famT ctorT where
  fam h := by
    obtain ⟨h1, h2⟩ := H.fam h
    exact ⟨h1.mono hle, h2⟩
  ctor h := by
    obtain ⟨h1, h2⟩ := H.ctor h
    exact ⟨h1.mono hle, h2⟩
  fam_ctor := H.fam_ctor
  rigid {n} h := by
    intro df hdf ls hhead
    rcases hrules df hdf with hold | ⟨hn, ls', hh, hfresh⟩
    · exact H.rigid h df hold ls hhead
    · rw [hhead] at hh
      cases hh
      obtain ⟨ci, hci⟩ := H.const h
      rw [hci] at hfresh
      cases hfresh
  witness h := (H.witness h).mono hle

/-! ## Definitions -/

theorem addConsts_fresh {cis : List VDefVal} (h : env.addConsts cis = some env') :
    (∀ ci ∈ cis, env.constants ci.name = none) ∧ (cis.map (·.name)).Nodup := by
  induction cis generalizing env with
  | nil => simp
  | cons ci cis ih =>
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env1, h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h2
    have hself := VEnv.addConst_self h1
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · unfold VEnv.addConst at h1
        split at h1 <;> cases h1
        assumption
      · have := ih1 c hc
        rw [VEnv.addConst_constants_eq h1] at this
        by_cases hn : ci.name = c.name
        · simp [hn] at this
        · simpa [hn] using this
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih2⟩
      obtain ⟨c, hc, hn⟩ := List.mem_map.mp hm
      have := ih1 c hc
      rw [hn, hself] at this
      cases this

theorem addConsts_defeqs {cis : List VDefVal} (h : env.addConsts cis = some env') :
    env'.defeqs = env.defeqs := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConsts] at h; subst h; rfl
  | cons ci cis ih =>
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env1, h1, h2⟩ := h
    exact (ih h2).trans (VEnv.addConst_defeqs h1)

theorem addDefEqs_defeqs {cis : List VDefVal} :
    (env.addDefEqs cis).defeqs df ↔ (∃ ci ∈ cis, df = ci.toDefEq) ∨ env.defeqs df := by
  induction cis generalizing env with
  | nil => simp [VEnv.addDefEqs]
  | cons ci cis ih =>
    change (VEnv.addDefEqs (env.addDefEq ci.toDefEq) cis).defeqs df ↔ _
    rw [ih]
    simp only [VEnv.addDefEq, List.mem_cons]
    constructor
    · rintro (⟨c, hc, rfl⟩ | rfl | h)
      · exact .inl ⟨c, .inr hc, rfl⟩
      · exact .inl ⟨ci, .inl rfl, rfl⟩
      · exact .inr h
    · rintro (⟨c, rfl | hc, rfl⟩ | h)
      · exact .inr (.inl rfl)
      · exact .inl ⟨c, hc, rfl⟩
      · exact .inr (.inr h)

theorem addDefEqs_constants {cis : List VDefVal} : (env.addDefEqs cis).constants = env.constants := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

/-- Record a block of definitions. -/
def Tables.addDefs (T : Tables) (cis : List VDefVal) : Tables :=
  { T with defs := fun n => (cis.find? (fun ci => ci.name == n)).orElse fun _ => T.defs n }

theorem Tables.addDefs_defs {T : Tables} {cis : List VDefVal} (hnd : (cis.map (·.name)).Nodup) :
    (T.addDefs cis).defs n = some v ↔ (v ∈ cis ∧ v.name = n) ∨
      ((∀ ci ∈ cis, ci.name ≠ n) ∧ T.defs n = some v) := by
  simp only [Tables.addDefs]
  cases hf : cis.find? (fun ci => ci.name == n) with
  | some w =>
    obtain ⟨hw, hwn⟩ := find?_name_some (f := fun ci : VDefVal => ci.name) hf
    simp only [Option.orElse_some, Option.some.injEq]
    constructor
    · rintro rfl; exact .inl ⟨hw, hwn⟩
    · rintro (⟨hv, hvn⟩ | ⟨hall, _⟩)
      · have := find?_name_of_mem (f := fun ci : VDefVal => ci.name) hnd hv
        rw [hvn, hf] at this
        exact Option.some.inj this
      · exact absurd hwn (hall w hw)
  | none =>
    simp only [Option.orElse_none]
    have hall : ∀ ci ∈ cis, ci.name ≠ n := fun ci hci hn => by
      have := List.find?_eq_none.mp hf ci hci
      simp [hn] at this
    constructor
    · intro h; exact .inr ⟨hall, h⟩
    · rintro (⟨hv, hvn⟩ | ⟨_, h⟩)
      · exact absurd hvn (hall v hv)
      · exact h

theorem Tables.Inv.addDefinitions (H : T.Inv env) {cis : List VDefVal} {env1 : VEnv}
    (hadd : env.addConsts cis = some env1) :
    (T.addDefs cis).Inv (env1.addDefEqs cis) := by
  obtain ⟨hfresh, hnd⟩ := addConsts_fresh hadd
  have hle1 := VEnv.addConsts_le hadd
  have hle : env ≤ env1.addDefEqs cis := hle1.trans VEnv.addDefEqs_le
  have hold : ∀ n, (∃ ci, env.constants n = some ci) → ∀ ci ∈ cis, ci.name ≠ n := by
    rintro n ⟨x, hx⟩ ci hci rfl
    rw [hfresh ci hci] at hx
    cases hx
  have hext : T.Extends (T.addDefs cis) := by
    refine ⟨fun {n v} h => ?_, id, id, id, id⟩
    exact (Tables.addDefs_defs hnd).mpr (.inr ⟨hold n (H.defs_const (by simp [h])), h⟩)
  refine ⟨fun {n v} h => ?_, fun {n data} h => ?_, fun h => ?_, fun {n} h => ?_, ?_,
    fun {df} h => ?_, fun {s info} h => ?_⟩
  · rcases (Tables.addDefs_defs hnd).mp h with ⟨hv, rfl⟩ | ⟨_, h⟩
    · refine ⟨rfl, ?_, ?_⟩
      · rw [addDefEqs_constants]; exact VEnv.addConsts_constants hadd v hv
      · exact addDefEqs_defeqs.mpr (.inl ⟨v, hv, rfl⟩)
    · obtain ⟨h1, h2, h3⟩ := H.defs h
      exact ⟨h1, hle.constants h2, hle.defeqs h3⟩
  · obtain ⟨h1, h2⟩ := H.recursors h
    exact ⟨h1, h2.mono hle hext⟩
  · obtain ⟨hq, h2, h3, h4, h5, h6, h7⟩ := H.quot h
    have hlift : ∀ ci ∈ cis, ci.name ≠ ``Quot.lift := hold _ ⟨_, hq.lift⟩
    have hind : ∀ ci ∈ cis, ci.name ≠ ``Quot.ind := hold _ ⟨_, hq.ind⟩
    refine ⟨hq.mono hle, h2, h3, ?_, h5, ?_, h7⟩
    · cases hd : (T.addDefs cis).defs ``Quot.lift with
      | none => rfl
      | some v =>
        rcases (Tables.addDefs_defs hnd).mp hd with ⟨hv, hvn⟩ | ⟨_, h⟩
        · exact absurd hvn (hlift v hv)
        · rw [h4] at h; cases h
    · cases hd : (T.addDefs cis).defs ``Quot.ind with
      | none => rfl
      | some v =>
        rcases (Tables.addDefs_defs hnd).mp hd with ⟨hv, hvn⟩ | ⟨_, h⟩
        · exact absurd hvn (hind v hv)
        · rw [h6] at h; cases h
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
    rcases (Tables.addDefs_defs hnd).mp hv with ⟨hmem, rfl⟩ | ⟨_, h⟩
    · change T.recursors v.name = none
      cases hn : T.recursors v.name with
      | none => rfl
      | some data => exact absurd rfl (hold _ (H.recursors_const (by simp [hn])) v hmem)
    · exact H.defs_recursors (by simp [h])
  · apply H.views.addRules hle
    intro df hdf
    rcases addDefEqs_defeqs.mp hdf with ⟨ci, hci, rfl⟩ | hdf
    · exact .inr ⟨ci.name, _, rfl, hfresh ci hci⟩
    · exact .inl (by rwa [addConsts_defeqs hadd] at hdf)
  · rcases addDefEqs_defeqs.mp h with ⟨ci, hci, rfl⟩ | hdf
    · exact .inl ⟨ci, (Tables.addDefs_defs hnd).mpr (.inl ⟨hci, rfl⟩), rfl⟩
    · rw [addConsts_defeqs hadd] at hdf
      rcases H.equations hdf with ⟨v, hv, rfl⟩ | h | h
      · exact .inl ⟨v, hext.defs hv, rfl⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  · rw [VEnv.addDefEqs_projections, VEnv.addConsts_projections hadd] at h
    exact H.projections h

/-! ## The quotient -/

/-- Boolean constant occurrence, for concrete terms. -/
def mentionsB (X : Name) : VExpr → Bool
  | .const n _ => n == X
  | .app f a | .lam f a | .forallE f a => mentionsB X f || mentionsB X a
  | .proj _ _ e => mentionsB X e
  | _ => false

theorem Mentions.of_mentionsB {e : VExpr} (h : mentionsB X e = true) : Mentions X e := by
  induction e with
  | const n _ =>
    simp only [mentionsB, beq_iff_eq] at h
    exact h
  | app _ _ ih₁ ih₂ | lam _ _ ih₁ ih₂ | forallE _ _ ih₁ ih₂ =>
    simp only [mentionsB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl (ih₁ h)
    · exact Or.inr (ih₂ h)
  | proj _ _ _ ih => exact ih h
  | _ => simp [mentionsB] at h

theorem addQuot_parts (h : env.addQuot = some env') :
    env ≤ env' ∧ (∀ df, env'.defeqs df ↔ df = quotDefEq ∨ env.defeqs df) ∧
    env'.projections = env.projections ∧
    env.constants ``Quot = none ∧ env.constants ``Quot.mk = none ∧
    env.constants ``Quot.lift = none ∧ env.constants ``Quot.ind = none := by
  have h' := h
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h'
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h'
  have l1 := VEnv.addConst_le ha
  have l2 := VEnv.addConst_le hb
  have l3 := VEnv.addConst_le hc
  have l4 := VEnv.addConst_le hd
  refine ⟨l1.trans <| l2.trans <| l3.trans <| l4.trans VEnv.addDefEq_le, fun df => ?_, ?_,
    VEnv.addConst_fresh ha, VEnv.LE.constants_eq_none_left l1 (VEnv.addConst_fresh hb),
    VEnv.LE.constants_eq_none_left (l1.trans l2) (VEnv.addConst_fresh hc),
    VEnv.LE.constants_eq_none_left (l1.trans (l2.trans l3)) (VEnv.addConst_fresh hd)⟩
  · simp only [VEnv.addDefEq]
    rw [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc, VEnv.addConst_defeqs hb,
      VEnv.addConst_defeqs ha]
  · change d.projections = env.projections
    rw [VEnv.addConst_projections hd, VEnv.addConst_projections hc,
      VEnv.addConst_projections hb, VEnv.addConst_projections ha]

def quotFams (n : Name) : Option FamData := if n = ``Quot then some quotFam else none
def quotCtors (n : Name) : Option CtorData := if n = ``Quot.mk then some quotCtor else none

/-- Record the quotient. -/
def Tables.addQuot (T : Tables) : Tables :=
  { T.addViews quotFams quotCtors with quot := true }

theorem Tables.Inv.addQuot (H : T.Inv env) (henv : env.WF) (henv' : env'.WF)
    (h : env.addQuot = some env') : T.addQuot.Inv env' := by
  obtain ⟨hle, hdfIff, hproj, fQ, fM, fL, fI⟩ := addQuot_parts h
  have hfreshT : ∀ n, env.constants n = none →
      T.fam n = none ∧ T.ctor n = none ∧ T.defs n = none ∧ T.recursors n = none := by
    intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hx : T.fam n with
      | none => rfl
      | some _ => obtain ⟨_, hc⟩ := H.fam_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc
    · cases hx : T.ctor n with
      | none => rfl
      | some _ => obtain ⟨_, hc⟩ := H.ctor_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc
    · cases hx : T.defs n with
      | none => rfl
      | some _ => obtain ⟨_, hc⟩ := H.defs_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc
    · cases hx : T.recursors n with
      | none => rfl
      | some _ => obtain ⟨_, hc⟩ := H.recursors_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc
  have hquotT : T.quot = false := by
    cases hq : T.quot with
    | false => rfl
    | true =>
      have := (H.quot hq).1.quot
      rw [fQ] at this
      cases this
  have hext : T.Extends T.addQuot := ⟨id, id, fun _ => rfl, addView_of_old, addView_of_old⟩
  have hQI : QuotInstalled env' := ⟨addQuot_quot h, addQuot_quotMk h, addQuot_quotLift h,
    addQuot_quotInd h, addQuot_defeq h⟩
  have hrigidNew : ∀ n, env.constants n = none → n ≠ ``Quot.lift → env'.Rigid n := by
    intro n hn hne df hdf ls hhead
    rcases (hdfIff df).mp hdf with rfl | hold
    · apply hne
      have : quotDefEq.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift
          [VLevel.param 0, VLevel.param 1] := rfl
      rw [this] at hhead
      exact (VExpr.const.inj hhead).1.symm
    · exact henv.ordered.rigid_of_absent hn df hold ls hhead
  have hmk : Mentions ``Quot.mk quotDefEq.lhs := Mentions.of_mentionsB (by decide)
  have hQmk : Mentions ``Quot quotMkConst.type := Mentions.of_mentionsB (by decide)
  have hok : NewViewsWF env' T.fam T.ctor quotFams quotCtors := by
    refine ⟨fun {n d} hn => ?_, fun {n k} hn => ?_⟩
    · simp only [quotFams] at hn
      split at hn <;> cases hn
      rename_i hq; subst hq
      obtain ⟨h1, h2, _, _⟩ := hfreshT _ fQ
      refine ⟨h1, h2, by simp [quotCtors], ?_, by simp [quotFam],
        fun c hc => ?_, hrigidNew _ fQ (by decide), ?_⟩
      · obtain ⟨u, hu⟩ := henv'.ordered.constWF (addQuot_quot h)
        refine ⟨quotConst, addQuot_quot h, rfl,
          [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))],
          VExpr.sort (.param 0), _, hu, rfl, ?_⟩
        exact VEnv.HasType.sort (by simp [VLevel.WF, quotFam])
      · simp only [quotFam, List.mem_singleton] at hc
        subst hc
        exact ⟨quotCtor, by simp [quotCtors], rfl, rfl, rfl⟩
      · exact .inr <| .inl ⟨quotDefEq, ``Quot.mk, quotMkConst, hQI.equation, hmk,
          addQuot_quotMk h, hQmk⟩
    · simp only [quotCtors] at hn
      split at hn <;> cases hn
      rename_i hq; subst hq
      obtain ⟨h1, h2, _, _⟩ := hfreshT _ fM
      refine ⟨h1, h2, by simp [quotFams], ?_, ⟨quotFam, by simp [quotFams, quotCtor], ?_⟩,
        hrigidNew _ fM (by decide), .inl ⟨quotDefEq, hQI.equation, hmk⟩⟩
      · exact ⟨quotMkConst,
          [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1],
          [], addQuot_quotMk h, rfl, rfl, rfl⟩
      · simp [quotFam]
  have hviews : ViewInv env' T.fam T.ctor := H.views.addRules hle fun df hdf => by
    rcases (hdfIff df).mp hdf with rfl | hold
    · exact .inr ⟨``Quot.lift, _, rfl, fL⟩
    · exact .inl hold
  refine ⟨fun {n v} hv => ?_, fun {n data} hd => ?_, fun _ => ?_, H.defs_recursors,
    hviews.addViews hok, fun {df} hdf => ?_, fun {s info} hp => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := H.defs hv
    exact ⟨h1, hle.constants h2, hle.defeqs h3⟩
  · obtain ⟨h1, h2⟩ := H.recursors hd
    exact ⟨h1, h2.mono hle hext⟩
  · obtain ⟨_, _, h3, h4⟩ := hfreshT _ fL
    obtain ⟨_, _, h3', h4'⟩ := hfreshT _ fI
    obtain ⟨h1, _⟩ := hfreshT _ fQ
    obtain ⟨_, h2, _⟩ := hfreshT _ fM
    refine ⟨hQI, addView_some.mpr (.inr ⟨h1, by simp [quotFams]⟩),
      addView_some.mpr (.inr ⟨h2, by simp [quotCtors]⟩), h3, h4, h3', h4'⟩
  · rcases (hdfIff df).mp hdf with rfl | hold
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · rcases H.equations hold with ⟨v, hv, rfl⟩ | ⟨hq, _⟩ | h
      · exact .inl ⟨v, hv, rfl⟩
      · rw [hquotT] at hq; cases hq
      · exact .inr (.inr h)
  · rw [hproj] at hp
    obtain ⟨h1, h2⟩ := H.projections hp
    exact ⟨addView_of_old h1, addView_of_old h2⟩

/-! ## Block installation -/

def selCtors (t : VInductiveType) : Bool := !t.ctors.isEmpty

theorem selCtors_iff {t : VInductiveType} : selCtors t = true ↔ t.ctors ≠ [] := by
  simp [selCtors]

/-- Record a block installation: the views of the families with constructors and the recursor
entries. -/
def Tables.addRecursor (T : Tables) (decl : VInductDecl) (entries : List RecursorData) :
    Tables :=
  { T.addViews (viewFams decl selCtors) (viewCtors decl selCtors) with
    recursors := RecursorData.installEntries T.recursors entries }

theorem Tables.Inv.freshT (H : T.Inv env) (hn : env.constants n = none) :
    T.fam n = none ∧ T.ctor n = none ∧ T.defs n = none ∧ T.recursors n = none := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hx : T.fam n with
    | none => rfl
    | some _ => obtain ⟨_, hc⟩ := H.fam_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc
  · cases hx : T.ctor n with
    | none => rfl
    | some _ => obtain ⟨_, hc⟩ := H.ctor_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc
  · cases hx : T.defs n with
    | none => rfl
    | some _ => obtain ⟨_, hc⟩ := H.defs_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc
  · cases hx : T.recursors n with
    | none => rfl
    | some _ => obtain ⟨_, hc⟩ := H.recursors_const (n := n) (by simp [hx]); rw [hn] at hc; cases hc

theorem installEntries_old {old : Name → Option RecursorData}
    {entries : List RecursorData} (h : ∀ data ∈ entries, data.name ≠ n) :
    RecursorData.installEntries old entries n = old n := by
  unfold RecursorData.installEntries
  rw [find?_name_none (f := fun d : RecursorData => d.name) h]
  rfl

theorem installEntries_some {old : Name → Option RecursorData}
    {entries : List RecursorData}
    (h : RecursorData.installEntries old entries n = some data) :
    (data ∈ entries ∧ data.name = n) ∨ ((∀ d ∈ entries, d.name ≠ n) ∧ old n = some data) := by
  unfold RecursorData.installEntries at h
  cases hf : entries.find? (fun d => d.name == n) with
  | some d =>
    rw [hf] at h
    cases h
    exact .inl (find?_name_some (f := fun d : RecursorData => d.name) hf)
  | none =>
    rw [hf] at h
    refine .inr ⟨fun d hd hn => ?_, h⟩
    have := List.find?_eq_none.mp hf d hd
    simp [hn] at this

/-- Block installation with the chosen compilation data (`Tables.Inv.install` chooses it). -/
theorem Tables.Inv.install {decl : VInductDecl} {block : VInductBlock}
    (H : T.Inv env) (henv : env.WF)
    (hcomp : decl.CompilesTo env block) (hblock : VInductBlock.WF env block)
    (hinstall : block.install env = some env')
    {cbase : VEnv} {expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {aux : List ContainerSpecialization} (hcle : cbase ≤ env)
    (hdata : CompilationData cbase decl expanded s g aux block)
    (hprior : ContainersInstalled cbase aux) :
    T.Extends (T.addRecursor decl (RecursorData.compilationEntries default decl s aux g)) ∧
      (T.addRecursor decl (RecursorData.compilationEntries default decl s aux g)).Inv env' := by
  let entries := RecursorData.compilationEntries default decl s aux g
  let T' := T.addRecursor decl entries
  have hle := VInductBlock.install_base_le hinstall
  obtain ⟨envTypes, envCtors, envRecs, htypes, hctors, hrecs, hinst⟩ := install_parts hinstall
  have hfreshAll : ∀ v ∈ block.types ++ block.ctors ++ block.recursors,
      env.constants v.name = none := by
    intro v hv
    simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact VEnv.addConstVals_names_fresh htypes v hv
    · exact VEnv.LE.constants_eq_none_left (VEnv.addConstVals_le htypes)
        (VEnv.addConstVals_names_fresh hctors v hv)
    · exact VEnv.LE.constants_eq_none_left ((VEnv.addConstVals_le htypes).trans
        ((VEnv.addConstVals_le hctors).trans VEnv.addEliminators_addProjections_le))
        (VEnv.addConstVals_names_fresh hrecs v hv)
  have hnd := hdata.sourceWF.2.1
  have htypesEq := hdata.types
  have hctorsEq := hdata.ctors
  have hnames := hdata.names
  have htypeMem : ∀ t ∈ decl.types, t.toVConstVal ∈ block.types := fun t ht => by
    rw [htypesEq]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have hctorMem : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c ∈ block.ctors := fun t ht c hc => by
    rw [hctorsEq]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩
  have hfreshType : ∀ t ∈ decl.types, env.constants t.name = none := fun t ht =>
    hfreshAll t.toVConstVal (by simp [htypeMem t ht])
  have hfreshCtor : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env.constants c.name = none :=
    fun t ht c hc => hfreshAll c (by simp [hctorMem t ht c hc])
  have hentryFresh : ∀ data ∈ entries, env.constants data.name = none := fun data hd =>
    hdata.recursorEntries_fresh hinstall hd
  have hentryNe : ∀ n, (∃ ci, env.constants n = some ci) → ∀ data ∈ entries, data.name ≠ n := by
    rintro n ⟨ci, hci⟩ data hd rfl
    rw [hentryFresh data hd] at hci
    cases hci
  have hext : T.Extends T' := by
    refine ⟨id, fun {n d} h => ?_, id, addView_of_old, addView_of_old⟩
    change RecursorData.installEntries T.recursors entries n = some d
    rw [installEntries_old (hentryNe n (H.recursors_const (by simp [h])))]
    exact h
  have hTypeConst : ∀ t ∈ decl.types, env'.constants t.name = some t.toVConstant := by
    intro t ht
    rw [hinst]
    simp only [VEnv.addDefEqRules_constants]
    exact (VEnv.addConstVals_le hrecs).constants (VEnv.addEliminators_addProjections_le.constants
      ((VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes (htypeMem t ht))))
  have hCtorConst : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env'.constants c.name = some c.toVConstant :=
    fun t ht c hc => VInductBlock.install_ctor_lookup hinstall (hctorMem t ht c hc)
  have hruleHead : ∀ df ∈ block.rules, ∃ h ls, df.lhs.stripLams.getAppFnArgs.1 = .const h ls ∧
      h ∈ block.recursors.map (·.name) := by
    intro df hdf
    obtain ⟨r, hr, ls, hh⟩ := hcomp.equation_head_owned df hdf
    exact ⟨r.name, ls, hh, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hnotRec : ∀ n ∈ block.types.map (·.name) ++ block.ctors.map (·.name),
      n ∉ block.recursors.map (·.name) := by
    intro n hn hr
    simp only [List.map_append, List.nodup_append] at hnames
    rcases List.mem_append.mp hn with hn | hn
    · exact hnames.2.2 _ (List.mem_append_left _ hn) _ hr rfl
    · exact hnames.2.2 _ (List.mem_append_right _ hn) _ hr rfl
  have hrigidNew : ∀ n, env.constants n = none →
      n ∈ block.types.map (·.name) ++ block.ctors.map (·.name) → env'.Rigid n := by
    intro n hn hmem df hdf ls hhead
    rcases (install_defeqs hinstall).mp hdf with hnew | hold
    · obtain ⟨h, ls', hh, hrec⟩ := hruleHead df hnew
      rw [hhead] at hh
      cases hh
      exact hnotRec _ hmem hrec
    · exact henv.ordered.rigid_of_absent hn df hold ls hhead
  obtain ⟨params, _, _, hTypeShape, _, hraw⟩ := hdata.sourceParameters
  have hTypeUv := hdata.sourceWF.2.2.1
  have hCtorUv := hdata.sourceWF.2.2.2.1
  have hctorUv : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.uvars = decl.uvars := fun t ht c hc =>
    hCtorUv c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)
  have hcbase : cbase ≤ env' := hcle.trans hle
  -- equations of the installed environment
  have hviews0 : ViewInv env' T.fam T.ctor := H.views.addRules hle fun df hdf => by
    rcases (install_defeqs hinstall).mp hdf with hnew | hold
    · obtain ⟨h, ls, hh, hrec⟩ := hruleHead df hnew
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrec
      exact .inr ⟨r.name, ls, hh, hfreshAll r (by simp [hr])⟩
    · exact .inl hold
  have hctorMention : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
      ∃ df, env'.defeqs df ∧ Mentions c.name df.lhs := by
    intro t ht c hc
    obtain ⟨equation, hmem, fn, levels, args, hmaj⟩ :=
      hdata.constructor_equation (List.mem_flatMap.mpr ⟨t, ht, hc⟩)
    refine ⟨equation, (install_defeqs hinstall).mpr (.inl hmem), ?_⟩
    apply Mentions.of_stripLams
    rw [hmaj]
    exact Or.inr Mentions.mkApps_head
  have hctorWitness : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, MetadataMentions env' c.name :=
    fun t ht c hc => .inl (hctorMention t ht c hc)
  have hok : NewViewsWF env' T.fam T.ctor (viewFams decl selCtors) (viewCtors decl selCtors) := by
    apply newViewsWF_decl hnd
    · intro t ht _
      obtain ⟨h1, h2, _⟩ := H.freshT (hfreshType t ht)
      exact ⟨h1, h2, fun c hc => by
        obtain ⟨h1, h2, _⟩ := H.freshT (hfreshCtor t ht c hc)
        exact ⟨h1, h2⟩⟩
    · intro t ht _
      exact famShape_of_typeShape ((hTypeShape t ht).mono hcbase) (hTypeUv t ht) (hTypeConst t ht)
    · intro t ht _ c hc
      exact ⟨hCtorConst t ht c hc, hraw t ht c hc, hctorUv t ht c hc⟩
    · intro t ht _
      refine ⟨hrigidNew _ (hfreshType t ht) (List.mem_append_left _ ?_), fun c hc =>
        hrigidNew _ (hfreshCtor t ht c hc) (List.mem_append_right _ ?_)⟩
      · exact List.mem_map.mpr ⟨_, htypeMem t ht, rfl⟩
      · exact List.mem_map.mpr ⟨_, hctorMem t ht c hc, rfl⟩
    · intro t ht hsel
      refine ⟨?_, hctorWitness t ht⟩
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (selCtors_iff.mp hsel)
      obtain ⟨ls, hres⟩ := hcomp.ctor_result t ht c hc
      obtain ⟨df, hdf, hm⟩ := hctorMention t ht c hc
      exact .inr <| .inl ⟨df, c.name, _, hdf, hm, hCtorConst t ht c hc,
        Mentions.of_forallResult hres⟩
  have hfamT' : ∀ t ∈ decl.types, t.ctors ≠ [] → T'.fam t.name = some (famView decl t) :=
    fun t ht hne => addView_some.mpr (.inr ⟨(H.freshT (hfreshType t ht)).1,
      viewFams_mem hnd ht (selCtors_iff.mpr hne)⟩)
  have hnewEvidence : ∀ data ∈ entries, RecursorEntryCompiled env' T' data := by
    intro data hd
    obtain ⟨owner, _, rfl⟩ := List.mem_map.mp hd
    have hinstance : (RecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux)
        g owner).recursorInstance = g := by
      cases g with
      | mk U levels target names =>
        change Instance.mk U levels target (fun owner => s.families[owner].name.str "rec") =
          Instance.mk U levels target names
        congr 1
        exact funext fun owner => (hdata.recursorNames owner).symm
    refine ⟨cbase, env, decl, expanded, aux, block, env', ?_, hprior, hcle, rfl, rfl, hinstall,
      .rfl, henv, hblock, hfamT'⟩
    rw [hinstance]
    exact hdata
  refine ⟨hext, fun {n v} hv => ?_, fun {n data} hd => ?_, fun hq => ?_, fun {n} hn => ?_,
    hviews0.addViews hok, fun {df} hdf => ?_, fun {s' info} hp => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := H.defs hv
    exact ⟨h1, hle.constants h2, hle.defeqs h3⟩
  · rcases installEntries_some hd with ⟨hmem, rfl⟩ | ⟨_, hold⟩
    · exact ⟨rfl, hnewEvidence data hmem⟩
    · obtain ⟨h1, h2⟩ := H.recursors hold
      exact ⟨h1, h2.mono hle hext⟩
  · obtain ⟨hQI, h2, h3, h4, h5, h6, h7⟩ := H.quot hq
    refine ⟨hQI.mono hle, addView_of_old h2, addView_of_old h3, h4, ?_, h6, ?_⟩
    · change RecursorData.installEntries T.recursors entries _ = none
      rw [installEntries_old (hentryNe _ ⟨_, hQI.lift⟩)]; exact h5
    · change RecursorData.installEntries T.recursors entries _ = none
      rw [installEntries_old (hentryNe _ ⟨_, hQI.ind⟩)]; exact h7
  · change RecursorData.installEntries T.recursors entries n = none
    rw [installEntries_old (hentryNe _ (H.defs_const hn))]
    exact H.defs_recursors hn
  · rcases (install_defeqs hinstall).mp hdf with hnew | hold
    · obtain ⟨data, hmem, index, howner, hgen⟩ := hdata.recursorEntries_equation hnew default
      exact .inr (.inr ⟨data, hdata.recursorEntries_lookup hmem, index, howner, hgen⟩)
    · rcases H.equations hold with ⟨v, hv, rfl⟩ | h | ⟨data, hd, rest⟩
      · exact .inl ⟨v, hv, rfl⟩
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨data, hext.recursors hd, rest⟩)
  · rcases (install_projections hinstall).mp hp with ⟨entry, hentry, rfl, rfl⟩ | hold
    · rw [hdata.projections] at hentry
      obtain ⟨t, ht, c, hctors1, rfl⟩ := VInductDecl.projectionEntries_origin hentry
      have hne : t.ctors ≠ [] := by simp [hctors1]
      refine ⟨?_, ?_⟩
      · rw [hfamT' t ht hne]
        simp [famView, projFam, hctors1]
      · have hc : c ∈ t.ctors := by simp [hctors1]
        refine addView_some.mpr (.inr ⟨(H.freshT (hfreshCtor t ht c hc)).2.1, ?_⟩)
        rw [viewCtors_mem ht (selCtors_iff.mpr hne) hc
          (ctorView_unique (fun t ht _ c hc => ⟨hCtorConst t ht c hc, hraw t ht c hc,
            hctorUv t ht c hc⟩) t ht (selCtors_iff.mpr hne) c hc)]
        rfl
    · obtain ⟨h1, h2⟩ := H.projections hold
      exact ⟨addView_of_old h1, addView_of_old h2⟩

end Lean4Lean.EnvTables
