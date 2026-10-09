import Lean4Lean.Theory.Typing.EnvTables.Arity

/-!
# Container constructors are recorded with their container's parameter count

A nested compilation specializes earlier *containers* (`ContainersInstalled`). The
certification is existential: it exhibits some finite compilation of the container installed
below the current environment, not necessarily the one of the actual history. This file shows
that the tables nevertheless record each container constructor with the container's own
parameter count: the container's equation for the constructor is an installed equation, and its
syntax pins down the actual recursor, its family, and its parameter count.
-/

namespace Lean4Lean.EnvTables
open _root_.Lean4Lean.EnvTables.VEnv InductiveSignature

/-! ## Variables -/

theorem mem_vars {i count below : Nat} :
    VExpr.bvar i ∈ vars count below ↔ below ≤ i ∧ i < below + count := by
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range, VExpr.bvar.injEq]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro h; exact ⟨i - below, by omega, by omega⟩

/-- The parameter/field split of `vars p (e + f) ++ vars f 0` is determined when `e ≥ 1`. -/
theorem vars_split_inj {p e f p' e' f' : Nat} (he : 1 ≤ e) (he' : 1 ≤ e')
    (h : vars p (e + f) ++ vars f 0 = vars p' (e' + f') ++ vars f' 0) : p = p' ∧ f = f' := by
  have hmem : ∀ i, (e + f ≤ i ∧ i < e + f + p ∨ 0 ≤ i ∧ i < 0 + f) ↔
      (e' + f' ≤ i ∧ i < e' + f' + p' ∨ 0 ≤ i ∧ i < 0 + f') := by
    intro i
    have := congrArg (VExpr.bvar i ∈ ·) h
    simpa only [List.mem_append, mem_vars, eq_iff_iff] using this
  have hf : f = f' := by
    rcases Nat.lt_trichotomy f f' with hlt | heq | hgt
    · have := (hmem f).mpr (.inr ⟨by omega, by omega⟩)
      rcases this with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    · exact heq
    · have := (hmem f').mp (.inr ⟨by omega, by omega⟩)
      rcases this with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hlen := congrArg List.length h
  simp only [List.length_append, InductiveSignature.length_vars] at hlen
  exact ⟨by omega, hf⟩

/-! ## Positional correspondence -/

theorem declaration_types_getElem (s : InductiveSignature) (o : Fin s.families.size) :
    s.declaration.types[o.val]'(by simp [declaration]) = s.declarationFamily o := by
  simp [declaration, declarationFamily]

theorem declaration_types_length (s : InductiveSignature) :
    s.declaration.types.length = s.families.size := by simp [declaration]

/-- Each family slot corresponds to its source family or auxiliary family. -/
theorem CaseCompilationData.family_slot {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (o : Fin s.families.size) :
    ∃ envTypes direct, base.addConstVals src.typeConstants = some envTypes ∧
      aux.mapM (fun a => a.specializedFamily src.uvars s.params) = some direct ∧
      ∃ h : o.val < (src.types ++ direct).length,
        RestoresFamily (compilationRestoration src aux) envTypes src.uvars
          (s.declarationFamily o) ((src.types ++ direct)[o.val]) := by
  obtain ⟨envTypes, direct, hT, hdirect, _, hfamilies⟩ := hdata.correspondence
  obtain ⟨h2, hr⟩ := List.forall₂_getElem_exists hfamilies o.val (by simp [declaration])
  refine ⟨envTypes, direct, hT, hdirect, h2, ?_⟩
  rw [← declaration_types_getElem]
  exact hr

/-! ## Recursor names -/

theorem appendIndexAfter_rec_inj {n q : Name} {i : Nat}
    (h : (n.str "rec").appendIndexAfter i = q.str "rec") : n = q := by
  simp [Lean.Name.appendIndexAfter, Lean.Name.modifyBase, Lean.Name.hasMacroScopes] at h
  exact h.1

theorem compilationRestoration_recursors_mem {src : VInductDecl}
    {aux : List ContainerSpecialization} (hp : pair ∈ (compilationRestoration src aux).recursors) :
    ∃ a ∈ aux, ∃ k, pair = (a.auxiliary.str "rec",
      (((src.types.head?).map (fun t : VInductiveType => t.name)).getD default).str "rec"
        |>.appendIndexAfter k) := by
  simp only [compilationRestoration, List.mem_map] at hp
  obtain ⟨⟨a, i⟩, hai, rfl⟩ := hp
  exact ⟨a, List.fst_mem_of_mem_zipIdx hai, i + 1, rfl⟩

/-- A source family keeps its recursor name. -/
theorem CaseCompilationData.source_recursorName {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    {F : VInductiveType} (hF : F ∈ src.types) :
    (compilationRestoration src aux).recursorName (F.name.str "rec") = F.name.str "rec" := by
  unfold Restoration.recursorName
  cases hf : (compilationRestoration src aux).recursors.find? (fun p => p.1 == F.name.str "rec") with
  | none => rfl
  | some pair =>
    have hm := List.mem_of_find?_eq_some hf
    have hn : pair.1 = F.name.str "rec" := by simpa using List.find?_some hf
    obtain ⟨a, ha, k, rfl⟩ := compilationRestoration_recursors_mem hm
    have haux : a.auxiliary = F.name := by simpa using hn
    exfalso
    exact hdata.source_head_disjoint
      (List.mem_flatMap.mpr ⟨F, hF, List.mem_cons_self⟩)
      (List.mem_map.mpr ⟨_, List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩, haux⟩)

/-- An auxiliary family's recursor is renamed after the first source family. -/
theorem CaseCompilationData.auxiliary_recursorName {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (o : Fin s.families.size) (ho : src.types.length ≤ o.val) :
    ∃ k, (compilationRestoration src aux).recursorName (s.families[o].name.str "rec") =
      ((((src.types.head?).map (fun t : VInductiveType => t.name)).getD default).str "rec"
        |>.appendIndexAfter k) := by
  obtain ⟨envTypes, direct, _, hdirect, hlt, hrel⟩ := CaseCompilationData.family_slot hdata o
  have hname : s.families[o].name = (src.types ++ direct)[o.val].name := hrel.name
  rw [List.getElem_append_right ho] at hname
  have hrel' := List.mapM_eq_some.mp hdirect
  have hlen := Lean4Lean.List.Forall₂.length_eq hrel'
  obtain ⟨hlt', hdf⟩ := List.forall₂_getElem_exists hrel' (o.val - src.types.length)
    (by simp at hlt; omega)
  rw [ContainerSpecialization.directFamily_name hdf] at hname
  have hj : o.val - src.types.length < aux.zipIdx.length := by simp; omega
  have hkey := List.getElem_mem (l := aux.zipIdx) hj
  have hkey' : ((aux.zipIdx[o.val - src.types.length]).1.auxiliary.str "rec",
      ((((src.types.head?).map (fun t : VInductiveType => t.name)).getD default).str "rec"
        |>.appendIndexAfter ((aux.zipIdx[o.val - src.types.length]).2 + 1))) ∈
      (compilationRestoration src aux).recursors :=
    List.mem_map.mpr ⟨_, hkey, rfl⟩
  have h1 : (aux.zipIdx[o.val - src.types.length]).1 = aux[o.val - src.types.length] := by
    simp [List.getElem_zipIdx]
  rw [h1, ← hname] at hkey'
  unfold Restoration.recursorName
  cases hf : (compilationRestoration src aux).recursors.find?
      (fun p => p.1 == s.families[o].name.str "rec") with
  | none =>
    have := List.find?_eq_none.mp hf _ hkey'
    simp at this
  | some pair =>
    obtain ⟨a, _, k, rfl⟩ := compilationRestoration_recursors_mem (List.mem_of_find?_eq_some hf)
    exact ⟨k, rfl⟩

/-! ## Syntax helpers -/

/-- The left body of a rule shape, with its outer lambdas removed. -/
theorem ruleBody_stripLams {Ds : List VExpr} {h : Name} {ls : List VLevel} {xs : List VExpr}
    {m : VExpr} :
    (VExpr.wrapLams Ds (VExpr.mkApps (.const h ls) (xs ++ [m]))).stripLams =
      .app (VExpr.mkApps (.const h ls) xs) m := by
  rw [VExpr.stripLams_wrapLams, VExpr.mkApps_snoc]; rfl

theorem ruleBody_inj {Ds Ds' : List VExpr} {h h' : Name} {ls ls' : List VLevel}
    {xs xs' : List VExpr} {m m' : VExpr}
    (heq : VExpr.wrapLams Ds (VExpr.mkApps (.const h ls) (xs ++ [m])) =
      VExpr.wrapLams Ds' (VExpr.mkApps (.const h' ls') (xs' ++ [m']))) :
    VExpr.mkApps (.const h ls) xs = VExpr.mkApps (.const h' ls') xs' ∧ m = m' := by
  have := congrArg VExpr.stripLams heq
  rw [ruleBody_stripLams, ruleBody_stripLams] at this
  exact VExpr.app.inj this

theorem mkApps_const_inj {h h' : Name} {ls ls' : List VLevel} {xs xs' : List VExpr}
    (heq : VExpr.mkApps (.const h ls) xs = VExpr.mkApps (.const h' ls') xs') :
    h = h' ∧ ls = ls' ∧ xs = xs' := by
  have h1 := congrArg VExpr.getAppFnArgs heq
  rw [spine_mkApps_exact _ _ rfl, spine_mkApps_exact _ _ rfl] at h1
  simp only [Prod.mk.injEq, VExpr.const.injEq] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

/-- A certified container was compiled and installed below the environment. -/
theorem ContainersInstalled.member {env : VEnv} {aux : List ContainerSpecialization}
    (H : ContainersInstalled env aux) {a : ContainerSpecialization} (ha : a ∈ aux) :
    ∃ base block installed, CompiledInductive base a.container block ∧
      block.install base = some installed ∧ installed ≤ env := by
  exact ContainersInstalled.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun env aux _ => ∀ a ∈ aux, ∃ base block installed,
      CompiledInductive base a.container block ∧ block.install base = some installed ∧
        installed ≤ env)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) (by simp)
    (fun hcompile _ hinstall hle _ _ ih => by
      intro a' ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact ⟨_, _, _, hcompile, hinstall, hle⟩
      · exact ih a' ha')
    H a ha

/-- A source family slot: its name and constructors. -/
theorem CaseCompilationData.source_slot {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (o : Fin s.families.size) (ho : o.val < src.types.length) :
    s.families[o].name = src.types[o.val].name ∧
    (∀ c ∈ src.types[o.val].ctors, ∃ j : Fin s.constructors.size,
      s.constructors[j].owner = o ∧ s.constructors[j].name = c.name) ∧
    (∀ j : Fin s.constructors.size, s.constructors[j].owner = o →
      ∃ c ∈ src.types[o.val].ctors, c.name = s.constructors[j].name) := by
  obtain ⟨_, direct, _, _, hlt, hrel⟩ := CaseCompilationData.family_slot hdata o
  have hget : (src.types ++ direct)[o.val] = src.types[o.val] := List.getElem_append_left ho
  rw [hget] at hrel
  refine ⟨hrel.name, ?_, ?_⟩
  · intro c hc
    obtain ⟨nc, hnc, hname, _⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrel.constructors c hc
    simp only [declarationFamily, List.mem_filterMap] at hnc
    obtain ⟨ctor, hctor, hsel⟩ := hnc
    split at hsel
    · rename_i hown
      cases hsel
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hctor
      refine ⟨⟨j, by simpa using hj⟩, ?_, ?_⟩
      · apply Fin.ext
        simp only [Fin.getElem_fin]
        rw [show s.constructors[j] = ctor by simpa using hjeq]
        exact hown
      · simp only [Fin.getElem_fin]
        rw [show s.constructors[j] = ctor by simpa using hjeq]
        exact hname
    · cases hsel
  · intro j hj
    have hd := s.declarationCtor_family j
    rw [hj] at hd
    obtain ⟨c, hc, hname, _⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _ hd
    exact ⟨c, hc, hname.symm⟩

/-- The restored equation of a source constructor. -/
theorem CompilationData.source_rule {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CompilationData base src exp s g aux block)
    (j : Fin s.constructors.size) (ho : s.constructors[j].owner.val < src.types.length)
    {c : VConstVal} (hc : c ∈ src.types[s.constructors[j].owner.val].ctors)
    (hname : c.name = s.constructors[j].name) {df : VDefEq}
    (hrestore : (compilationRestoration src aux).equation (g.equation j) = some df) :
    ∃ Ds idx, df.lhs = VExpr.wrapLams Ds (VExpr.mkApps
      (.const ((src.types[s.constructors[j].owner.val]).name.str "rec") (VLevel.params g.uvars))
      (vars (s.params.length + (s.families.size + s.constructors.size))
        s.constructors[j].fields.length ++ idx ++
        [VExpr.mkApps (.const c.name g.levels)
          (vars s.params.length (s.families.size + s.constructors.size +
            s.constructors[j].fields.length) ++ vars s.constructors[j].fields.length 0)])) := by
  obtain ⟨Ds, idx, R, major, hlhs, _, _, _, _, hmaj⟩ := CompilationData.rule_shape hdata j hrestore
  have hF := List.getElem_mem (l := src.types) ho
  have hfam := (CaseCompilationData.source_slot hdata.toCaseCompilationData _ ho).1
  have hcn : c.name ∈ familyNames src.types :=
    List.mem_flatMap.mpr ⟨_, hF, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
  have hrec : (compilationRestoration src aux).recursorName
      (g.recursorName s.constructors[j].owner) =
      (src.types[s.constructors[j].owner.val]).name.str "rec" := by
    rw [hdata.recursorNames, hfam]
    exact CaseCompilationData.source_recursorName hdata.toCaseCompilationData hF
  rw [hrec] at hlhs
  rcases hmaj with ⟨hnone, rfl⟩ | ⟨spec, hspec, hsome, _, _⟩
  · have hhn := hdata.headName_source hcn
    unfold Restoration.headName at hhn
    rw [← hname] at hnone hlhs
    rw [hnone] at hhn
    simp only at hhn
    rw [hhn] at hlhs
    exact ⟨Ds, idx, hlhs⟩
  · exfalso
    have : spec.auxiliary = c.name := by
      rw [hname]; simpa using List.find?_some hsome
    exact hdata.source_head_disjoint hcn (List.mem_map.mpr ⟨spec, hspec, this⟩)

theorem head_of_ruleBody {Ds : List VExpr} {h : Name} {ls : List VLevel} {xs : List VExpr}
    {m : VExpr} {df : VDefEq}
    (hl : df.lhs = VExpr.wrapLams Ds (VExpr.mkApps (.const h ls) (xs ++ [m]))) :
    VDefEq.head df = .const h ls := by
  unfold VDefEq.head
  rw [hl, ruleBody_stripLams, ← VExpr.mkApps_snoc]
  exact VExpr.getAppFnArgs_mkApps_head _ _

theorem CaseCompilationData.families_size_ge {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block) :
    src.types.length ≤ s.families.size := by
  obtain ⟨_, _, _, _, _, hfamilies⟩ := hdata.correspondence
  have := Lean4Lean.List.Forall₂.length_eq hfamilies
  rw [declaration_types_length] at this
  rw [this]; simp

/-- Every constructor of a certified container is recorded with the container's own view. -/
theorem container_ctor {T : Tables} {env base : VEnv} {aux : List ContainerSpecialization}
    (HT : T.Inv env) (hprior : ContainersInstalled base aux) (hle : base ≤ env)
    {a : ContainerSpecialization} (ha : a ∈ aux) {c : VConstVal} (hc : c ∈ a.source.ctors) :
    T.ctor c.name = some (ctorView a.container a.source c) := by
  obtain ⟨base', block', inst', hcomp', hinst', hle'⟩ := ContainersInstalled.member hprior ha
  obtain ⟨b'', exp', s', g', aux', hb'', hdata', hprior'⟩ := hcomp'.exists_compilation
  have hfam_lt : a.family.val < s'.families.size :=
    Nat.lt_of_lt_of_le a.family.isLt (CaseCompilationData.families_size_ge hdata'.toCaseCompilationData)
  let o' : Fin s'.families.size := ⟨a.family.val, hfam_lt⟩
  have hsrc : a.container.types[o'.val] = a.source := rfl
  have hc' : c ∈ a.container.types[o'.val].ctors := by rw [hsrc]; exact hc
  obtain ⟨j, hjown, hjname⟩ := (CaseCompilationData.source_slot hdata'.toCaseCompilationData o' a.family.isLt).2.1 c hc'
  have hjlt : s'.constructors[j].owner.val < a.container.types.length := by
    rw [hjown]; exact a.family.isLt
  obtain ⟨ρ, hρmem, hρ⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata'.equations) (g'.equation j)
    (List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩)
  have hρenv : env.defeqs ρ :=
    (hle'.trans hle).defeqs (VInductBlock.install_rule hinst' hρmem)
  have hsrc' : a.container.types[s'.constructors[j].owner.val] = a.source := by
    simp only [hjown]; rfl
  have hcj : c ∈ a.container.types[s'.constructors[j].owner.val].ctors := by
    rw [hsrc']; exact hc
  obtain ⟨Ds, idx, hρlhs⟩ := CompilationData.source_rule hdata' j hjlt hcj hjname.symm hρ
  rw [hsrc'] at hρlhs
  have hhead := head_of_ruleBody hρlhs
  have hcconst : env.constants c.name = some c.toVConstant :=
    (hle'.trans hle).constants (VInductBlock.install_ctor_lookup hinst' (by
      rw [hcomp'.ctors_eq]; exact List.mem_flatMap.mpr ⟨a.source, List.getElem_mem _, hc⟩))
  have hcuv : c.uvars = a.container.uvars :=
    hdata'.sourceWF.2.2.2.1 c (List.mem_flatMap.mpr ⟨a.source, List.getElem_mem _, hc⟩)
  have hnp' : s'.params.length = a.container.nparams := by
    rw [hdata'.model.nparams, hdata'.nparams]
  rcases HT.equations hρenv with ⟨v, _, hv⟩ | ⟨_, hq⟩ | ⟨dX, hdX, iX, hiX, hgX⟩
  · exfalso
    have h1 := congrArg (fun df : VDefEq => df.lhs.stripLams) hv
    simp only [hρlhs, ruleBody_stripLams] at h1
    cases h1
  · exfalso
    rw [hq, quot_head] at hhead
    simp at hhead
  · obtain ⟨_, hevX⟩ := HT.recursors hdX
    have hX := recursor_head HT hdX hiX hgX
    rw [hhead] at hX
    have hnameX : a.source.name.str "rec" = dX.name := (VExpr.const.inj hX).1
    obtain ⟨bX, ibX, srcX, expX, auxX, blockX, instX, hdataX, _, _, hrX, _, _, _, _, _, hfamX⟩ := hevX
    have hgX' : (compilationRestoration srcX auxX).equation (dX.recursorInstance.equation iX) =
        some ρ := by
      simpa only [RecursorData.equation, hrX] using hgX
    have hdXname : dX.name = (compilationRestoration srcX auxX).recursorName
        (dX.schema.signature.families[dX.owner].name.str "rec") := by
      simp only [RecursorData.name, hrX]
    by_cases hoX : dX.owner.val < srcX.types.length
    · have hoX' : dX.schema.signature.constructors[iX].owner.val < srcX.types.length := by
        rw [hiX]; exact hoX
      obtain ⟨cX, hcX, hcXname⟩ :=
        (CaseCompilationData.source_slot hdataX.toCaseCompilationData dX.owner hoX).2.2 iX hiX
      have hcX' : cX ∈ srcX.types[dX.schema.signature.constructors[iX].owner.val].ctors := by
        simp only [hiX]; exact hcX
      obtain ⟨DsX, idxX, hXlhs⟩ := CompilationData.source_rule hdataX iX hoX' hcX' hcXname hgX'
      obtain ⟨hpre, hmaj⟩ := ruleBody_inj (hρlhs.symm.trans hXlhs)
      obtain ⟨hcn, _, hargs⟩ := mkApps_const_inj hmaj
      obtain ⟨hhn, _, _⟩ := mkApps_const_inj hpre
      have hFX : srcX.types[dX.schema.signature.constructors[iX].owner.val].name = a.source.name := by
        simpa using hhn.symm
      have he' : 1 ≤ s'.families.size + s'.constructors.size := by omega
      have heX : 1 ≤ dX.schema.signature.families.size + dX.schema.signature.constructors.size := by
        have := dX.owner.isLt; omega
      obtain ⟨hnp, _⟩ := vars_split_inj he' heX hargs
      have hne : srcX.types[dX.owner.val].ctors ≠ [] := List.ne_nil_of_mem hcX
      have hfam := hfamX _ (List.getElem_mem hoX) hne
      obtain ⟨_, _, hks⟩ := HT.views.fam hfam
      obtain ⟨k, hk, hkfam, hkuv, hknp⟩ :=
        hks cX.name (List.mem_map.mpr ⟨cX, hcX, rfl⟩)
      rw [← hcn] at hk
      rw [hk]
      obtain ⟨⟨ci, doms, indices, hci, hciuv, htype, hlen⟩, _⟩ := HT.views.ctor hk
      rw [hcconst] at hci
      cases hci
      have harity : c.type.forallArity = doms.length := by
        change c.toVConstant.type.forallArity = _
        rw [htype, VExpr.forallArity_wrapForalls,
          VExpr.forallArity_eq_zero_of_getAppFnArgs (VExpr.getAppFnArgs_mkApps_const _ _ _)]
        rfl
      have hnpX : dX.schema.signature.params.length = srcX.nparams := by
        rw [hdataX.model.nparams, hdataX.nparams]
      simp only [famView] at hkuv hknp
      obtain ⟨kf, ku, kp, kn⟩ := k
      simp only [ctorView, Option.some.injEq, CtorData.mk.injEq]
      simp only at hkfam hkuv hknp hciuv hlen
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hkfam]
        have : srcX.types[dX.owner.val] =
            srcX.types[dX.schema.signature.constructors[iX].owner.val] := by simp only [hiX]
        rw [this, hFX]
      · rw [← hciuv]; exact hcuv
      · omega
      · omega
    · exfalso
      obtain ⟨k, hk⟩ := CaseCompilationData.auxiliary_recursorName hdataX.toCaseCompilationData dX.owner (by omega)
      have hF0 := appendIndexAfter_rec_inj (hnameX.trans (hdXname.trans hk)).symm
      obtain ⟨t0, rest, hts⟩ := List.exists_cons_of_ne_nil hdataX.sourceWF.1
      have hsz := CaseCompilationData.families_size_ge hdataX.toCaseCompilationData
      have h0 : 0 < srcX.types.length := by rw [hts]; simp
      let o0 : Fin dX.schema.signature.families.size := ⟨0, by omega⟩
      have hname0 : (compilationRestoration srcX auxX).recursorName
          (dX.schema.signature.families[o0].name.str "rec") = a.source.name.str "rec" := by
        have hs := (CaseCompilationData.source_slot hdataX.toCaseCompilationData o0 h0).1
        rw [hs, CaseCompilationData.source_recursorName hdataX.toCaseCompilationData (List.getElem_mem h0)]
        simp only [hts, List.head?_cons, Option.map_some, Option.getD_some] at hF0
        simp [hts, hF0]
      have hnd := hdataX.recursorEntries_nodup (key := default)
      simp only [RecursorData.compilationEntries] at hnd
      have heq : (RecursorData.ofInstance default
            (CaseSchema.ofCompilation srcX dX.schema.signature auxX) dX.recursorInstance o0).name =
          (RecursorData.ofInstance default
            (CaseSchema.ofCompilation srcX dX.schema.signature auxX) dX.recursorInstance dX.owner).name := by
        change (compilationRestoration srcX auxX).recursorName
            (dX.schema.signature.families[o0].name.str "rec") =
          (compilationRestoration srcX auxX).recursorName
            (dX.schema.signature.families[dX.owner].name.str "rec")
        rw [hname0, ← hdXname, ← hnameX]
      have hsame := List.eq_of_mem_of_nodup_map hnd
        (List.mem_map_of_mem (List.mem_finRange o0)) (List.mem_map_of_mem (List.mem_finRange dX.owner))
        heq
      have := congrArg (fun d : RecursorData => d.owner.val) hsame
      simp [o0, RecursorData.ofInstance] at this
      omega

end Lean4Lean.EnvTables
