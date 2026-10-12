import Lean4Lean.Theory.Typing.Confluence.SingletonEquation
import Lean4Lean.Theory.Typing.Confluence.JoinTelescope

/-! # Alignment of a `Prop`-source singleton instance with its generic equation

A typed instance `rec A (c B)` of a registered ι rule of a large-eliminating singleton at a
`Prop` source joins the β-redex of the rule's generic equation at the recursor's parameters,
motives and minors and the major's fields (`singletonInstance_alignJ`). The joins of the index
arguments with the constructor's index expressions come from the joinable typing of the instance
(`HasTypeJ`): the major's type joins both the recursor's major domain and the constructor's
declared result, so injectivity of joins of rigid spines (`FullCRDefEq.rigid_spine_inv`) relates
their arguments. The constructor's declared (source) type is definitionally equal, in the
environment of the declaration's type formers, to the normalized constructor type the equation is
generated from (`RestoresFamily.constructors`); the alignment takes the joins of such
environment-level equalities as a hypothesis, supplied by the induction along the environment's
history. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

theorem FullCRDefEq.forall₂_refl (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {l : List VExpr}, (∀ a ∈ l, ∃ A, Γ ⊢ a : A) → List.Forall₂ (FullCRDefEq Γ) l l
  | [], _ => .nil
  | _ :: _, H =>
    let ⟨_, h⟩ := H _ (List.mem_cons_self ..)
    .cons (.refl hΓ h) (FullCRDefEq.forall₂_refl hΓ fun b hb => H b (List.mem_cons_of_mem _ hb))

theorem FullCRDefEq.forall₂_trans (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : List.Forall₂ (FullCRDefEq Γ) l₁ l₂) (H2 : List.Forall₂ (FullCRDefEq Γ) l₂ l₃) :
    List.Forall₂ (FullCRDefEq Γ) l₁ l₃ :=
  Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans hΓ h') H1 H2

theorem FullCRDefEq.forall₂_symm (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {l₁ l₂ : List VExpr}, List.Forall₂ (FullCRDefEq Γ) l₁ l₂ → List.Forall₂ (FullCRDefEq Γ) l₂ l₁
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.symm hΓ) (FullCRDefEq.forall₂_symm hΓ hs)

theorem FullCRDefEq.forall₂_defeq (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {l₁ l₂ : List VExpr}, List.Forall₂ (FullCRDefEq Γ) l₁ l₂ →
      List.Forall₂ (IsDefEqU env univs Γ) l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.defeq hΓ) (FullCRDefEq.forall₂_defeq hΓ hs)

omit [Params] in
theorem EqUpToLevels.instOuter_same {U : Nat} (H : EqUpToLevels U e e') :
    ∀ {args : List VExpr}, (∀ a ∈ args, EqUpToLevels U a a) →
      EqUpToLevels U (e.instOuter args) (e'.instOuter args)
  | [], _ => H
  | a :: as, h => by
    simp only [VExpr.instOuter_cons]
    exact EqUpToLevels.instOuter_same (EqUpToLevels.instN (h a (List.mem_cons_self ..)) H)
      fun b hb => h b (List.mem_cons_of_mem _ hb)

omit [Params] in
theorem List.forall₂_map_map {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | _ :: _, H => .cons (H _ (List.mem_cons_self ..))
    (List.forall₂_map_map fun b hb => H b (List.mem_cons_of_mem _ hb))

omit [Params] in
/-- A normalized constructor of a signature corresponds, through the empty restoration, to a
source constructor whose type is definitionally equal to the normalized constructor type. -/
theorem RestoresFamily.normalized_ctor {s : InductiveSignature} {envTypes : VEnv} {uvars : Nat}
    {sources : List VInductiveType}
    (H : List.Forall₂ (RestoresFamily {} envTypes uvars) s.declaration.types sources)
    {ctor : Constructor s.families.size} (hctor : ctor ∈ s.constructors.toList) :
    ∃ st ∈ sources, ∃ sc ∈ st.ctors, st.name = s.families[ctor.owner].name ∧
      sc.name = ctor.name ∧ envTypes.IsDefEqU uvars [] (s.constructorType ctor) sc.type := by
  have hnt : ∃ nt ∈ s.declaration.types, nt.name = s.families[ctor.owner].name ∧
      ({ name := ctor.name, uvars := s.uvars, type := s.constructorType ctor } : VConstVal) ∈ nt.ctors := by
    refine ⟨_, List.mem_map.2 ⟨(s.families[ctor.owner], ctor.owner.val),
      List.mk_mem_zipIdx_iff_getElem?.2 (by simp), rfl⟩, rfl, ?_⟩
    simp only [List.mem_filterMap]
    exact ⟨ctor, hctor, by simp⟩
  obtain ⟨nt, hnt, hname, hmem⟩ := hnt
  obtain ⟨st, hst, hR⟩ := Lean4Lean.List.Forall₂.forall_exists_l H nt hnt
  obtain ⟨sc, hsc, hn, -, restored, hres, hdef⟩ := Lean4Lean.List.Forall₂.forall_exists_l hR.constructors _ hmem
  rw [Restoration.expr_empty] at hres
  cases Option.some.inj hres
  exact ⟨st, hst, sc, hsc, hR.name.symm.trans hname, hn.symm, hdef⟩

theorem singletonInstance_alignJ
    {Γ : List VExpr} {data : RecursorData} {decl : VInductDecl} {env₀ env₁ : VEnv}
    {rec : VRecursor} {ru : VRecRule} {index : Fin data.schema.signature.constructors.size}
    {equation : VDefEq} {levels ctorLevels : List VLevel} {recArgs ctorArgs : List VExpr}
    {T T' : VExpr}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hAt : RecursorRegisteredAt env data decl env₀ env₁) (hname : rec.name = data.name)
    (hrec : rec ∈ decl.recs)
    (hru : ru ∈ rec.rules) (hgen : data.equation index = some equation)
    (hof : VRecRule.OfEquation rec ru equation) (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero)
    (h1 : recArgs.length = rec.getMajorIdx) (h2 : ctorArgs.length = ru.ctorParams + ru.nfields)
    (ht : Γ ⊢ VExpr.mkApps (.const rec.name levels)
        (recArgs ++ [VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs]) : T)
    (hJ : HasTypeJ Γ (VExpr.mkApps (.const rec.name levels)
        (recArgs ++ [VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs])) T)
    (hβ : Γ ⊢ VExpr.mkApps (equation.lhs.instL levels)
        (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
          ctorArgs.drop ru.ctorParams) : T')
    (hNJ : ∀ {base E : VEnv}, base ≤ env₀ → base.addConstVals decl.typeConstants = some E →
      ∀ {A B : VExpr}, E.IsDefEqU decl.uvars [] A B → ∀ {Γ' : List VExpr} {cls : List VLevel},
        OnCtx Γ' (env.IsType univs) → (∀ l ∈ cls, l.WF univs) → cls.length = decl.uvars →
        Γ' ⊢ A.instL cls ≫≪ B.instL cls) :
    Γ ⊢ VExpr.mkApps (.const rec.name levels)
        (recArgs ++ [VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs]) ≫≪
      VExpr.mkApps (equation.lhs.instL levels)
        (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
          ctorArgs.drop ru.ctorParams) := by
  have H := hAt.registered
  have F := RecursorData.singletonSignature H hlarge (packed := levels) hzero
  obtain ⟨base, expanded, g, auxiliaries, block, hdata, hprior, hbase, hr, hsf, hu, hl, htg,
    hwf, hadd, hrecs, he, hbwf⟩ := hAt
  have hinst := RecursorRegistered.recursorInstance_eq hdata hu hl htg
  have hres0 : compilationRestoration decl auxiliaries = {} := hr.symm.trans F.restoration
  have haux : auxiliaries = [] := hdata.noAuxiliaries_of_singleton F.families
  have hg : (compilationRestoration decl auxiliaries).equation (g.equation index) =
      some equation := by
    simpa only [RecursorData.equation, hinst, hr] using hgen
  rw [hres0, Restoration.equation_empty] at hg
  cases Option.some.inj hg
  subst hinst
  generalize hgdef : data.recursorInstance = g at *
  let s := data.schema.signature
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let np := s.params.length
  let D := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let idx := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let fn := VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
    (vars (np + extra) nf ++ idx)
  let major := VExpr.mkApps (.const ctor.name g.levels) (vars np (extra + nf) ++ vars nf 0)
  let lb := VExpr.app fn major
  have hlb : (g.equation index).lhs = VExpr.wrapLams D lb := by
    simp only [Instance.equation, Instance.recursorHead, Instance.constructorApp, D, lb, fn,
      major, idx, ctor, s, np, nf, extra, Nat.add_zero]
    rw [List.append_assoc (vars _ _), ← List.append_assoc, VExpr.mkApps_append]; rfl
  have hDlen : D.length = np + extra + nf := by
    simp only [D, Instance.params, Instance.motives, Instance.minors, insertBinders,
      InductiveSignature.fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList, np, nf, extra, s, ctor]
    omega
  -- the rule's counts
  have hof2 := hof.2.1
  have hof3 := hof.2.2.1
  obtain ⟨maj, hmaj1, hmaj2, hmaj3⟩ := hof.2.2.2
  rw [hlb, VExpr.lamBody_wrapLams_app] at hof2 hof3 hmaj1
  have hrname : rec.name = g.recursorName ctor.owner := by
    simp only [lb, VExpr.headConst?, VExpr.getAppFn_app, fn, VExpr.getAppFn_mkApps,
      VExpr.getAppFn] at hof2
    exact (Option.some.inj hof2).symm
  simp only [lb, VExpr.getAppArgs_app, fn, VExpr.getAppArgs_mkApps, VExpr.getAppArgs,
    List.nil_append, List.length_append, List.length_singleton] at hof3 hmaj1
  have hmajEq : maj = major := by
    simpa using hmaj1.symm
  subst hmajEq
  have hctorName : ru.ctor = ctor.name := by
    simp only [major, VExpr.headConst?, VExpr.getAppFn_mkApps, VExpr.getAppFn] at hmaj2
    exact (Option.some.inj hmaj2).symm
  have hcpnf : ru.ctorParams + ru.nfields = np + nf := by
    simp only [major, VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append,
      List.length_append] at hmaj3
    simpa [vars] using hmaj3.symm
  have hvl : ∀ n k, (vars n k).length = n := fun n k => by simp [vars]
  have hmajorIdx : rec.getMajorIdx = np + extra + idx.length := by
    rw [hvl] at hof3; omega
  have hnp : np = decl.nparams := hdata.model.nparams.trans hdata.nparams
  have hcp : ru.ctorParams = np := by
    rcases hwf.rules_ctorParams rec hrec ru hru with ⟨c, hcm, hcn, hcp⟩ | ⟨D', hD', c, hcm, hcn, hcp⟩
    · rw [hcp, hnp]
    · exfalso
      rcases hdata.constructor_name_cases index with ⟨c', hc'm, hc'n⟩ | ⟨a, ha, -⟩
      · rw [hres0] at hc'n
        simp only [Restoration.headName, Restoration.recursorName] at hc'n
        have hcn' : c.name = c'.name := by
          rw [← hcn, hctorName]; exact hc'n
        obtain ⟨type', htype', hctor'⟩ := List.mem_flatMap.1 hc'm
        have hfresh := addInduct_ctor_fresh hadd htype' hctor'
        obtain ⟨type, htype, hctor⟩ := List.mem_flatMap.1 hcm
        cases hD' with
        | intro _ _ _ _ _ hadd' hle' =>
          have := hle'.constants (addInduct_ctor_find hadd' htype hctor)
          rw [hcn', hfresh] at this
          cases this
      · rw [haux] at ha; cases ha
  have hnf' : ru.nfields = nf := by omega
  obtain ⟨rb, hrb, krb, argsrb, hrbShape⟩ : ∃ rb, (g.equation index).rhs = VExpr.wrapLams D rb ∧
      ∃ k args', rb = VExpr.mkApps (.bvar k) args' :=
    ⟨_, rfl, _, _, rfl⟩
  have hk : rec.numParams + rec.numMotives + rec.numMinors = np + extra := by
    obtain ⟨j, hj, A, -, -, -, hshape⟩ := hwf.rule_shape rec hrec ru hru
    have h1 := hshape.1
    rw [← hof.1, hrb, hrbShape, VExpr.lamArity_wrapLams_mkApps_bvar, hDlen, hnf'] at h1
    omega
  -- the source constructor, its installed constant and its normalization
  obtain ⟨envTypes, direct, htypes, hdirect, -, hcorr⟩ := hdata.correspondence
  rw [haux] at hdirect
  cases Option.some.inj hdirect
  rw [haux, show compilationRestoration decl [] = {} from haux ▸ hres0] at hcorr
  simp only [List.reverse_nil, List.append_nil] at hcorr
  have hctorMem : ctor ∈ s.constructors.toList := Array.getElem_mem_toList ..
  obtain ⟨st, hst, sc, hsc, hstn, hscn, hNdef⟩ := RestoresFamily.normalized_ctor hcorr hctorMem
  have hscc : env.constants sc.name = some sc.toVConstant :=
    he.constants (addInduct_ctor_find hadd hst hsc)
  obtain ⟨Ds, Rs, hSeq, hDsle, hvalid, hhead⟩ := hdata.sourceParameters.rawCtorShape st hst sc hsc
  -- the owner
  have howner : ctor.owner = data.owner := by
    have hf : data.schema.signature.families.size = 1 := F.families
    have ha := ctor.owner.isLt
    have hb := data.owner.isLt
    exact Fin.ext (by simp only [ctor, s] at ha ⊢; omega)
  -- the recursor side: the major's joinable type joins the recursor's major domain
  let nind := (s.families[data.owner]).indices.length
  have hnind : idx.length = nind := by
    simp only [idx, List.length_map, nind, ← howner]; exact F.arity ctor hctorMem
  let preR := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.families[data.owner]).indices.map (·.instL g.levels)) extra
  let majR := g.familyApp data.owner (vars np (extra + nind)) (vars nind 0)
  have hrecT : env.constants rec.name = some ⟨data.uvars, VExpr.wrapForalls preR
      (.forallE majR (VExpr.mkApps (.bvar (nind + 1 + s.constructors.size +
        (s.families.size - 1 - data.owner.val))) (vars nind 1 ++ [.bvar 0])))⟩ := by
    rw [hname, F.recursor, hgdef]
    simp only [Instance.recursorType, preR, majR, nind, insertBinders, List.length_map,
      List.length_zipIdx, VExpr.wrapForalls_append]
    rfl
  have hpreR : recArgs.length = preR.length := by
    simp only [h1, hmajorIdx, preR, Instance.params, Instance.motives, Instance.minors,
      insertBinders, List.length_append, List.length_map, List.length_zipIdx, Array.length_toList,
      hnind, np, extra, nind, s]
    omega
  have hJapp : HasTypeJ Γ (.app (VExpr.mkApps (.const rec.name levels) recArgs)
      (VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs)) T := by
    rw [← VExpr.mkApps_snoc]; exact hJ
  obtain ⟨X, hJM, hjR⟩ := HasTypeJ.major_join hΓ hrecT hpreR hJapp
  let famL := g.levels.map (·.inst levels)
  let fam := (s.families[data.owner]).name
  have hlenR : recArgs.length = np + extra + nind := by rw [h1, hmajorIdx, hnind]
  have hmajR : (majR.instL levels).instOuter recArgs =
      VExpr.mkApps (.const fam famL) (recArgs.take np ++ recArgs.drop (np + extra)) := by
    simp only [majR, Instance.familyApp, InductiveSignature.familyApp, VExpr.instL_mkApps,
      VExpr.instL, List.map_append, vars_instL, VExpr.instOuter_mkApps, VExpr.instOuter_const]
    rw [map_instOuter_vars _ _ _ (by omega), map_instOuter_vars _ _ _ (by omega)]
    simp only [show recArgs.length - (np + (extra + nind)) = 0 by omega, List.drop_zero,
      show recArgs.length - (nind + 0) = np + extra by omega]
    rw [List.take_of_length_le (l := recArgs.drop (np + extra)) (by simp; omega)]
  rw [hmajR] at hjR
  -- the constructor side: its declared result joins the major's joinable type
  have hctc : env.constants ru.ctor = some ⟨sc.uvars, VExpr.wrapForalls Ds Rs⟩ := by
    rw [hctorName, ← hscn, hscc, ← hSeq]
  have hMX : Γ ⊢ VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs :
      VExpr.mkApps (.const fam famL) (recArgs.take np ++ recArgs.drop (np + extra)) :=
    hJM.hasType.defeqU_r henv hΓ (hjR.defeq hΓ).symm
  have hRs : Rs = VExpr.mkApps (.const st.name (VLevel.params decl.uvars))
      (VExpr.getAppFnArgs.go Rs []).2 := by
    have := VExpr.mkApps_getAppFnArgs_eq Rs
    have hh : (VExpr.getAppFnArgs.go Rs []).1 = _ := hhead
    rw [hh] at this; exact this.symm
  have hfam : fam = st.name := by rw [hstn]; simp only [fam, s, ctor, howner]
  have hrig : env.Rigid st.name := by
    have := (H.family_head_rigid henv index (owner := data.owner) howner).2
    rw [F.restoration] at this
    simpa [Restoration.headName, Restoration.recursorName, fam, ← hfam] using this
  obtain ⟨_, hMc⟩ := HasType.mkApps_head henv.orderedStrong hΓ (f := .const ru.ctor ctorLevels) hMX
  obtain ⟨_, hcl, hcll⟩ := hMc.const_inv henv.orderedStrong hΓ
  rw [hctc] at hcl; cases hcl
  have hctT : Γ ⊢ .const ru.ctor ctorLevels : VExpr.wrapForalls (Ds.map (·.instL ctorLevels))
      (VExpr.mkApps (.const st.name ((VLevel.params decl.uvars).map (·.inst ctorLevels)))
        ((VExpr.getAppFnArgs.go Rs []).2.map (·.instL ctorLevels))) := by
    have := HasType.const (Γ := Γ) hctc hcll.1 hcll.2
    rw [hRs] at this
    simpa [VExpr.instL_wrapForalls, VExpr.instL_mkApps, VExpr.instL] using this
  have hctT' : Γ ⊢ .const ru.ctor ctorLevels :
      VExpr.wrapForalls (Ds.map (·.instL ctorLevels)) (Rs.instL ctorLevels) := by
    have := HasType.const (Γ := Γ) hctc hcll.1 hcll.2
    simpa [VExpr.instL_wrapForalls] using this
  have harity : ctorArgs.length = Ds.length := by
    have := HasType.mkApps_rigid_arity henv hΓ hrig hctT (by rw [← hfam]; exact hMX)
    simpa using this
  -- the family head is typed by a telescope ending in a sort, at every universe specialization
  have hsU : s.uvars = decl.uvars := hdata.model.uvars.trans hdata.uvars
  have hSH : ∀ L' : List VLevel, (∀ l ∈ L', l.WF univs) → L'.length = s.uvars →
      SortHeaded st.name L' := by
    intro L' hw hl Γ' hΓ'
    have hle : base ≤ env := hbase.trans ((addInduct_le hadd).trans he)
    obtain ⟨domains, level, hH, -⟩ := hdata.family_head_type hprior henv hΓ' hle
      (fun family hf => he.constants (addInduct_type_find hadd hf)) data.owner hw hl
    rw [haux, show compilationRestoration decl [] = {} from haux ▸ hres0] at hH
    simp only [Restoration.headName, Restoration.headLevels, Restoration.recursorName] at hH
    exact ⟨_, _, by simpa [← hfam, fam] using hH⟩
  -- the constructor's declared result at the instance
  have hjC := HasTypeJ.const_spine_join hΓ hctc harity hJM
  have hscU : sc.uvars = decl.uvars := hwf.ctors_uvars st hst sc hsc
  have hcL : ctorLevels.length = decl.uvars := hcll.2.trans hscU
  obtain ⟨srcIdx, hsrc, -⟩ := VInductDecl.RawIndAppAt.instOuter (hvalid.instL ctorLevels)
    (levels := (VLevel.params decl.uvars).map (·.inst ctorLevels))
    (by rw [hRs, VExpr.instL_mkApps, VExpr.getAppFnArgs_mkApps_head]; rfl) ctorArgs
    (by rw [harity]; omega)
  rw [hsrc, VLevel.inst_map_id hcL] at hjC
  -- injectivity of the joined family applications
  obtain ⟨_, hrecH⟩ := HasType.mkApps_head henv.orderedStrong hΓ (f := .const rec.name levels) ht
  obtain ⟨_, -, hlevW, -⟩ := hrecH.const_inv henv.orderedStrong hΓ
  have hfamLW : ∀ l ∈ famL, l.WF univs := by
    intro l hl
    obtain ⟨l0, -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hlevW
  have hfamLl : famL.length = s.uvars := by simp only [famL, List.length_map, ← hgdef]; exact F.uvars
  have jMC := hjR.trans hΓ (hjC.symm hΓ)
  rw [hfam] at jMC
  have hXT := hJM.hasType
  obtain ⟨_, hXs⟩ := hXT.isType henv.ordered hΓ
  have hleftT := hXs.defeqU_l henv hΓ (hjR.defeq hΓ).symm
  rw [hfam] at hleftT
  have hinj := FullCRDefEq.rigid_spine_inv hΓ hrig (hSH famL hfamLW hfamLl)
    (hSH ctorLevels hcll.1 (hcL.trans hsU.symm)) hleftT jMC
  rw [← hnp] at hinj
  have hnpR : (recArgs.take np).length = (ctorArgs.take np).length := by
    simp only [List.length_take]; omega
  obtain ⟨hP, hI⟩ := (Lean4Lean.List.Forall₂.append_of_left hnpR).mp hinj
  -- the source constructor's indices join the normalized ones
  have hND := hNJ hbase htypes hNdef hΓ hcll.1 hcL
  have hnorm : (s.constructorType ctor).instL ctorLevels = VExpr.wrapForalls
      ((s.params ++ s.fieldTypes ctor).map (·.instL ctorLevels))
      (VExpr.mkApps (.const fam (((VLevel.params s.uvars)).map (·.inst ctorLevels)))
        (vars np nf ++ ctor.indices.map (·.instL ctorLevels))) := by
    simp only [InductiveSignature.constructorType, InductiveSignature.familyApp,
      VExpr.instL_wrapForalls, VExpr.instL_mkApps, VExpr.instL, List.map_append, vars_instL,
      fam, howner]
    rfl
  rw [hnorm, VLevel.inst_map_id (hcL.trans hsU.symm), hSeq, VExpr.instL_wrapForalls] at hND
  have hDslen : Ds.length = np + nf := by rw [← harity, h2, hcp, hnf']
  have hpeel := FullCRDefEq.wrapForalls_instOuter hΓ (args := ctorArgs) (by simpa using harity)
    (by simp [InductiveSignature.fieldTypes, hDslen, np, nf, ctor, s]) hctT' ⟨_, hJM.hasType⟩
    (hND.symm hΓ)
  rw [hsrc, VLevel.inst_map_id hcL] at hpeel
  have hctl : ctorArgs.length = np + nf := by rw [h2, hcp, hnf']
  have hnormR : (VExpr.mkApps (.const fam ctorLevels) (vars np nf ++
      ctor.indices.map (·.instL ctorLevels))).instOuter ctorArgs =
      VExpr.mkApps (.const fam ctorLevels) (ctorArgs.take np ++
        (ctor.indices.map (·.instL ctorLevels)).map (·.instOuter ctorArgs)) := by
    simp only [VExpr.instOuter_mkApps, VExpr.instOuter_const, List.map_append]
    rw [map_instOuter_vars _ _ _ (by omega)]
    simp only [show ctorArgs.length - (np + nf) = 0 by omega, List.drop_zero]
  rw [hnormR, hfam, ← hnp] at hpeel
  rw [← hnp] at hjC
  have hsrcT := hXs.defeqU_l henv hΓ (hjC.defeq hΓ).symm
  have hinj2 := FullCRDefEq.rigid_spine_inv hΓ hrig (hSH ctorLevels hcll.1 (hcL.trans hsU.symm))
    (hSH ctorLevels hcll.1 (hcL.trans hsU.symm)) hsrcT hpeel
  obtain ⟨-, hI2⟩ := (Lean4Lean.List.Forall₂.append_of_left rfl).mp hinj2
  -- the universe levels of the constructor are those of the recursor's family
  have hlevEq : List.Forall₂ (· ≈ ·) famL ctorLevels :=
    (henv.headInversion.rigid_rigid hΓ hrig hrig
      ((jMC.defeq hΓ).typeChain henv hΓ hleftT)).2.1
  have hcI : ∀ e ∈ ctor.indices, (e.instL famL).ClosedN (np + nf) := by
    have hle : base ≤ env := hbase.trans ((addInduct_le hadd).trans he)
    have hTle : envTypes ≤ env := VEnv.addConstVals_le_target hle htypes (by
      intro value hvalue
      obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
      exact he.constants (addInduct_type_find hadd hfamily))
    obtain ⟨_, hd⟩ := hNdef
    have hc := ((hd.mono hTle).closedN' henv.ordered.closed ⟨⟩).1
    simp only [InductiveSignature.constructorType, InductiveSignature.familyApp] at hc
    have hb := (VExpr.ClosedN.wrapForalls_inv_singleton hc).2
    have hargs := (VExpr.ClosedN.mkApps_inv hb).2
    intro e he'
    have := hargs e (List.mem_append_right _ he')
    refine VExpr.ClosedN.instL ?_
    simpa [InductiveSignature.fieldTypes, np, nf, s, ctor] using this
  -- the β-body of the equation at the constructor's parameters
  let Amm := (recArgs.drop np).take extra
  let args'' := ctorArgs.take np ++ Amm ++ ctorArgs.drop np
  let idxE := (ctor.indices.map (·.instL famL)).map (·.instOuter ctorArgs)
  have hAmm : Amm.length = extra := by simp only [Amm, List.length_take, List.length_drop]; omega
  have hargs''len : args''.length = np + extra + nf := by
    simp only [args'', List.length_append, List.length_take, List.length_drop, hAmm]; omega
  have hbody : (lb.instL levels).instOuter args'' =
      .app (VExpr.mkApps (.const rec.name levels) (ctorArgs.take np ++ Amm ++ idxE))
        (VExpr.mkApps (.const ru.ctor famL) ctorArgs) := by
    have hguv : g.uvars = data.uvars := by rw [← hgdef]; rfl
    have hlevl : levels.length = g.uvars := by
      obtain ⟨_, hci, -, hll⟩ := hrecH.const_inv henv.orderedStrong hΓ
      rw [hrecT] at hci; cases hci; rw [hll, hguv]
    have hv : ∀ n k, n + k ≤ args''.length →
        (vars n k).map (fun a => (a.instL levels).instOuter args'') =
          (args''.drop (args''.length - (n + k))).take n := by
      intro n k h
      have : (vars n k).map (fun a => (a.instL levels).instOuter args'') =
          ((vars n k).map (VExpr.instL levels)).map (·.instOuter args'') := by
        simp [List.map_map, Function.comp_def]
      rw [this, vars_instL, map_instOuter_vars _ _ _ h]
    have hTA : (ctorArgs.take np ++ Amm).length = np + extra := by
      simp only [List.length_append, List.length_take, hAmm]; omega
    have hA : (vars (np + extra) nf).map (fun a => (a.instL levels).instOuter args'') =
        ctorArgs.take np ++ Amm := by
      rw [hv _ _ (by omega), hargs''len, show np + extra + nf - (np + extra + nf) = 0 by omega,
        List.drop_zero]
      simp only [args'', List.append_assoc]
      rw [← List.append_assoc, List.take_left' hTA]
    have hIdx : idx.map (fun a => (a.instL levels).instOuter args'') = idxE := by
      simp only [idx, idxE, List.map_map]
      apply List.map_congr_left
      intro e he
      simp only [Function.comp_def, VExpr.instL_liftN, VExpr.instL_instL]
      have hcl := hcI e he
      have hA' : (ctorArgs.take np ++ Amm).length = np + extra := by
        simp only [List.length_append, List.length_take, hAmm]; omega
      have := instOuter_liftN_skip (X := e.instL famL) (A := ctorArgs.take np ++ Amm)
        (B := ctorArgs.drop np) (P := np) (r := extra)
        (by simp only [List.length_drop, hctl]; simpa [show np + nf - np = nf by omega] using
          hcl.mono (by omega)) hA'
      rw [show (ctorArgs.drop np).length = nf by simp; omega] at this
      rw [show args'' = (ctorArgs.take np ++ Amm) ++ ctorArgs.drop np from rfl, this,
        List.take_left' (by simp; omega), List.take_append_drop]
    have hB : (vars np (extra + nf) ++ vars nf 0).map (fun a => (a.instL levels).instOuter args'') =
        ctorArgs := by
      rw [List.map_append, hv _ _ (by omega), hv _ _ (by omega), hargs''len,
        show np + extra + nf - (np + (extra + nf)) = 0 by omega, List.drop_zero,
        show np + extra + nf - (nf + 0) = np + extra by omega]
      have e1 : args''.take np = ctorArgs.take np := by
        simp only [args'', List.append_assoc]; exact List.take_left' (by simp; omega)
      have e2 : args''.drop (np + extra) = ctorArgs.drop np := by
        show (ctorArgs.take np ++ Amm ++ ctorArgs.drop np).drop (np + extra) = _
        exact List.drop_left' hTA
      rw [e1, e2, List.take_of_length_le (l := ctorArgs.drop np) (i := nf) (by simp; omega), List.take_append_drop]
    simp only [lb, fn, major, VExpr.instL, VExpr.instL_mkApps, VExpr.instOuter_app',
      VExpr.instOuter_mkApps, VExpr.instOuter_const, List.map_append]
    rw [VLevel.inst_map_id hlevl, ← hrname, ← hctorName]
    simp only [List.map_map, Function.comp_def] at hA hIdx hB ⊢
    rw [hA, hIdx]
    rw [← List.map_append, hB]
  -- the index arguments join the equation's index expressions at the constructor's arguments
  let normIdxC := (ctor.indices.map (·.instL ctorLevels)).map (·.instOuter ctorArgs)
  have hargsEq : ∀ a ∈ ctorArgs, EqUpToLevels univs a a := fun a ha => by
    obtain ⟨_, h⟩ := mkApps_arg_type hΓ hJM.hasType ha
    exact eqUpToLevels_rfl hΓ h
  have hLev : List.Forall₂ (FullCRDefEq Γ) normIdxC idxE := by
    simp only [normIdxC, idxE, List.map_map]
    refine List.forall₂_map_map fun e he => ?_
    have hmem : (e.instL ctorLevels).instOuter ctorArgs ∈ normIdxC :=
      List.mem_map.2 ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, rfl⟩
    obtain ⟨_, -, ⟨-, ⟨_, hty⟩, -⟩⟩ := Lean4Lean.List.Forall₂.forall_exists_r hI2 _ hmem
    refine FullCRDefEq.of_eqUpToLevels hΓ ?_ hty
    refine EqUpToLevels.instOuter_same (EqUpToLevels.instL_expr e hcll.1 hfamLW ?_) hargsEq
    exact Lean4Lean.List.Forall₂.flip (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) hlevEq)
  have hJI := FullCRDefEq.forall₂_trans hΓ (FullCRDefEq.forall₂_trans hΓ hI hI2) hLev
  -- typings
  have hrecArgs : ∀ a ∈ recArgs, ∃ A, Γ ⊢ a : A := fun a ha =>
    mkApps_arg_type hΓ ht (List.mem_append_left _ ha)
  have hAmmT : ∀ a ∈ Amm, ∃ A, Γ ⊢ a : A := fun a ha =>
    hrecArgs a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  have hdropT : ∀ a ∈ ctorArgs.drop np, ∃ A, Γ ⊢ a : A := fun a ha =>
    mkApps_arg_type hΓ hJM.hasType (List.mem_of_mem_drop ha)
  have hsplitD : recArgs.drop np = Amm ++ recArgs.drop (np + extra) := by
    have := List.take_append_drop extra (recArgs.drop np)
    simp only [List.drop_drop] at this
    simp only [Amm]
    rw [show np + extra = extra + np by omega]
    first | exact this.symm | (rw [Nat.add_comm] at this; exact this.symm)
  have hsplit : recArgs = recArgs.take np ++ Amm ++ recArgs.drop (np + extra) := by
    rw [List.append_assoc, ← hsplitD, List.take_append_drop]
  -- the instance joins the β-body
  have htApp : Γ ⊢ .app (VExpr.mkApps (.const rec.name levels) recArgs)
      (VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs) : T := by
    rw [← VExpr.mkApps_snoc]; exact ht
  obtain ⟨_, _, hfnT, -⟩ := htApp.app_inv henv.orderedStrong hΓ
  have hfnJ : Γ ⊢ VExpr.mkApps (.const rec.name levels) recArgs ≫≪
      VExpr.mkApps (.const rec.name levels) (ctorArgs.take np ++ Amm ++ idxE) := by
    have h := FullCRDefEq.mkApps hΓ (.refl hΓ hrecH)
      (List.Forall₂.append' (List.Forall₂.append' hP (FullCRDefEq.forall₂_refl hΓ hAmmT)) hJI)
      (by rw [← hsplit]; exact hfnT)
    rwa [← hsplit] at h
  have hMJ : Γ ⊢ VExpr.mkApps (.const ru.ctor ctorLevels) ctorArgs ≫≪
      VExpr.mkApps (.const ru.ctor famL) ctorArgs :=
    FullCRDefEq.mkApps hΓ (.normalEq hΓ (.constDF hctc hcll.1 hfamLW hcll.2
      (Lean4Lean.List.Forall₂.flip (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) hlevEq))))
      (FullCRDefEq.forall₂_refl hΓ fun a ha => mkApps_arg_type hΓ hJM.hasType ha) hJM.hasType
  have htu := FullCRDefEq.app hΓ hfnJ hMJ htApp
  rw [← hbody] at htu
  -- the β-redex of the equation at the constructor's parameters reduces to the β-body
  have hDl : (D.map (VExpr.instL levels)).length = args''.length := by
    simp [hDlen, hargs''len]
  have hred : FullReduction Γ (VExpr.mkApps ((g.equation index).lhs.instL levels) args'')
      ((lb.instL levels).instOuter args'') := by
    rw [hlb, VExpr.instL_wrapLams]; exact FullReduction.mkApps_wrapLams hDl.symm
  -- the stub's arguments
  have hargsEq' : recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
      ctorArgs.drop ru.ctorParams = recArgs.take np ++ Amm ++ ctorArgs.drop np := by
    rw [hk, hcp, List.take_add]
  rw [hargsEq'] at hβ ⊢
  have hargsJ : List.Forall₂ (FullCRDefEq Γ) (recArgs.take np ++ Amm ++ ctorArgs.drop np) args'' :=
    List.Forall₂.append' (List.Forall₂.append' hP (FullCRDefEq.forall₂_refl hΓ hAmmT))
      (FullCRDefEq.forall₂_refl hΓ hdropT)
  have hβJ := FullCRDefEq.mkApps hΓ (.refl hΓ (show Γ ⊢ _ : _ from
    (HasType.mkApps_head henv.orderedStrong hΓ hβ).choose_spec)) hargsJ hβ
  have hred' := FullCRDefEq.of_reduction hΓ hβJ.2.1.choose_spec hred
  rw [VExpr.mkApps_snoc]
  exact (htu.trans hΓ (hred'.symm hΓ)).trans hΓ (hβJ.symm hΓ)

end Lean4Lean.VEnv
