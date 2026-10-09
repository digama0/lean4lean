import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EmptyRule
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.RecursorEquations

/-! # Validity of ordinary recursor rules

`RuleValid.recursor`: a generated equation of a finite compilation without container
specializations is valid in the model of a well-formed environment, given

* that the rules headed by its recursor are exactly its block's equations (`HeadExcl`);
* that the major's family has only its recorded result sort at the ends of the chain
  observations of its type (`FamSort`, a semantic fact proved from the soundness of an earlier
  environment along the declaration history);
* for singleton elimination, that the fields not determined by an index are proof binders
  (`ProofBinder`, also from earlier soundness).

The proof splits on the admissibility of the elimination: with family sorts that are never
zero the rule is an instance of `sound_pat` whose mode C hypothesis is contradictory
(`recursor_C_absurd`); with a zero target sort its right-hand side has no observations
(`sound_pat_empty`); with singleton elimination it is an instance of `sound_pat` in mode C
(the rule is the only one of its head, the major-only fields are proof binders). -/

namespace Lean4Lean
namespace VEnv
namespace Model
open InductiveSignature

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The constant `I` has only the sort `l` at the ends of the chain observations of its type,
at every instantiation. -/
def FamSort (env : VEnv) (I : Name) (l : VLevel) : Prop :=
  ∀ (U : Nat) (Δ : List VExpr) (ci : VConstant) (lsI : List VLevel) (ks : List Key)
    (z : List Nat → Nat), OnCtx Δ (env.IsType U) → env.constants I = some ci →
    (∀ l ∈ lsI, l.WF U) →
    Obs env U Δ .id .empty (ci.type.instL lsI) (piCodChain ks (.sort z)) → z = (l.inst lsI).eval

/-- Every rule of `env` headed by `n` belongs to `rs`. -/
def HeadExcl (env : VEnv) (n : Name) (rs : List VDefEq) : Prop :=
  ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' ∈ rs

/-- The binder `x` of `doms` is a proof binder: at every typed valuation its type is
definitionally a proposition and all its observations are typed at `Sort 0`. -/
def ProofBinder (env : VEnv) (U : Nat) (Δ : List VExpr) (doms : List VExpr) (ls : List VLevel)
    (x : Nat) (Γ : List VExpr) : Prop :=
  ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
    TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
    (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧ env.HasType U Δ P (.sort .zero)) ∧
    ∀ τ, Obs env U Δ v vS (binderTy doms ls x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0]

/-- The static facts about the family `I` of a rule's major that select its binding mode: `I`
is not projection-registered and `ctor` is not a projection constructor, or `I` has a valid
projection entry with the constructor `ctor`, `np` parameters, `nf` fields and a result level
equivalent to `L`. Discharged for well-formed environments in `Model/EnvValid.lean`. -/
def ProjMajor (env : VEnv) (I ctor : Name) (np nf : Nat) (L : VLevel) : Prop :=
  ((∀ info, ¬ env.projections I info) ∧ ¬ IsProjCtor env ctor) ∨
  ∃ info, env.projections I info ∧ ProjValid env I info ∧ info.ctorName = ctor ∧
    info.nparams = np ∧ info.numFields = nf ∧ info.resultLevel ≈ L

theorem ProjMajor.weak {I ctor : Name} {np nf : Nat} {L : VLevel}
    (h : ProjMajor env I ctor np nf L) : MajorFamEntry env I ctor := by
  rcases h with h | ⟨info, h1, -, h2, -⟩
  · exact .inl h
  · exact .inr ⟨info, h1, h2⟩

/-- `MajorFam` from `ProjMajor` at a major with exactly the registered numbers of parameter and
field arguments, given that the family's level is never zero at the major's levels or that the
fields not bound by the leading arguments are proofs. -/
theorem ProjMajor.majorFam {I ctor : Name} {L : VLevel} {Γ doms lead ms : List VExpr}
    {fs : List Nat} {ls lsC : List VLevel}
    (h : ProjMajor env I ctor ms.length fs.length L)
    (hnz : (L.inst (lsC.map (·.inst ls))).IsNeverZero ∨
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs env U Δ v vS (binderTy doms ls x) τ →
          ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0]) :
    MajorFam env U Δ Γ I ctor doms lead ms fs ls lsC := by
  rcases h with h | ⟨info, hp, hPV, hcn, hnp, hnf, hL⟩
  · exact .inl h
  refine .inr ⟨info, hp, hPV, hcn, by omega, fun x j _ _ => by omega, ?_⟩
  rcases hnz with hnz | hnz
  · exact .inl (hnz.of_equiv (VLevel.inst_congr_l (Eq.symm hL : L ≈ info.resultLevel)))
  · exact .inr hnz

theorem eqLead_length_owner {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g aux block) (index : Fin s.constructors.size) :
    (g.eqLead index).length = s.params.length + (s.families.size + s.constructors.size) +
      s.families[s.constructors[index].owner].indices.length := by
  have h := H.model.constructorArity s.constructors[index] (by simp)
  rw [g.eqLead_length, h]

/-- Uniqueness of an ordinary recursor rule per head and constructor. -/
theorem recursor_uniq {s : InductiveSignature} {g : Instance s}
    (C : CompilationData base source expanded s g [] block) (index : Fin s.constructors.size)
    (hex : HeadExcl env (g.recursorName s.constructors[index].owner) block.rules) :
    ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const (g.recursorName s.constructors[index].owner) lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = (g.eqLead index).length ∧
        (ctor' = s.constructors[index].name → df' = g.equation index) := by
  intro df' doms' lsP' lead' ctor' lsC' ms' fs' body' hdf' hl' _
  have hm := hex df' hdf' lsP' (by rw [hl']; exact VExpr.stripLams_wrapLams_mkApps_head)
  rw [C.ordinary_rules] at hm
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
  obtain ⟨-, n2, -, l2, a2⟩ := wrapLams_pat_inj (hl'.symm.trans (g.equation_lhs_eq j))
  obtain ⟨c2, -, -⟩ := VExpr.mkApps_const_inj a2
  have ho := C.recursorName_inj n2
  refine ⟨?_, fun hc => ?_⟩
  · rw [l2, eqLead_length_owner C, eqLead_length_owner C]; simp only [ho]
  · have := C.ctor_inj ho.symm (c2.symm.trans hc)
    subst this; rfl

/-- Inversion at a rigid constant: a rigid observation of its spine comes from the `const`
clause. -/
theorem const_rigid_inv {σ : VExpr.Subst} {S : ObSets} {keys : List Key}
    (hrig : env.Rigid n) (h : Obs' σ S (.const n ls) (wrap keys (.rigid n' ℓs m z))) :
    ∃ ci τs, env.constants n = some ci ∧ (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls))
        (wrap keys (.rigid n' ℓs m z)) τs := by
  rcases Obs.const_iff.1 h with ⟨ci, τs, keys', r, e, _, hci, hτs, hty, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r, e, _, _, _, _, _, hr, _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, keys', r, e, _, _, _, _, _, _, ⟨_, _, _, rfl, _⟩, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · rw [← e] at hty; exact ⟨ci, τs, hci, hτs, hty⟩
  · exact absurd (by rw [hlhs]; rfl) (hrig df hdf _)
  · have hrn : r.NotApp := by
      rcases hr with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨rfl, rfl⟩ := wrap_inj e trivial hrn
    rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig df hdf lsP)
  · cases (wrap_inj e trivial trivial).2
  · cases (wrap_inj e trivial trivial).2
  · cases (wrap_inj e trivial trivial).2

/-- Mode C is impossible at a recursor whose major family has a result sort that is
never zero. -/
theorem recursor_C_absurd {s : InductiveSignature} {g : Instance s} {ls : List VLevel}
    {o : Fin s.families.size} {RH : VExpr} {keys : List Key} {m : Nat}
    (hΔ : OnCtx Δ (env.IsType U)) (hlw : ∀ l ∈ ls, l.WF U)
    (hIrig : env.Rigid s.families[o].name)
    (hfs : FamSort env s.families[o].name s.families[o].resultLevel)
    (hnz : (s.families[o].resultLevel.inst g.levels).IsNeverZero)
    (hkl : keys.length + 1 = (g.recDoms o).length)
    (h : Obs' .id .empty ((VExpr.wrapForalls (g.recDoms o) RH).instL ls) (piCodChain keys
      (.piDomOb (.rigid s.families[o].name ((g.levels.map (·.inst ls)).map (·.eval)) m
        fun _ => 0)))) : False := by
  have hlsI : ∀ l ∈ g.levels.map (·.inst ls), l.WF U := by
    intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hlw
  rw [show g.recDoms o = (g.params ++ g.motives ++ g.minors ++
      insertBinders (s.families[o].indices.map (·.instL g.levels))
        (s.families.size + s.constructors.size)) ++
      [g.familyApp o (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[o].indices.length)) (vars s.families[o].indices.length 0)] from rfl,
    VExpr.instL_wrapForalls, List.map_append, VExpr.wrapForalls_append] at h
  rw [show g.recDoms o = (g.params ++ g.motives ++ g.minors ++
      insertBinders (s.families[o].indices.map (·.instL g.levels))
        (s.families.size + s.constructors.size)) ++
      [g.familyApp o (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[o].indices.length)) (vars s.families[o].indices.length 0)] from rfl] at hkl
  obtain ⟨σ', S', h⟩ := tele_obs_inv (by simp at hkl ⊢; omega) h
  simp only [List.map_cons, List.map_nil, VExpr.wrapForalls, List.foldr_cons,
    List.foldr_nil] at h
  have h := Obs.piDomOb_mem h
  simp only [Instance.familyApp, InductiveSignature.familyApp, VExpr.instL_mkApps,
    VExpr.instL] at h
  obtain ⟨keys', -, hc⟩ := wrap_of_obs_mkApps h
  obtain ⟨ci, τs, hci, hτs, hty⟩ := const_rigid_inv hIrig hc
  obtain ⟨ks, -, hks⟩ := typed_wrap_rigid hty
  have e := hfs _ _ _ _ _ _ hΔ hci hlsI (hτs _ hks)
  have e0 := congrFun e []
  rw [← VLevel.inst_inst, VLevel.eval_inst] at e0
  exact hnz _ e0.symm

/-- Mode C is impossible at a head whose major family has a result sort that is never zero
(general form: the major domain is any rigid spine with a `FamSort`). -/
theorem C_absurd_gen {T : VExpr} {dsH : List VExpr} {RH : VExpr} {I : Name}
    {lsI : List VLevel} {iargs : List VExpr} {k : Nat} {L : VLevel} {ls : List VLevel}
    {keys : List Key} {m : Nat}
    (hΔ : OnCtx Δ (env.IsType U)) (hlw : ∀ l ∈ ls, l.WF U)
    (eH : T = .wrapForalls dsH RH) (hlen : dsH.length = k + 1)
    (hkH : dsH[k]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    (hfs : FamSort env I L) (hnz : ((L.inst lsI).inst ls).IsNeverZero) (hkl : keys.length = k)
    (h : Obs' .id .empty (T.instL ls) (piCodChain keys
      (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) m fun _ => 0)))) : False := by
  have hlsI : ∀ l ∈ lsI.map (·.inst ls), l.WF U := by
    intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hlw
  have hsplit : dsH = dsH.take k ++ [.mkApps (.const I lsI) iargs] := by
    conv => lhs; rw [← List.take_append_drop k dsH]
    congr 1
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    rw [List.getElem?_eq_getElem (by omega)] at hkH
    injection hkH with hkH; rw [hkH]
  rw [eH, hsplit, VExpr.instL_wrapForalls, List.map_append, VExpr.wrapForalls_append] at h
  obtain ⟨σ', S', h⟩ := tele_obs_inv (by simp; omega) h
  simp only [List.map_cons, List.map_nil, VExpr.wrapForalls, List.foldr_cons,
    List.foldr_nil] at h
  have h := Obs.piDomOb_mem h
  simp only [VExpr.instL_mkApps, VExpr.instL] at h
  obtain ⟨keys', -, hc⟩ := wrap_of_obs_mkApps h
  obtain ⟨ci', τs, hci, hτs, hty⟩ := const_rigid_inv hIrig hc
  obtain ⟨ks, -, hks⟩ := typed_wrap_rigid hty
  have e := hfs _ _ _ _ _ _ hΔ hci hlsI (hτs _ hks)
  have e0 := congrFun e []
  rw [← VLevel.inst_inst] at e0
  exact hnz _ e0.symm

theorem liftN_wrapForalls_sort {w : VLevel} : ∀ (ds : List VExpr) (n k : Nat),
    ∃ ds' : List VExpr, (VExpr.wrapForalls ds (.sort w)).liftN n k = .wrapForalls ds' (.sort w) ∧
      ds'.length = ds.length
  | [], _, _ => ⟨[], rfl, rfl⟩
  | d :: ds, n, k => by
    obtain ⟨ds', h, l⟩ := liftN_wrapForalls_sort ds n (k + 1)
    refine ⟨d.liftN n k :: ds', ?_, by simp [l]⟩
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.liftN] at h ⊢
    rw [h]

theorem eqDoms_reverse_motive {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) :
    (g.eqDoms index).reverse[s.constructors[index].fields.length + s.constructors.size +
      (s.families.size - 1 - s.constructors[index].owner.val)]? =
      some (g.motive s.families[s.constructors[index].owner] s.constructors[index].owner.val) := by
  have hlen := g.eqDoms_length index
  have ho := s.constructors[index].owner.isLt
  rw [List.getElem?_reverse (by omega)]
  rw [show (g.eqDoms index).length - 1 - (s.constructors[index].fields.length +
    s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val)) =
    s.params.length + s.constructors[index].owner.val by omega]
  simp only [Instance.eqDoms, List.append_assoc]
  rw [List.getElem?_append_right (by simp [Instance.params]),
    List.getElem?_append_left (by simp [Instance.params, Instance.motives])]
  simp [Instance.params, Instance.motives]

theorem motive_eq {s : InductiveSignature} (g : Instance s) (o : Fin s.families.size) :
    ∃ ds0 : List VExpr, g.motive s.families[o] o.val = .wrapForalls ds0 (.sort g.targetLevel) ∧
      ds0.length = s.families[o].indices.length + 1 :=
  ⟨_, rfl, by simp [insertBinders]⟩

/-- The binder type of a binder whose domain is a telescope ending in a sort. -/
theorem binderTy_wrapForalls_sort {ds mds0 : List VExpr} {m : Nat} {w : VLevel}
    (hget : ds.reverse[m]? = some (.wrapForalls mds0 (.sort w))) (ls : List VLevel) :
    ∃ mds : List VExpr, binderTy ds ls m = .wrapForalls mds (.sort (w.inst ls)) ∧
      mds.length = mds0.length := by
  unfold binderTy
  rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  obtain ⟨ds', h, l⟩ := liftN_wrapForalls_sort (w := w) mds0 (m + 1) 0
  refine ⟨ds'.map (·.instL ls), ?_, by simp [l]⟩
  rw [h, VExpr.instL_wrapForalls]
  rfl

/-- The binder type of the motive of a generated equation is a telescope ending in the
target sort. -/
theorem motive_binderTy {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) (ls : List VLevel) :
    ∃ mds : List VExpr, binderTy (g.eqDoms index) ls
      (s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)) =
      .wrapForalls mds (.sort (g.targetLevel.inst ls)) ∧
      mds.length = s.families[s.constructors[index].owner].indices.length + 1 := by
  have hlen := g.eqDoms_length index
  have ho := s.constructors[index].owner.isLt
  have e1 : (g.eqDoms index).reverse.getD (s.constructors[index].fields.length +
      s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val)) default =
      g.motive s.families[s.constructors[index].owner] s.constructors[index].owner.val := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega)]
    rw [show (g.eqDoms index).length - 1 - (s.constructors[index].fields.length +
      s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val)) =
      s.params.length + s.constructors[index].owner.val by omega]
    simp only [Instance.eqDoms, List.append_assoc]
    rw [List.getElem?_append_right (by simp [Instance.params]),
      List.getElem?_append_left (by simp [Instance.params, Instance.motives])]
    simp [Instance.params, Instance.motives]
  obtain ⟨ds0, e0, l0⟩ : ∃ ds0 : List VExpr,
      g.motive s.families[s.constructors[index].owner] s.constructors[index].owner.val =
        .wrapForalls ds0 (.sort g.targetLevel) ∧
      ds0.length = s.families[s.constructors[index].owner].indices.length + 1 :=
    ⟨_, rfl, by simp [insertBinders]⟩
  unfold binderTy
  rw [e1, e0]
  obtain ⟨ds', h, l⟩ := liftN_wrapForalls_sort (w := g.targetLevel) ds0
    (s.constructors[index].fields.length + s.constructors.size +
      (s.families.size - 1 - s.constructors[index].owner.val) + 1) 0
  refine ⟨ds'.map (·.instL ls), ?_, by simp [l, l0]⟩
  rw [h, VExpr.instL_wrapForalls]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Validity of an ordinary recursor rule**. -/
theorem RuleValid.recursor {s : InductiveSignature} {g : Instance s} {base' installed : VEnv}
    (henv : env.Ordered) (hdr : env.DeltaRules)
    (hctor : ∀ c, IsCtor env c → env.Rigid c) (hcres : ∀ c, IsInstalledCtor env c → env.CtorResultRigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (C : CompilationData base source expanded s g [] block)
    (hinst : block.install base' = some installed) (hle : installed ≤ env)
    (index : Fin s.constructors.size) (hdf : env.defeqs (g.equation index))
    (hpm : ProjMajor env s.families[s.constructors[index].owner].name s.constructors[index].name
      s.params.length s.constructors[index].fields.length
      s.families[s.constructors[index].owner].resultLevel)
    (hex : HeadExcl env (g.recursorName s.constructors[index].owner) block.rules)
    (hfs : FamSort env s.families[s.constructors[index].owner].name
        s.families[s.constructors[index].owner].resultLevel)
    (hPF : ∀ envE, base.addConstVals expanded.typeConstants = some envE →
      s.SingletonElimination envE g.uvars g.levels →
      ∀ U Δ Γ ls, OnCtx Δ (env.IsType U) → (∀ l ∈ ls, l.WF U) → ls.length = g.uvars →
      ∀ i < s.constructors[index].fields.length,
        VExpr.bvar (s.constructors[index].fields.length - 1 - i) ∉ s.constructors[index].indices →
        ProofBinder env U Δ (g.eqDoms index) ls (s.constructors[index].fields.length - 1 - i) Γ) :
    RuleValid env (g.equation index) := by
  intro U Δ Γ ls u hΔ hlw hlen _ ihT _ ihL _ ihR
  have hl := g.equation_lhs_eq index
  obtain ⟨body, hr⟩ := g.equation_rhs_eq index
  have hlsP : (VLevel.params g.uvars).map (·.inst ls) = ls := VLevel.inst_map_id hlen
  have hcl := henv.closed.2 hdf
  -- the recursor
  have hrec : g.recursor s.constructors[index].owner ∈ block.recursors := by
    rw [C.ordinary_recursors]; exact List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩
  have hci := hle.constants (VInductBlock.install_recursor_lookup hinst hrec)
  obtain ⟨RH, eH⟩ := g.recursorType_eq_hi s.constructors[index].owner
  have hlenH : (g.recDoms s.constructors[index].owner).length = (g.eqLead index).length + 1 := by
    rw [g.recDoms_length, eqLead_length_owner C]
  have hkH := g.recDoms_major s.constructors[index].owner
  rw [← eqLead_length_owner C] at hkH
  -- the constructor and its family
  have hcisN : IsInstalledCtor env s.constructors[index].name :=
    ⟨_, hdf, _, _, _, by rw [hl, VExpr.stripLams_wrapLams, VExpr.mkApps_snoc]; rfl⟩
  have hcis : IsCtor env s.constructors[index].name := .inl hcisN
  obtain ⟨ci, hci', F, lsF, hF, -, hrigF⟩ := hcres _ hcisN
  obtain ⟨fc, hfc, hfcn, lsc, hfch⟩ := C.ordinary_ctor index
  have hfc' := hle.constants (VInductBlock.install_ctor_lookup hinst (by rw [C.ctors]; exact hfc))
  rw [hfcn, hci'] at hfc'
  cases hfc'
  rw [hfch] at hF
  cases hF
  have hcf : CtorFam env s.constructors[index].name s.families[s.constructors[index].owner].name :=
    ⟨_, _, hci', hfch⟩
  have huniq := recursor_uniq C index hex
  have hpm' : ProjMajor env s.families[s.constructors[index].owner].name
      s.constructors[index].name (eqMs index).length (eqFs index).length
      s.families[s.constructors[index].owner].resultLevel := by
    simpa [eqMs, eqFs, InductiveSignature.length_vars] using hpm
  obtain ⟨envE, hE, hadm⟩ := C.admissible
  rcases hadm.elimination with hnz | hsmall | hsing
  · -- data families: mode C is impossible
    have hnz' := hnz s.families[s.constructors[index].owner]
      (Array.mem_toList_iff.2 (Array.getElem_mem s.constructors[index].owner.isLt))
    exact sound_pat henv hΔ hdf hl hr (g.equation_cov index) hlsP hcl.1.1 hcl.2.1 hci eH hlenH hkH
      hrigF hcf hcis (hpm'.majorFam (.inl (by rw [← VLevel.inst_inst]; exact hnz'.inst)))
      (hctor _ hcis) hctor
      hpctor hdr huniq
      (fun keys hkl hobs => absurd (by rw [eH] at hobs; exact hobs)
        (fun h => recursor_C_absurd hΔ hlw hrigF hfs hnz' (by rw [hlenH, hkl]) h))
      ihL ihR (.extra hdf hlw hlen)
  · -- small elimination: the right-hand side has no observations
    obtain ⟨mds, emds, lmds⟩ := motive_binderTy g index ls
    have hcl' : ((g.equation index).type.instL ls).ClosedN := hcl.1.2.instL
    refine sound_pat_empty henv hΔ hdf hl hr hlsP hcl.1.1 hcl.2.1 (hctor _ hcis) hctor hpctor hdr
      huniq hci eH hlenH hkH hpm.weak ihL.1 ihR fun σ S W tv o => ?_
    refine rhs_empty_motive henv hΔ (doms := (g.eqDoms index).map (·.instL ls))
      (by rw [g.equation_type_eq, VExpr.instL_wrapForalls]) (by rw [hr, instL_wrapLams])
      hcl' ihT.2 (by simp only [VExpr.instL_mkApps, VExpr.instL]; rfl)
      (by have := lookup_binderTy (Γ := []) (ls := ls) (doms := g.eqDoms index)
            (x := s.constructors[index].fields.length + s.constructors.size +
              (s.families.size - 1 - s.constructors[index].owner.val))
            (by rw [g.eqDoms_length]; have := s.constructors[index].owner.isLt; omega)
          rw [List.append_nil, emds] at this; exact this)
      (by have h := C.model.constructorArity s.constructors[index] (by simp)
          rw [lmds]
          simp only [Instance.eqIndices, List.length_append, List.length_map,
            List.length_singleton, Fin.getElem_fin] at h ⊢
          omega)
      (funext fun v => by
        rw [VLevel.eval_inst]; exact (VLevel.equiv_def.1 hsmall _).trans rfl)
      ihR.1 W tv o
  · -- singleton elimination: mode C with propositional major-only fields
    have hpf : ∀ x < (g.eqDoms index).length,
        (∀ i : Nat, (g.eqLead index)[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v (((g.eqDoms index).map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ (((g.eqDoms index).map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy (g.eqDoms index) ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs env U Δ v vS (binderTy (g.eqDoms index) ls x) τ →
          ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0] := by
      intro x hx hnl v vS Wv tvv
      have notLead : VExpr.bvar x ∉ g.eqLead index := fun hy => by
        obtain ⟨i, hi, e⟩ := List.getElem_of_mem hy
        exact hnl i (List.getElem?_eq_some_iff.2 ⟨hi, e⟩)
      have hdl := g.eqDoms_length index
      have hxf : x < s.constructors[index].fields.length := by
        refine Nat.lt_of_not_le fun h => notLead (List.mem_append_left _ (InductiveSignature.mem_vars h ?_))
        omega
      have hidx : VExpr.bvar (s.constructors[index].fields.length - 1 -
          (s.constructors[index].fields.length - 1 - x)) ∉ s.constructors[index].indices := by
        rw [show s.constructors[index].fields.length - 1 -
          (s.constructors[index].fields.length - 1 - x) = x by omega]
        intro hm
        apply notLead
        refine List.mem_append_right _ (List.mem_map.2 ⟨_, hm, ?_⟩)
        have hxf' := hxf
        simp only [Fin.getElem_fin] at hxf'
        simp [VExpr.instL, VExpr.liftN, liftVar, hxf']
      have := hPF envE hE hsing.1 U Δ Γ ls hΔ hlw hlen
        (s.constructors[index].fields.length - 1 - x) (by omega) hidx v vS Wv tvv
      rwa [show s.constructors[index].fields.length - 1 -
        (s.constructors[index].fields.length - 1 - x) = x by omega] at this
    refine sound_pat henv hΔ hdf hl hr (g.equation_cov index) hlsP hcl.1.1 hcl.2.1 hci eH hlenH
      hkH hrigF hcf hcis (hpm'.majorFam (.inr hpf)) (hctor _ hcis)
      hctor hpctor hdr huniq
      (fun keys hkl hobs => ⟨fun df' ls' hdf' hh => ?_, hpf⟩) ihL ihR
      (.extra hdf hlw hlen)
    · have hm := hex df' hdf' ls' hh
      rw [C.ordinary_rules] at hm
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
      have h1 := hsing.1.2.1
      have : j = index := Fin.ext (by have := j.isLt; have := index.isLt; omega)
      rw [this]

end Model
end VEnv
end Lean4Lean