import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound

/-! # Static notions for the soundness of ι rules

* `FamSort env I l`: the type observations of the constant `I` end in the sort `l` only
  (the family's recorded result sort), at every instantiation;
* `ProofBinder`: a binder of a rule telescope whose type is a proposition at every typed
  valuation, with no observations of its own;
* `ProjMajor`: the projection facts of a rule's major family, from which `MajorFam` follows
  (`ProjMajor.majorFam`);
* `C_absurd_gen`: mode C is impossible at a recursor whose major family has a result sort that
  is never zero.

These notions are stated independently of the generator syntax. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The constant `I` has only the sort `l` at the ends of the chain observations of its type,
at every instantiation. -/
def FamSort (env : VEnv) (I : Name) (l : VLevel) : Prop :=
  ∀ (U : Nat) (Δ : List VExpr) (ci : VConstant) (lsI : List VLevel) (ks : List Key)
    (z : List Nat → Nat), OnCtx Δ (env.IsType U) → env.constants I = some ci →
    (∀ l ∈ lsI, l.WF U) →
    Obs env U Δ .id .empty (ci.type.instL lsI) (piCodChain ks (.sort z)) → z = (l.inst lsI).eval

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
equivalent to `L`. -/
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
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ |
    ⟨_, _, _, _, keys', r, e, _, _, _, _, _, _, ⟨_, _, _, rfl, _⟩, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · rw [← e] at hty; exact ⟨ci, τs, hci, hτs, hty⟩
  · exact absurd (by rw [hlhs]; rfl) (hrig.defeqs df hdf _)
  · have hrn : r.NotApp := by
      rcases hr with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨rfl, rfl⟩ := wrap_inj e trivial hrn
    rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs df hdf lsP)
  · exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  · cases (wrap_inj e trivial trivial).2
  · cases (wrap_inj e trivial trivial).2
  · cases (wrap_inj e trivial trivial).2

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

end Model
end VEnv
end Lean4Lean
