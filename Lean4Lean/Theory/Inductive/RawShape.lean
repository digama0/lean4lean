import Lean4Lean.Theory.Inductive.Formation

/-! Constructor skeleton correspondence ignores field-domain and projection
implementation choices while retaining forall binders, constant-headed application
spines, and literal common-parameter variables. It asserts no positivity. -/

namespace Lean4Lean
namespace VExpr

inductive RawShapeRel : VExpr → VExpr → Prop
  | bvar : RawShapeRel (.bvar i) (.bvar i)
  | const : RawShapeRel (.const name levels) (.const name levels)
  | sort : RawShapeRel (.sort u) (.sort v)
  | proj : RawShapeRel (.proj name index major) (.proj name' index' major')
  | lam : RawShapeRel (.lam domain body) (.lam domain' body')
  | forallE : RawShapeRel body body' → RawShapeRel (.forallE domain body) (.forallE domain' body')
  | app : RawShapeRel fn fn' → RawShapeRel arg arg' → RawShapeRel (.app fn arg) (.app fn' arg')
  | lamApp : RawShapeRel (mkApps (.lam domain body) args) (mkApps (.lam domain' body') args')

theorem RawShapeRel.refl (e : VExpr) : RawShapeRel e e := by
  induction e with
  | bvar => exact .bvar
  | const => exact .const
  | sort => exact .sort
  | proj => exact .proj
  | lam => exact .lam
  | forallE _ _ _ ih => exact .forallE ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2

theorem RawShapeRel.symm (H : RawShapeRel e e') : RawShapeRel e' e := by
  induction H with
  | bvar => exact .bvar
  | const => exact .const
  | sort => exact .sort
  | proj => exact .proj
  | lam => exact .lam
  | forallE _ ih => exact .forallE ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lamApp => exact .lamApp

theorem RawShapeRel.liftN (H : RawShapeRel e e') :
    RawShapeRel (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k with
  | bvar => exact .bvar
  | const => exact .const
  | sort => exact .sort
  | proj => exact .proj
  | lam => exact .lam
  | forallE _ ih => exact .forallE ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lamApp => simpa only [VExpr.liftN_mkApps, VExpr.liftN] using (RawShapeRel.lamApp)

private theorem raw_head_mkApps (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => simpa only [mkApps, List.foldl_cons, getAppFnArgs_app] using ih (.app fn a)

theorem RawShapeRel.bvar_inv (H : RawShapeRel e e') (h : e' = .bvar i) : e = .bvar i := by
  cases H <;> try cases h <;> try rfl
  case lamApp =>
    have hh := congrArg (fun e => e.getAppFnArgs.1) h
    rw [raw_head_mkApps] at hh
    cases hh

theorem RawShapeRel.forallE_inv (H : RawShapeRel e e') (h : e' = .forallE domain body) :
    ∃ domain' body', e = .forallE domain' body' ∧ RawShapeRel body' body := by
  cases H <;> try { cases h }
  case forallE hbody => cases h; exact ⟨_, _, rfl, hbody⟩
  case lamApp =>
    have hh := congrArg (fun e => e.getAppFnArgs.1) h
    rw [raw_head_mkApps] at hh
    cases hh

theorem RawShapeRel.wrapForalls (H : RawShapeRel e e') (domains : List VExpr) :
    RawShapeRel (VExpr.wrapForalls domains e) (VExpr.wrapForalls domains e') := by
  induction domains with
  | nil => exact H
  | cons _ _ ih => exact .forallE ih

theorem RawShapeRel.wrapForalls_inv (H : RawShapeRel e (VExpr.wrapForalls domains result)) :
    ∃ domains' result', e = VExpr.wrapForalls domains' result' ∧
      domains'.length = domains.length ∧ RawShapeRel result' result := by
  induction domains generalizing e with
  | nil => exact ⟨[], e, rfl, rfl, H⟩
  | cons d ds ih =>
    obtain ⟨d', b', rfl, hb⟩ := H.forallE_inv rfl
    obtain ⟨ds', r', rfl, hlen, hr⟩ := ih hb
    exact ⟨d' :: ds', r', rfl, by simp [hlen], hr⟩

theorem RawShapeRel.const_spine_inv (H : RawShapeRel e e')
    (hhead : e'.getAppFnArgs.1 = .const name levels) :
    e.getAppFnArgs.1 = .const name levels ∧
      List.Forall₂ RawShapeRel e.getAppFnArgs.2 e'.getAppFnArgs.2 := by
  induction H with
  | const => exact ⟨hhead, .nil⟩
  | @app fn fn' arg arg' hfn harg ihfn _ =>
    simp only [getAppFnArgs_app] at hhead ⊢
    obtain ⟨hf, hargs⟩ := ihfn hhead
    refine ⟨hf, ?_⟩
    have happ : ∀ {as bs}, List.Forall₂ RawShapeRel as bs →
        List.Forall₂ RawShapeRel (as ++ [arg]) (bs ++ [arg']) := by
      intro as bs h
      induction h with
      | nil => exact .cons harg .nil
      | cons h _ ih => exact .cons h ih
    exact happ hargs
  | lamApp => rw [raw_head_mkApps] at hhead; cases hhead
  | bvar | sort | proj | lam | forallE => cases hhead

end VExpr

/-- Raw constructor skeletons are invariant under changes confined to binder
domains and opaque projection calls. No index support equality is needed. -/
theorem VInductDecl.RawCtorShape.of_rawShapeRel
    {decl : VInductDecl} {type : VInductiveType} {ctor ctor' : VConstVal}
    (hrel : VExpr.RawShapeRel ctor'.type ctor.type)
    (hshape : decl.RawCtorShape type ctor) : decl.RawCtorShape type ctor' := by
  obtain ⟨ds, result, hctor, hlen, hvalid, hhead⟩ := hshape
  rw [hctor] at hrel
  obtain ⟨ds', result', hctor', hlen', hr⟩ := hrel.wrapForalls_inv
  obtain ⟨hhead', hargs⟩ := hr.const_spine_inv hhead
  obtain ⟨family, hfamily, htarget, ls, hfn, hls, hcount, hparams⟩ := hvalid
  have hlength : result'.getAppFnArgs.2.length = result.getAppFnArgs.2.length := by
    have hl : ∀ {as bs}, List.Forall₂ VExpr.RawShapeRel as bs → as.length = bs.length := by
      intro as bs h
      induction h with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    exact hl hargs
  have hparams' : result'.getAppFnArgs.2.take decl.nparams = result.getAppFnArgs.2.take decl.nparams := by
    apply List.ext_getElem
    · simp [hlength]
    · intro i hi hi'
      have ht : i < result.getAppFnArgs.2.length := by simp only [List.length_take] at hi'; omega
      have hs : i < result'.getAppFnArgs.2.length := by rw [hlength]; exact ht
      have hr := List.Forall₂.getElem_of hargs i hs ht
      have hm := List.getElem_mem (l := result.getAppFnArgs.2.take decl.nparams) hi'
      simp only [List.getElem_take] at hm
      change (result.getAppFnArgs.2[i]'ht) ∈ result.getAppFnArgs.2.take decl.nparams at hm
      change result.getAppFnArgs.2.take decl.nparams = _ at hparams
      rw [hparams] at hm
      simp only [VInductDecl.paramVars, List.mem_map] at hm
      obtain ⟨j, _, hj⟩ := hm
      have heq := hr.bvar_inv hj.symm
      simpa only [List.getElem_take] using heq.trans hj
  refine ⟨ds', result', hctor', by omega, ?_, hhead'⟩
  refine ⟨family, hfamily, htarget, VLevel.params decl.uvars, ?_, by simp, ?_, ?_⟩
  · have hn := (VExpr.const.inj (hhead.symm.trans hfn)).1
    simpa [hn, VExpr.getAppFnArgs] using hhead'
  · change result'.getAppFnArgs.2.length = _
    rw [hlength]
    exact hcount
  · change result'.getAppFnArgs.2.take decl.nparams = _
    rw [hparams']
    simpa [hlen', VExpr.getAppFnArgs] using hparams

end Lean4Lean
