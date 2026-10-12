import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaArgs

/-! # Uniqueness of the lead of an ι clause

`IotaStatic.lead_unique`: the static data of an ι rule read off its recursor's type determine the
leading arguments of the clause: the minor premise of the constructor is the last domain before
the indices ending in the constructor, and the indices it records determine the lead's index
entries independently of the split into parameters and motives. Hence `LeadUniq` holds for every
lead with `IotaStatic` data (`IotaStatic.leadUniq`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

theorem piBody_wrapForalls_app : ∀ (ds : List VExpr) (f a : VExpr),
    (VExpr.wrapForalls ds (.app f a)).piBody = .app f a
  | [], _, _ => rfl
  | _ :: ds, f, a => by
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.piBody]
    exact piBody_wrapForalls_app ds f a

theorem piBinders_wrapForalls_app : ∀ (ds : List VExpr) (f a : VExpr),
    (VExpr.wrapForalls ds (.app f a)).piBinders = ds
  | [], _, _ => rfl
  | d :: ds, f, a => by
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.piBinders]
    exact congrArg (d :: ·) (piBinders_wrapForalls_app ds f a)

theorem endsInCtor_of {c : Name} {Dm args margs : List VExpr} {f : VExpr} {lsC : List VLevel} :
    EndsInCtor c (.wrapForalls Dm (.mkApps f (args ++ [.mkApps (.const c lsC) margs]))) := by
  refine ⟨f, args, lsC, margs, ?_⟩
  rw [VExpr.mkApps_snoc, piBody_wrapForalls_app]

theorem EndsInCtorAt.endsInCtor {c : Name} {p : Nat} {A : VExpr} (h : EndsInCtorAt c p A) :
    EndsInCtor c A := by
  obtain ⟨Dm, args, lsC, margs, rfl⟩ := h
  exact endsInCtor_of

theorem VExpr.mkApps_bvar_head_inj {i j : Nat} {a b : List VExpr}
    (h : VExpr.mkApps (.bvar i) a = VExpr.mkApps (.bvar j) b) : i = j := by
  have := congrArg VExpr.getAppFn h
  simp only [VExpr.getAppFn_mkApps, VExpr.getAppFn] at this
  injection this

theorem IotaStatic.lead_unique {ci : VConstant} {ctor : Name} {k nind nf : Nat}
    {doms dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel} {iargs lead : List VExpr}
    {doms' dsH' : List VExpr} {RH' : VExpr} {I' : Name} {lsI' : List VLevel}
    {iargs' lead' : List VExpr}
    (h1 : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (h2 : IotaStatic ci ctor k nind nf doms' dsH' RH' I' lsI' iargs' lead') : lead' = lead := by
  obtain ⟨-, eH, hl, -, np, pos, nih, mv, pm, cI, Dm, margs, lsC, hnp, hpk, hcl, hDml, hpm, hmv,
    ⟨rargs, hRH⟩, hpos, rfl, hmax⟩ := h1
  obtain ⟨-, eH', hl', -, np', pos', nih', mv', pm', cI', Dm', margs', lsC', hnp', hpk', hcl',
    hDml', hpm', hmv', ⟨rargs', hRH'⟩, hpos', rfl, hmax'⟩ := h2
  obtain ⟨rfl, eR⟩ := VExpr.wrapForalls_inj_of_length (hl.trans hl'.symm) (eH.symm.trans eH')
  -- the motive
  have hpp' : pm = pm' := by
    have := VExpr.mkApps_bvar_head_inj (hRH.symm.trans (eR.trans hRH'))
    omega
  subst hpp'
  -- the minor's position
  have hend : ∀ {pos Dm mv margs lsC} {cI : List VExpr} {nih np : Nat}, mv = pos - 1 - pm + Dm.length →
      EndsInCtorAt ctor (pos - 1 - pm) (.wrapForalls Dm (.mkApps (.bvar mv)
        (cI.map (fun e => (e.liftN nih).liftN (pos - np) (nf + nih)) ++
          [.mkApps (.const ctor lsC) margs]))) := by
    intro pos Dm mv margs lsC cI nih np hmv
    subst hmv
    exact ⟨Dm, _, lsC, margs, rfl⟩
  have hpp : pos = pos' := by
    rcases Nat.lt_trichotomy pos pos' with h | h | h
    · exact absurd (hend hmv') (hmax pos' _ h hpk' hpos')
    · exact h
    · exact absurd (hend hmv) (hmax' pos _ h hpk hpos)
  subst hpp
  have e := Option.some.inj (hpos.symm.trans hpos')
  rw [VExpr.mkApps_snoc, VExpr.mkApps_snoc] at e
  have hDl : Dm.length = Dm'.length := by
    have := congrArg VExpr.piBinders e
    rw [piBinders_wrapForalls_app, piBinders_wrapForalls_app] at this
    rw [this]
  obtain ⟨rfl, e2⟩ := VExpr.wrapForalls_inj_of_length hDl e
  have hnih : nih = nih' := by omega
  subst hnih
  injection e2 with e3 e4
  have e5 := congrArg VExpr.getAppArgs e3
  simp only [VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append] at e5
  -- the recorded indices
  have hlen : cI.length = cI'.length := by omega
  congr 1
  apply List.ext_getElem (by simp [hlen])
  intro j hj hj'
  simp only [List.getElem_map]
  have eX := e5
  have ej := List.getElem_of_eq eX (i := j) (by simpa using hj')
  simp only [List.getElem_map] at ej
  -- move the inner lift outward and cancel it
  have comm : ∀ (x : VExpr) (m : Nat),
      (x.liftN nih).liftN m (nf + nih) = (x.liftN m nf).liftN nih := by
    intro x m
    have := VExpr.liftN'_comm x m nih nf 0 (Nat.zero_le _)
    rw [Nat.add_comm nih nf] at this
    exact this.symm
  rw [comm, comm, VExpr.liftN_inj] at ej
  have a1 : ∀ (x : VExpr) (q : Nat), q ≤ pos →
      x.liftN (k - q) nf = (x.liftN (pos - q) nf).liftN (k - pos) nf := by
    intro x q hq
    rw [VExpr.liftN'_liftN_hi]; congr 1; omega
  rw [a1 _ np' hnp', a1 _ np hnp, ej]

theorem IotaStatic.leadUniq {ci : VConstant} {ctor : Name} {k nind nf : Nat}
    {doms dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel} {iargs lead : List VExpr}
    (h : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead) :
    LeadUniq ci ctor k nind nf lead :=
  fun _ _ _ _ _ _ _ h' => h.lead_unique h'

end Model
end VEnv
end Lean4Lean
