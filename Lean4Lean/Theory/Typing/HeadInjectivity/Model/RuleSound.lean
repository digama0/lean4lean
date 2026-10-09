import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleLemmas
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EtaBind

/-! # Soundness of a pattern rule (the `extra` case at rules with a constructor major)

`sound_pat`: for a stored rule `lhs ≡ rhs` whose left-hand side is a lambda telescope over a
constant head applied to leading arguments and a constructor major, given the rule's
syntactic facts (pattern, binder coverage, the family of the major domain in the head's type,
the constructor's family, rule uniqueness per head and constructor, and in mode C the
propositional typing of the major-only fields), the soundness of the instantiated rule
follows from the soundness and semantic typing (`HTS`) of its typing premises (section 4.1 of
the design notes, computation rules). For a major
of a projection-registered family (`MajorFam`) the rule clause is identified from
the head type and the fields are bound by the eta binding (never-zero entries; right to left via
`eta_field_cls` and the field observations of the major, `ctor_field_obs`) or the proof binding. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem DomsSD.left : ∀ {pre post : List VExpr} {Γ},
    DomsSD env U Δ Γ (pre ++ post) → DomsSD env U Δ Γ pre
  | [], _, _, _ => .nil
  | _ :: _, _, _, .cons h h' => .cons h (DomsSD.left h')

theorem TypeChain.tyCls_subst (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (W : Ctx.SubstEq env U Δ v v Γ) (h : env.TypeChain U Γ X Y) :
    TyCls env U Δ (X.subst v) = TyCls env U Δ (Y.subst v) := by
  induction h with
  | single h => let ⟨_, h⟩ := h; exact TyCls.eq_of_defeq (h.substDF henv W.wf hΔ W)
  | tail _ h ih => let ⟨_, h⟩ := h; exact ih.trans (TyCls.eq_of_defeq (h.substDF henv W.wf hΔ W))

/-- All constructor observations of a constructor spine with the keys `keys`. -/
def ctorObs (c : Name) (ℓs : List (List Nat → Nat)) (keys : List Key) : List Ob :=
  .ctorHead c ℓs keys.length :: (List.range keys.length).flatMap fun i =>
    match keys[i]? with
    | some k => .ctorArg i k.2.1 :: k.2.2.map (.ctorArgOb i (keys.take i))
    | none => []

theorem ctorObs_end (h : r ∈ ctorObs c ℓs keys) : CtorEnd c ℓs keys r := by
  simp only [ctorObs, List.mem_cons, List.mem_flatMap, List.mem_range] at h
  rcases h with rfl | ⟨i, hi, h⟩
  · exact .inl rfl
  · rw [List.getElem?_eq_getElem hi] at h
    simp only [List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨k, hk, rfl⟩
    · exact .inr (.inl ⟨i, hi, rfl⟩)
    · exact .inr (.inr ⟨i, hi, k, hk, rfl⟩)

theorem mem_ctorObs_head : .ctorHead c ℓs keys.length ∈ ctorObs c ℓs keys := List.mem_cons_self ..

theorem mem_ctorObs_arg (hi : i < keys.length) :
    .ctorArg i (keys[i]).2.1 ∈ ctorObs c ℓs keys := by
  simp only [ctorObs, List.mem_cons, List.mem_flatMap, List.mem_range]
  refine .inr ⟨i, hi, ?_⟩
  rw [List.getElem?_eq_getElem hi]; exact List.mem_cons_self ..

theorem mem_ctorObs_argOb (hi : i < keys.length) (hk : k ∈ (keys[i]).2.2) :
    .ctorArgOb i (keys.take i) k ∈ ctorObs c ℓs keys := by
  simp only [ctorObs, List.mem_cons, List.mem_flatMap, List.mem_range]
  refine .inr ⟨i, hi, ?_⟩
  rw [List.getElem?_eq_getElem hi]
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem hk)

/-- The instantiated pattern of a rule. -/
theorem pat_instL {df : VDefEq} {fs : List Nat}
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body) (hlsP : lsP.map (·.inst ls) = ls) :
    df.lhs.instL ls = .wrapLams (doms.map (·.instL ls)) (.mkApps (.const n ls)
      (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
        (ms.map (·.instL ls) ++ fs.map .bvar)])) ∧
    df.rhs.instL ls = .wrapLams (doms.map (·.instL ls)) (body.instL ls) := by
  refine ⟨?_, by rw [hr, instL_wrapLams]⟩
  rw [hl, instL_wrapLams]
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, hlsP]

/-- Demands for the arguments of a spine: a bare rule variable demands its observations. -/
def argDemand (doms : Nat) (Lx : Nat → List Ob) : VExpr → List Ob
  | .bvar x => if x < doms then Lx x else []
  | _ => []

theorem argDemand_ok {vS : ObSets} {Lx : Nat → List Ob} (hLx : ∀ x < nd, vS x = listSet (Lx x))
    (σ : VExpr.Subst) : ∀ args : List VExpr, List.Forall₂ (fun K a => ∀ y ∈ K, Obs' σ vS a y)
      (args.map (argDemand nd Lx)) args
  | [] => .nil
  | a :: as => by
    refine .cons ?_ (argDemand_ok hLx σ as)
    intro y hy
    cases a with
    | bvar x =>
      simp only [argDemand] at hy
      split at hy
      · rename_i hx; exact .bvar (by rw [hLx x hx]; exact hy)
      · cases hy
    | _ => cases hy

theorem closedN_wrapLams : ∀ {ds : List VExpr} {b : VExpr} {k : Nat},
    (VExpr.wrapLams ds b).ClosedN k →
      b.ClosedN (k + ds.length) ∧ ∀ i (h : i < ds.length), (ds[i]).ClosedN (k + i)
  | [], _, _, h => ⟨h, nofun⟩
  | d :: ds, b, k, h => by
    simp only [VExpr.wrapLams, List.foldr_cons] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := closedN_wrapLams (ds := ds) h2
    refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using h3, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := h4 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem binderTy_closed {doms : List VExpr} (h : ∀ i (h : i < doms.length), (doms[i]).ClosedN i)
    (hx : x < doms.length) : (binderTy doms ls x).ClosedN doms.length := by
  have hx' : x < doms.reverse.length := by simpa using hx
  simp only [binderTy, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx',
    Option.getD_some, List.getElem_reverse]
  have := (h (doms.length - 1 - x) (by omega)).liftN (n := x+1) (j := 0)
  have e : doms.length - 1 - x + (x + 1) = doms.length := by omega
  rw [e] at this
  exact this.instL

/-- The body of a semantically typed lambda telescope is sound, and its domains are. -/
theorem HTS.wrapLams_body : ∀ {ds : List VExpr} {Γ b P},
    HTS env U Δ Γ (.wrapLams ds b) P → SoundAt env U Δ Γ (.wrapLams ds b) (.wrapLams ds b) P →
    ∃ B, SoundAt env U Δ (ds.reverse ++ Γ) b b B ∧ DomsSD env U Δ Γ ds
  | [], _, _, _, _, h => ⟨_, h, .nil⟩
  | A :: ds, Γ, b, P, H, _ => by
    obtain ⟨B, u, v, -, hA, hb, hsb, -, -⟩ := H.lam_inv rfl
    obtain ⟨B', h1, h2⟩ := HTS.wrapLams_body hb hsb.2
    exact ⟨B', by simpa [List.reverse_cons, List.append_assoc] using h1, .cons hA h2⟩

theorem liftN_subst_shift (D : VExpr) (σ : VExpr.Subst) :
    ∀ x, (D.liftN (x+1)).subst σ = D.subst fun i => σ (i + (x+1))
  | 0 => by
    rw [show D.liftN 1 = D.lift from rfl, VExpr.lift_subst]; rfl
  | x+1 => by
    rw [show D.liftN (x+1+1) = (D.liftN (x+1)).lift by
      rw [VExpr.lift, VExpr.liftN_liftN]]
    rw [VExpr.lift_subst, liftN_subst_shift D σ.tail x]
    rfl

theorem wrap_le (h : o ≼ o') : wrap ks o ≼ wrap ks o' := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact Ob.Le.app' Covers.refl ih

theorem SubstEq.entry_typed : ∀ {L : List VExpr} {v : VExpr.Subst} {x : Nat},
    Ctx.SubstEq env U Δ v v (L ++ Γ) → (hx : x < L.length) →
    ∃ u, env.HasType U (L.drop (x+1) ++ Γ) (L[x]) (.sort u)
  | A :: L, v, 0, .cons _ hA _, _ => ⟨_, hA⟩
  | A :: L, v, x+1, .cons W _ _, hx => SubstEq.entry_typed W (by simpa using hx)

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The domain class of a bare-variable argument is the class of the variable's type. -/
theorem bvar_dom_cls (W : Ctx.SubstEq env U Δ v v Γ) (H : HTS env U Δ Γ (.bvar x) A')
    (hL : Lookup Γ x A) : TyCls env U Δ (A'.subst v) = TyCls env U Δ (A.subst v) := by
  obtain ⟨A₀, hL₀, h⟩ := H.bvar_chain rfl
  cases hL.uniq hL₀
  rcases h with rfl | h
  · rfl
  · exact (TypeChain.tyCls_subst henv hΔ W h).symm

/-- The family indicator at the major domain of a closed head type typed in a context with a
typed valuation. -/
theorem major_indicator_gen {Th : VExpr} {ls : List VLevel} {uH : VLevel} {Γ0 : List VExpr}
    {σ0 : VExpr.Subst} {S0 : ObSets} {dsH : List VExpr} {RH : VExpr} {k : Nat} {I : Name}
    {lsI : List VLevel} {iargs : List VExpr} {τ₀ : List Ob} {o : Ob}
    (hTcl : Th.ClosedN) (hT : HTS env U Δ Γ0 Th (.sort uH))
    (W0 : Ctx.SubstEq env U Δ σ0 σ0 Γ0) (tv0 : TV env U Δ Γ0 σ0 S0)
    (eT : Th = .wrapForalls (dsH.map (·.instL ls)) (RH.instL ls)) (hlen : dsH.length = k + 1)
    (hk : dsH[k]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    {keys : List Key} (hkeys : keys.length = k + 1)
    (hτ₀ : ∀ τ ∈ τ₀, Obs' .id .empty Th τ)
    (hty : TypedOb env U Δ cv (wrap keys o) τ₀) :
    ∃ u : VLevel, Obs' .id .empty Th (piCodChain (keys.take k)
      (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval))) := by
  have hk' : k < dsH.length := by omega
  have hsplit : dsH.map (·.instL ls) =
      (dsH.take k).map (·.instL ls) ++ [(VExpr.mkApps (.const I lsI) iargs).instL ls] := by
    conv => lhs; rw [← List.take_append_drop k dsH]
    rw [List.map_append]; congr 1
    rw [List.drop_eq_getElem_cons hk', List.drop_eq_nil_of_le (by omega)]
    simp only [List.map_cons, List.map_nil]
    rw [List.getElem?_eq_getElem hk'] at hk; injection hk with hk; rw [hk]
  have hτ₀' : ∀ τ ∈ τ₀, Obs' σ0 S0 Th τ := fun τ hτ => (Obs.closed_iff_id hTcl).2 (hτ₀ τ hτ)
  rw [eT] at hT hτ₀' hTcl ⊢
  have hpi := hT.piSD
  obtain ⟨σH, SH, hkH, -⟩ := tele_unwind henv hΔ hpi W0 tv0
    (by simp [hkeys, hlen]) hty hτ₀'
  rw [hsplit] at hkH hT
  have hkeys' : keys = keys.take k ++ keys.drop k := (List.take_append_drop k keys).symm
  rw [hkeys'] at hkH
  obtain ⟨σ₁, S₁, hk1, -⟩ := hkH.split (by simp; omega)
  have hpi' := hT.piSD
  obtain ⟨W₁, tv₁⟩ := hk1.typed henv hΔ (DomsSD.left hpi'.doms) W0 tv0
  obtain ⟨u, hA, -⟩ := HTS.tele_dom (pre := (dsH.take k).map (·.instL ls)) (post := [])
    (by simpa using hT)
  simp only [VExpr.instL] at hA W₁ tv₁
  have hr := spine_rigid_obs henv hΔ hA W₁ tv₁ hIrig
  simp only [List.length_map] at hr
  have hd : Obs' σ₁ S₁ (.wrapForalls [(VExpr.mkApps (.const I lsI) iargs).instL ls] (RH.instL ls))
      (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval)) := by
    simp only [VExpr.wrapForalls, List.foldr_cons, List.foldr_nil, VExpr.instL_mkApps,
      VExpr.instL]
    exact Obs.piDomOb hr
  have := tele_obs hk1 hd
  refine ⟨u, ?_⟩
  rw [hsplit, VExpr.wrapForalls_append] at hTcl ⊢
  exact (Obs.closed_iff_id hTcl).1 this

/-- Binding a variable that occurs bare among the leading arguments, from its key at its
first occurrence. -/
theorem bind_lead {doms lead : List VExpr} {ls : List VLevel} {v : VExpr.Subst} {vS : ObSets}
    {infoL : List (Key × VExpr)} {Lx : Nat → List Ob} {x i : Nat}
    (Wv : Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ))
    (hLx : ∀ x < doms.length, vS x = listSet (Lx x)) (hx : x < doms.length)
    (hinfoL : List.Forall₂ (KeyData env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS) infoL
      (lead.map (·.instL ls)))
    (hKsi : List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2)
      ((lead.map (·.instL ls)).map (argDemand doms.length Lx)) infoL)
    (hi : lead[i]? = some (.bvar x)) :
    ∃ k : Key, (infoL.map (·.1))[i]? = some k ∧
      TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst v)) k.2.1 ∧ k.2.1 (v x) ∧
      vS x = listSet k.2.2 := by
  have hil : i < lead.length := (List.getElem?_eq_some_iff.1 hi).1
  have hlen := List.Forall₂.length_eq hinfoL
  have hi' : i < infoL.length := by simp at hlen; omega
  have ha : (lead.map (·.instL ls))[i]'(by simpa using hil) = .bvar x := by
    simp only [List.getElem_map]
    rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
  obtain ⟨_, hkd⟩ := List.forall₂_getElem_exists hinfoL i hi'
  obtain ⟨_, hks⟩ := List.forall₂_getElem_exists hKsi i (by simpa using hil)
  rw [ha] at hkd
  simp only [List.getElem_map, ha, argDemand, hx, ite_true] at hks
  obtain ⟨h1, h2, h3, h4, -⟩ := hkd
  have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
  have eD := bvar_dom_cls henv hΔ Wv h4 hL
  have hvx := (Wv.lookup hL).hasType.1
  refine ⟨(infoL[i]).1, by simp [hi'], ?_, ?_, ?_⟩
  · rw [h1, h3, eD]; exact .of_hasType hvx
  · rw [h1]; exact ElCls.self
  · rw [hLx x hx]
    funext y; apply propext; constructor
    · exact fun h => hks y h
    · intro h; have := Obs.bvar_iff.1 (h2 y h); rwa [hLx x hx] at this

/-- Binding a field variable from the constructor observations of the major. -/
theorem bind_field {doms margs : List VExpr} {ls : List VLevel} {v : VExpr.Subst} {vS : ObSets}
    {cinfo : List (Key × VExpr)} {Lx : Nat → List Ob} {x q : Nat} {c : Name}
    {ℓs : List (List Nat → Nat)}
    (Wv : Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ))
    (hx : x < doms.length)
    (hcinfo : List.Forall₂ (KeyData env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS) cinfo
      margs)
    (hcKs : List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2)
      (margs.map (argDemand doms.length Lx)) cinfo)
    (hq : margs[q]? = some (.bvar x)) :
    ∃ cl, .ctorArg q cl ∈ ctorObs c ℓs (cinfo.map (·.1)) ∧
      TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst v)) cl ∧ cl (v x) ∧
      ∀ k ∈ Lx x, .ctorArgOb q ((cinfo.map (·.1)).take q) k ∈ ctorObs c ℓs (cinfo.map (·.1)) := by
  have hql : q < margs.length := (List.getElem?_eq_some_iff.1 hq).1
  have hlen := List.Forall₂.length_eq hcinfo
  have hq' : q < cinfo.length := by omega
  have ha : margs[q] = .bvar x := (List.getElem?_eq_some_iff.1 hq).2
  obtain ⟨_, hkd⟩ := List.forall₂_getElem_exists hcinfo q hq'
  obtain ⟨_, hks⟩ := List.forall₂_getElem_exists hcKs q (by simpa using hql)
  rw [ha] at hkd
  simp only [List.getElem_map, ha, argDemand, hx, ite_true] at hks
  obtain ⟨h1, -, h3, h4, -⟩ := hkd
  have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
  have eD := bvar_dom_cls henv hΔ Wv h4 hL
  have hvx := (Wv.lookup hL).hasType.1
  have hq'' : q < (cinfo.map (·.1)).length := by simpa using hq'
  refine ⟨(cinfo[q]).1.2.1, ?_, ?_, ?_, fun k hk => ?_⟩
  · have := mem_ctorObs_arg (c := c) (ℓs := ℓs) hq''; simpa using this
  · rw [h1, h3, eD]; exact .of_hasType hvx
  · rw [h1]; exact ElCls.self
  · have := mem_ctorObs_argOb (c := c) (ℓs := ℓs) hq'' (k := k) (by simpa using hks k hk)
    simpa using this

/-- **Right to left** for a pattern rule headed by an arbitrary constant or eliminator `hd`
whose head type is `type.instL ls`: every observation of the right side is one of the left
side.  The instantiated sides are `eL` and `eR`; the head enters only through `hHead` (its
head type), `hrule` (its rule clause of `Obs`) and the mode C fact `Single`, which `hC`
supplies together with the propositional fields. -/
theorem pat_rhs_sub_head {df : VDefEq} {hd type : VExpr} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets} {Single : Prop}
    (hhd : (∃ c ls, hd = .const c ls) ∨ ∃ b o ls, hd = .elim b o ls)
    (hHead : ∀ Th, HeadTy env U hd Th → Th = type.instL ls)
    (eL : df.lhs.instL ls = .wrapLams (doms.map (·.instL ls)) (.mkApps hd
      (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
        (ms.map (·.instL ls) ++ fs.map .bvar)])))
    (eR : df.rhs.instL ls = .wrapLams (doms.map (·.instL ls)) (body.instL ls))
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (eH : type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    (hcf : CtorFam env ctor I)
    (hcis : IsCtor env ctor) (hfam : MajorFam env U Δ Γ I ctor doms lead ms fs ls lsC)
    (hrule : ∀ {σ' τ : VExpr.Subst} {S₀ S' : ObSets} {lkeys : List Key} {Dm : VExpr → Prop}
        {cm : VExpr → Prop} {Km : List Ob} {τs : List Ob} {o : Ob} (mC : Bool),
      (∀ τ ∈ τs, Obs' .id .empty (type.instL ls) τ) →
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (type.instL ls)) hd)
        (wrap (lkeys ++ [(Dm, cm, Km)]) o) τs →
      lkeys.length = lead.length →
      (mC = true → Single) →
      (mC = true → Obs' .id .empty (type.instL ls)
        (piCodChain lkeys (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval))
          iargs.length fun _ => 0)))) →
      (mC = false → (∃ ℓs, .ctorHead ctor ℓs (ms.length + fs.length) ∈ Km) ∨
        EtaHead env I ctor type lkeys.length) →
      RuleBind env U Δ doms ls lead ms.length fs mC I ctor lsC lkeys cm Km τ S' →
      KeysBacked (lkeys ++ [(Dm, cm, Km)]) → Obs' τ S' (body.instL ls) o →
      Obs' σ' S₀ hd (wrap (lkeys ++ [(Dm, cm, Km)]) o))
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (type.instL ls) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0))) →
      Single ∧
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms ls x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])
    (hL : HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (heq : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.rhs.instL ls)) (Obs' σ S (df.lhs.instL ls)) := by
  intro o ho
  refine ⟨o, ?_, .refl⟩
  obtain ⟨τs, hτs, hty⟩ := (hR σ σ S W tv tv).2.2.1 o ho
  rw [← vcls_defeq henv hΔ W heq] at hty
  rw [eL] at hty
  rw [eR] at ho
  obtain ⟨lk, v, vS, p, hk, rfl, hp⟩ := Obs.wrapLams_iff.1 ho
  rw [eL] at hL ⊢
  obtain ⟨T', hX, hdoms, τc, hτc, hpty⟩ := hL.lamSpine henv hΔ rfl W tv hk hτs hty
  obtain ⟨Wv, tvv⟩ := hk.typed henv hΔ hdoms W tv
  have hinner := hk.inner
  obtain ⟨Lx, hLx⟩ : ∃ Lx : Nat → List Ob, ∀ x < doms.length, vS x = listSet (Lx x) :=
    ⟨fun x => if h : x < doms.length then Classical.choose (hinner x (by simpa using h))
      else [], fun x hx => by
        simp only [hx, dite_true]; exact Classical.choose_spec (hinner x (by simpa using hx))⟩
  -- the first pass of the head spine
  have hKs := argDemand_ok (env := env) (U := U) (Δ := Δ) (nd := doms.length) hLx v
    (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
      (ms.map (·.instL ls) ++ fs.map .bvar)])
  rw [List.map_append] at hKs
  obtain ⟨Th, info, hTh, hThcl, hTT, hinfo, hKsi, P1, -, dP2⟩ :=
    hX.spineH henv hΔ rfl hhd Wv tvv _ hKs τc hτc
  obtain rfl := hHead _ hTh
  obtain ⟨Γ0, σ0, S0, uH, hHT, W0, tv0⟩ : ∃ Γ0 σ0 S0 uH, HTS env U Δ Γ0 (type.instL ls) (.sort uH) ∧
      Ctx.SubstEq env U Δ σ0 σ0 Γ0 ∧ TV env U Δ Γ0 σ0 S0 := by
    rcases hTT with ⟨uH, hHT, -⟩ | ⟨-, uH, hHT, -⟩
    · exact ⟨[], .id, .empty, uH, hHT, .nil, TV.empty⟩
    · exact ⟨_, v, vS, uH, hHT, Wv, tvv⟩
  obtain ⟨infoL, kaM, rfl, hinfoL, hkaM⟩ := List.forall₂_snoc_right hinfo
  obtain ⟨KsL, KsM, eKs, hKsiL, -⟩ := List.forall₂_snoc_right hKsi
  obtain ⟨rfl, -⟩ := List.append_inj' eKs rfl
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 p hpty
  have hlenL : infoL.length = lead.length := by
    have := List.Forall₂.length_eq hinfoL; simpa using this
  obtain ⟨u, hind⟩ := major_indicator_gen (dsH := dsH) (RH := RH) henv hΔ hThcl hHT W0 tv0
    (by rw [eH, VExpr.instL_wrapForalls]) hlenH hkH hIrig
    (keys := (infoL ++ [kaM]).map (·.1)) (by simp [hlenL]) hτ₀ hty₀
  rw [show ((infoL ++ [kaM]).map (·.1)).take lead.length = infoL.map (·.1) by
    simp [List.map_append, hlenL]] at hind
  obtain ⟨xr, hxr, lr⟩ := dP2 infoL kaM [] rfl _ hind
  rw [lr.rigid_inv] at hxr
  have firstOcc : ∀ x : Nat, (∃ i : Nat, lead[i]? = some (VExpr.bvar x)) →
      ∃ i : Nat, lead[i]? = some (VExpr.bvar x) ∧ ∀ j < i, lead[j]? ≠ some (VExpr.bvar x) := by
    intro x ⟨i₀, hi₀⟩
    have hmem : VExpr.bvar x ∈ lead := List.mem_of_getElem? hi₀
    obtain ⟨i, hi⟩ : ∃ i, lead.idxOf? (VExpr.bvar x) = some i := by
      cases h : lead.idxOf? (VExpr.bvar x) with
      | none => exact absurd hmem (by simpa using h)
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hil, h1, h2⟩ := List.idxOf?_eq_some_iff.1 hi
    refine ⟨i, List.getElem?_eq_some_iff.2 ⟨hil, h1⟩, fun j hj e => ?_⟩
    obtain ⟨hjl, e⟩ := List.getElem?_eq_some_iff.1 e
    exact h2 j hj e
  have fieldIdx : ∀ x : Nat, x ∈ fs → ∃ j : Nat, fs[j]? = some x := fun x hx => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
    exact ⟨j, List.getElem?_eq_some_iff.2 ⟨hj, e⟩⟩
  -- the common conclusion from a rule clause instance
  have finish : ∀ (infoL' : List (Key × VExpr)) (kaM' : Key × VExpr) (S' : ObSets) (mC : Bool)
      (τ₀' : List Ob),
      List.Forall₂ (KeyData env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS)
        (infoL' ++ [kaM']) (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)]) →
      (∀ τ ∈ τ₀', Obs' .id .empty (type.instL ls) τ) →
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (type.instL ls)) hd)
        (wrap ((infoL' ++ [kaM']).map (·.1)) p) τ₀' →
      (mC = true → Single) →
      (mC = true → Obs' .id .empty (type.instL ls) (piCodChain (infoL'.map (·.1))
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0)))) →
      (mC = false → (∃ ℓs, .ctorHead ctor ℓs (ms.length + fs.length) ∈ kaM'.1.2.2) ∨
        EtaHead env I ctor type (infoL'.map (·.1)).length) →
      RuleBind env U Δ doms ls lead ms.length fs mC I ctor lsC (infoL'.map (·.1)) kaM'.1.2.1
        kaM'.1.2.2 v S' →
      (∀ x o, vS x o → S' x o) →
      Obs' σ S (.wrapLams (doms.map (·.instL ls)) (.mkApps hd
        (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
          (ms.map (·.instL ls) ++ fs.map .bvar)]))) (wrap lk p) := by
    intro infoL' kaM' S' mC τ₀' hinfo' hτ₀' hty₀' hsingle hmobs hhdC hbind hS'
    have hlen' : infoL'.length = lead.length := by
      have := List.Forall₂.length_eq hinfo'; simpa using this
    have hc := hrule (σ' := v) (S₀ := vS) (Dm := kaM'.1.1) (cm := kaM'.1.2.1) (Km := kaM'.1.2.2)
      (lkeys := infoL'.map (·.1)) mC hτ₀' (by simpa using hty₀') (by simp [hlen'])
      hsingle hmobs hhdC hbind (by simpa using KeyData.forall₂_backed hinfo') (hp.mono hS')
    have hXo := obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo') (by simpa using hc)
    exact Obs.wrapLams_iff.2 ⟨lk, v, vS, p, hk, rfl, hXo⟩
  by_cases hm : u.eval = fun _ => 0
  · -- mode C: the major is ignored, its only own fields are proofs
    rw [hm] at hind
    obtain ⟨hsingle, hpf⟩ := hC _ (by simp [hlenL]) hind
    refine finish infoL kaM vS true τ₀ (forall₂_append_single hinfoL hkaM) hτ₀ hty₀
      (fun _ => hsingle) (fun _ => hind) nofun ⟨tvv.1, ?_⟩ fun _ _ h => h
    intro x hx
    by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
    · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := bind_lead henv hΔ Wv hLx hx hinfoL hKsiL hi
      exact .inl ⟨i, k, hi, hfirst, hk1, hk2, hk3, hk4⟩
    · have hnb : ∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x) := fun i h => hb ⟨i, h⟩
      have hxf : x ∈ fs := (hcov x hx).resolve_left fun h => by
        obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
        exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
      obtain ⟨j, hj⟩ := fieldIdx x hxf
      obtain ⟨hP, hprop⟩ := hpf x hx hnb v vS Wv tvv
      have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
      refine .inr ⟨hnb, j, hj, .inr (.inl ⟨⟨_, .self, (Wv.lookup hL).hasType.1⟩, hP, ?_⟩)⟩
      funext k; apply propext; constructor
      · intro hk
        obtain ⟨τs', hτs', htk⟩ := tvv.2 x _ hL k hk
        exact htk.not_prop fun τ hτ => hprop τ (hτs' τ hτ)
      · nofun
  · rcases hfam with ⟨hIP, hcnp⟩ | ⟨info, hpI, hPV, hcn, hfull, hnpj, hnzp⟩
    · -- mode AB: the major's constructor observations
      obtain ⟨-, -, -, hHTSm, -⟩ := hkaM
      have hKc := argDemand_ok (env := env) (U := U) (Δ := Δ) (nd := doms.length) hLx v
        (ms.map (·.instL ls) ++ fs.map .bvar)
      obtain ⟨cc, cinfo, hcc, -, -, hcinfo, hcKs, cP1, -, -⟩ :=
        hHTSm.spine henv hΔ rfl Wv tvv _ hKc
          [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval]
          (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hxr)
      have hCT : CtorTyped env ctor
          [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval] :=
        ⟨I, _, _, _, List.mem_singleton_self _, hcf, hm, hIP⟩
      have hcobs : ∀ r ∈ ctorObs ctor ((lsC.map (·.inst ls)).map (·.eval)) (cinfo.map (·.1)),
          Obs' v vS (.mkApps (.const ctor (lsC.map (·.inst ls)))
            (ms.map (·.instL ls) ++ fs.map .bvar)) r := by
        intro r hr
        have hend := ctorObs_end hr
        have hrty : TypedOb env U Δ (vcls env U Δ v (.mkApps (.const ctor (lsC.map (·.inst ls)))
            (ms.map (·.instL ls) ++ fs.map .bvar)) kaM.2) r
            [.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length u.eval] := by
          rcases hend with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
          · exact .ctorHead hCT
          · exact .ctorArg hCT
          · exact .ctorArgOb hCT
        obtain ⟨τ₀c, h1, h2⟩ := cP1 r hrty
        exact obs_mkApps_of_wrap (KeyData.forall₂_keys hcinfo)
          (.ctor hcis hcnp hcc h1 h2 hend (KeyData.forall₂_backed hcinfo))
      have hKs2 := forall₂_append_single (argDemand_ok (env := env) (U := U) (Δ := Δ)
        (nd := doms.length) hLx v (lead.map (·.instL ls))) hcobs
      obtain ⟨Th2, info2, hTh2, -, -, hinfo2, hKsi2, P12, -, -⟩ :=
        hX.spineH henv hΔ rfl hhd Wv tvv _ hKs2 τc hτc
      have hbk2 := KeyData.forall₂_backed hinfo2
      obtain rfl := hHead _ hTh2
      obtain ⟨infoL2, kaM2, rfl, hinfoL2, -⟩ := List.forall₂_snoc_right hinfo2
      obtain ⟨KsL2, KsM2, eKs2, hKsiL2, hKsM2⟩ := List.forall₂_snoc_right hKsi2
      obtain ⟨rfl, e2⟩ := List.append_inj' eKs2 rfl
      cases e2
      obtain ⟨τ₀2, hτ₀2, hty₀2⟩ := P12 p hpty
      have hclen : (cinfo.map (·.1)).length = ms.length + fs.length := by
        have := List.Forall₂.length_eq hcinfo; simp at this ⊢; omega
      have hmarg : ∀ j x, fs[j]? = some x →
          (ms.map (·.instL ls) ++ fs.map VExpr.bvar)[ms.length + j]? = some (.bvar x) := by
        intro j x hj
        rw [List.getElem?_append_right (by simp)]
        simp [hj]
      classical
      let S' : ObSets := fun x =>
        if x < doms.length ∧ (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ x ∈ fs then
          fun k => ∃ pre, .ctorArgOb (ms.length + fs.idxOf x) pre k ∈ kaM2.1.2.2
        else vS x
      have hfsj : ∀ x, x ∈ fs → fs[fs.idxOf x]? = some x := fun x hx =>
        List.getElem?_eq_some_iff.2 ⟨List.idxOf_lt_length_of_mem hx, List.getElem_idxOf _⟩
      have hbM : Backed (fun o => o ∈ kaM2.1.2.2) :=
        hbk2 _ (List.mem_map_of_mem (List.mem_append_right _ (List.mem_singleton_self _)))
      refine finish infoL2 kaM2 S' false τ₀2 hinfo2 hτ₀2 hty₀2 nofun nofun
        (fun _ => .inl ⟨_, hKsM2 _ (hclen ▸ mem_ctorObs_head)⟩) ⟨fun x => ?_, ?_⟩ ?_
      · simp only [S']
        split
        · intro k ⟨pre, hk⟩ w hw
          exact ⟨pre, hbM _ hk _ (by simp only [Ob.wit]; exact List.mem_map_of_mem hw)⟩
        · exact tvv.1 x
      · intro x hx
        by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
        · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
          obtain ⟨k, hk1, hk2, hk3, hk4⟩ := bind_lead henv hΔ Wv hLx hx hinfoL2 hKsiL2 hi
          have : S' x = vS x := by
            simp only [S']; rw [if_neg]; rintro ⟨-, h, -⟩; exact h i hi
          exact .inl ⟨i, k, hi, hfirst, hk1, hk2, hk3, this.trans hk4⟩
        · have hnb : ∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x) := fun i h => hb ⟨i, h⟩
          have hxf : x ∈ fs := (hcov x hx).resolve_left fun h => by
            obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
            exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
          obtain ⟨cl, hcl, hcty, hcm, -⟩ := bind_field (c := ctor)
            (ℓs := (lsC.map (·.inst ls)).map (·.eval)) henv hΔ Wv hx hcinfo hcKs
            (hmarg _ _ (hfsj x hxf))
          refine .inr ⟨hnb, fs.idxOf x, hfsj x hxf, .inl ⟨rfl, cl, hKsM2 _ hcl, hcty, hcm, ?_⟩⟩
          simp only [S']; rw [if_pos ⟨hx, hnb, hxf⟩]
      · intro x o ho
        simp only [S']
        split
        · rename_i hMF
          obtain ⟨hx, hnb, hxf⟩ := hMF
          obtain ⟨_, -, -, -, hall⟩ := bind_field (c := ctor)
            (ℓs := (lsC.map (·.inst ls)).map (·.eval)) henv hΔ Wv hx hcinfo hcKs
            (hmarg _ _ (hfsj x hxf))
          rw [hLx x hx] at ho
          exact ⟨_, hKsM2 _ (hall o ho)⟩
        · exact ho
    · -- a projection-registered family: the eta binding (never zero) or the proof binding
      have hEH : ∀ k, k = lead.length → EtaHead env I ctor type k := fun k hk =>
        ⟨info, dsH, RH, lsI, iargs, hpI, hcn, eH, hk ▸ hlenH, hk ▸ hkH⟩
      rcases hnzp with hnz | hpf
      · -- the eta binding: fields read from the field observations of the major key
        obtain ⟨-, -, -, hHTSm, hSDm, -⟩ := hkaM
        subst hcn
        obtain ⟨hlsW, hlsl⟩ := ctor_spine_levels henv hΔ hpI Wv hSDm
        have hmarg : ∀ j x, fs[j]? = some x →
            (ms.map (·.instL ls) ++ fs.map VExpr.bvar)[ms.length + j]? = some (.bvar x) := by
          intro j x hj
          rw [List.getElem?_append_right (by simp)]
          simp [hj]
        have hfsj : ∀ x, x ∈ fs → fs[fs.idxOf x]? = some x := fun x hx =>
          List.getElem?_eq_some_iff.2 ⟨List.idxOf_lt_length_of_mem hx, List.getElem_idxOf _⟩
        -- the field observations of the major
        have hfo : ∀ j x k, fs[j]? = some x → info.nparams ≤ ms.length + j → x < doms.length →
            k ∈ Lx x → ∃ L, Obs' v vS (.mkApps (.const info.ctorName (lsC.map (·.inst ls)))
              (ms.map (·.instL ls) ++ fs.map .bvar))
              (.fieldOb I (ms.length + j - info.nparams) L k) := by
          intro j x k hj hnp hxd hk
          have H' := hHTSm
          rw [← List.take_append_drop info.nparams (ms.map (·.instL ls) ++ fs.map VExpr.bvar)]
            at H'
          have hjd : ms.length + j - info.nparams <
              ((ms.map (·.instL ls) ++ fs.map VExpr.bvar).drop info.nparams).length := by
            have := (List.getElem?_eq_some_iff.1 hj).1; simp; omega
          have hget : ((ms.map (·.instL ls) ++ fs.map VExpr.bvar).drop info.nparams)[
              ms.length + j - info.nparams]'hjd = .bvar x := by
            have h1 : ((ms.map (·.instL ls) ++ fs.map VExpr.bvar).drop info.nparams)[
                ms.length + j - info.nparams]? = some (.bvar x) := by
              rw [List.getElem?_drop,
                show info.nparams + (ms.length + j - info.nparams) = ms.length + j by omega]
              exact hmarg j x hj
            exact (List.getElem?_eq_some_iff.1 h1).2
          have hkx : Obs' v vS ((ms.map (·.instL ls) ++ fs.map VExpr.bvar).drop info.nparams)[
              ms.length + j - info.nparams] k := by
            rw [hget]; exact .bvar (by rw [hLx x hxd]; exact hk)
          have := ctor_field_obs henv hΔ hpI hPV hlsW hlsl hnz Wv tvv H'
            (by simp; omega) (by simp; omega) hjd hkx
          rwa [List.take_append_drop] at this
        classical
        obtain ⟨Kd, hKd, hKdc⟩ := exists_list_witness
          (Q := Obs' v vS (.mkApps (.const info.ctorName (lsC.map (·.inst ls)))
            (ms.map (·.instL ls) ++ fs.map .bvar)))
          (P := fun (a : Nat × Ob) o => ∃ L, o = .fieldOb I (ms.length + a.1 - info.nparams) L a.2)
          (((List.range fs.length).filter fun j => decide (info.nparams ≤ ms.length + j ∧
              fs.getD j 0 < doms.length)).flatMap fun j => (Lx (fs.getD j 0)).map fun k => (j, k))
          (by
            intro a ha
            simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq,
              List.mem_map] at ha
            obtain ⟨j, ⟨hjl, hnp, hxd⟩, k, hk, rfl⟩ := ha
            have hj : fs[j]? = some (fs.getD j 0) := by
              rw [← List.getElem_eq_getD 0 (h := hjl), List.getElem?_eq_getElem hjl]
            obtain ⟨L, hL⟩ := hfo j _ k hj hnp hxd hk
            exact ⟨_, hL, L, rfl⟩)
        have hKdx : ∀ j x k, fs[j]? = some x → info.nparams ≤ ms.length + j → x < doms.length →
            k ∈ Lx x → ∃ L, .fieldOb I (ms.length + j - info.nparams) L k ∈ Kd := by
          intro j x k hj hnp hxd hk
          have hjl : j < fs.length := (List.getElem?_eq_some_iff.1 hj).1
          have hfx : fs.getD j 0 = x := by
            rw [← List.getElem_eq_getD 0 (h := hjl)]; exact (List.getElem?_eq_some_iff.1 hj).2
          obtain ⟨o, ho, L, rfl⟩ := hKdc (j, k) (by
            simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq,
              List.mem_map]
            exact ⟨j, ⟨hjl, hnp, by rw [hfx]; exact hxd⟩, k, by rw [hfx]; exact hk, rfl⟩)
          exact ⟨L, ho⟩
        -- the second pass of the head spine, with the field observations of the major
        have hKs2 := forall₂_append_single (argDemand_ok (env := env) (U := U) (Δ := Δ)
          (nd := doms.length) hLx v (lead.map (·.instL ls))) hKd
        obtain ⟨Th2, info2, hTh2, -, -, hinfo2, hKsi2, P12, -, -⟩ :=
          hX.spineH henv hΔ rfl hhd Wv tvv _ hKs2 τc hτc
        have hbk2 := KeyData.forall₂_backed hinfo2
        obtain rfl := hHead _ hTh2
        obtain ⟨infoL2, kaM2, rfl, hinfoL2, hkaM2⟩ := List.forall₂_snoc_right hinfo2
        obtain ⟨KsL2, KsM2, eKs2, hKsiL2, hKsM2⟩ := List.forall₂_snoc_right hKsi2
        obtain ⟨rfl, e2⟩ := List.append_inj' eKs2 rfl
        cases e2
        obtain ⟨τ₀2, hτ₀2, hty₀2⟩ := P12 p hpty
        obtain ⟨hcm2, -, hDm2, hHTS2, hSD2, -⟩ := hkaM2
        have hlenL2 : infoL2.length = lead.length := by
          have := List.Forall₂.length_eq hinfoL2; simpa using this
        let S' : ObSets := fun x =>
          if x < doms.length ∧ (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ x ∈ fs then
            fun k => ∃ L, .fieldOb I (ms.length + fs.idxOf x - info.nparams) L k ∈ kaM2.1.2.2
          else vS x
        have hbM : Backed (fun o => o ∈ kaM2.1.2.2) :=
          hbk2 _ (List.mem_map_of_mem (List.mem_append_right _ (List.mem_singleton_self _)))
        refine finish infoL2 kaM2 S' false τ₀2 hinfo2 hτ₀2 hty₀2 nofun nofun
          (fun _ => .inr (hEH _ (by simp [hlenL2]))) ⟨fun x => ?_, ?_⟩ ?_
        · simp only [S']
          split
          · intro k ⟨L, hk⟩ w hw
            exact ⟨L, hbM _ hk _ (Ob.mem_wit_fieldOb.2 (.inr ⟨w, hw, rfl⟩))⟩
          · exact tvv.1 x
        · intro x hx
          by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
          · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
            obtain ⟨k, hk1, hk2, hk3, hk4⟩ := bind_lead henv hΔ Wv hLx hx hinfoL2 hKsiL2 hi
            have : S' x = vS x := by
              simp only [S']; rw [if_neg]; rintro ⟨-, h, -⟩; exact h i hi
            exact .inl ⟨i, k, hi, hfirst, hk1, hk2, hk3, this.trans hk4⟩
          · have hnb : ∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x) := fun i h => hb ⟨i, h⟩
            have hxf : x ∈ fs := (hcov x hx).resolve_left fun h => by
              obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
              exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
            have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
            have hnp := hnpj x _ (hfsj x hxf) hnb
            obtain ⟨E, hvx⟩ := eta_field_cls henv hΔ hpI hPV Wv tvv hHTS2 hSD2
              (by simp; omega) hnz (hmarg _ _ (hfsj x hxf)) hnp hL
            have ecm : kaM2.1.2.1 = ElCls env U Δ (TyCls env U Δ (kaM2.2.subst v))
                ((VExpr.mkApps (.const info.ctorName (lsC.map (·.inst ls)))
                  (ms.map (·.instL ls) ++ fs.map .bvar)).subst v) := by
              rw [hcm2, hDm2]
            refine .inr ⟨hnb, fs.idxOf x, hfsj x hxf,
              .inr (.inr ⟨rfl, info, hpI, rfl, hnp, hnz, ?_, ?_, ?_⟩)⟩
            · rw [ecm, E]; exact TypedElCls.of_hasType hvx
            · rw [ecm, E]; exact ElCls.self
            · simp only [S']; rw [if_pos ⟨hx, hnb, hxf⟩]
        · intro x o ho
          simp only [S']
          split
          · rename_i hMF
            obtain ⟨hx, hnb, hxf⟩ := hMF
            rw [hLx x hx] at ho
            obtain ⟨L, hmem⟩ := hKdx _ x o (hfsj x hxf) (hnpj x _ (hfsj x hxf) hnb) hx ho
            exact ⟨L, hKsM2 _ hmem⟩
          · exact ho
      · -- the proof binding for every field not bound by the leading arguments
        refine finish infoL kaM vS false τ₀ (forall₂_append_single hinfoL hkaM) hτ₀ hty₀ nofun
          nofun (fun _ => .inr (hEH _ (by simp [hlenL]))) ⟨tvv.1, ?_⟩ fun _ _ h => h
        intro x hx
        by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
        · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
          obtain ⟨k, hk1, hk2, hk3, hk4⟩ := bind_lead henv hΔ Wv hLx hx hinfoL hKsiL hi
          exact .inl ⟨i, k, hi, hfirst, hk1, hk2, hk3, hk4⟩
        · have hnb : ∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x) := fun i h => hb ⟨i, h⟩
          have hxf : x ∈ fs := (hcov x hx).resolve_left fun h => by
            obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
            exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
          obtain ⟨j, hj⟩ := fieldIdx x hxf
          obtain ⟨hP, hprop⟩ := hpf x hx hnb v vS Wv tvv
          have hL := lookup_binderTy (Γ := Γ) (ls := ls) hx
          refine .inr ⟨hnb, j, hj, .inr (.inl ⟨⟨_, .self, (Wv.lookup hL).hasType.1⟩, hP, ?_⟩)⟩
          funext k; apply propext; constructor
          · intro hk
            obtain ⟨τs', hτs', htk⟩ := tvv.2 x _ hL k hk
            exact htk.not_prop fun τ hτ => hprop τ (hτs' τ hτ)
          · nofun

/-- **Right to left** for a pattern rule: every observation of the right side is one of the
left side. -/
theorem pat_rhs_sub {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (hdf : env.defeqs df)
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (hci : env.constants n = some ci) (eH : ci.type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    (hcf : CtorFam env ctor I)
    (hcis : IsCtor env ctor) (hfam : MajorFam env U Δ Γ I ctor doms lead ms fs ls lsC)
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (ci.type.instL ls) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0))) →
      (∀ df' ls', env.defeqs df' → df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' = df) ∧
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms ls x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])
    (hL : HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (heq : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.rhs.instL ls)) (Obs' σ S (df.lhs.instL ls)) := by
  obtain ⟨eL, eR⟩ := pat_instL hl hr hlsP
  refine pat_rhs_sub_head henv hΔ (hd := .const n ls) (type := ci.type)
    (Single := ∀ df' ls', env.defeqs df' → df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' →
      df' = df) (.inl ⟨_, _, rfl⟩) ?_ eL eR hcov eH hlenH hkH hIrig hcf hcis hfam
    (fun _ => Obs.rule hdf hl hr hci) hC hL hR heq W tv
  rintro Th (⟨_, _, ci', e, hci', -, rfl⟩ | ⟨_, _, _, _, _, e, -⟩) <;> cases e
  cases hci.symm.trans hci'
  rfl

/-- **Left to right** for a pattern rule: every observation of the left side is subsumed by
one of the right side. -/
theorem pat_lhs_sub {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (hdf : env.defeqs df)
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c) (hdr : env.DeltaRules)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const n lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧ (ctor' = ctor → df' = df))
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (hci : env.constants n = some ci) (eH : ci.type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs))
    (hfam : MajorFamEntry env I ctor)
    (hRH : HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.lhs.instL ls)) (Obs' σ S (df.rhs.instL ls)) := by
  obtain ⟨eL, eR⟩ := pat_instL hl hr hlsP
  intro o ho
  rw [eL] at ho
  obtain ⟨lk, v, vS, p, hk, rfl, hp⟩ := Obs.wrapLams_iff.1 ho
  rw [eR] at hRH hR ⊢
  obtain ⟨B, hBs, hdomsR⟩ := HTS.wrapLams_body hRH hR
  obtain ⟨Wv, tvv⟩ := hk.typed henv hΔ hdomsR W tv
  obtain ⟨keys, hkeys, hc⟩ := wrap_of_obs_mkApps_le hp
  have headOf : df.lhs.stripLams.getAppFnArgs.1 = .const n lsP := by
    rw [hl]; exact VExpr.stripLams_wrapLams_mkApps_head
  rcases Obs.const_iff.1 hc with ⟨_, _, _, _, _, hrig, _⟩ | ⟨df', _, _, hdf', hlhs', _⟩ |
    ⟨_, _, _, _, _, hcn, _⟩ |
    ⟨df'', doms'', lsP'', lead'', ctor'', lsC'', ms'', fs'', body'', ci, τs, lkeys, Dm, cm, Km,
      p'', mC, τ, S'', I', ℓsI', mI', e, hdf'', hl'', hr'', hci'', -, -, hlen'', hsingle, -, hhd,
      hbind, -, hbody⟩ | ⟨fam, info, _, _, _, _, _, hpi, hcn, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrig, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, hrig, _⟩
  · exact absurd headOf (hrig df hdf lsP)
  · have := hdr.excl df' df hdf' hdf n _ lsP hlhs' headOf
    subst this
    exact absurd (hl.symm.trans hlhs') VExpr.wrapLams_mkApps_snoc_ne_const
  · exact absurd headOf (hctor n hcn df hdf lsP)
  rotate_left
  · exact absurd headOf (hpctor n ⟨fam, info, hpi, hcn⟩ df hdf lsP)
  · exact absurd headOf (hrig df hdf lsP)
  · exact absurd headOf (hrig df hdf lsP)
  obtain ⟨hleadlen, huq⟩ := huniq df'' doms'' lsP'' lead'' ctor'' lsC'' ms'' fs'' body'' hdf'' hl'' hr''
  have hklen : keys.length = lead.length + 1 := by
    have := List.Forall₂.length_eq hkeys; simpa using this
  obtain ⟨ekeys, rfl⟩ := wrap_inj_len (by simp [hklen, hlen'', hleadlen]) e
  subst ekeys
  obtain ⟨lkeys', mk, ekl, hkeysL, hkM⟩ := List.forall₂_snoc_right hkeys
  obtain ⟨rfl, emk⟩ := List.append_inj' ekl (by simp)
  cases emk
  obtain ⟨hcmM, hKmcov⟩ := hkM
  cases hci.symm.trans hci''
  -- the clause's rule is the given one
  have hdf_eq : df'' = df := by
    cases mC with
    | true => exact (hsingle rfl df lsP hdf headOf).symm
    | false =>
      apply huq
      rcases hhd rfl with ⟨ℓs, hmem⟩ | hEH
      · obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
        rw [ly.ctorHead_inv] at hy
        obtain ⟨_, _, hend⟩ := ctor_spine_inv hcrig hy (.inl ⟨_, _, _, rfl⟩)
        rcases hend with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩
        · injection h
        · cases h
        · cases h
      · -- the head type names the family `I`, which is projection-registered
        have hll : lkeys.length = lead.length := hlen''.trans hleadlen
        obtain ⟨rfl, info', hpi', hcn'⟩ :=
          hEH.fam eH (by rw [hll]; exact hlenH) (by rw [hll]; exact hkH)
        rcases hfam with ⟨hnp, -⟩ | ⟨info, hpi, hcn⟩
        · exact absurd hpi' (hnp _)
        · cases henv.projections_unique hpi hpi'
          exact hcn'.symm.trans hcn
  subst hdf_eq
  obtain ⟨rfl, -, -, rfl, emaj⟩ := wrapLams_pat_inj (hl''.symm.trans hl)
  obtain ⟨rfl, rfl, emargs⟩ := VExpr.mkApps_const_inj emaj
  obtain ⟨-, rfl⟩ := wrapLams_inj_len rfl (hr''.symm.trans hr)
  -- closedness
  have hbcl : (body''.instL ls).ClosedN doms''.length := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms'' body'').ClosedN 0)).1
    simpa using this.instL
  have hdcl : ∀ i (h : i < doms''.length), (doms''[i]).ClosedN i := by
    have := (closedN_wrapLams (hl ▸ hlcl :
      (VExpr.wrapLams doms'' (.mkApps (.const n lsP)
        (lead'' ++ [.mkApps (.const ctor'' lsC'') (ms ++ fs.map .bvar)]))).ClosedN 0)).2
    simpa using this
  -- the major's arguments
  have hmargs : ∀ j x, fs''[j]? = some x →
      (ms.map (·.instL ls) ++ fs.map VExpr.bvar)[ms''.length + j]? = some (.bvar x) := by
    intro j x hj
    have e1 : ms.map (·.instL ls) ++ fs.map VExpr.bvar =
        (ms'' ++ fs''.map VExpr.bvar).map (·.instL ls) := by
      rw [emargs]; simp [List.map_append, VExpr.instL]
    rw [e1, List.getElem?_map, List.getElem?_append_right (by simp)]
    simp [hj, VExpr.instL]
  -- facts about the constructor observations of the major
  have argOf : ∀ j x cl, fs''[j]? = some x → .ctorArg (ms''.length + j) cl ∈ Km → cl (v x) := by
    intro j x cl hj hcl
    obtain ⟨y, hy, ly⟩ := hKmcov _ hcl
    rw [ly.ctorArg_inv] at hy
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inl ⟨_, _, rfl⟩))
    rcases hend with h | ⟨i, hi, h⟩ | ⟨_, _, _, _, h⟩
    · cases h
    · injection h with e1 e2; subst e1; subst e2
      obtain ⟨_, hci', -⟩ := List.forall₂_getElem_exists hck _ hi
      have := hmargs j x hj
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨_, ha⟩ := this
      rw [hci', ha]; exact ElCls.self
    · cases h
  have argObOf : ∀ j x pre k, fs''[j]? = some x →
      .ctorArgOb (ms''.length + j) pre k ∈ Km → ∃ k', vS x k' ∧ k' ≼ k := by
    intro j x pre k hj hk
    obtain ⟨y, hy, ly⟩ := hKmcov _ hk
    obtain ⟨k₀, rfl, l₀⟩ := ly.ctorArgOb_inv
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inr ⟨_, _, _, rfl⟩))
    rcases hend with h | ⟨_, _, h⟩ | ⟨i, hi, k', hk', h⟩
    · cases h
    · cases h
    · injection h with e1 e2 e3; subst e1
      obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hck _ hi
      have := hmargs j x hj
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨_, ha⟩ := this
      obtain ⟨k₁, hk₁, l₁⟩ := hcov k' hk'
      rw [ha] at hk₁
      exact ⟨k₁, Obs.bvar_iff.1 hk₁, l₁.trans (e3 ▸ l₀)⟩
  -- the binding, restricted to the rule's variables
  classical
  let τ' : VExpr.Subst := fun x => if x < doms''.length then τ x else v x
  let S' : ObSets := fun x => if x < doms''.length then S'' x else vS x
  have hτ'1 : ∀ x, x < doms''.length → τ' x = τ x := fun x hx => if_pos hx
  have hτ'2 : ∀ x, doms''.length ≤ x → τ' x = v x := fun x hx => if_neg (by omega)
  have hbody' : Obs' τ' S' (body''.instL ls) p :=
    (Obs.closed_iff hbcl (fun i hi => (hτ'1 i hi).symm) (fun i hi => (if_pos hi).symm)).1 hbody
  have hcov : ∀ x o, S' x o → ∃ o', vS x o' ∧ o' ≼ o := by
    intro x o ho
    by_cases hx : x < doms''.length
    · simp only [S', hx, if_true] at ho
      rcases hbind.2 x hx with ⟨i, k, hi, -, hki, -, -, hkS⟩ |
        ⟨-, j, hj, ⟨-, -, -, -, -, hS⟩ | ⟨-, -, hS⟩ | ⟨-, info', hpi', -, hle', -, -, -, hS⟩⟩
      · rw [hkS] at ho
        have hil : i < lkeys.length := by
          have := List.Forall₂.length_eq hkeysL
          have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
        obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hkeysL i hil
        have hk : lkeys[i] = k := by
          have := List.getElem?_eq_some_iff.1 hki; exact this.2
        rw [hk] at hcov
        obtain ⟨o', ho', l⟩ := hcov o ho
        have ha : (lead''.map (·.instL ls))[i]'(by
            have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
          simp only [List.getElem_map]
          rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
        rw [ha] at ho'
        exact ⟨o', Obs.bvar_iff.1 ho', l⟩
      · rw [hS] at ho
        obtain ⟨pre, hpre⟩ := ho
        exact argObOf j x pre o hj hpre
      · rw [hS] at ho; cases ho
      · -- eta: a field observation of the major key
        rw [hS] at ho
        obtain ⟨L, hmem⟩ := ho
        obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
        obtain ⟨L', y₀, rfl, l₀⟩ := ly.fieldOb_inv
        obtain ⟨info'', hpi'', -, a, ha, k', hk', l'⟩ := projctor_spine_inv hcrig hy
        cases henv.projections_unique hpi' hpi''
        rw [show info'.nparams + (ms''.length + j - info'.nparams) = ms''.length + j by omega,
          hmargs j x hj] at ha
        cases ha
        exact ⟨k', Obs.bvar_iff.1 hk', l'.trans l₀⟩
    · simp only [S', hx, if_false] at ho
      exact ⟨o, ho, .refl⟩
  obtain ⟨p₁, hp₁, l₁⟩ := hbody'.mono_le hcov
  -- the binding is related to the actual variables
  have hL := fun x (hx : x < doms''.length) => lookup_binderTy (Γ := Γ) (ls := ls) hx
  have hbcl' : ∀ x, x < doms''.length →
      (binderTy doms'' ls x).subst τ = (binderTy doms'' ls x).subst τ' := fun x hx =>
    (binderTy_closed hdcl hx).subst_congr fun i hi => (hτ'1 i hi).symm
  have W' : Ctx.SubstEq env U Δ τ' v ((doms''.map (·.instL ls)).reverse ++ Γ) := by
    refine SubstEq.of_heads_ind Wv (fun x hx => hτ'2 x (by simpa using hx))
      fun x A hx hLA hW => ?_
    have hx' : x < doms''.length := by simpa using hx
    cases hLA.uniq (hL x hx')
    rw [hτ'1 x hx', ← hbcl' x hx']
    have hvx := (Wv.lookup (hL x hx')).hasType.1
    have hvx' : env.HasType U Δ (v x) ((binderTy doms'' ls x).subst τ) := by
      have hD := SubstEq.entry_typed Wv hx
      obtain ⟨uD, hDt⟩ := hD
      have hDD := hDt.substDF henv hW.wf hΔ hW
      have eA : (binderTy doms'' ls x) =
          ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx).liftN (x+1) := (hL x hx').uniq
            (lookup_append _ x hx)
      have e1 := liftN_subst_shift ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) τ' x
      have e2 := liftN_subst_shift ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) v x
      rw [← eA] at e1 e2
      rw [hbcl' x hx', e1]; rw [e2] at hvx; exact hDD.symm.defeqDF hvx
    rcases hbind.2 x hx' with ⟨i, k, hi, -, hki, hkt, hkm, -⟩ |
      ⟨-, j, hj, ⟨-, cl, hcl, hct, hcm, -⟩ | ⟨⟨X, hX, hτX⟩, ⟨P, hP, hPs⟩, -⟩ |
        ⟨-, info', hpi', hcn', hle', -, hTE, hpc, -⟩⟩
    · have hil : i < lkeys.length := by
        have := List.Forall₂.length_eq hkeysL
        have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
      obtain ⟨_, hcls, -⟩ := List.forall₂_getElem_exists hkeysL i hil
      have hk : lkeys[i] = k := (List.getElem?_eq_some_iff.1 hki).2
      have ha : (lead''.map (·.instL ls))[i]'(by
          have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
        simp only [List.getElem_map]
        rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
      rw [hk, ha] at hcls
      have hvk : k.2.1 (v x) := by rw [hcls]; exact ElCls.self
      exact hkt.defeq henv hΔ hkm hvk
    · exact hct.defeq henv hΔ hcm (argOf j x cl hj hcl)
    · -- proof binding: both are proofs of the proposition `P`
      have hτx : env.HasType U Δ (τ x) ((binderTy doms'' ls x).subst τ) :=
        TyCls.defeq henv hΔ hX hτX
      have h1 := TyCls.defeq_rev henv hΔ hP hτx
      have h2 := TyCls.defeq_rev henv hΔ hP hvx'
      exact TyCls.defeq henv hΔ hP (.proofIrrel hPs h1 h2)
    · -- eta binding: the anchor is a projection of the major, whose field is `v x`
      refine eta_anchor_defeq henv hΔ hpi' hTE hpc (lsc := lsC''.map (·.inst ls))
        (margs := (ms.map (·.instL ls) ++ fs.map VExpr.bvar).map (·.subst v)) ?_ ?_ hvx'
      · rw [show cm = (Dm, cm, Km).2.1 from rfl, hcmM]
        simp only [VExpr.subst_mkApps, VExpr.subst]
        rw [hcn']; exact ElCls.self
      · rw [List.getElem?_map,
          show info'.nparams + (ms''.length + j - info'.nparams) = ms''.length + j by omega,
          hmargs j x hj]
        rfl
  have hctx := DomsSD.ctxSD (L := []) (Γ := Γ) hdomsR .nil
  simp only [List.append_nil] at hctx
  have tvτ := TV.transfer henv hΔ hctx W' (fun x hx => hτ'2 x (by simpa using hx)) tvv
  obtain ⟨p₂, hp₂, l₂⟩ := (hBs τ' v vS W' tvτ tvv).1 p₁ hp₁
  exact ⟨wrap lk p₂, Obs.wrapLams_iff.2 ⟨lk, v, vS, p₂, hk, rfl, hp₂⟩, wrap_le (l₂.trans l₁)⟩

/-- **Soundness of a pattern rule.** -/
theorem sound_pat {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (hdf : env.defeqs df)
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (hci : env.constants n = some ci) (eH : ci.type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    (hcf : CtorFam env ctor I)
    (hcis : IsCtor env ctor) (hfam : MajorFam env U Δ Γ I ctor doms lead ms fs ls lsC)
   
    (hcrig : env.Rigid ctor)
    (hctor : ∀ c, IsCtor env c → env.Rigid c) (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hdr : env.DeltaRules)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const n lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧ (ctor' = ctor → df' = df))
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (ci.type.instL ls) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0))) →
      (∀ df' ls', env.defeqs df' → df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' = df) ∧
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms ls x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])
    (ihL : SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (heq : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)) :
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) := by
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  have hLc := hlcl.instL (ls := ls)
  have hRc := hrcl.instL (ls := ls)
  refine ⟨fun o h => ?_, fun o h => ?_, (ihL.1 σ σ S W.left tv tv).2.2.1,
    (ihR.1 σ' σ' S W' tv' tv').2.2.1⟩
  · obtain ⟨o', h1, l⟩ := pat_lhs_sub henv hΔ hdf hl hr hlsP hlcl hrcl hcrig hctor hpctor hdr huniq
      hci eH hlenH hkH hfam.weak ihR.2 ihR.1 W.left tv o h
    exact ⟨o', (Obs.closed_iff_id hRc).2 ((Obs.closed_iff_id hRc).1 h1), l⟩
  · obtain ⟨o', h1, l⟩ := pat_rhs_sub henv hΔ hdf hl hr hcov hlsP hci eH hlenH hkH hIrig hcf
      hcis hfam hC ihL.2 ihR.1 heq W' tv' o h
    exact ⟨o', (Obs.closed_iff_id hLc).2 ((Obs.closed_iff_id hLc).1 h1), l⟩

end

end Model
end VEnv
end Lean4Lean
