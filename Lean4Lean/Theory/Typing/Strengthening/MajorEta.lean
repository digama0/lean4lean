import Lean4Lean.Theory.Typing.Strengthening.SpineClosure
import Batteries.Tactic.OpenPrivate

/-! # Typing strengthening: descent of the composite major-eta step

Direction F. B3's closure of the eta-normal relation
records, on the source side, the composite step `MajorEtaIota`: structure eta at a neutral major
of structure type followed by a redex fired at the root (`RootFire`: a stored iota rule or a case
step consuming the expansion). Its descent at the root of a lift (`MajorEtaDescends`,
`EtaNormal.lean`) is proved here:

* `telInst_descend`: spine descent at a head typed below at a closed telescope (each argument
  retyped at its domain by `TypedFrontN.retype`, the domain a type below by telescope
  instantiation);
* `structExpand_descend`: the structure eta expansion at the data below is typed below, its
  projections by the field-type closure `ProjFieldFrontN` (which is why that closure is a
  hypothesis here; it is free outside `Prop`, `projField_of_neverZero`), the spine by
  `telInst_descend` at the constructor's closed telescope, and the lifted expansion is typed
  above by spine congruence from the expansion above (`IsDefEqU.mkApps_args`);
* `majorEtaDescends : TypedFrontN → CaseRedexDescends → CheckVars → ProjFieldFrontN →
  MajorEtaDescends`. The major's family type below is read from the head of the application
  typed below (`RecursorRegistered.major_type`, `QuotRegistered.major_type`,
  `HasType.caseMajor_type`) and identified with the structure by rigidity of both heads
  (`rigid_rigid`); so the descent does not use `ProjFrontN` (which would be circular, since
  spine exposure descends composite steps) and has no `numFields = 0` special case. The fired
  redex is transported to the lifted expansion at the data below: its right-hand side and check
  do not read the constructor's parameters (`pat_iota_params`; for case steps the capture is
  unchanged by `schema_struct_major` and `CaseRedex.transport`), and then descends by
  `ParRed.descend`. -/

namespace Lean4Lean.VEnv.StrengtheningMajorEta
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaClosure VEnv.StrengtheningSpineExposure
  VEnv.StrengtheningClosures InductiveSignature

open private closed_wrapForalls_domain from Lean4Lean.Theory.Typing.CaseReduction

variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr}

/-- Spine descent at a head typed below at a closed telescope: if the lifted spine is typed
above and every argument is typed below at some type, the arguments are a typed instance of the
telescope below. Each argument is retyped at its domain (`TypedFrontN.retype`), the domain being
a type below by telescope instantiation at the earlier arguments (strong induction on the
position). -/
theorem telInst_descend (henv : env.WF) (hTF : TypedFrontN env) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    {h : VExpr} {ds : List VExpr} {r : VExpr} (hh : env.HasType U Γ h (wrapForalls ds r))
    (hcl : (wrapForalls ds r).ClosedN 0)
    {as : List VExpr} (hlen : as.length = ds.length) (hwf : ∀ a ∈ as, VExpr.WF env U Γ a)
    (habove : VExpr.WF env U Γ' (mkApps (h.liftN 1 k) (as.map (·.liftN 1 k)))) :
    TelInst env U Γ ds as := by
  have hctx := (IsType.wrapForalls_inv henv hΓ (hh.isType henv.ordered hΓ)).1
  have hh' : env.HasType U Γ' (h.liftN 1 k) (wrapForalls ds r) := by
    have := hh.weakN henv.ordered W
    rwa [hcl.liftN_eq (Nat.zero_le _)] at this
  have habove' := (HasType.mkApps_wrapForalls henv hΓ' hh' habove (by simpa using hlen)).1
  refine ⟨hlen, fun j hj hj' => ?_⟩
  induction j using Nat.strongRecOn with
  | _ j ih =>
  have hD : env.IsType U Γ (ds[j].instOuter (as.take j)) := by
    refine IsType.instOuter_telescope henv (doms := ds.take j)
      (OnCtx.getElem_reverse_append hctx j hj').2 (by simp [List.length_take]; omega) ?_
    intro i hi hi'
    simp only [List.length_take] at hi hi'
    have hi₁ : i < j := by omega
    rw [List.getElem_take, List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hi₁)]
    exact ih i hi₁ (by omega) (by omega)
  have hab := habove' j (by simpa using hj) hj'
  have hdcl : ds[j].ClosedN (as.take j).length := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    simpa using closed_wrapForalls_domain hcl hj'
  rw [List.getElem_map, ← List.map_take, ← instantiateParams_eq_instOuter,
    ← instantiateParams_liftN hdcl, instantiateParams_eq_instOuter] at hab
  obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hj)
  obtain ⟨u, hDu⟩ := hD
  exact hTF.retype henv W hΓ hΓ' hA hDu hab

theorem forall₂_symm {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l l' : List α}, List.Forall₂ R l l' → List.Forall₂ R l' l
  | _, _, .nil => .nil
  | _, _, .cons h hs' => .cons (hs _ _ h) (forall₂_symm hs hs')

/-- Two appended lists with equal first components agree after dropping at least the first
component. -/
theorem drop_append_eq_of_length {α : Type} {l₁ l₂ l : List α} (h : l₁.length = l₂.length) {n : Nat}
    (hn : l₁.length ≤ n) : (l₁ ++ l).drop n = (l₂ ++ l).drop n := by
  induction l₁ generalizing l₂ n with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons => simp at h
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      cases n with
      | zero => simp at hn
      | succ n =>
        simp only [List.cons_append, List.drop_succ_cons]
        exact ih (by simpa using h) (by simpa using hn)

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => Params.env.IsDefEq univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => Params.env.IsDefEqU univs Γ e1 e2

/-- The structure eta expansion below. Given the major typed below at the structure type (with
levels and parameters convertible above to those of the expansion above), the expansion at the
data below is typed below at the structure type: its projections are typed below by the
field-type closure (`ProjFieldFrontN`, `projDF`), the lifted expansion is typed above by spine
congruence from the expansion above (`IsDefEqU.mkApps_args`), the spine descends at the
constructor's closed telescope (`telInst_descend`) and is retyped at the structure type. Also
returns the typing above of the lifted expansion and its conversion to the expansion above. -/
theorem structExpand_descend (hTF : TypedFrontN Params.env) (hField : ProjFieldFrontN Params.env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {family : Name} {info : VProjectionInfo} {lv levels : List VLevel} {args params : List VExpr}
    {m₀ : VExpr} (hl : Params.env.projections family info) (hi : info.nindices = 0)
    (hm₀ : Γ ⊢ m₀ : mkApps (.const family lv) args) (hlen : args.length = info.nparams)
    (hm : Γ' ⊢ m₀.liftN 1 k : mkApps (.const family levels) params)
    (hexp : Γ' ⊢ structExpand family info levels params (m₀.liftN 1 k) :
      mkApps (.const family levels) params)
    (hlv : List.Forall₂ (· ≈ ·) lv levels)
    (hargs : List.Forall₂ (Params.env.IsDefEqU univs Γ') (args.map (·.liftN 1 k)) params) :
    Γ ⊢ structExpand family info lv args m₀ : mkApps (.const family lv) args ∧
    Γ' ⊢ (structExpand family info lv args m₀).liftN 1 k : mkApps (.const family levels) params ∧
    Γ' ⊢ structExpand family info levels params (m₀.liftN 1 k) ≡
      (structExpand family info lv args m₀).liftN 1 k := by
  obtain ⟨decl, type, ctor, -, -, -, -, -, hnparams, -, -, -, hctorType, -, hwf, -, Hraw, -⟩ :=
    henv.ordered.projectionShape hl
  obtain ⟨doms, result, hshape, hle, -, -, harity⟩ := Hraw.forallArity
  have hnum : info.numFields = doms.length - info.nparams := by
    rw [VProjectionInfo.numFields, ← hctorType, harity]
  have hshape' : info.ctorType = wrapForalls doms result := by rw [← hctorType, hshape]
  have hclosed : info.ctorType.Closed := by
    rw [← hctorType]
    obtain ⟨_, h⟩ := hwf
    exact VExpr.WF.closedN henv.ordered ⟨_, h⟩ trivial
  have hctorC := henv.ordered.projectionConstructor hl
  -- the structure type below, its head and levels
  obtain ⟨u, hsort⟩ := hm₀.isType henv hΓ
  obtain ⟨_, hhead⟩ := mkApps_head_typed henv.ordered hΓ hsort
  obtain ⟨_, _, hlvWF, _⟩ := hhead.const_inv henv hΓ
  -- the expansion above: its head
  have hexp' : Γ' ⊢ mkApps (.const info.ctorName levels) (structArgs family info params (m₀.liftN 1 k)) :
      mkApps (.const family levels) params := hexp
  obtain ⟨_, hheadE⟩ := mkApps_head_typed henv.ordered hΓ' hexp'
  obtain ⟨ci', hci', hlevelsWF, hlevelsLen⟩ := hheadE.const_inv henv hΓ'
  rw [hctorC] at hci'
  cases hci'
  have hlvLen : lv.length = info.uvars := (Lean4Lean.List.Forall₂.length_eq hlv).trans hlevelsLen
  -- the projections above and below
  have hprojA : ∀ i, i < info.numFields → ∃ A, Γ' ⊢ .proj family i (m₀.liftN 1 k) : A := fun i hi =>
    schema_mkApps_arg_type hΓ' hexp'
      (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  have hm₀' : Γ ⊢ m₀ : mkApps (.const family lv) (args ++ []) := by simpa using hm₀
  have hidx : ([] : List VExpr).length = info.nindices := by simp [hi]
  have hprojB : ∀ i, i < info.numFields → ∃ F, Γ ⊢ .proj family i m₀ : F := by
    intro i hi
    obtain ⟨A, hA⟩ := hprojA i hi
    obtain ⟨F, l, hF, hFs, hguard⟩ := hField W hΓ hΓ' hl hlvLen hlen hidx hm₀' hA
    exact ⟨F, .projDF hl hlvWF hlvLen hlen hidx hF hFs hm₀' hm₀' hclosed hguard⟩
  -- the lifted expansion at the data below, above
  have hconstDF : Γ' ⊢ .const info.ctorName levels ≡ .const info.ctorName lv :
      info.ctorType.instL levels :=
    .constDF hctorC hlevelsWF hlvWF hlevelsLen
      (forall₂_symm (fun (_ _ : VLevel) h => (Eq.symm h : _)) hlv)
  have hprojsRefl : List.Forall₂ (Params.env.IsDefEqU univs Γ')
      ((List.range info.numFields).map fun i => VExpr.proj family i (m₀.liftN 1 k))
      ((List.range info.numFields).map fun i => VExpr.proj family i (m₀.liftN 1 k)) := by
    apply Lean4Lean.List.Forall₂.rfl
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    obtain ⟨A, hA⟩ := hprojA i (List.mem_range.mp hi)
    exact ⟨_, hA⟩
  have hargsR : List.Forall₂ (Params.env.IsDefEqU univs Γ')
      (structArgs family info params (m₀.liftN 1 k))
      (structArgs family info (args.map (·.liftN 1 k)) (m₀.liftN 1 k)) :=
    List.Forall₂.append' (forall₂_symm (fun _ _ h => IsDefEqU.symm h) hargs) hprojsRefl
  have hconv : Γ' ⊢ structExpand family info levels params (m₀.liftN 1 k) ≡
      structExpand family info lv (args.map (·.liftN 1 k)) (m₀.liftN 1 k) :=
    IsDefEqU.mkApps_args hΓ' ⟨_, hconstDF⟩ hargsR hexp'
  have hliftE : (structExpand family info lv args m₀).liftN 1 k =
      structExpand family info lv (args.map (·.liftN 1 k)) (m₀.liftN 1 k) := structExpand_liftN
  have hEabove : Γ' ⊢ (structExpand family info lv args m₀).liftN 1 k :
      mkApps (.const family levels) params := by
    rw [hliftE]
    exact hexp.defeqU_l henv hΓ' hconv
  -- the expansion below is typed at some type: spine descent at the constructor telescope
  have hctorT : Γ ⊢ .const info.ctorName lv :
      wrapForalls (doms.map (·.instL lv)) (result.instL lv) := by
    have := HasType.const (Γ := Γ) hctorC hlvWF hlvLen
    rwa [show (⟨info.uvars, info.ctorType⟩ : VConstant).type = info.ctorType from rfl, hshape',
      VExpr.instL_wrapForalls] at this
  have hclT : (wrapForalls (doms.map (·.instL lv)) (result.instL lv)).ClosedN 0 := by
    rw [← VExpr.instL_wrapForalls, ← hshape']
    exact hclosed.instL
  have hlenAs : (structArgs family info args m₀).length = (doms.map (·.instL lv)).length := by
    simp only [structArgs, List.length_append, List.length_map, List.length_range, hlen, hnum]
    rw [hnparams] at hle
    omega
  have hwfAs : ∀ a ∈ structArgs family info args m₀, VExpr.WF Params.env univs Γ a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, hsort⟩ _ ha
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact hprojB i (List.mem_range.mp hi)
  have habove : VExpr.WF Params.env univs Γ'
      (mkApps ((VExpr.const info.ctorName lv).liftN 1 k)
        ((structArgs family info args m₀).map (·.liftN 1 k))) := by
    have := hEabove
    rw [hliftE, structExpand_eq, structArgs_liftN] at this
    exact ⟨_, this⟩
  have htel := telInst_descend henv hTF W hΓ hΓ' hctorT hclT hlenAs hwfAs habove
  have hE₀ := HasType.mkApps_of_tel hctorT htel
  refine ⟨hTF.retype henv W hΓ hΓ' hE₀ hsort ?_, hEabove, by rw [hliftE]; exact hconv⟩
  have hm₀W : Γ' ⊢ m₀.liftN 1 k : (mkApps (.const family lv) args).liftN 1 k := hm₀.weakN henv W
  exact hEabove.defeqU_r henv hΓ' (hm.uniqU henv hΓ' hm₀W)

/-- Descent of the composite step: structure eta at a neutral major followed by a redex fired at
the root (`MajorEtaIota`), on the lift of a term typed below. The major's family type below is
read from the head of the typed application (`RecursorRegistered.major_type`,
`QuotRegistered.major_type`, `HasType.caseMajor_type`), identified with the structure by rigidity
(`rigid_rigid`), the expansion below is typed by `structExpand_descend`, the fired redex is
transported to the lifted expansion at the data below (the right-hand side does not read the
parameters: `pat_iota_params`, `schema_struct_major`), and the fire descends by
`ParRed.descend`. -/
theorem majorEtaDescends (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (hField : ProjFieldFrontN Params.env) : MajorEtaDescends := by
  intro k Γ Γ' e T c W hΓ hΓ' he h
  obtain ⟨f, m, family, info, levels, params, heq, hl, hp, hi, hm, hexp, hfire⟩ := h
  obtain ⟨f₀, m₀, rfl, rfl, rfl⟩ := liftN_eq_app_inv heq
  obtain ⟨A, B, hf₀, hm₀A⟩ := he.app_inv henv hΓ
  -- (1) the family type of the major below, with a rigid head
  have key : ∃ I lv args, Γ ⊢ m₀ : mkApps (.const I lv) args ∧ Params.env.Rigid I := by
    rcases hfire with ⟨p, r, m1, m2, hpat, hmatch, -, -⟩ | ⟨rule, actual, hred, hX, -⟩
    · obtain ⟨sp, rfl⟩ := pat_simple hpat
      cases sp with
      | defn c => cases hmatch
      | iota rc mr cc kc =>
        obtain ⟨vs, M, hXe, hvs⟩ := iota_matches_spine hmatch
        obtain ⟨hf, -⟩ := VExpr.app.inj hXe
        obtain ⟨vs₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hf
        have hvs₀ : vs₀.length = mr := by simpa using hvs
        rcases pat_recursor hpat with ⟨data, hreg, rfl, hoff, -, ⟨index, hown⟩, -⟩ |
          ⟨hq, rfl, rfl, rfl, rfl, -⟩
        · obtain ⟨-, -, args, hM⟩ := hreg.major_type henv hΓ he (hvs₀.trans hoff.symm)
          exact ⟨_, _, args, hM, (hreg.family_head_rigid henv index hown).2⟩
        · obtain ⟨_, hhead⟩ := mkApps_head_typed henv.ordered hΓ hf₀
          obtain ⟨ci, hci, hw, hlen⟩ := hhead.const_inv henv hΓ
          rw [hq.lift] at hci
          cases hci
          have hlen2 : m1.length = 2 := hlen
          obtain ⟨u, v, rfl⟩ : ∃ u v, m1 = [u, v] := by
            match m1, hlen2 with
            | [u, v], _ => exact ⟨_, _, rfl⟩
          obtain ⟨a, r, b, fn, cp, rfl⟩ : ∃ a r b fn cp, vs₀ = [a, r, b, fn, cp] := by
            match vs₀, hvs₀ with
            | [a, r, b, fn, cp], _ => exact ⟨_, _, _, _, _, rfl⟩
          exact ⟨_, _, _, hq.major_type henv hΓ (hw u (by simp)) (hw v (by simp)) ⟨_, he⟩,
            hq.quot_rigid henv⟩
    · obtain ⟨schema, block, owner, hl', hg⟩ := hred.source.generates
      obtain ⟨hb, ho⟩ := hg.owned
      obtain ⟨base, source, sourceBlock, -, -, hcert, -, -⟩ := henv.eliminator_installed hl'
      have hlenA : actual.arguments.length = caseMajorArity schema owner :=
        hred.arguments_length.trans (hcert.arguments_length hg)
      have hX' : VExpr.app (f₀.liftN 1 k) (structExpand family info levels params (m₀.liftN 1 k)) =
          .app (mkApps (.elim actual.block actual.owner actual.levels) actual.arguments)
            (mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments) := hX
      obtain ⟨hf, -⟩ := VExpr.app.inj hX'
      obtain ⟨args₀, rfl, hargsEq⟩ := liftN_eq_mkApps_elim_inv hf
      have hlen₀ : args₀.length = caseMajorArity schema owner := by
        rw [← hlenA, hargsEq, List.length_map]
      have hbo : actual.block = block := hred.block_eq.trans hb
      have hoo : actual.owner = owner.val := hred.owner_eq.trans ho
      rw [hbo, hoo] at he
      obtain ⟨fargs, hM⟩ := HasType.caseMajor_type henv hΓ hl' hlen₀
        ⟨_, by rw [VExpr.mkApps_snoc]; exact he⟩
      exact ⟨_, _, fargs, hM, henv.case_family_head_rigid hl' hg⟩
  -- (2) the identification with the structure
  obtain ⟨I, lv, args, hm₀, hI⟩ := key
  have hm₀W : Γ' ⊢ m₀.liftN 1 k : mkApps (.const I lv) (args.map (·.liftN 1 k)) := by
    simpa only [liftN_mkApps, liftN] using hm₀.weakN henv W
  obtain ⟨_, hsortI⟩ := hm₀W.isType henv hΓ'
  have hconv : Γ' ⊢ mkApps (.const I lv) (args.map (·.liftN 1 k)) ≡
      mkApps (.const family levels) params := hm₀W.uniqU henv hΓ' hm
  obtain ⟨hIf, hlv, hargs⟩ := henv.headInversion.rigid_rigid hΓ' hI (henv.projectionRigid hl)
    (hconv.typeChain henv hΓ' hsortI)
  subst I
  have hlen : args.length = info.nparams := by
    have := Lean4Lean.List.Forall₂.length_eq hargs
    rw [List.length_map] at this
    omega
  -- (3) the expansion below
  obtain ⟨hE₀, hE₀above, hconvE⟩ :=
    structExpand_descend hTF hField W hΓ hΓ' hl hi hm₀ hlen hm hexp hlv hargs
  have hAconv : Γ ⊢ A ≡ mkApps (.const family lv) args := hm₀A.uniqU henv hΓ hm₀
  have hE₀A : Γ ⊢ structExpand family info lv args m₀ : A := hE₀.defeqU_r henv hΓ hAconv.symm
  have hX₀ : Γ ⊢ .app f₀ (structExpand family info lv args m₀) :
      B.inst (structExpand family info lv args m₀) := hf₀.app hE₀A
  -- (4) the fire transported to the lift of the expanded application
  have hliftX : (VExpr.app f₀ (structExpand family info lv args m₀)).liftN 1 k =
      .app (f₀.liftN 1 k) (structExpand family info lv (args.map (·.liftN 1 k)) (m₀.liftN 1 k)) := by
    simp only [liftN, structExpand_liftN]
  have hf₀W : Γ' ⊢ f₀.liftN 1 k : .forallE (A.liftN 1 k) (B.liftN 1 (k+1)) := by
    simpa [liftN] using hf₀.weakN henv W
  have hm₀AW : Γ' ⊢ m₀.liftN 1 k : A.liftN 1 k := hm₀A.weakN henv W
  obtain ⟨uA, hAsort⟩ := hm.isType henv hΓ'
  have hAI : Γ' ⊢ mkApps (.const family levels) params ≡ A.liftN 1 k : .sort uA :=
    (hm.uniqU henv hΓ' hm₀AW).of_l henv hΓ' hAsort
  have hconvE' : Γ' ⊢ structExpand family info levels params (m₀.liftN 1 k) ≡
      structExpand family info lv (args.map (·.liftN 1 k)) (m₀.liftN 1 k) :
      mkApps (.const family levels) params := by
    have := hconvE.of_l henv hΓ' hexp
    rwa [structExpand_liftN] at this
  have happconv : Γ' ⊢ .app (f₀.liftN 1 k) (structExpand family info levels params (m₀.liftN 1 k)) ≡
      .app (f₀.liftN 1 k) (structExpand family info lv (args.map (·.liftN 1 k)) (m₀.liftN 1 k)) :=
    ⟨_, IsDefEq.appDF hf₀W (.defeqDF hAI hconvE')⟩
  have hstep : ParRed Γ' ((VExpr.app f₀ (structExpand family info lv args m₀)).liftN 1 k) c := by
    rw [hliftX]
    rcases hfire with ⟨p, r, m1, m2, hpat, hmatch, hck, rfl⟩ | ⟨rule, actual, hred, hX, rfl⟩
    · obtain ⟨sp, rfl⟩ := pat_simple hpat
      cases sp with
      | defn c => cases hmatch
      | iota rc mr cc kc =>
        obtain ⟨g1, f2, g2, hF, hM, rfl⟩ := Pattern.Matches.app_inv hmatch
        have hM' := hM.const_arguments
        rw [structExpand_eq] at hM'
        obtain ⟨rfl, rfl, -⟩ := VExpr.mkApps_const_inj hM'
        have hM₁ : ((Pattern.const info.ctorName).varN kc).Matches
            (mkApps (.const info.ctorName levels) (structArgs family info params (m₀.liftN 1 k)))
            levels g2 := hM
        have hlenS : (structArgs family info params (m₀.liftN 1 k)).length =
            (structArgs family info (args.map (·.liftN 1 k)) (m₀.liftN 1 k)).length := by
          simp [structArgs, hlen, hp]
        obtain ⟨g2', hM₂, -⟩ := Pattern.Matches.constVarN_transport (R := fun _ _ => True)
          (ls' := lv) kc hM₁ (forall₂_of_pointwise hlenS fun _ _ _ => trivial)
        obtain ⟨hrhs, hckT⟩ := pat_iota_params hpat hl rfl hM₁ hM₂ hp (by simp [hlen])
        have hm_s := Pattern.Matches.app hF hM₂
        change ParRed Γ' _ (Pattern.RHS.apply
          (p := .app ((Pattern.const rc).varN mr) ((Pattern.const info.ctorName).varN kc))
          m1 (Sum.elim g1 g2) r.1)
        rw [hrhs m1 g1]
        exact ParRed.extra hpat hm_s (hckT m1 g1 _ hck) (fun _ => .rfl)
    · have hX' : VExpr.app (f₀.liftN 1 k) (structExpand family info levels params (m₀.liftN 1 k)) =
          .app (mkApps (.elim actual.block actual.owner actual.levels) actual.arguments)
            (mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments) := hX
      obtain ⟨hf, hctor⟩ := VExpr.app.inj hX'
      rw [structExpand_eq] at hctor
      obtain ⟨hcn, hcl, hca⟩ := VExpr.mkApps_const_inj hctor
      obtain ⟨-, -, hnf⟩ := schema_struct_major hred hΓ' hl (by rw [← hcn, ← hcl, ← hca]; exact hexp)
      let actual' : CaseSchema.Application :=
        { actual with ctorLevels := lv,
                      ctorArguments := structArgs family info (args.map (·.liftN 1 k)) (m₀.liftN 1 k) }
      have hcapEq : rule.capture actual' = rule.capture actual := by
        simp only [CaseSchema.AppliedRule.capture, actual', ← hca]
        congr 1
        have hl₁ : (structArgs family info (args.map (·.liftN 1 k)) (m₀.liftN 1 k)).length =
            (structArgs family info params (m₀.liftN 1 k)).length := by simp [structArgs, hlen, hp]
        rw [hl₁]
        exact drop_append_eq_of_length (by simp [hlen, hp]) (by
          simp only [structArgs, List.length_append, List.length_map, List.length_range, hp]
          omega)
      have hexpr' : actual'.expr =
          .app (f₀.liftN 1 k) (structExpand family info lv (args.map (·.liftN 1 k)) (m₀.liftN 1 k)) := by
        simp only [CaseSchema.Application.expr, actual', ← hf, ← hcn]
        rfl
      have hred' : CaseRedex Params.env univs Γ' rule actual' :=
        CaseRedex.transport hΓ' hred rfl rfl rfl rfl (by rw [← hcl]; exact hlv) rfl
          (by simp [actual', structArgs, hlen, hp, ← hca])
          (by
            rw [hcapEq]
            exact Lean4Lean.List.Forall₂.rfl fun e he => let ⟨_, h⟩ := hred.capture_typed he; ⟨_, h⟩)
          (by rw [← hX, hexpr']; exact happconv)
      rw [← hexpr', ← hcapEq]
      exact ParRed.schema hred' rfl (fun i hi => .rfl)
  -- (5) descent of the fire and assembly
  obtain ⟨c₀, rfl, hstep₀⟩ := ParRed.descend hTF hcase hcv W hΓ hΓ' hX₀ hstep
  exact ⟨c₀, rfl, (ReflTransGen.tail .rfl (FullStep.app .rfl
    (FullStep.structEta hl hlen hi hm₀ hE₀))).tail (.core hstep₀)⟩

end

end Lean4Lean.VEnv.StrengtheningMajorEta
