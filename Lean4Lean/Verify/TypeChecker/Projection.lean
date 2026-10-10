import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Verify.Typing.LevelEquiv

/-!
# The projection telescope walk

`inferProj` walks the constructor telescope of a structure, instantiating the parameter binders
with the parameters of the structure type and the field binders with projections of the major.
The lemmas here refine both executable walks by the syntactic instantiation
`VProjectionInfo.instantiateProjectionParameters` of the translated telescope: the executable
residual translates to the abstract residual. A field binder whose body has no loose bound
variables is kept without substitution by the executable; its translation is a lift, so the
substitution is a no-op on the abstract side, and the projection need not be typable.
-/

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

/-- The projections of `e'` at indices `position, …, position + m - 1`. -/
def projs (st : Name) (e' : VExpr) (position m : Nat) : List VExpr :=
  (List.range m).map fun j => .proj st (position + j) e'

@[simp] theorem projs_zero : projs st e' position 0 = [] := rfl

@[simp] theorem projs_length : (projs st e' position m).length = m := by simp [projs]

theorem projs_succ :
    projs st e' position (m + 1) = .proj st position e' :: projs st e' (position + 1) m := by
  simp only [projs, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 2
  funext j; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

theorem instantiateProjectionParameters.WF_all {c : VContext} {args : Array Expr} :
    ∀ {remaining : Nat} {s : State} {type : Expr} {ds : List VExpr} {b : VExpr} {position : Nat}
      {xs' : List VExpr},
    c.TrExprS type (VExpr.wrapForalls ds b) → ∀ (hle : remaining ≤ ds.length)
      (hlen : xs'.length = remaining),
    (∀ k (_hk : k < remaining), ∃ a, args[position + k]? = some a ∧
      c.TrExprS a (xs'[k]'(by omega))) →
    (∀ k (hk : k < remaining), ∃ D', VExpr.LEquiv c.lparams.length
      ((ds[k]'(by omega)).instOuter (xs'.take k)) D' ∧ c.HasType (xs'[k]'(by omega)) D') →
    s.ngen.namePrefix = pfx →
    (instantiateProjectionParameters type args position remaining).WF c s fun r _ =>
      ∀ t, r = some t → (((∃ R,
        VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls ds b) xs' = some R ∧
        c.TrExprS t R) ∧
      ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type →
        (∀ k (_hk : k < remaining) a, args[position + k]? = some a → FVarsIn P a) →
        FVarsIn P t) ∧
      ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
        (∀ k (_hk : k < remaining) a, args[position + k]? = some a →
          a.levelParamsIn Us = true ∧ FVarsIn P a) →
        t.levelParamsIn Us = true) ∧
      ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → type.ParamUniformIn c.env heads As ls →
        FVarsIn P type →
        (∀ k (_hk : k < remaining) a, args[position + k]? = some a →
          a.ParamUniformIn c.env heads As ls ∧ FVarsIn P a) →
        t.ParamUniformIn c.env heads As ls := by
  intro remaining
  induction remaining with
  | zero =>
    intro s type ds b position xs' hT _ hlen _ _ _
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact .pure fun t ht => by
      cases ht; exact ⟨⟨⟨⟨_, rfl, hT⟩, fun _ _ h _ => h⟩, fun _ _ _ h _ _ => h⟩,
        fun _ _ _ _ _ h _ _ => h⟩
  | succ remaining ih =>
    intro s type ds b position xs' hT hle hlen hargs hty hpfx
    cases ds with | nil => simp at hle | cons d ds' => ?_
    cases xs' with | nil => cases hlen | cons a' xs'' => ?_
    have hT' : c.TrExprS type (.forallE d (VExpr.wrapForalls ds' b)) := hT
    unfold instantiateProjectionParameters
    refine ((whnf.WF_below_of_fvarsIn hT').and (whnf.WF_paramUniform hT' hpfx)).bind fun e₁ _ le H₁ => ?_
    obtain ⟨⟨⟨hbe, -, hs⟩, hle₁⟩, hh₁⟩ := H₁
    have h₁ := hs _ _ rfl
    split <;> [skip; exact .pure nofun]
    rename_i n d₁ body bi
    let .forallE hd hW hd₁ hbody := h₁
    split <;> [skip; exact .pure nofun]
    rename_i a ha
    have ⟨a₀, ha₀, ha₀'⟩ := hargs 0 (Nat.succ_pos _)
    simp only [Nat.add_zero] at ha₀
    rw [ha] at ha₀; cases ha₀
    have ⟨D', hL, hD'⟩ := hty 0 (Nat.succ_pos _)
    simp only [List.take_zero, VExpr.instOuter_nil, List.getElem_cons_zero] at hL hD'
    have ⟨_, hd'⟩ := hd
    have hda : c.HasType a' d :=
      hD'.defeqU_r c.Ewf c.Δwf (hL.defeq c.Ewf c.Δwf.toCtx ⟨_, hd'⟩).symm
    have hinst := hbody.inst c.Ewf.orderedStrong hda ha₀'
    rw [Expr.instantiate1_eq]
    have hT'' : c.TrExprS (body.instantiate1' a)
        (VExpr.wrapForalls (VExpr.instDomains ds' a' 0) (b.inst a' (0 + ds'.length))) := by
      rw [← VExpr.wrapForalls_inst]; exact hinst
    refine (ih hT'' (by simpa using Nat.le_of_succ_le_succ hle) (by simpa using hlen) ?_ ?_
      (State.LE.namePrefix_eq hpfx le)).mono fun r _ _ H t ht => ?_
    · intro k hk
      have ⟨a₁, h1, h2⟩ := hargs (k + 1) (Nat.succ_lt_succ hk)
      exact ⟨a₁, by rw [← h1]; congr 1; omega, h2⟩
    · intro k hk
      have ⟨D', h1, h2⟩ := hty (k + 1) (Nat.succ_lt_succ hk)
      refine ⟨D', ?_, h2⟩
      have hk' : k < xs''.length := by simp at hlen; omega
      rw [VExpr.instDomains_getElem _ _ _ _ (by simp at hle; omega), Nat.zero_add]
      simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
        List.length_take, Nat.min_eq_left (Nat.le_of_lt hk')] at h1
      exact h1
    · obtain ⟨⟨⟨⟨R, hR, hR'⟩, hfv⟩, hlv⟩, hhv⟩ := H t ht
      refine ⟨⟨⟨⟨R, ?_, hR'⟩, fun P hP hfvt hfva => ?_⟩, fun Us P hsc hlt hfvt hla => ?_⟩,
        fun heads As ls P hsc hht hfvt hha => ?_⟩
      · show VProjectionInfo.instantiateProjectionParameters
          (.forallE d (VExpr.wrapForalls ds' b)) (a' :: xs'') = some R
        simp only [VProjectionInfo.instantiateProjectionParameters, VExpr.wrapForalls_inst]
        exact hR
      · refine hfv P hP (FVarsIn.instantiate1 (hbe P hP hfvt).2 (hfva 0 (Nat.succ_pos _) a ?_))
          fun k hk a₁ h => hfva (k + 1) (Nat.succ_lt_succ hk) a₁ (by rw [← h]; congr 1; omega)
        simpa using ha
      · have ha0 := hla 0 (Nat.succ_pos _) a (by simpa using ha)
        have hb₁ := hle₁ Us P hsc hlt hfvt
        simp only [Expr.levelParamsIn, Bool.and_eq_true] at hb₁
        refine hlv Us P hsc (Expr.levelParamsIn_instantiate1 hb₁.2 ha0.1)
          (FVarsIn.instantiate1 (hbe P hsc.1 hfvt).2 ha0.2)
          fun k hk a₁ h => hla (k + 1) (Nat.succ_lt_succ hk) a₁ (by rw [← h]; congr 1; omega)
      · have ha0 := hha 0 (Nat.succ_pos _) a (by simpa using ha)
        have hb₁ := hh₁ heads As ls P hsc hht hfvt
        refine hhv heads As ls P hsc ((hb₁.forallE_inv.2).instantiate1' hsc.params.fvars ha0.1 0)
          (FVarsIn.instantiate1 (hbe P hsc.up hfvt).2 ha0.2)
          fun k hk a₁ h => hha (k + 1) (Nat.succ_lt_succ hk) a₁ (by rw [← h]; congr 1; omega)

/-! ### The walk over the constructor type

Along the walk the current type translates to the remaining telescope, and `whnf` returns a
term translating to that same `forallE` (`whnf.WF_below_of_fvarsIn`). A parameter or a dependent
field is substituted (`TrExprS.inst`); at a non-dependent field the executable keeps the body,
whose translation under the binder is the lift of a translation outside it
(`TrExprS.lowerClosedBV`, strengthening of the binder), so the substitution of the projection is
a no-op on the abstract side and the projection need not be typable. -/

/-- A body with no loose bound variable, translated under a binder, is translated outside it,
to a term whose lift is its translation under the binder. The binder is replaced by a fresh
free variable, which is then removed (`TrExprS.restrictFV_inv`, strengthening). -/
theorem TrExprS.lowerClosedBV {c : VContext} {s : State} (wf : s.WF c) (hd : c.IsType d')
    (h : body.looseBVarRange' = 0)
    (H : TrExprS c.venv c.lparams ((none, .vlam d') :: c.vlctx) body B) :
    ∃ B₀, c.TrExprS body B₀ ∧ B = B₀.lift := by
  let v : FVarId := ⟨s.ngen.curr⟩
  have hΔ : VLCtx.WF c.venv c.lparams.length ((some (v, []), .vlam d') :: c.vlctx) := by
    refine ⟨c.Δwf, ?_, hd⟩
    rintro _ _ ⟨⟩; simp; exact fun h => s.ngen.not_reserves_self (wf.ngen_wf _ h)
  have := H.inst_fvar c.Ewf.orderedStrong hΔ
  rw [Expr.instantiate1'_eq_self (by rw [h]; exact Nat.zero_le _)] at this
  obtain ⟨B₀, hB₀, rfl⟩ := this.restrictFV_inv c.Ewf (.skip_fvar _ _ .refl) hΔ
    (by simpa using H.fvarsIn)
  exact ⟨B₀, hB₀, rfl⟩

theorem instantiateProjectionFields.WF_all {c : VContext} {G : VLevel → Prop}
    (he : c.TrExprS struct e')
    (hG0 : G .zero) (hG : maybePropType = false → ∀ u, G u) :
    ∀ {remaining : Nat} {s : State} {type : Expr} {ds : List VExpr} {b : VExpr}
      {position : Nat},
    c.TrExprS type (VExpr.wrapForalls ds b) →
    ∀ (hle : remaining ≤ ds.length),
    (∀ m (hm : m < remaining) u,
      c.HasType ((ds[m]'(by omega)).instOuter (projs st e' position m)) (.sort u) → G u →
      c.HasType (.proj st (position + m) e')
        ((ds[m]'(by omega)).instOuter (projs st e' position m))) →
    s.ngen.namePrefix = pfx →
    (instantiateProjectionFields st struct maybePropType type position remaining).WF c s
      fun r _ => ∀ t, r = some t → (((∃ R,
        VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls ds b)
          (projs st e' position remaining) = some R ∧
        c.TrExprS t R) ∧
      ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P t) ∧
      ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
        struct.levelParamsIn Us = true → FVarsIn P struct → t.levelParamsIn Us = true) ∧
      ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → type.ParamUniformIn c.env heads As ls →
        FVarsIn P type → struct.ParamUniformIn c.env heads As ls → FVarsIn P struct →
        projAvoidsHeads c.env heads st → t.ParamUniformIn c.env heads As ls := by
  intro remaining
  induction remaining with
  | zero =>
    intro s type ds b position hT _ _ _
    exact .pure fun t ht => by
      cases ht; exact ⟨⟨⟨⟨_, rfl, hT⟩, fun _ _ h _ => h⟩, fun _ _ _ h _ _ _ => h⟩,
        fun _ _ _ _ _ h _ _ _ _ => h⟩
  | succ remaining ih =>
    intro s type ds b position hT hle hproj hpfx
    cases ds with | nil => simp at hle | cons d ds' => ?_
    have hTS : c.TrExprS type (.forallE d (VExpr.wrapForalls ds' b)) := hT
    unfold instantiateProjectionFields
    refine ((whnf.WF_below_of_fvarsIn hTS).and (whnf.WF_paramUniform hTS hpfx)).bind
      fun e₁ s₁ le₁ H₁ => ?_
    obtain ⟨⟨⟨hbe, -, hs⟩, hle₁⟩, hh₁⟩ := H₁
    have hpfx₁ := State.LE.namePrefix_eq hpfx le₁
    have h₁ := hs _ _ rfl
    split <;> [skip; exact .pure nofun]
    rename_i n d₁ body bi
    let .forallE hd hW hd₁ hbody := h₁
    have hbl : ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
        d₁.levelParamsIn Us = true ∧ body.levelParamsIn Us = true := fun Us P hsc hlt hfvt => by
      have := hle₁ Us P hsc hlt hfvt
      simpa only [Expr.levelParamsIn, Bool.and_eq_true] using this
    -- the continuation: the walk on the rest of the telescope
    have cont : ∀ {s : State} (type' : Expr), s.ngen.namePrefix = pfx →
        c.TrExprS type' ((VExpr.wrapForalls ds' b).inst (.proj st position e')) →
        (∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P type') →
        (∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
          struct.levelParamsIn Us = true → FVarsIn P struct → type'.levelParamsIn Us = true) →
        (∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → type.ParamUniformIn c.env heads As ls →
          FVarsIn P type → struct.ParamUniformIn c.env heads As ls → FVarsIn P struct →
          projAvoidsHeads c.env heads st → type'.ParamUniformIn c.env heads As ls) →
        RecM.WF c s (instantiateProjectionFields st struct maybePropType type' (position + 1)
          remaining) fun r _ => ∀ t, r = some t → (((∃ R,
          VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls (d :: ds') b)
            (projs st e' position (remaining + 1)) = some R ∧
            c.TrExprS t R) ∧
          ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P t) ∧
          ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
            struct.levelParamsIn Us = true → FVarsIn P struct → t.levelParamsIn Us = true) ∧
          ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → type.ParamUniformIn c.env heads As ls →
            FVarsIn P type → struct.ParamUniformIn c.env heads As ls → FVarsIn P struct →
            projAvoidsHeads c.env heads st → t.ParamUniformIn c.env heads As ls := by
      intro s type' hps hT'' hfv' hlv' hhv'
      rw [VExpr.wrapForalls_inst] at hT''
      have E : ∀ m (hm' : m < ds'.length),
          ((VExpr.instDomains ds' (.proj st position e') 0)[m]'(by simpa using hm')).instOuter
              (projs st e' (position + 1) m) =
            (ds'[m]'hm').instOuter (projs st e' position (m + 1)) := by
        intro m hm'
        rw [VExpr.instDomains_getElem _ _ _ _ hm', projs_succ,
          VExpr.instOuter_cons, projs_length, Nat.zero_add]
      refine (ih hT'' (by simpa using Nat.le_of_succ_le_succ hle) ?_ hps).mono
        fun r _ _ H t ht => ?_
      · intro m hm u
        have hm' : m < ds'.length := by simp at hle; omega
        rw [E m hm', show position + 1 + m = position + (m + 1) by omega]
        exact hproj (m + 1) (Nat.succ_lt_succ hm) u
      · obtain ⟨⟨⟨⟨R, hR, hR'⟩, hfv⟩, hlv⟩, hhv⟩ := H t ht
        refine ⟨⟨⟨⟨R, ?_, hR'⟩, fun P hP hfvt hfvs => hfv P hP (hfv' P hP hfvt hfvs) hfvs⟩,
          fun Us P hsc hlt hfvt hls hfvs =>
            hlv Us P hsc (hlv' Us P hsc hlt hfvt hls hfvs) (hfv' P hsc.1 hfvt hfvs) hls hfvs⟩,
          fun heads As ls P hsc hht hfvt hhs hfvs hok =>
            hhv heads As ls P hsc (hhv' heads As ls P hsc hht hfvt hhs hfvs hok)
              (hfv' P hsc.up hfvt hfvs) hhs hfvs hok⟩
        rw [projs_succ]
        show VProjectionInfo.instantiateProjectionParameters (.forallE d (VExpr.wrapForalls ds' b))
          (_ :: _) = some R
        simp only [VProjectionInfo.instantiateProjectionParameters, VExpr.wrapForalls_inst]
        exact hR
    -- typing of the projection at the current binder, from the sort of the domain
    have hp0 : ∀ u, c.HasType d (.sort u) → G u → c.HasType (.proj st position e') d := by
      intro u hu hGu
      have := hproj 0 (Nat.succ_pos _) u (by simpa using hu) hGu
      simpa using this
    split
    · -- the body depends on the field: substitute the projection
      have main {s : State} (hps : s.ngen.namePrefix = pfx)
          (hp : c.HasType (.proj st position e') d) :
          RecM.WF c s (instantiateProjectionFields st struct maybePropType
            (body.instantiate1 (.proj st position struct)) (position + 1) remaining)
            fun r _ => ∀ t, r = some t → (((∃ R,
              VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls (d :: ds') b)
                (projs st e' position (remaining + 1)) = some R ∧
            c.TrExprS t R) ∧
              ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P t) ∧
              ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
                struct.levelParamsIn Us = true → FVarsIn P struct →
                t.levelParamsIn Us = true) ∧
              ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → type.ParamUniformIn c.env heads As ls →
                FVarsIn P type → struct.ParamUniformIn c.env heads As ls → FVarsIn P struct →
                projAvoidsHeads c.env heads st → t.ParamUniformIn c.env heads As ls := by
        have hp_tr : c.TrExprS (.proj st position struct) (.proj st position e') :=
          .proj he ⟨_, hp⟩
        rw [Expr.instantiate1_eq]
        exact cont _ hps (hbody.inst c.Ewf.orderedStrong hp hp_tr)
          (fun P hP hfvt hfvs => FVarsIn.instantiate1 (hbe P hP hfvt).2 hfvs)
          (fun Us P hsc hlt hfvt hls _ =>
            Expr.levelParamsIn_instantiate1 (hbl Us P hsc hlt hfvt).2 hls)
          fun heads As ls P hsc hht hfvt hhs _ hok =>
            (hh₁ heads As ls P hsc hht hfvt).forallE_inv.2.instantiate1' hsc.params.fvars
              (.proj hok hhs) 0
      split
      · rename_i hmp
        refine (isProp.WF hd₁).bind fun bp _ le₂ hbp => ?_
        split <;> [skip; exact .pure nofun]
        rename_i hbp'
        exact main (State.LE.namePrefix_eq hpfx₁ le₂) (hp0 .zero (hbp (by simpa using hbp')) hG0)
      · rename_i hmp
        have ⟨u, hu⟩ := hd
        exact main hpfx₁ (hp0 u hu (hG (by simpa using hmp) u))
    · -- the body does not depend on the field
      rename_i hnl
      have hlr : body.looseBVarRange' = 0 := by simpa [Expr.hasLooseBVars] using hnl
      refine .stateWF fun wf₁ => ?_
      obtain ⟨B₀, hB₀, hBeq⟩ := TrExprS.lowerClosedBV wf₁ hd hlr hbody
      refine cont _ hpfx₁ ?_ (fun P hP hfvt _ => (hbe P hP hfvt).2)
        (fun Us P hsc hlt hfvt _ _ => (hbl Us P hsc hlt hfvt).2)
        fun heads As ls P hsc hht hfvt _ _ _ => (hh₁ heads As ls P hsc hht hfvt).forallE_inv.2
      rw [hBeq, VExpr.inst_lift]; exact hB₀

/-! ### The walk past the fields

`inferProj` does not compare the field index with the constructor's field count: like
`type_checker::infer_proj`, it walks the constructor telescope and fails when a binder is missing.
Past the fields the walk reaches the constructor's result type, an application of the rigid
structure type, which `whnf` cannot turn into a binder (head inversion). -/

/-- An application spine headed by the constant `n`. -/
def _root_.Lean4Lean.VExpr.HeadName (n : Name) : VExpr → Prop
  | .const m _ => m = n
  | .app f _ => VExpr.HeadName n f
  | _ => False

theorem _root_.Lean4Lean.VExpr.HeadName.eq_mkApps {n : Name} :
    ∀ {e : VExpr}, e.HeadName n → ∃ ls xs, e = VExpr.mkApps (.const n ls) xs
  | .const m ls, h => ⟨ls, [], by cases h; rfl⟩
  | .app f a, h => by
    obtain ⟨ls, xs, rfl⟩ := VExpr.HeadName.eq_mkApps (e := f) h
    exact ⟨ls, xs ++ [a], by simp [VExpr.mkApps]⟩

theorem _root_.Lean4Lean.VExpr.HeadName.inst {n : Name} {e : VExpr} (h : e.HeadName n) :
    (e.inst a k).HeadName n := by
  induction e generalizing k with
  | app f _ ihf _ => exact ihf h
  | const => exact h
  | _ => exact h.elim

theorem _root_.Lean4Lean.VExpr.HeadName.instL {n : Name} {e : VExpr} (h : e.HeadName n) :
    (e.instL ls).HeadName n := by
  induction e with
  | app f _ ihf _ => exact ihf h
  | const => exact h
  | _ => exact h.elim

theorem _root_.Lean4Lean.VExpr.HeadName.instOuterAt {n : Name} :
    ∀ {e : VExpr} (args : List VExpr) (k : Nat), e.HeadName n → (e.instOuterAt args k).HeadName n
  | _, [], _, h => h
  | _, _ :: as, k, h => VExpr.HeadName.instOuterAt as k h.inst

theorem _root_.Lean4Lean.VExpr.HeadName.of_lequiv {n : Name} {e e' : VExpr}
    (H : VExpr.LEquiv U e e') (h : e'.HeadName n) : e.HeadName n := by
  induction H with
  | refl => exact h
  | const => exact h
  | app _ _ ihf _ => exact ihf h
  | _ => exact h.elim

theorem _root_.Lean4Lean.VExpr.HeadName.of_getAppFnArgs_go {n : Name} {e : VExpr}
    {args : List VExpr} {ls : List VLevel}
    (h : (VExpr.getAppFnArgs.go e args).1 = .const n ls) : e.HeadName n := by
  induction e generalizing args with
  | app f a ihf _ => exact ihf (args := a :: args) h
  | const => simp [VExpr.getAppFnArgs.go] at h; exact h.1
  | _ => simp [VExpr.getAppFnArgs.go] at h

theorem _root_.Lean4Lean.VExpr.HeadName.of_getAppFnArgs {n : Name} {e : VExpr}
    {ls : List VLevel} (h : e.getAppFnArgs.1 = .const n ls) : e.HeadName n :=
  .of_getAppFnArgs_go h

/-- `whnf` of a term translating to an application of a rigid constant is not a binder. -/
theorem whnf.WF_not_forallE {c : VContext} {s : State} {t : Expr} {R : VExpr} {n : Name}
    (ht : c.TrExprS t R) (hR : R.HeadName n) (hrigid : c.venv.Rigid n) :
    RecM.WF c s (whnf t) fun w _ => ∀ nm d b bi, w ≠ .forallE nm d b bi := by
  refine (whnf.WF ht).mono fun w _ _ ⟨_, W, hW, hdef⟩ nm d b bi hw => ?_
  subst hw
  let .forallE hA hB _ _ := hW
  obtain ⟨ls, xs, rfl⟩ := hR.eq_mkApps
  have ⟨_, hu⟩ := VEnv.IsType.forallE hA hB
  exact VEnv.IsDefEqU.rigidApp_forallE_inv c.Ewf c.Δwf.toCtx hrigid
    (hu.defeqU_l c.Ewf c.Δwf hdef) hdef.symm

/-- Splitting the field walk after `k` steps. -/
theorem instantiateProjectionFields_add (st : Name) (struct : Expr) (mp : Bool) :
    ∀ (k r : Nat) (type : Expr) (pos : Nat),
      instantiateProjectionFields st struct mp type pos (k + r) =
        (instantiateProjectionFields st struct mp type pos k >>= fun
          | some t => instantiateProjectionFields st struct mp t (pos + k) r
          | none => pure none)
  | 0, r, type, pos => by simp [instantiateProjectionFields]
  | k + 1, r, type, pos => by
    rw [show k + 1 + r = (k + r) + 1 by omega]
    simp only [instantiateProjectionFields, bind_assoc]
    congr 1; funext w
    split
    · split
      · split
        · simp only [bind_assoc]; congr 1; funext b
          split <;> first
            | simp; done
            | rw [instantiateProjectionFields_add st struct mp k r,
                show pos + 1 + k = pos + (k + 1) by omega]
        · rw [instantiateProjectionFields_add st struct mp k r,
            show pos + 1 + k = pos + (k + 1) by omega]
      · rw [instantiateProjectionFields_add st struct mp k r,
          show pos + 1 + k = pos + (k + 1) by omega]
    · simp

/-- Past the fields, the walk returns nothing, or (after no further step) its input. -/
theorem instantiateProjectionFields.WF_stuck {c : VContext} {t : Expr} {R : VExpr} {n : Name}
    (ht : c.TrExprS t R) (hR : R.HeadName n) (hrigid : c.venv.Rigid n) :
    ∀ (r pos : Nat) (s : State),
      (instantiateProjectionFields st struct mp t pos r).WF c s
        fun o _ => ∀ t', o = some t' → t' = t
  | 0, _, _ => by
    unfold instantiateProjectionFields; exact .pure fun _ h => (Option.some.inj h).symm
  | _ + 1, _, _ => by
    unfold instantiateProjectionFields
    refine (whnf.WF_not_forallE ht hR hrigid).bind fun w _ _ hw => ?_
    split
    · exact absurd rfl (hw _ _ _ _)
    · exact .pure nofun

end Lean4Lean.TypeChecker.Inner
