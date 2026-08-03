import Lean4Lean.Verify.ModDivReflect
import Lean4Lean.Verify.BitwiseReflect
import Lean4Lean.Environment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

open private Lean.Kernel.Environment.add from Lean.Environment

theorem ConstantInfo.defnInfo_safety (v : DefinitionVal) :
    (ConstantInfo.defnInfo v).safety = v.safety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  cases v.safety <;> rfl

theorem checkNoMVarNoFVar.WF {env : Environment} {n : Name} {e : Expr} :
    (Lean.Kernel.Environment.checkNoMVarNoFVar env n e).WF fun _ =>
      e.hasMVar = false ∧ e.hasFVar = false := by
  intro _ h
  simp [Lean.Kernel.Environment.checkNoMVarNoFVar,
    Lean.Kernel.Environment.checkNoMVar,
    Lean.Kernel.Environment.checkNoFVar] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · simp_all

theorem checkName.WF {env : Environment} {n : Name} {allowPrimitive : Bool}
    (hmap : env.constants.WF) :
    (Lean.Kernel.Environment.checkName env n allowPrimitive).WF fun _ =>
      env.find? n = none ∧
      (Lean.Kernel.Environment.primitives.contains n → allowPrimitive = true) := by
  intro _ h
  by_cases hfresh : env.constants.contains n = true
  · unfold Lean.Kernel.Environment.checkName at h
    rw [if_pos (by simpa [Lean.Kernel.Environment.contains] using hfresh)] at h
    change (Except.error (.alreadyDeclared env n) : Except Exception Unit) =
      .ok _ at h
    contradiction
  · have hfresh' : env.constants.contains n = false := by
      simpa using hfresh
    have hfind : env.find? n = none := by
      rw [SMap.find?_isSome] at hfresh'
      have hm : env.constants.find? n = none := by
        cases hm : env.constants.find? n <;> simp_all
      change env.constants.find?' n = none
      rwa [hmap.find?'_eq_find?]
    by_cases hallow : allowPrimitive = true
    · exact ⟨hfind, fun _ => hallow⟩
    · have hallow' : allowPrimitive = false := by simpa using hallow
      by_cases hp :
          Lean.Kernel.Environment.primitives.contains n = true
      · unfold Lean.Kernel.Environment.checkName at h
        rw [if_neg (by simpa [Lean.Kernel.Environment.contains] using hfresh),
          if_neg hallow, if_pos hp] at h
        change (Except.error _ : Except Exception Unit) = .ok _ at h
        contradiction
      · exact ⟨hfind, fun hp' => (hp hp').elim⟩

theorem checkConstantValBody.WF
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {env : Environment} {v : ConstantVal} :
    TypeChecker.M.WF c s (checkConstantValBody env v) fun _ _ =>
      ∃ type', c.TrExprS v.type type' ∧ c.IsType type' := by
  simp only [checkConstantValBody]
  have hdup :
      (Lean.Kernel.Environment.checkDuplicatedUnivParams v.levelParams).WF
        fun _ => True :=
    fun _ _ => trivial
  refine (TypeChecker.M.WF.liftExcept hdup).bind fun _ _ _ _ => ?_
  refine (TypeChecker.M.WF.liftExcept checkNoMVarNoFVar.WF).bind
    fun _ _ _ hclosed => ?_
  have hfvars : v.type.FVarsIn (· ∈ c.vlctx.fvars) := by
    apply fvarsIn_iff.mpr
    refine ⟨?_, fvarsIn_iff_hasMVar.mpr hclosed.1⟩
    intro fv hfv
    have hempty : v.type.fvarsList = [] := fvarsList_eq_nil.2 hclosed.2
    simp [hempty] at hfv
  refine (TypeChecker.checkType.WF hfvars).bind fun sort _ _ hsort => ?_
  rcases hsort with ⟨type', sort', _, htype, hsort, htypeT⟩
  refine (TypeChecker.ensureSort.WF hsort).bind fun _ _ _ h => .pure ?_
  rcases h with ⟨⟨sort'', hsort'', heq⟩, u, rfl⟩
  cases hsort'' with
  | sort hu =>
    exact ⟨type', htype, _, htypeT.defeqU_r c.Ewf c.Δwf heq.symm⟩

theorem checkConstantVal.WF
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {env : Environment} {v : ConstantVal} {allowPrimitive : Bool}
    (hmap : env.constants.WF) :
    TypeChecker.M.WF c s (checkConstantVal env v allowPrimitive) fun _ _ =>
      env.find? v.name = none ∧
      (Lean.Kernel.Environment.primitives.contains v.name →
        allowPrimitive = true) ∧
      ∃ type', c.TrExprS v.type type' ∧ c.IsType type' := by
  simp only [checkConstantVal]
  refine (TypeChecker.M.WF.liftExcept (checkName.WF hmap)).bind
    fun _ _ _ hname => ?_
  exact checkConstantValBody.WF.mono fun _ _ _ hbody =>
    ⟨hname.1, hname.2, hbody⟩

def MutualHeaderRel (safety : DefinitionSafety) (env : Environment)
    (venv : VEnv) (v₀ v : DefinitionVal) (v' : VDefVal) : Prop :=
  v.safety = safety ∧
  v.levelParams = v₀.levelParams ∧
  env.find? v.name = none ∧
  ¬Lean.Kernel.Environment.primitives.contains v.name ∧
  v'.name = v.name ∧
  v'.uvars = v.levelParams.length ∧
  TrExprS venv v.levelParams [] v.type v'.type ∧
  v'.toVConstant.WF venv

theorem MutualHeaderRel.toFinal (H : MutualHeaderRel safety env venv v₀ v v') :
    TrConstVal safety venv (.defnInfo v) v'.toVConstVal := by
  rcases H with ⟨hs, _, _, _, hn, hu, ht, _⟩
  exact ⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hs]
    exact DefinitionSafety.le_rfl,
    by
      dsimp [ConstantInfo.levelParams, ConstantInfo.toConstantVal]
      exact hu.symm,
    ht⟩, hn.symm⟩

theorem MutualHeaderRel.toOpaque (H : MutualHeaderRel safety env venv v₀ v v') :
    TrConstVal safety venv (.opaqueInfo (mutualOpaqueHeader v)) v'.toVConstVal := by
  rcases H with ⟨hs, _, _, _, hn, hu, ht, _⟩
  refine ⟨⟨?_, ?_, ht⟩, hn.symm⟩
  · subst safety
    cases h : v.safety with
    | «unsafe» => simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial, mutualOpaqueHeader, h]
    | safe => simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial, mutualOpaqueHeader, h]
    | «partial» =>
      simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial, mutualOpaqueHeader, h] using
        (DefinitionSafety.le_safe (a := .partial))
  · exact hu.symm

theorem List.Forall₂.mutualHeader_names_nodup
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs')
    (hnodup : (vs.map (fun v => v.name)).Nodup) :
    (vs'.map (fun v => v.name)).Nodup := by
  have heq : vs.map (fun v => v.name) = vs'.map (fun v => v.name) := by
    induction H with
    | nil => rfl
    | @cons a b xs ys h hrel ih =>
      simp only [List.map_cons]
      have htail : (xs.map (fun v => v.name)).Nodup := by
        exact (List.nodup_cons.mp (show
          (a.name :: xs.map (fun v => v.name)).Nodup by simpa using hnodup)).2
      rw [← h.2.2.2.2.1, ih htail]
  rw [← heq]
  exact hnodup

theorem List.Forall₂.mutualHeader_toFinal
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs') :
    List.Forall₂ (fun v v' =>
      TrConstVal safety venv (.defnInfo v) v'.toVConstVal) vs vs' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.toFinal ih

theorem List.Forall₂.mutualHeader_toOpaque
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs') :
    List.Forall₂ (fun v v' =>
      TrConstVal safety venv (.opaqueInfo (mutualOpaqueHeader v)) v'.toVConstVal) vs vs' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.toOpaque ih

theorem List.Forall₂.mutualHeader_fresh
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs') :
    ∀ v ∈ vs, env.find? v.name = none := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h.2.2.1
    · exact ih v hv

theorem List.Forall₂.mutualHeader_sameSafety
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs') :
    ∀ v ∈ vs, v.safety = safety := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h.1
    · exact ih v hv

theorem List.Forall₂.mutualHeader_notPrimitive
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs') :
    ∀ v ∈ vs, ¬Lean.Kernel.Environment.primitives.contains v.name := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h.2.2.2.1
    · exact ih v hv

theorem List.Forall₂.mutualHeader_target_notPrimitive
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs') :
    ∀ v' ∈ vs', ¬Lean.Kernel.Environment.primitives.contains v'.name := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro v' hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simpa [h.2.2.2.2.1] using h.2.2.2.1
    · exact ih v' hv

theorem List.Forall₂.mutualHeader_types
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs') :
    ∀ v' ∈ vs', v'.toVConstant.WF venv := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro v' hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h.2.2.2.2.2.2.2
    · exact ih v' hv

theorem List.Forall₂.mutualHeader_target_fresh
    (H : List.Forall₂ (MutualHeaderRel safety env venv v₀) vs vs')
    (htr : TrEnv safety env venv) :
    ∀ v' ∈ vs', venv.constants v'.name = none := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro v' hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · cases hc : venv.constants v'.name with
      | none => rfl
      | some ci =>
        have hs := (htr.find?_iff (name := v'.name)).2 ⟨ci, hc⟩
        obtain ⟨ci', hfind, _⟩ := hs
        rw [h.2.2.2.2.1, h.2.2.1] at hfind
        contradiction
    · exact ih v' hv

theorem mutualNamesUnique_nodup (h : mutualNamesUnique vs = true) :
    (vs.map (fun v => v.name)).Nodup := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
    simp only [mutualNamesUnique, Bool.and_eq_true, Bool.not_eq_true'] at h
    apply List.nodup_cons.mpr
    refine ⟨?_, ih h.2⟩
    intro hmem
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp hmem
    have : vs.any (fun w => w.name == v.name) = true :=
      List.any_eq_true.mpr ⟨w, hw, by simpa [heq]⟩
    rw [h.1] at this
    contradiction

theorem checkMutualHeaders.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v₀ : DefinitionVal) (vs : List DefinitionVal)
    (safety : DefinitionSafety) (hsafety₀ : v₀.safety = safety)
    (state : TypeChecker.VState := {}) :
    (checkMutualHeaders env v₀ vs).WF
      (.mk' wf safety v₀.levelParams) state fun _ _ =>
        ∃ vs', List.Forall₂
          (MutualHeaderRel safety env (ves.venv safety) v₀) vs vs' := by
  induction vs generalizing state with
  | nil =>
    exact .pure ⟨[], .nil⟩
  | cons v vs ih =>
    unfold checkMutualHeaders
    by_cases hsafety : v.safety != v₀.safety
    · rw [if_pos hsafety]
      exact .throw
    · rw [if_neg hsafety]
      have hsafety' : v.safety = v₀.safety := by simpa using hsafety
      by_cases hlevels : v.levelParams != v₀.levelParams
      · rw [if_pos hlevels]
        exact .throw
      · rw [if_neg hlevels]
        simp only [pure_bind]
        have hlevels' : v.levelParams = v₀.levelParams := by simpa using hlevels
        refine (checkConstantVal.WF
          (c := .mk' wf safety v₀.levelParams) (s := state)
          (env := env) (v := v.toConstantVal)
          (wf.tr (safety := safety)).map_wf).bind fun _ state' _ hchecked => ?_
        obtain ⟨hfresh, hreserved, type', htype, htypeWF⟩ := hchecked
        have hn : ¬Lean.Kernel.Environment.primitives.contains v.name := by
          intro hp
          have := hreserved hp
          contradiction
        let v' : VDefVal := {
          name := v.name
          uvars := v.levelParams.length
          type := type'
          value := default }
        have htype' : TrExprS (ves.venv safety) v.levelParams [] v.type type' := by
          simpa [hlevels'] using htype
        have hvWF : v'.toVConstant.WF (ves.venv safety) := by
          simpa [v', hlevels'] using htypeWF
        refine (ih (state := state')).mono fun _ _ _ ⟨vs', hvs'⟩ =>
          ⟨v' :: vs', .cons ?_ hvs'⟩
        exact ⟨hsafety'.trans hsafety₀, hlevels', hfresh, hn, rfl, rfl,
          htype', hvWF⟩

theorem TypeChecker.M.WF.runContext
    {c : TypeChecker.VContext} {x : TypeChecker.M α} {Q : α → Prop}
    {env : Environment} {safety : DefinitionSafety} {lctx : LocalContext}
    {lparams : List Name} {fuel : FuelConfig}
    (hc : c.toContext = { env, safety, lctx, lparams, fuel })
    (hstate : TypeChecker.VState.WF c {})
    (H : x.WF c {} fun a _ => Q a) :
    (TypeChecker.M.run env safety lctx lparams fuel x).WF Q := by
  unfold TypeChecker.M.WF at H
  rw [hc] at H
  intro a eq
  simp [TypeChecker.M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq
  rename_i eq
  let ⟨_, _, _, _, hpost⟩ := H hstate _ _ eq
  exact hpost

theorem checkBodyCore.WF' (c : TypeChecker.VContext)
    (decl : Declaration) (name : Name) (type value : Expr) (type' : VExpr)
    (hdeclType : c.TrExprS type type')
    (hclosed : value.hasMVar = false ∧ value.hasFVar = false)
    (state : TypeChecker.VState := {}) :
    ((do
      let valueType ← TypeChecker.checkType value
      if !(← TypeChecker.isDefEq valueType type) then
        throw <| Exception.declTypeMismatch c.env decl valueType) :
      TypeChecker.M Unit).WF c state fun _ _ =>
        ∃ value', c.TrExprS value value' ∧ c.HasType value' type' := by
  have hfvars : value.FVarsIn (· ∈ c.vlctx.fvars) := by
    apply fvarsIn_iff.mpr
    refine ⟨?_, fvarsIn_iff_hasMVar.mpr hclosed.1⟩
    intro fv hfv
    have hempty : value.fvarsList = [] := fvarsList_eq_nil.2 hclosed.2
    simp [hempty] at hfv
  refine (TypeChecker.checkType.WF hfvars).bind
    fun _ _ _ ⟨value', valueType', _, hvalue, hvalueType, hhasType⟩ => ?_
  refine (TypeChecker.isDefEq.WF hvalueType hdeclType).bind
    fun equal _ _ hequal => ?_
  split
  · exact .throw
  · refine .pure ⟨value', hvalue, ?_⟩
    have heq : equal = true := by cases equal <;> simp_all
    exact hhasType.defeqU_r c.Ewf c.Δwf (hequal heq)

def MutualBodyRel (safety : DefinitionSafety) (env : Environment)
    (base headers : VEnv) (v₀ v : DefinitionVal) (v' : VDefVal) : Prop :=
  ∃ header,
    MutualHeaderRel safety env base v₀ v header ∧
    v'.toVConstVal = header.toVConstVal ∧
    TrExprS headers v.levelParams [] v.value v'.value ∧
    v'.WF headers

def MutualHeaderSame (header v' : VDefVal) : Prop :=
  v'.name = header.name ∧ v'.toVConstant = header.toVConstant

theorem checkMutualBodies.WF
    (c : TypeChecker.VContext)
    (origEnv : Environment)
    (all : List DefinitionVal) (v₀ : DefinitionVal)
    (base : VEnv) (hbase : base ≤ c.venv)
    (hcparams : c.lparams = v₀.levelParams)
    (hcctx : c.vlctx = [])
    (H : List.Forall₂ (MutualHeaderRel c.safety origEnv base v₀) vs headers')
    (state : TypeChecker.VState := {}) :
    (checkMutualBodies c.env all vs).WF c state fun _ _ =>
      ∃ vs', List.Forall₂
          (MutualBodyRel c.safety origEnv base c.venv v₀) vs vs' ∧
        List.Forall₂ MutualHeaderSame headers' vs' := by
  induction H generalizing state with
  | nil => exact .pure ⟨[], .nil, .nil⟩
  | @cons v header vs headers hhead htail ih =>
    unfold checkMutualBodies checkMutualBody
    simpa only [bind_assoc] using
      ((TypeChecker.M.WF.liftExcept checkNoMVarNoFVar.WF).bind
        fun _ state' _ hclosed => by
          have htype : c.TrExprS v.type header.type := by
            have := hhead.2.2.2.2.2.2.1.mono hbase
            change TrExprS c.venv c.lparams c.vlctx v.type header.type
            rw [hcparams, hcctx]
            simpa [hhead.2.1] using this
          simpa only [pure_bind, bind_assoc] using
            ((checkBodyCore.WF' c (.mutualDefnDecl all) v.name
              v.type v.value header.type htype hclosed state').bind
                fun _ state'' _ hbody => by
                  obtain ⟨value', hvalue, hvalueWF⟩ := hbody
                  let v' : VDefVal := { header with value := value' }
                  have hvalue' : TrExprS c.venv v.levelParams [] v.value v'.value := by
                    change TrExprS c.venv c.lparams c.vlctx v.value v'.value at hvalue
                    rw [hcparams, hcctx] at hvalue
                    simpa [v', hhead.2.1] using hvalue
                  have hvWF : v'.WF c.venv := by
                    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' header.type at hvalueWF
                    rw [hcparams, hcctx] at hvalueWF
                    unfold VDefVal.WF
                    simpa [v', hhead.2.1, hhead.2.2.2.2.2.1] using hvalueWF
                  refine (ih (state := state'')).mono
                    (R := fun _ _ => ∃ finals,
                      List.Forall₂
                        (MutualBodyRel c.safety origEnv base c.venv v₀)
                          (v :: vs) finals ∧
                      List.Forall₂ MutualHeaderSame (header :: headers) finals) ?_
                  rintro _ _ _ ⟨vs', hvs', hsame⟩
                  refine ⟨v' :: vs', .cons ?_ hvs', .cons ⟨rfl, rfl⟩ hsame⟩
                  exact ⟨header, hhead, rfl, hvalue', hvWF⟩))

theorem List.Forall₂.mutualBody_toFinal
    (H : List.Forall₂
      (MutualBodyRel safety env base headers v₀) vs vs') :
    List.Forall₂ (fun v v' =>
      TrConstVal safety base (.defnInfo v) v'.toVConstVal) vs vs' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih =>
    obtain ⟨header, hheader, hsame, _, _⟩ := h
    exact .cons (hsame ▸ hheader.toFinal) ih

theorem List.Forall₂.mutualBody_bodies
    (H : List.Forall₂
      (MutualBodyRel safety env base headers v₀) vs vs') :
    List.Forall₂ (fun v v' =>
      TrExprS headers v.levelParams [] v.value v'.value) vs vs' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih =>
    obtain ⟨_, _, _, hbody, _⟩ := h
    exact .cons hbody ih

theorem List.Forall₂.mutualBody_wfs
    (H : List.Forall₂
      (MutualBodyRel safety env base headers v₀) vs vs') :
    ∀ v' ∈ vs', v'.WF headers := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    obtain ⟨_, _, _, _, hwf⟩ := h
    intro v' hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hwf
    · exact ih v' hv

theorem List.Forall₂.mutualBody_types
    (H : List.Forall₂
      (MutualBodyRel safety env base headers v₀) vs vs') :
    ∀ v' ∈ vs', v'.toVConstant.WF base := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    obtain ⟨header, hheader, hsame, _, _⟩ := h
    intro v' hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · rw [hsame]
      exact hheader.2.2.2.2.2.2.2
    · exact ih v' hv

theorem List.Forall₂.trConst_names_eq
    {info : DefinitionVal → ConstantInfo}
    {vs : List DefinitionVal} {vs' : List VDefVal}
    (H : List.Forall₂ (fun v v' =>
      TrConstVal safety env (info v) v'.toVConstVal) vs vs')
    (hname : ∀ v, (info v).name = v.name) :
    vs.map (fun v => v.name) = vs'.map (fun v => v.name) := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    simp only [List.map_cons]
    rw [← h.2, hname, ih]

theorem List.Forall₂.trConst_mono
    {info : DefinitionVal → ConstantInfo}
    {vs : List DefinitionVal} {vs' : List VDefVal}
    {base env : VEnv}
    (H : List.Forall₂ (fun v v' =>
      TrConstVal safety base (info v) v'.toVConstVal) vs vs')
    (hs : safety' ≤ safety) (hle : base ≤ env) :
    List.Forall₂ (fun v v' =>
      TrConstVal safety' env (info v) v'.toVConstVal) vs vs' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons ⟨h.1.sf_mono hs |>.mono hle, h.2⟩ ih

theorem List.Forall₂.trConst_target_fresh
    {info : DefinitionVal → ConstantInfo}
    {vs : List DefinitionVal} {vs' : List VDefVal}
    {base : VEnv} {env : Environment}
    (H : List.Forall₂ (fun v v' =>
      TrConstVal safety base (info v) v'.toVConstVal) vs vs')
    (hname : ∀ v, (info v).name = v.name)
    (htr : TrEnv safety env base)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none) :
    ∀ v' : VDefVal, v' ∈ vs' → base.constants v'.name = none := by
  intro w hw
  have hnames := Lean4Lean.List.Forall₂.trConst_names_eq H hname
  have hwname : w.name ∈ vs'.map (fun v => v.name) := List.mem_map.mpr ⟨w, hw, rfl⟩
  rw [← hnames] at hwname
  obtain ⟨v, hv, hn⟩ := List.mem_map.mp hwname
  cases hc : base.constants w.name with
  | none => rfl
  | some ci =>
    have hs := (htr.find?_iff (name := w.name)).2 ⟨ci, hc⟩
    obtain ⟨ci', hfind, _⟩ := hs
    rw [← hn, hfresh v hv] at hfind
    contradiction

theorem List.Forall₂.mutualBodies_mono
    {vs : List DefinitionVal} {vs' : List VDefVal} {env env' : VEnv}
    (H : List.Forall₂ (fun v v' =>
      TrExprS env v.levelParams [] v.value v'.value) vs vs')
    (hle : env ≤ env') :
    List.Forall₂ (fun v v' =>
      TrExprS env' v.levelParams [] v.value v'.value) vs vs' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.mono hle) ih

theorem checkBodyCore.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (name : Name) (levelParams : List Name)
    (type value : Expr) (type' : VExpr)
    (hdeclType : TrExprS (ves.venv safety) levelParams [] type type')
    (hclosed : value.hasMVar = false ∧ value.hasFVar = false)
    (state : TypeChecker.VState := {}) :
    ((do
      let valueType ← TypeChecker.checkType value
      if !(← TypeChecker.isDefEq valueType type) then
        throw <| Exception.declTypeMismatch env decl valueType) :
      TypeChecker.M Unit).WF
      (.mk' wf safety levelParams) state fun _ _ =>
        ∃ value', TrExprS (ves.venv safety) levelParams [] value value' ∧
          (ves.venv safety).HasType levelParams.length [] value' type' :=
  checkBodyCore.WF' (.mk' wf safety levelParams) decl name type value type'
    hdeclType hclosed state

theorem checkBody.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (name : Name) (levelParams : List Name)
    (type value : Expr) (type' : VExpr)
    (hdeclType : TrExprS (ves.venv safety) levelParams [] type type')
    (state : TypeChecker.VState := {}) :
    ((do
      Lean.Kernel.Environment.checkNoMVarNoFVar env name value
      let valueType ← TypeChecker.checkType value
      if !(← TypeChecker.isDefEq valueType type) then
        throw <| Exception.declTypeMismatch env decl valueType) :
      TypeChecker.M Unit).WF
      (.mk' wf safety levelParams) state fun _ _ =>
        ∃ value', TrExprS (ves.venv safety) levelParams [] value value' ∧
          (ves.venv safety).HasType levelParams.length [] value' type' := by
  refine (TypeChecker.M.WF.liftExcept checkNoMVarNoFVar.WF).bind
    fun _ state' _ hclosed => ?_
  exact checkBodyCore.WF wf decl name levelParams type value type'
    hdeclType hclosed state'

theorem checkDefinitionBody.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (state : TypeChecker.VState := {}) :
    (checkDefinitionBody env v).WF
      (.mk' wf .safe v.levelParams) state fun _ _ =>
        ∃ v' : VDefVal,
          v.levelParams.length = v'.uvars ∧
          TrExprS (ves.venv .safe) v.levelParams [] v.type v'.type ∧
          v.name = v'.name ∧
          TrExprS (ves.venv .safe) v.levelParams [] v.value v'.value ∧
          v'.WF (ves.venv .safe) := by
  unfold checkDefinitionBody
  refine checkConstantValBody.WF.bind fun _ state' _ hheader => ?_
  obtain ⟨type', htype, _⟩ := hheader
  exact (checkBody.WF wf (.defnDecl v) v.name v.levelParams
    v.type v.value type' htype state').mono fun _ _ _ hbody => by
      obtain ⟨value', hvalue, hvalueT⟩ := hbody
      exact ⟨{
        name := v.name, uvars := v.levelParams.length,
        type := type', value := value' },
        rfl, htype, rfl, hvalue, hvalueT⟩

theorem checkTheorem.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : TheoremVal) :
    ((do
      checkConstantVal env v.toConstantVal
      if !(← TypeChecker.isProp v.type) then
        throw <| Exception.thmTypeIsNotProp env v.name v.type
      Lean.Kernel.Environment.checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← TypeChecker.isDefEq valType v.type) then
        throw <| Exception.declTypeMismatch env (.thmDecl v) valType) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.thmInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          ¬Lean.Kernel.Environment.primitives.contains v.name := by
  refine (checkConstantVal.WF
    (c := .mk' wf .safe v.levelParams) (s := {})
    (env := env) (v := v.toConstantVal)
    (wf.tr (safety := .safe)).map_wf).bind fun _ state' _ hheader => ?_
  obtain ⟨hfresh, hreserved, type', htype, _⟩ := hheader
  have hn : ¬Lean.Kernel.Environment.primitives.contains v.name := by
    intro hp
    have := hreserved hp
    contradiction
  refine (TypeChecker.isProp.WF htype).bind fun prop state'' _ hprop => ?_
  split
  · exact .throw
  · refine (checkBody.WF wf (.thmDecl v) v.name v.levelParams
      v.type v.value type' htype state'').mono fun _ _ _ hbody => ?_
    obtain ⟨value', hvalue, hvalueWF⟩ := hbody
    let v' : VDefVal := {
      name := v.name
      uvars := v.levelParams.length
      type := type'
      value := value' }
    refine ⟨v', ?_, by simpa [v'] using hvalueWF, hfresh, hn⟩
    exact ⟨⟨⟨by
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial], rfl, htype⟩, rfl⟩,
      by simpa [v'] using hvalue⟩

theorem checkOpaque.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : OpaqueVal) (safety : DefinitionSafety)
    (hsafety : safety = if v.isUnsafe then .unsafe else .safe) :
    ((do
      checkConstantVal env v.toConstantVal
      Lean.Kernel.Environment.checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← TypeChecker.isDefEq valType v.type) then
        throw <| Exception.declTypeMismatch env (.opaqueDecl v) valType) :
      TypeChecker.M Unit).WF (.mk' wf safety v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrOpaqueVal safety (ves.venv safety) v v' ∧
          v'.WF (ves.venv safety) ∧ env.find? v.name = none ∧
          ¬Lean.Kernel.Environment.primitives.contains v.name := by
  refine (checkConstantVal.WF
    (c := .mk' wf safety v.levelParams) (s := {})
    (env := env) (v := v.toConstantVal)
    (wf.tr (safety := safety)).map_wf).bind fun _ state' _ hheader => ?_
  obtain ⟨hfresh, hreserved, type', htype, _⟩ := hheader
  have hn : ¬Lean.Kernel.Environment.primitives.contains v.name := by
    intro hp
    have := hreserved hp
    contradiction
  refine (checkBody.WF (safety := safety) wf (.opaqueDecl v) v.name v.levelParams
    v.type v.value type' htype state').mono fun _ _ _ hbody => ?_
  obtain ⟨value', hvalue, hvalueWF⟩ := hbody
  let v' : VDefVal := {
    name := v.name
    uvars := v.levelParams.length
    type := type'
    value := value' }
  refine ⟨v', ?_, by simpa [v'] using hvalueWF, hfresh, hn⟩
  exact ⟨⟨⟨by
    rw [hsafety]
    simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial], rfl, htype⟩, rfl⟩,
    by simpa [v'] using hvalue⟩

theorem checkSafeNatAddDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app .natSucc (.app (.app v'.value (.bvar 1)) (.bvar 0))) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natAdd.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatModDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mod)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatModPrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natMod.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl rfl htype hvalue).bind fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := by
    rcases hevidence with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlevels, _⟩
    exact hlevels
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatDivDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.div)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatDivPrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natDiv.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl rfl htype hvalue).bind fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := by
    rcases hevidence with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlevels, _⟩
    exact hlevels
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatGcdDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.gcd)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatGcdPrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natGcd.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind
      fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := hevidence.choose_spec.1
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatBitwiseDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.bitwise)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatBitwisePrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natBitwise.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) hname rfl rfl htype).bind
      fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := by
    rcases hevidence with ⟨_, _, _, hlevels, _⟩
    exact hlevels
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatPredDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pred)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app v'.value .natZero) .natZero ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app v'.value (.app .natSucc (.bvar 0)))
            (.lam .nat <| .bvar 0) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natPred.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatSubDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.sub)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.pred ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.const ``Nat.pred [])
                (.app (.app v'.value (.bvar 1)) (.bvar 0))) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natSub.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hpred, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hpred, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatMulDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mul)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.add ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat .natZero) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app (.const ``Nat.add [])
                (.app (.app v'.value (.bvar 1)) (.bvar 0))) (.bvar 1)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natMul.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, haddC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, haddC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatPowDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pow)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.mul ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .app .natSucc .natZero) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app (.const ``Nat.mul [])
                (.app (.app v'.value (.bvar 1)) (.bvar 0))) (.bvar 1)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natPow.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hmulC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hmulC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩


theorem checkSafeNatShiftLeftDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftLeft)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.mul ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 0)) (.app .natSucc (.bvar 1)))
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value
                (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
                (.bvar 1)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natShiftLeft.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hmulC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hmulC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩


theorem checkSafeNatShiftRightDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftRight)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.div ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 0)) (.app .natSucc (.bvar 1)))
            (.lam .nat <| .lam .nat <|
              .app (.app (.const ``Nat.div [])
                (.app (.app v'.value (.bvar 0)) (.bvar 1))) (.natLit 2)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natShiftRight.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hdivC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hdivC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatBEqDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.beq)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app v'.value .natZero) .natZero) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value .natZero)
              (.app .natSucc (.bvar 0))) (.lam .nat .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.app .natSucc (.bvar 0)))
              .natZero) (.lam .nat .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.app .natSucc (.bvar 1)))
                (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.bvar 0)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natBEq.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩



theorem checkSafeNatBLEDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.ble)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app v'.value .natZero) .natZero) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value .natZero)
              (.app .natSucc (.bvar 0))) (.lam .nat .boolTrue) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.app .natSucc (.bvar 0)))
              .natZero) (.lam .nat .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.app .natSucc (.bvar 1)))
                (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.bvar 0)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natBLE.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatXorDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.xor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal, ∃ op' : VExpr,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Nat.bitwise ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          v'.value = .app (.const ``Nat.bitwise []) op' ∧
          (ves.venv .safe).HasType v.levelParams.length [] op'
            (.forallE .bool <| .forallE .bool .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolFalse) .boolFalse) .boolFalse ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolTrue) .boolFalse) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolFalse) .boolTrue) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolTrue) .boolTrue) .boolFalse := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natXor.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname hshape htype hvalue).bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, _, hbitwise, hty, op', hvalueShape,
    hopTy, hff, htf, hft, htt⟩ := hcheck hallow
  refine ⟨v', op', ?_, hvalueT, hcheckedName.1, hlevels,
    hnat, hbitwise, hty, hvalueShape, hopTy, hff, htf, hft, htt⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatLandDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.land)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal, ∃ op' : VExpr,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).contains ``Nat.bitwise ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          v'.value = .app (.const ``Nat.bitwise []) op' ∧
          (ves.venv .safe).HasType v.levelParams.length [] op'
            (.forallE .bool <| .forallE .bool .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0))
            (.lam .bool .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0))
            (.lam .bool <| .bvar 0) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natLand.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname hshape rfl htype hvalue).bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hbitwise, hty, op', hvalueShape,
    hopTy, hf, ht⟩ := hcheck hallow
  refine ⟨v', op', ?_, hvalueT, hcheckedName.1, hlevels,
    hnat, hbool, hbitwise, hty, hvalueShape, hopTy, hf, ht⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩


theorem checkSafeNatLorDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.lor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal, ∃ op' : VExpr,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).contains ``Nat.bitwise ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          v'.value = .app (.const ``Nat.bitwise []) op' ∧
          (ves.venv .safe).HasType v.levelParams.length [] op'
            (.forallE .bool <| .forallE .bool .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0))
            (.lam .bool <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0))
            (.lam .bool .boolTrue) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natLor.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname hshape rfl htype hvalue).bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hbitwise, hty, op', hvalueShape,
    hopTy, hf, ht⟩ := hcheck hallow
  refine ⟨v', op', ?_, hvalueT, hcheckedName.1, hlevels,
    hnat, hbool, hbitwise, hty, hvalueShape, hopTy, hf, ht⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeCharOfNatDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Char.ofNat)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat .char) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.charOfNat.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) hname hsafety rfl htype).bind
      fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hty⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hnat, hty⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeStringOfListDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``String.ofList)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .listChar .string) ∧
          (ves.venv .safe).HasType v.levelParams.length []
            .listCharNil .listChar ∧
          (ves.venv .safe).HasType v.levelParams.length []
            .listCharCons
              (.forallE .char <| .forallE .listChar .listChar) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.stringOfList.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) hname hsafety rfl htype).bind
      fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hty, hnil, hcons⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels,
    hty, hnil, hcons⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩



theorem checkSafeNonprimitiveDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.WF_of_not_primitive (v := v) hn).bind
    fun allow state'' _ hallow => ?_
  subst allow
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hname => ?_
  refine ⟨v', ?_, ?_, hname.1⟩
  · exact ⟨⟨⟨by
      rw [ConstantInfo.defnInfo_safety, hsafety]
      exact DefinitionSafety.le_rfl,
      huvars, htype⟩, hvname⟩, hvalue⟩
  · exact hvalueT

theorem TrEnv.addConst_of_find?_eq_none
    {env : Environment} {venv : VEnv} {n : Name} {ci : VConstant}
    (htr : TrEnv safety env venv) (hfresh : env.find? n = none) :
    ∃ venv', venv.addConst n ci = some venv' := by
  have hnone : venv.constants n = none := by
    cases h : venv.constants n with
    | none => rfl
    | some ci' =>
      have hs := (htr.find?_iff (name := n)).2 ⟨ci', h⟩
      rcases hs with ⟨ci₀, hci₀, _⟩
      rw [hfresh] at hci₀
      contradiction
  unfold VEnv.addConst
  rw [hnone]
  exact ⟨_, rfl⟩

theorem VEnv.addConst_mono {env₁ env₂ env₁' env₂' : VEnv}
    (hle : env₁ ≤ env₂)
    (hadd₁ : env₁.addConst n ci = some env₁')
    (hadd₂ : env₂.addConst n ci = some env₂') : env₁' ≤ env₂' := by
  constructor
  · intro m a hm
    by_cases hnm : n = m
    · subst m
      rw [VEnv.addConst_self hadd₁] at hm
      cases hm
      exact VEnv.addConst_self hadd₂
    · rw [VEnv.addConst_constants_of_ne hadd₁ hnm] at hm
      rw [VEnv.addConst_constants_of_ne hadd₂ hnm]
      exact hle.constants hm
  · intro df hdf
    have hdef₁ : env₁'.defeqs = env₁.defeqs := by
      unfold VEnv.addConst at hadd₁
      split at hadd₁ <;> cases hadd₁
      rfl
    have hdef₂ : env₂'.defeqs = env₂.defeqs := by
      unfold VEnv.addConst at hadd₂
      split at hadd₂ <;> cases hadd₂
      rfl
    rw [hdef₁] at hdf
    rw [hdef₂]
    exact hle.defeqs hdf

theorem VEnv.addMutualHeaders_spec
    {env : VEnv} {vs : List VDefVal}
    (hfresh : ∀ v ∈ vs, env.constants v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup) :
    ∃ headers,
      env.addMutualHeaders vs = some headers ∧
      env ≤ headers ∧
      ∀ v ∈ vs, headers.constants v.name = some v.toVConstant := by
  induction vs generalizing env with
  | nil =>
    exact ⟨env, rfl, VEnv.LE.rfl, by simp⟩
  | cons v vs ih =>
    have hnone := hfresh v (by simp)
    obtain ⟨next, hhead⟩ : ∃ next, env.addConst v.name v.toVConstant = some next := by
      unfold VEnv.addConst
      rw [hnone]
      exact ⟨_, rfl⟩
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    have hfresh' : ∀ w ∈ vs, next.constants w.name = none := by
      intro w hw
      rw [VEnv.addConst_constants_of_ne hhead]
      · exact hfresh w (by simp [hw])
      · intro heq
        exact hnodupPair.1 (heq ▸ List.mem_map.mpr ⟨w, hw, rfl⟩)
    obtain ⟨headers, htail, hle, hcontains⟩ := ih hfresh' hnodupPair.2
    refine ⟨headers, ?_, (VEnv.addConst_le hhead).trans hle, ?_⟩
    · simp [VEnv.addMutualHeaders, hhead, htail]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hle.constants (VEnv.addConst_self hhead)
      · exact hcontains w hw

theorem VEnv.addMutualHeaders_congr
    {env : VEnv} {vs₁ vs₂ : List VDefVal}
    (H : List.Forall₂ MutualHeaderSame vs₁ vs₂) :
    env.addMutualHeaders vs₁ = env.addMutualHeaders vs₂ := by
  induction H generalizing env with
  | nil => rfl
  | cons h _ ih =>
    simp only [VEnv.addMutualHeaders]
    rw [h.1, h.2]
    cases hhead : env.addConst _ _ <;> simp [hhead, ih]

theorem VEnv.HasPrimitives.addMutualHeaders
    {env headers : VEnv} {vs : List VDefVal}
    (H : env.HasPrimitives)
    (hn : ∀ v ∈ vs, ¬Lean.Kernel.Environment.primitives.contains v.name)
    (hadd : env.addMutualHeaders vs = some headers) :
    headers.HasPrimitives := by
  induction vs generalizing env headers with
  | nil =>
    simp [VEnv.addMutualHeaders] at hadd
    subst headers
    exact H
  | cons v vs ih =>
    cases hhead : env.addConst v.name v.toVConstant with
    | none => simp [VEnv.addMutualHeaders, hhead] at hadd
    | some next =>
      simp [VEnv.addMutualHeaders, hhead] at hadd
      exact ih (H.addConst_of_not_primitive hhead (hn v (by simp)))
        (fun w hw => hn w (by simp [hw])) hadd

theorem VEnv.addMutualHeaders_mono
    {env₁ env₂ headers₁ headers₂ : VEnv} {vs : List VDefVal}
    (hle : env₁ ≤ env₂)
    (hadd₁ : env₁.addMutualHeaders vs = some headers₁)
    (hadd₂ : env₂.addMutualHeaders vs = some headers₂) :
    headers₁ ≤ headers₂ := by
  induction vs generalizing env₁ env₂ headers₁ headers₂ with
  | nil =>
    simp [VEnv.addMutualHeaders] at hadd₁ hadd₂
    subst headers₁
    subst headers₂
    exact hle
  | cons v vs ih =>
    cases hhead₁ : env₁.addConst v.name v.toVConstant with
    | none => simp [VEnv.addMutualHeaders, hhead₁] at hadd₁
    | some next₁ =>
      cases hhead₂ : env₂.addConst v.name v.toVConstant with
      | none => simp [VEnv.addMutualHeaders, hhead₂] at hadd₂
      | some next₂ =>
        simp [VEnv.addMutualHeaders, hhead₁] at hadd₁
        simp [VEnv.addMutualHeaders, hhead₂] at hadd₂
        exact ih (VEnv.addConst_mono hle hhead₁ hhead₂) hadd₁ hadd₂

theorem VEnv.addDefEq_mono {env₁ env₂ : VEnv} (hle : env₁ ≤ env₂) :
    env₁.addDefEq df ≤ env₂.addDefEq df := by
  constructor
  · exact hle.constants
  · intro df' hdf'
    change df' = df ∨ env₁.defeqs df' at hdf'
    change df' = df ∨ env₂.defeqs df'
    exact hdf'.imp id hle.defeqs

theorem VEnv.addMutualDefEqs_mono {env₁ env₂ : VEnv} {vs : List VDefVal}
    (hle : env₁ ≤ env₂) :
    env₁.addMutualDefEqs vs ≤ env₂.addMutualDefEqs vs := by
  induction vs generalizing env₁ env₂ with
  | nil => exact hle
  | cons v vs ih => exact ih (VEnv.addDefEq_mono hle)

theorem VEnv.addMutualDefEqs_le {env : VEnv} {vs : List VDefVal} :
    env ≤ env.addMutualDefEqs vs := by
  induction vs generalizing env with
  | nil => exact VEnv.LE.rfl
  | cons v vs ih => exact VEnv.addDefEq_le.trans ih

theorem VEnv.HasPrimitives.addMutualDefEqs
    {env : VEnv} {vs : List VDefVal} (H : env.HasPrimitives) :
    (env.addMutualDefEqs vs).HasPrimitives := by
  induction vs generalizing env with
  | nil => exact H
  | cons v vs ih => exact ih H.addDefEq

theorem TrEnv.block
    (htr : TrEnv safety env venv)
    (hfresh : env.find? ci.name = none)
    (hsafety : ¬safety ≤ ci.safety) :
    TrEnv safety (env.add ci) venv := by
  change TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv
  exact .block (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hsafety htr

theorem TrEnv.blockMutualFinal
    (htr : TrEnv safety env venv)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup)
    (hsafety : ∀ v ∈ vs, ¬safety ≤ v.safety) :
    TrEnv safety (addMutualFinalEnv env vs) venv := by
  induction vs generalizing env with
  | nil => simpa [addMutualFinalEnv] using htr
  | cons v vs ih =>
    have hheadFresh := hfresh v (by simp)
    have hheadNone : env.constants.find? v.name = none := by
      rw [← htr.map_wf.find?'_eq_find?]
      exact hheadFresh
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    have hmap' := htr.map_wf.insert v.name (.defnInfo v) hheadNone
    have hfresh' : ∀ w ∈ vs,
        (env.add (.defnInfo v)).find? w.name = none := by
      intro w hw
      change (env.constants.insert v.name (.defnInfo v)).find?' w.name = none
      rw [hmap'.find?'_eq_find?, htr.map_wf.find?_insert]
      split
      · rename_i heq
        have hmem : w.name ∈ vs.map (fun x => x.name) :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ hmem)).elim
      · rw [← htr.map_wf.find?'_eq_find?]
        exact hfresh w (by simp [hw])
    have hnext := TrEnv.block (ci := .defnInfo v) htr hheadFresh
      (by rw [ConstantInfo.defnInfo_safety]; exact hsafety v (by simp))
    simpa [addMutualFinalEnv] using
      ih hnext hfresh' hnodupPair.2
        (fun w hw => hsafety w (by simp [hw]))

theorem TrEnv.addAxiom
    (htr : TrEnv safety env venv)
    (hci : TrConstant safety venv (.axiomInfo ci) ci')
    (hfresh : env.find? ci.name = none)
    (hciWF : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv') :
    TrEnv safety (env.add (.axiomInfo ci)) venv' := by
  change TrEnv' safety
    (env.constants.insert ci.name (.axiomInfo ci)) env.quotInit venv'
  exact .axiom hci (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hciWF hadd htr

theorem TrEnv.addDefinition
    (htr : TrEnv safety env venv)
    (hci : TrDefVal safety venv (.defnInfo ci) ci')
    (hfresh : env.find? ci.name = none)
    (hciWF : ci'.WF venv)
    (hadd : venv.addConst ci.name ci'.toVConstant = some venv') :
    TrEnv safety (env.add (.defnInfo ci))
      (venv'.addDefEq ci'.toDefEq) := by
  change TrEnv' safety
    (env.constants.insert ci.name (.defnInfo ci)) env.quotInit
    (venv'.addDefEq ci'.toDefEq)
  exact .defn hci (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hciWF hadd htr

theorem TrEnv.addTheorem
    (htr : TrEnv safety env venv)
    (hci : TrDefVal safety venv (.thmInfo ci) ci')
    (hfresh : env.find? ci.name = none)
    (hciWF : ci'.WF venv)
    (hadd : venv.addConst ci.name ci'.toVConstant = some venv') :
    TrEnv safety (env.add (.thmInfo ci))
      (venv'.addDefEq ci'.toDefEq) := by
  change TrEnv' safety
    (env.constants.insert ci.name (.thmInfo ci)) env.quotInit
    (venv'.addDefEq ci'.toDefEq)
  exact .theorem hci (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hciWF hadd htr

theorem TrEnv.addUnsafeDefinition
    {ci : DefinitionVal} {ci' : VDefVal}
    (htr : TrEnv .unsafe env venv)
    (hheader : TrConstVal .unsafe venv (.defnInfo ci) ci'.toVConstVal)
    (hfresh : env.find? ci.name = none)
    (hheaderWF : ci'.toVConstant.WF venv)
    (hadd : venv.addConst ci.name ci'.toVConstant = some venv')
    (hvalue : TrExprS venv' ci.levelParams [] ci.value ci'.value)
    (hvalueWF : ci'.WF venv') :
    TrEnv .unsafe (env.add (.defnInfo ci))
      (venv'.addDefEq ci'.toDefEq) := by
  change TrEnv' .unsafe
    (env.constants.insert ci.name (.defnInfo ci)) env.quotInit
    (venv'.addDefEq ci'.toDefEq)
  exact .unsafeDefn hheader (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hheaderWF hadd hvalue hvalueWF htr

theorem TrEnv.addOpaque
    (htr : TrEnv safety env venv)
    (hci : TrOpaqueVal safety venv ci ci')
    (hfresh : env.find? ci.name = none)
    (hciWF : ci'.WF venv)
    (hadd : venv.addConst ci.name ci'.toVConstant = some venv') :
    TrEnv safety (env.add (.opaqueInfo ci)) venv' := by
  change TrEnv' safety
    (env.constants.insert ci.name (.opaqueInfo ci)) env.quotInit venv'
  exact .opaque hci (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hciWF hadd htr

@[simp] theorem addMutualCheckEnv_constants :
    (addMutualCheckEnv env vs).constants =
      ConstMap.addMutualOpaqueHeaders env.constants vs := by
  induction vs generalizing env with
  | nil => rfl
  | cons v vs ih =>
    simp only [addMutualCheckEnv, ConstMap.addMutualOpaqueHeaders, List.foldl_cons]
    exact ih

@[simp] theorem addMutualCheckEnv_quotInit :
    (addMutualCheckEnv env vs).quotInit = env.quotInit := by
  induction vs generalizing env with
  | nil => rfl
  | cons v vs ih =>
    simp only [addMutualCheckEnv, List.foldl_cons]
    exact ih.trans rfl

@[simp] theorem addMutualFinalEnv_constants :
    (addMutualFinalEnv env vs).constants =
      ConstMap.addMutualDefinitions env.constants vs := by
  induction vs generalizing env with
  | nil => rfl
  | cons v vs ih =>
    simp only [addMutualFinalEnv, ConstMap.addMutualDefinitions, List.foldl_cons]
    exact ih

@[simp] theorem addMutualFinalEnv_quotInit :
    (addMutualFinalEnv env vs).quotInit = env.quotInit := by
  induction vs generalizing env with
  | nil => rfl
  | cons v vs ih =>
    simp only [addMutualFinalEnv, List.foldl_cons]
    exact ih.trans rfl

theorem ConstMap.foldInsert_no_inductInfo
    {C : ConstMap} {vs : List DefinitionVal}
    {info : DefinitionVal → ConstantInfo}
    (hmap : C.WF)
    (hfresh : ∀ v ∈ vs, C.find? v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup)
    (hkind : ∀ v i, info v ≠ .inductInfo i)
    (hold : C.find? n ≠ some (.inductInfo i)) :
    (vs.foldl (fun C v => C.insert v.name (info v)) C).find? n ≠
      some (.inductInfo i) := by
  induction vs generalizing C with
  | nil => exact hold
  | cons v vs ih =>
    have hheadNone := hfresh v (by simp)
    have hmap' := hmap.insert v.name (info v) hheadNone
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    have hfresh' : ∀ w ∈ vs,
        (C.insert v.name (info v)).find? w.name = none := by
      intro w hw
      rw [hmap.find?_insert]
      split
      · rename_i heq
        have hmem : w.name ∈ vs.map (fun x => x.name) :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ hmem)).elim
      · exact hfresh w (by simp [hw])
    apply ih hmap' hfresh' hnodupPair.2
    intro hfind
    rw [hmap.find?_insert] at hfind
    split at hfind
    · exact hkind v i (Option.some.inj hfind)
    · exact hold hfind

theorem TrEnv'.no_inductInfo (H : TrEnv' .unsafe C Q venv) :
    C.find? name ≠ some (.inductInfo info) := by
  induction H with
  | empty => simp [SMap.find?]
  | block _ hhidden _ _ =>
    exact False.elim <| hhidden DefinitionSafety.unsafe_le
  | «axiom» _ _ _ _ H ih
  | defn _ _ _ _ H ih
  | «theorem» _ _ _ _ H ih
  | unsafeDefn _ _ _ _ _ _ H ih
  | «opaque» _ _ _ _ H ih =>
    rw [H.map_wf.find?_insert]
    split
    · simp
    · exact ih
  | «mutual» _ hfresh _ _ _ _ _ H ih =>
    exact ConstMap.foldInsert_no_inductInfo H.map_wf hfresh.1 hfresh.2
      (fun _ _ h => by cases h) ih
  | mutualCheck _ hfresh _ _ H ih =>
    exact ConstMap.foldInsert_no_inductInfo H.map_wf hfresh.1 hfresh.2
      (fun _ _ h => by cases h) ih
  | quot _ hadd H ih =>
    dsimp [AddQuot, AddQuot1] at hadd
    obtain ⟨lp₁, ty₁, env₁, _, hn₁, _,
      lp₂, ty₂, env₂, _, hn₂, _,
      lp₃, ty₃, env₃, _, hn₃, _,
      lp₄, ty₄, env₄, _, hn₄, _, rfl, _⟩ := hadd
    have wf₀ := H.map_wf
    have wf₁ := wf₀.insert ``Quot
      (.quotInfo (.mk (.mk ``Quot lp₁ ty₁) .type)) hn₁
    have wf₂ := wf₁.insert ``Quot.mk
      (.quotInfo (.mk (.mk ``Quot.mk lp₂ ty₂) .ctor)) hn₂
    have wf₃ := wf₂.insert ``Quot.lift
      (.quotInfo (.mk (.mk ``Quot.lift lp₃ ty₃) .lift)) hn₃
    rw [wf₃.find?_insert]
    split
    · simp
    rw [wf₂.find?_insert]
    split
    · simp
    rw [wf₁.find?_insert]
    split
    · simp
    rw [wf₀.find?_insert]
    split
    · simp
    exact ih
  | induct _ hadd _ _ => exact nomatch hadd

theorem TrEnv.addMutualCheckHeaders
    (htr : TrEnv safety env venv)
    (hrel : List.Forall₂ (fun v v' =>
      TrConstVal safety venv (.opaqueInfo (mutualOpaqueHeader v)) v'.toVConstVal) vs vs')
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup)
    (htypes : ∀ v' ∈ vs', v'.toVConstant.WF venv)
    (hadd : venv.addMutualHeaders vs' = some headers) :
    TrEnv safety (addMutualCheckEnv env vs) headers := by
  rw [TrEnv, addMutualCheckEnv_constants, addMutualCheckEnv_quotInit]
  refine .mutualCheck hrel ⟨?_, hnodup⟩ htypes hadd htr
  intro v hv
  rw [← htr.map_wf.find?'_eq_find?]
  exact hfresh v hv

theorem TrEnv.addMutual
    (htr : TrEnv safety env venv)
    (hrel : List.Forall₂ (fun v v' =>
      TrConstVal safety venv (.defnInfo v) v'.toVConstVal) vs vs')
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup)
    (htypes : ∀ v' ∈ vs', v'.toVConstant.WF venv)
    (hadd : venv.addMutualHeaders vs' = some headers)
    (hcontains : ∀ v' ∈ vs', headers.constants v'.name = some v'.toVConstant)
    (hbodies : List.Forall₂ (fun v v' =>
      TrExprS headers v.levelParams [] v.value v'.value) vs vs')
    (hwfs : ∀ v' ∈ vs', v'.WF headers) :
    TrEnv safety (addMutualFinalEnv env vs) (headers.addMutualDefEqs vs') := by
  rw [TrEnv, addMutualFinalEnv_constants, addMutualFinalEnv_quotInit]
  refine .mutual hrel ⟨?_, hnodup⟩ htypes hadd hcontains hbodies hwfs htr
  intro v hv
  rw [← htr.map_wf.find?'_eq_find?]
  exact hfresh v hv

theorem Environment.safePrimitives_add_of_not_primitive
    {env : Environment} {ci ci' : ConstantInfo} {n : Name}
    (hmap : env.constants.WF)
    (hfresh : env.find? ci.name = none)
    (hold : env.find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [])
    (hn : ¬Lean.Kernel.Environment.primitives.contains ci.name) :
    (env.add ci).find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [] := by
  intro hfind hprim
  have hfresh' : SMap.find? env.constants ci.name = none := by
    rw [← hmap.find?'_eq_find?]
    exact hfresh
  have hmap' := hmap.insert ci.name ci hfresh'
  change (env.constants.insert ci.name ci).find?' n = some ci' at hfind
  rw [hmap'.find?'_eq_find?, hmap.find?_insert] at hfind
  split at hfind
  · rename_i hname
    have hname' : ci.name = n := LawfulBEq.eq_of_beq hname
    subst n
    exact (hn hprim).elim
  · apply hold ?_ hprim
    change env.constants.find?' n = some ci'
    rw [hmap.find?'_eq_find?]
    exact hfind

theorem Environment.safePrimitives_addMutualCheckEnv
    (hmap : env.constants.WF)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup)
    (hn : ∀ v ∈ vs, ¬Lean.Kernel.Environment.primitives.contains v.name)
    (hold : env.find? n = some ci →
      Lean.Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []) :
    (addMutualCheckEnv env vs).find? n = some ci →
      Lean.Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  induction vs generalizing env with
  | nil => simpa [addMutualCheckEnv] using hold
  | cons v vs ih =>
    have hheadFresh := hfresh v (by simp)
    have hheadNone : env.constants.find? v.name = none := by
      rw [← hmap.find?'_eq_find?]
      exact hheadFresh
    let header : ConstantInfo := .opaqueInfo (mutualHeader v)
    have hmap' : (env.add header).constants.WF := by
      change (env.constants.insert v.name header).WF
      exact hmap.insert v.name header hheadNone
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    have hfresh' : ∀ w ∈ vs, (env.add header).find? w.name = none := by
      intro w hw
      change (env.constants.insert v.name header).find?' w.name = none
      rw [(hmap.insert v.name header hheadNone).find?'_eq_find?, hmap.find?_insert]
      split
      · rename_i heq
        have hmem : w.name ∈ vs.map (fun x => x.name) :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ hmem)).elim
      · rw [← hmap.find?'_eq_find?]
        exact hfresh w (by simp [hw])
    have hold' := Environment.safePrimitives_add_of_not_primitive
      (env := env) (ci := header) hmap hheadFresh hold
      (hn v (by simp))
    simpa [addMutualCheckEnv, header] using
      ih hmap' hfresh' hnodupPair.2
        (fun w hw => hn w (by simp [hw])) hold'

theorem Environment.safePrimitives_addMutualFinalEnv
    (hmap : env.constants.WF)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup)
    (hn : ∀ v ∈ vs, ¬Lean.Kernel.Environment.primitives.contains v.name)
    (hold : env.find? n = some ci →
      Lean.Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []) :
    (addMutualFinalEnv env vs).find? n = some ci →
      Lean.Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  induction vs generalizing env with
  | nil => simpa [addMutualFinalEnv] using hold
  | cons v vs ih =>
    have hheadFresh := hfresh v (by simp)
    have hheadNone : env.constants.find? v.name = none := by
      rw [← hmap.find?'_eq_find?]
      exact hheadFresh
    let header : ConstantInfo := .defnInfo v
    have hmap' : (env.add header).constants.WF := by
      change (env.constants.insert v.name header).WF
      exact hmap.insert v.name header hheadNone
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    have hfresh' : ∀ w ∈ vs, (env.add header).find? w.name = none := by
      intro w hw
      change (env.constants.insert v.name header).find?' w.name = none
      rw [(hmap.insert v.name header hheadNone).find?'_eq_find?, hmap.find?_insert]
      split
      · rename_i heq
        have hmem : w.name ∈ vs.map (fun x => x.name) :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ hmem)).elim
      · rw [← hmap.find?'_eq_find?]
        exact hfresh w (by simp [hw])
    have hold' := Environment.safePrimitives_add_of_not_primitive
      (env := env) (ci := header) hmap hheadFresh hold
      (hn v (by simp))
    simpa [addMutualFinalEnv, header] using
      ih hmap' hfresh' hnodupPair.2
        (fun w hw => hn w (by simp [hw])) hold'

theorem Environment.safePrimitives_add_of_safe_primitive
    {env : Environment} {ci ci' : ConstantInfo} {n : Name}
    (hmap : env.constants.WF)
    (hfresh : env.find? ci.name = none)
    (hold : env.find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [])
    (hnewSafety : ci.safety = .safe) (hnewLevels : ci.levelParams = []) :
    (env.add ci).find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [] := by
  intro hfind hprim
  have hfresh' : SMap.find? env.constants ci.name = none := by
    rw [← hmap.find?'_eq_find?]
    exact hfresh
  have hmap' := hmap.insert ci.name ci hfresh'
  change (env.constants.insert ci.name ci).find?' n = some ci' at hfind
  rw [hmap'.find?'_eq_find?, hmap.find?_insert] at hfind
  split at hfind
  · cases hfind
    exact ⟨hnewSafety, hnewLevels⟩
  · apply hold ?_ hprim
    change env.constants.find?' n = some ci'
    rw [hmap.find?'_eq_find?]
    exact hfind

theorem VEnvs.WF.addMutual
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {blockSafety : DefinitionSafety} {vs : List DefinitionVal}
    {vs' : List VDefVal} {headers₀ : VEnv}
    (hsameSafety : ∀ v ∈ vs, v.safety = blockSafety)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnodup : (vs.map (fun v => v.name)).Nodup)
    (hn : ∀ v ∈ vs, ¬Lean.Kernel.Environment.primitives.contains v.name)
    (hn' : ∀ v' ∈ vs', ¬Lean.Kernel.Environment.primitives.contains v'.name)
    (hrel : List.Forall₂ (fun v v' =>
      TrConstVal blockSafety (ves.venv blockSafety)
        (.defnInfo v) v'.toVConstVal) vs vs')
    (htypes : ∀ v' ∈ vs',
      v'.toVConstant.WF (ves.venv blockSafety))
    (hadd₀ : (ves.venv blockSafety).addMutualHeaders vs' = some headers₀)
    (hcontains₀ : ∀ v' ∈ vs',
      headers₀.constants v'.name = some v'.toVConstant)
    (hbodies : List.Forall₂ (fun v v' =>
      TrExprS headers₀ v.levelParams [] v.value v'.value) vs vs')
    (hwfs : ∀ v' ∈ vs', v'.WF headers₀) :
    ∃ ves' : VEnvs, ves'.WF (addMutualFinalEnv env vs) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have hnames : vs.map (fun v => v.name) = vs'.map (fun v => v.name) :=
    Lean4Lean.List.Forall₂.trConst_names_eq hrel (fun _ => rfl)
  have hnodup' : (vs'.map (fun v => v.name)).Nodup := by
    rw [← hnames]
    exact hnodup
  have htargetFresh (safety : DefinitionSafety) :
      ∀ v' ∈ vs', (ves.venv safety).constants v'.name = none := by
    intro w hw
    have hwname : w.name ∈ vs'.map (fun v => v.name) :=
      List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [← hnames] at hwname
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hwname
    cases hc : (ves.venv safety).constants w.name with
    | none => rfl
    | some ci =>
      have hs := ((wf.tr (safety := safety)).find?_iff (name := w.name)).2
        ⟨ci, hc⟩
      obtain ⟨ci', hfind, _⟩ := hs
      rw [← hvw, hfresh v hv] at hfind
      contradiction
  have haddExists (safety : DefinitionSafety) :
      ∃ headers,
        (ves.venv safety).addMutualHeaders vs' = some headers ∧
        ves.venv safety ≤ headers ∧
        ∀ v' ∈ vs', headers.constants v'.name = some v'.toVConstant :=
    VEnv.addMutualHeaders_spec (htargetFresh safety) hnodup'
  let added (safety : DefinitionSafety) : VEnv :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addMutualHeaders vs' = some (added safety) :=
    (Classical.choose_spec (haddExists safety)).1
  have haddedLe (safety : DefinitionSafety) :
      ves.venv safety ≤ added safety :=
    (Classical.choose_spec (haddExists safety)).2.1
  have hcontains (safety : DefinitionSafety) :
      ∀ v' ∈ vs', (added safety).constants v'.name = some v'.toVConstant :=
    (Classical.choose_spec (haddExists safety)).2.2
  let ves' : VEnvs := ⟨fun safety =>
    if safety ≤ blockSafety then
      (added safety).addMutualDefEqs vs'
    else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ blockSafety
      · have hbase : ves.venv blockSafety ≤ ves.venv safety := wf.mono hs
        have hheaders : headers₀ ≤ added safety :=
          VEnv.addMutualHeaders_mono hbase hadd₀ (hadd safety)
        have hrel' := Lean4Lean.List.Forall₂.trConst_mono hrel hs hbase
        have hbodies' := Lean4Lean.List.Forall₂.mutualBodies_mono
          hbodies hheaders
        simpa [ves', hs] using TrEnv.addMutual
          (wf.tr (safety := safety)) hrel' hfresh hnodup
          (fun v' hv => (htypes v' hv).mono hbase) (hadd safety)
          (hcontains safety)
          hbodies'
          (fun v' hv => (hwfs v' hv).mono hheaders)
      · simpa [ves', hs] using TrEnv.blockMutualFinal
          (wf.tr (safety := safety)) hfresh hnodup
          (fun v hv hle => by
            rw [hsameSafety v hv] at hle
            exact hs hle)
    · intro safety
      by_cases hs : safety ≤ blockSafety
      · simp only [ves', hs, ↓reduceIte]
        exact ((wf.hasPrimitives (safety := safety)).addMutualHeaders
          hn' (hadd safety)).addMutualDefEqs
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_addMutualFinalEnv
        (wf.tr (safety := .safe)).map_wf hfresh hnodup hn
        wf.safePrimitives hfind hprim
    · intro safety safety' hsafety
      by_cases hs : safety ≤ blockSafety
      · by_cases hs' : safety' ≤ blockSafety
        · simp only [ves', hs, hs', ↓reduceIte]
          exact VEnv.addMutualDefEqs_mono <|
            VEnv.addMutualHeaders_mono (wf.mono hsafety)
              (hadd safety') (hadd safety)
        · simp only [ves', hs, hs', ↓reduceIte]
          exact (wf.mono hsafety).trans <|
            (haddedLe safety).trans VEnv.addMutualDefEqs_le
      · have hs' : ¬safety' ≤ blockSafety := fun h =>
          hs (DefinitionSafety.le_trans hsafety h)
        simpa [ves', hs, hs'] using wf.mono hsafety
  · intro safety
    by_cases hs : safety ≤ blockSafety
    · simp only [ves', hs, ↓reduceIte]
      exact (haddedLe safety).trans VEnv.addMutualDefEqs_le
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl

theorem VEnvs.WF.addSafeDefinition_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal}
    (hsafety : v.safety = .safe)
    (hfresh : env.find? v.name = none)
    (htr : TrDefVal .safe (ves.venv .safe) (.defnInfo v) v')
    (hvWF : v'.WF (ves.venv .safe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) : VEnv :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => (added safety).addDefEq v'.toDefEq⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      have hsafe : ves.venv .safe ≤ ves.venv safety :=
        wf.mono DefinitionSafety.le_safe
      have hsafety' : safety ≤ (ConstantInfo.defnInfo v).safety := by
        simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
          ConstantInfo.isPartial, hsafety] using
          (DefinitionSafety.le_safe (a := safety))
      have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) v' := by
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨hsafety',
          hconst.2.1, hconst.2.2.mono hsafe⟩, hname⟩,
          hvalue.mono hsafe⟩
      exact TrEnv.addDefinition (wf.tr (safety := safety)) htr' hfresh
        (hvWF.mono hsafe) (hadd safety)
    · intro safety
      exact (wf.hasPrimitives (safety := safety)).addDef_of_not_primitive
        (hadd safety) hn
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      have hbase := wf.mono hs
      have haddMono := VEnv.addConst_mono hbase (hadd safety') (hadd safety)
      exact VEnv.addDefEq_mono haddMono
  · intro safety
    exact (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le

theorem VEnvs.WF.addSafeTheorem_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : TheoremVal} {v' : VDefVal}
    (hfresh : env.find? v.name = none)
    (htr : TrDefVal .safe (ves.venv .safe) (.thmInfo v) v')
    (hvWF : v'.WF (ves.venv .safe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.thmInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) := Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs := ⟨fun safety => (added safety).addDefEq v'.toDefEq⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      have hbase : ves.venv .safe ≤ ves.venv safety :=
        wf.mono DefinitionSafety.le_safe
      have htr' : TrDefVal safety (ves.venv safety) (.thmInfo v) v' := by
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨by
          simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
            ConstantInfo.isPartial] using
            (DefinitionSafety.le_safe (a := safety)),
          hconst.2.1, hconst.2.2.mono hbase⟩, hname⟩,
          hvalue.mono hbase⟩
      exact TrEnv.addTheorem (wf.tr (safety := safety)) htr' hfresh
        (hvWF.mono hbase) (hadd safety)
    · intro safety
      exact (wf.hasPrimitives (safety := safety)).addDef_of_not_primitive
        (hadd safety) hn
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .thmInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      exact VEnv.addDefEq_mono <| VEnv.addConst_mono (wf.mono hs)
        (hadd safety') (hadd safety)
  · intro safety
    exact (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le

theorem VEnvs.WF.addSafeOpaque_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : OpaqueVal} {v' : VDefVal}
    (hfresh : env.find? v.name = none)
    (htr : TrOpaqueVal .safe (ves.venv .safe) v v')
    (hvWF : v'.WF (ves.venv .safe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.opaqueInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) := Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs := ⟨added⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      have hbase : ves.venv .safe ≤ ves.venv safety :=
        wf.mono DefinitionSafety.le_safe
      have htr' : TrOpaqueVal safety (ves.venv safety) v v' := by
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨DefinitionSafety.le_trans DefinitionSafety.le_safe hconst.1,
          hconst.2.1, hconst.2.2.mono hbase⟩, hname⟩,
          hvalue.mono hbase⟩
      exact TrEnv.addOpaque (wf.tr (safety := safety)) htr' hfresh
        (hvWF.mono hbase) (hadd safety)
    · intro safety
      exact (wf.hasPrimitives (safety := safety)).addConst_of_not_primitive
        (hadd safety) hn
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .opaqueInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      exact VEnv.addConst_mono (wf.mono hs) (hadd safety') (hadd safety)
  · intro safety
    exact VEnv.addConst_le (hadd safety)

theorem VEnvs.WF.addUnsafeOpaque_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : OpaqueVal} {v' : VDefVal}
    (hunsafe : v.isUnsafe = true)
    (hfresh : env.find? v.name = none)
    (htr : TrOpaqueVal .unsafe (ves.venv .unsafe) v v')
    (hvWF : v'.WF (ves.venv .unsafe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.opaqueInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) := Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => if safety ≤ .unsafe then added safety else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · have hbase : ves.venv .unsafe ≤ ves.venv safety := wf.mono hs
        have htr' : TrOpaqueVal safety (ves.venv safety) v v' := by
          rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
          exact ⟨⟨(hconst.sf_mono hs).mono hbase, hname⟩,
            hvalue.mono hbase⟩
        simpa [ves', hs] using
          TrEnv.addOpaque (wf.tr (safety := safety)) htr' hfresh
            (hvWF.mono hbase) (hadd safety)
      · simpa [ves', hs] using
          TrEnv.block (ci := .opaqueInfo v)
            (wf.tr (safety := safety)) hfresh (by
              simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
                ConstantInfo.isPartial, hunsafe] using hs)
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · simp only [ves', hs, ↓reduceIte]
        exact (wf.hasPrimitives (safety := safety)).addConst_of_not_primitive
          (hadd safety) hn
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .opaqueInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      by_cases hu : safety ≤ .unsafe
      · by_cases hu' : safety' ≤ .unsafe
        · simp only [ves', hu, hu', ↓reduceIte]
          exact VEnv.addConst_mono (wf.mono hs)
            (hadd safety') (hadd safety)
        · simp only [ves', hu, hu', ↓reduceIte]
          exact (wf.mono hs).trans (VEnv.addConst_le (hadd safety))
      · have hu' : ¬safety' ≤ .unsafe := fun h =>
          hu (DefinitionSafety.le_trans hs h)
        simpa [ves', hu, hu'] using wf.mono hs
  · intro safety
    by_cases hs : safety ≤ .unsafe
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.addConst_le (hadd safety)
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl

theorem VEnvs.WF.addSafePrimitiveDefinition
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal}
    (hsafety : v.safety = .safe) (hlevels : v.levelParams = [])
    (hfresh : env.find? v.name = none)
    (htr : TrDefVal .safe (ves.venv .safe) (.defnInfo v) v')
    (hvWF : v'.WF (ves.venv .safe))
    (hpreserves : ∀ (safety : DefinitionSafety) {out : VEnv},
      (ves.venv safety).addConst v.name v'.toVConstant = some out →
      (out.addDefEq v'.toDefEq).WF →
      (out.addDefEq v'.toDefEq).HasPrimitives) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) : VEnv :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => (added safety).addDefEq v'.toDefEq⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      have hsafe : ves.venv .safe ≤ ves.venv safety :=
        wf.mono DefinitionSafety.le_safe
      have hsafety' : safety ≤ (ConstantInfo.defnInfo v).safety := by
        rw [ConstantInfo.defnInfo_safety, hsafety]
        exact DefinitionSafety.le_safe
      have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) v' := by
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨hsafety', hconst.2.1, hconst.2.2.mono hsafe⟩,
          hname⟩, hvalue.mono hsafe⟩
      exact TrEnv.addDefinition (wf.tr (safety := safety)) htr' hfresh
        (hvWF.mono hsafe) (hadd safety)
    · intro safety
      apply hpreserves safety (hadd safety)
      exact (TrEnv.addDefinition (wf.tr (safety := safety)) (by
        have hsafe : ves.venv .safe ≤ ves.venv safety :=
          wf.mono DefinitionSafety.le_safe
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨by
          rw [ConstantInfo.defnInfo_safety, hsafety]
          exact DefinitionSafety.le_safe,
          hconst.2.1, hconst.2.2.mono hsafe⟩, hname⟩,
          hvalue.mono hsafe⟩) hfresh
        (hvWF.mono (wf.mono DefinitionSafety.le_safe))
        (hadd safety)).wf
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_safe_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf hfresh
        wf.safePrimitives (by rw [ConstantInfo.defnInfo_safety, hsafety])
        (by simpa using hlevels) hfind hprim
    · intro safety safety' hs
      have haddMono := VEnv.addConst_mono (wf.mono hs)
        (hadd safety') (hadd safety)
      exact VEnv.addDefEq_mono haddMono
  · intro safety
    exact (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le

theorem VEnvs.WF.addPartialDefinition_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal}
    (hsafety : v.safety = .partial)
    (hfresh : env.find? v.name = none)
    (htr : TrDefVal .partial (ves.venv .partial) (.defnInfo v) v')
    (hvWF : v'.WF (ves.venv .partial))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) : VEnv :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => if safety ≤ .partial then
      (added safety).addDefEq v'.toDefEq else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ .partial
      · have hbase : ves.venv .partial ≤ ves.venv safety := wf.mono hs
        have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) v' := by
          rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
          exact ⟨⟨⟨by
            rw [ConstantInfo.defnInfo_safety, hsafety]
            exact hs,
            hconst.2.1, hconst.2.2.mono hbase⟩, hname⟩,
            hvalue.mono hbase⟩
        simpa [ves', hs] using
          TrEnv.addDefinition (wf.tr (safety := safety)) htr' hfresh
            (hvWF.mono hbase) (hadd safety)
      · simpa [ves', hs] using
          TrEnv.block (ci := .defnInfo v)
            (wf.tr (safety := safety)) hfresh (by
            rw [ConstantInfo.defnInfo_safety, hsafety]
            exact hs)
    · intro safety
      by_cases hs : safety ≤ .partial
      · simp only [ves', hs, ↓reduceIte]
        exact (wf.hasPrimitives (safety := safety)).addDef_of_not_primitive
          (hadd safety) hn
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      by_cases hsp : safety ≤ .partial
      · by_cases hsp' : safety' ≤ .partial
        · simp only [ves', hsp, hsp', ↓reduceIte]
          exact VEnv.addDefEq_mono <|
            VEnv.addConst_mono (wf.mono hs) (hadd safety') (hadd safety)
        · simp only [ves', hsp, hsp', ↓reduceIte]
          exact (wf.mono hs).trans <|
            (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le
      · have hsp' : ¬safety' ≤ .partial := fun h =>
          hsp (DefinitionSafety.le_trans hs h)
        simpa [ves', hsp, hsp'] using wf.mono hs
  · intro safety
    by_cases hs : safety ≤ .partial
    · simp only [ves', hs, ↓reduceIte]
      exact (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl

theorem VEnvs.WF.addUnsafeAxiom_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : AxiomVal} {v' : VConstant}
    (hunsafe : v.isUnsafe = true)
    (hfresh : env.find? v.name = none)
    (htr : TrConstant .unsafe (ves.venv .unsafe) (.axiomInfo v) v')
    (hvWF : v'.WF (ves.venv .unsafe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.axiomInfo v)) ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      (ves.venv .unsafe).addConst v.name v' = some (ves'.venv .unsafe) := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v' = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v' = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => if safety ≤ .unsafe then added safety else ves.venv safety⟩
  refine ⟨ves', ?_, ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · have hbase : ves.venv .unsafe ≤ ves.venv safety := wf.mono hs
        have htr' : TrConstant safety (ves.venv safety) (.axiomInfo v) v' :=
          (htr.sf_mono hs).mono hbase
        simpa [ves', hs] using
          TrEnv.addAxiom (wf.tr (safety := safety)) htr' hfresh
            (hvWF.mono hbase) (hadd safety)
      · simpa [ves', hs] using
          TrEnv.block (ci := .axiomInfo v)
            (wf.tr (safety := safety)) hfresh (by
              simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
                ConstantInfo.isPartial, hunsafe] using hs)
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · simp only [ves', hs, ↓reduceIte]
        exact (wf.hasPrimitives (safety := safety)).addConst_of_not_primitive
          (hadd safety) hn
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .axiomInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      by_cases hu : safety ≤ .unsafe
      · by_cases hu' : safety' ≤ .unsafe
        · simp only [ves', hu, hu', ↓reduceIte]
          exact VEnv.addConst_mono (wf.mono hs)
            (hadd safety') (hadd safety)
        · simp only [ves', hu, hu', ↓reduceIte]
          exact (wf.mono hs).trans (VEnv.addConst_le (hadd safety))
      · have hu' : ¬safety' ≤ .unsafe := fun h =>
          hu (DefinitionSafety.le_trans hs h)
        simpa [ves', hu, hu'] using wf.mono hs
  · intro safety
    by_cases hs : safety ≤ .unsafe
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.addConst_le (hadd safety)
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl
  · simpa [ves', DefinitionSafety.le_rfl] using hadd .unsafe

theorem VEnvs.WF.addSafeAxiom_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : AxiomVal} {v' : VConstant}
    (hunsafe : v.isUnsafe = false)
    (hfresh : env.find? v.name = none)
    (htr : TrConstant .safe (ves.venv .safe) (.axiomInfo v) v')
    (hvWF : v'.WF (ves.venv .safe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.axiomInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v' = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v' = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs := ⟨added⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      have hbase : ves.venv .safe ≤ ves.venv safety :=
        wf.mono DefinitionSafety.le_safe
      have htr' : TrConstant safety (ves.venv safety) (.axiomInfo v) v' := by
        exact (htr.sf_mono DefinitionSafety.le_safe).mono hbase
      exact TrEnv.addAxiom (wf.tr (safety := safety)) htr' hfresh
        (hvWF.mono hbase) (hadd safety)
    · intro safety
      exact (wf.hasPrimitives (safety := safety)).addConst_of_not_primitive
        (hadd safety) hn
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .axiomInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      exact VEnv.addConst_mono (wf.mono hs)
        (hadd safety') (hadd safety)
  · intro safety
    exact VEnv.addConst_le (hadd safety)

theorem VEnvs.WF.addUnsafeDefinition_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal} {out : VEnv}
    (hsafety : v.safety = .unsafe)
    (hfresh : env.find? v.name = none)
    (hheader : TrConstVal .unsafe (ves.venv .unsafe)
      (.defnInfo v) v'.toVConstVal)
    (hheaderWF : v'.toVConstant.WF (ves.venv .unsafe))
    (hadd : (ves.venv .unsafe).addConst v.name v'.toVConstant = some out)
    (hvalue : TrExprS out v.levelParams [] v.value v'.value)
    (hvalueWF : v'.WF out)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let ves' : VEnvs := ⟨fun safety => if safety ≤ .unsafe then
    out.addDefEq v'.toDefEq else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · have heq := DefinitionSafety.le_antisymm hs
            (DefinitionSafety.unsafe_le (a := safety))
        subst safety
        simpa [ves'] using TrEnv.addUnsafeDefinition
          (wf.tr (safety := .unsafe)) hheader hfresh hheaderWF hadd
          hvalue hvalueWF
      · simpa [ves', hs] using
          TrEnv.block (ci := .defnInfo v)
            (wf.tr (safety := safety)) hfresh (by
              simpa [ConstantInfo.defnInfo_safety, hsafety] using hs)
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · have heq := DefinitionSafety.le_antisymm hs
            (DefinitionSafety.unsafe_le (a := safety))
        subst safety
        simp only [ves', DefinitionSafety.le_rfl, ↓reduceIte]
        exact (wf.hasPrimitives (safety := .unsafe)).addDef_of_not_primitive
          hadd hn
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      by_cases hu : safety ≤ .unsafe
      · have heq := DefinitionSafety.le_antisymm hu
            (DefinitionSafety.unsafe_le (a := safety))
        subst safety
        by_cases hu' : safety' ≤ .unsafe
        · have heq' := DefinitionSafety.le_antisymm hu'
              (DefinitionSafety.unsafe_le (a := safety'))
          subst safety'
          exact VEnv.LE.rfl
        · simp only [ves', DefinitionSafety.le_rfl, hu', ↓reduceIte]
          exact (wf.mono DefinitionSafety.unsafe_le).trans <|
            (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
      · have hu' : ¬safety' ≤ .unsafe := fun h =>
          hu (DefinitionSafety.le_trans hs h)
        simpa [ves', hu, hu'] using wf.mono hs
  · intro safety
    by_cases hs : safety ≤ .unsafe
    · have heq := DefinitionSafety.le_antisymm hs
          (DefinitionSafety.unsafe_le (a := safety))
      subst safety
      simp only [ves', DefinitionSafety.le_rfl, ↓reduceIte]
      exact (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl

theorem addDefinition.WF_safe_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNonprimitiveDefinition.WF wf v hsafety hn).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh⟩ := h
  exact wf.addSafeDefinition_of_not_primitive hsafety hfresh htr hvWF hn

theorem checkPartialNonprimitiveDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      if allowPrimitive then
        throw <| Exception.other
          s!"primitive definition {v.name} must be safe"
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .partial (ves.venv .partial) (.defnInfo v) v' ∧
          v'.WF (ves.venv .partial) ∧ env.find? v.name = none := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.WF_of_not_primitive
    (c := .mk' wf .safe v.levelParams) (s := state') hn).bind
      fun allow _ _ hallow => ?_
  subst allow
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hname => ?_
  have hmono : ves.venv .safe ≤ ves.venv .partial :=
    wf.mono (by decide)
  refine ⟨v', ?_, hvalueT.mono hmono, hname.1⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype.mono hmono⟩, hvname⟩, hvalue.mono hmono⟩

theorem addDefinition.WF_partial_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkPartialNonprimitiveDefinition.WF wf v hsafety hn).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh⟩ := h
  exact wf.addPartialDefinition_of_not_primitive
    hsafety hfresh htr hvWF hn

theorem addDefinition.WF_partial_of_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hp : Lean.Kernel.Environment.primitives.contains v.name) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind] at hrun
  split at hrun <;> cases hrun
  rename_i _ _ hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i _ primitiveResult hprimitive
      clear hbody
      split at hrun
      · change (Except.error _ : Except Exception (Unit × State)) =
          Except.ok _ at hrun
        contradiction
      · rename_i hfalse
        have hfalse' : primitiveResult.fst = false := by
          cases h : primitiveResult.fst <;> simp_all
        rw [hfalse'] at hrun
        change ((fun x => (x, _)) <$> env.checkName v.name false) =
          Except.ok _ at hrun
        simp [Lean.Kernel.Environment.checkName, hp] at hrun
        split at hrun <;>
          change (Except.error _ : Except Exception (Unit × State)) =
            Except.ok _ at hrun <;>
          contradiction

theorem addDefinition.WF_safe_natAdd
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatAddDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.add := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.add v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatAddDef
    hnat' hname' hadd' hwf' huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natMod
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mod)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatModDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.mod := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.mod v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatModPrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨zeroL', zeroR', go', goTy', topL', topR', goL', goR',
        hzeroL, hzeroR, hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
        hparams, hnat, hbool, hble, hsub, hty, hzeroEq,
        selector, hgoHas, htopEq, hgoEq⟩
    exact ⟨zeroL', zeroR', go', goTy', topL', topR', goL', goR',
      hzeroL.mono hmono, hzeroR.mono hmono, hgoS.mono hmono,
      hgoTyS.mono hmono, htopL.mono hmono, htopR.mono hmono,
      hgoL.mono hmono, hgoR.mono hmono, hparams,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbool; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hble; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hsub; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono, hzeroEq.mono hmono, selector.mono hmono,
      hgoHas.mono hmono, htopEq.mono hmono, hgoEq.mono hmono⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natDiv
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.div)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatDivDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.div := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.div v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatDivPrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨go', goTy', topL', topR', goL', goR',
        hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
        hparams, hnat, hbool, hble, hsub, hty,
        selector, hgoHas, htopEq, hgoEq⟩
    exact ⟨go', goTy', topL', topR', goL', goR',
      hgoS.mono hmono, hgoTyS.mono hmono,
      htopL.mono hmono, htopR.mono hmono,
      hgoL.mono hmono, hgoR.mono hmono, hparams,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbool; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hble; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hsub; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono, selector.mono hmono,
      hgoHas.mono hmono, htopEq.mono hmono, hgoEq.mono hmono⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natGcd
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.gcd)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatGcdDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.gcd := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.gcd v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatGcdPrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨cert, hparams, hnat, hbeq, hmod, hty, hvalid, hshape⟩
    exact ⟨cert, hparams,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbeq; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hmod; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono, hvalid.mono hmono rfl rfl, hshape⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natBitwise
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.bitwise)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBitwiseDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.bitwise := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.bitwise v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatBitwisePrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨cert, ite, decide, hparams, hbool, hnat, hbeq,
        haddC, hmodC, hdivC, hty, hcert,
        hiteS, hite, hdecideS, hdecide⟩
    exact ⟨cert, ite, decide, hparams,
      let ⟨ci, hci⟩ := hbool; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbeq; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := haddC; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hmodC; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hdivC; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono,
      hcert.mono hmono rfl rfl,
      hiteS.mono hmono,
      ⟨hite.1.mono hmono,
        fun b x y => (hite.2 b x y).mono hmono⟩,
      hdecideS.mono hmono,
      hdecide.mono hmono⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natPred
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pred)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatPredDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.pred := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.pred v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatPredDef
    hnat' hname' hadd' hwf' huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natSub
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.sub)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatSubDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hpred, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hpred' : (ves.venv safety).contains ``Nat.pred := by
    obtain ⟨ci, hci⟩ := hpred
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.sub := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.sub v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatSubDef
    (wf.tr (safety := safety)).wf hpred' hname' hadd' hwf'
    huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natMul
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mul)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatMulDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, haddC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have haddC' : (ves.venv safety).contains ``Nat.add := by
    obtain ⟨ci, hci⟩ := haddC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.mul := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.mul v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatMulDef
    (wf.tr (safety := safety)).wf haddC' hname' hadd' hwf'
    huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natPow
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pow)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatPowDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hmulC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hmulC' : (ves.venv safety).contains ``Nat.mul := by
    obtain ⟨ci, hci⟩ := hmulC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.pow := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.pow v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatPowDef
    (wf.tr (safety := safety)).wf hmulC' hname' hadd' hwf'
    huvars' hty' hz' hs'


theorem addDefinition.WF_safe_natShiftLeft
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftLeft)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatShiftLeftDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hmulC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hmulC' : (ves.venv safety).contains ``Nat.mul := by
    obtain ⟨ci, hci⟩ := hmulC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.shiftLeft := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.shiftLeft v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatShiftLeftDef
    (wf.tr (safety := safety)).wf hmulC' hname' hadd' hwf'
    huvars' hty' hz' hs'


theorem addDefinition.WF_safe_natShiftRight
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftRight)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatShiftRightDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hdivC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hdivC' : (ves.venv safety).contains ``Nat.div := by
    obtain ⟨ci, hci⟩ := hdivC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.shiftRight := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.shiftRight v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatShiftRightDef
    (wf.tr (safety := safety)).wf hdivC' hname' hadd' hwf'
    huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natBEq
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.beq)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBEqDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hbool,
    hty, h00, h0s, hs0, hss⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.beq := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have h00' := h00.mono hmono
  have h0s' := h0s.mono hmono
  have hs0' := hs0.mono hmono
  have hss' := hss.mono hmono
  rw [hlevels] at hty' h00' h0s' hs0' hss'
  have hadd' : (ves.venv safety).addConst ``Nat.beq v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatBEqDef
    hnat' hbool' hname' hadd' hwf' huvars' hty' h00' h0s' hs0' hss'



theorem addDefinition.WF_safe_natBLE
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.ble)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBLEDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hbool,
    hty, h00, h0s, hs0, hss⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.ble := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have h00' := h00.mono hmono
  have h0s' := h0s.mono hmono
  have hs0' := hs0.mono hmono
  have hss' := hss.mono hmono
  rw [hlevels] at hty' h00' h0s' hs0' hss'
  have hadd' : (ves.venv safety).addConst ``Nat.ble v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatBLEDef
    hnat' hbool' hname' hadd' hwf' huvars' hty' h00' h0s' hs0' hss'

theorem addDefinition.WF_safe_charOfNat
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Char.ofNat)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeCharOfNatDefinition.WF
    wf v hname hsafety).run wf |>.map fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, _, hty⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  rw [hlevels] at hty'
  have hadd' : (ves.venv safety).addConst ``Char.ofNat v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addCharOfNat
    hadd' hwf' huvars' hty'

theorem addDefinition.WF_safe_stringOfList
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``String.ofList)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeStringOfListDefinition.WF
    wf v hname hsafety).run wf |>.map fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hty, hnil, hcons⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hnil' := hnil.mono hmono
  have hcons' := hcons.mono hmono
  rw [hlevels] at hty' hnil' hcons'
  have hadd' : (ves.venv safety).addConst
      ``String.ofList v'.toVConstant = some out := by
    simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addStringOfList
    hadd' hwf' huvars' hty' hnil' hcons'

theorem addDefinition.WF_safe_natLand_of_shape
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.land)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatLandDefinition.WF wf v op hname hshape hsafety).run wf
    |>.map fun _ h => ?_
  obtain ⟨v', op', htr, hvWF, hfresh, hlevels, hnat, hbool, hbitwise,
    hty, hvalue, hopTy, hf, ht⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hbitwise' : (ves.venv safety).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwise
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.land := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hf' := hf.mono hmono
  have ht' := ht.mono hmono
  rw [hlevels] at hty' hopTy' hf' ht'
  have hadd' : (ves.venv safety).addConst ``Nat.land v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatLandDef
    (wf.tr (safety := safety)).wf hnat' hbool' hbitwise'
    hname' hadd' hwf' huvars' hty' hvalue
    hopTy' hf' ht'

theorem addDefinition.WF_safe_natLor_of_shape
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.lor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatLorDefinition.WF wf v op hname hshape hsafety).run wf
    |>.map fun _ h => ?_
  obtain ⟨v', op', htr, hvWF, hfresh, hlevels, hnat, hbool, hbitwise,
    hty, hvalue, hopTy, hf, ht⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hbitwise' : (ves.venv safety).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwise
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.lor := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hf' := hf.mono hmono
  have ht' := ht.mono hmono
  rw [hlevels] at hty' hopTy' hf' ht'
  have hadd' : (ves.venv safety).addConst ``Nat.lor v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatLorDef
    (wf.tr (safety := safety)).wf hnat' hbool' hbitwise'
    hname' hadd' hwf' huvars' hty' hvalue
    hopTy' hf' ht'

theorem addDefinition.WF_safe_natXor_of_shape
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.xor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatXorDefinition.WF wf v op hname hshape hsafety).run wf
    |>.map fun _ h => ?_
  obtain ⟨v', op', htr, hvWF, hfresh, hlevels, hnat, hbitwise,
    hty, hvalue, hopTy, hff, htf, hft, htt⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbitwise' : (ves.venv safety).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwise
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.xor := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hff' := hff.mono hmono
  have htf' := htf.mono hmono
  have hft' := hft.mono hmono
  have htt' := htt.mono hmono
  rw [hlevels] at hty' hopTy' hff' htf' hft' htt'
  have hadd' : (ves.venv safety).addConst ``Nat.xor v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatXorDef
    hnat' hbitwise' hname' hadd' hwf' huvars' hty' hvalue
    hopTy' hff' htf' hft' htt'

private theorem addDefinition.success_natLand_value_shape
    {env env' : Environment} {v : DefinitionVal}
    (hname : v.name = ``Nat.land) (hsafety : v.safety = .safe)
    (hsuccess : addDefinition env v = .ok env') :
    ∃ op, v.value = .app (.const ``Nat.bitwise []) op := by
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  split at hrun <;> cases hrun
  rename_i _ _ _ _ hrun
  simp [(· >>= ·), ReaderT.bind] at hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i hprimitive
      clear hrun hbody
      simp only [Environment.checkPrimitiveDef, hname] at hprimitive
      simp [TypeChecker.getEnv, (· >>= ·), ReaderT.bind,
        MonadReader.read, readThe, MonadReaderOf.read, Pure.pure,
        ReaderT.read, ReaderT.pure, StateT.bind, StateT.pure,
        Except.pure, Except.bind] at hprimitive
      split at hprimitive
      · split at hprimitive
        · rename_i and hshape
          exact ⟨and, hshape⟩
        · exfalso
          change Except.error _ = Except.ok _ at hprimitive
          cases hprimitive
      · exfalso
        change Except.error _ = Except.ok _ at hprimitive
        cases hprimitive

theorem addDefinition.WF_safe_natLand
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.land)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  obtain ⟨op, hshape⟩ :=
    addDefinition.success_natLand_value_shape hname hsafety hsuccess
  exact addDefinition.WF_safe_natLand_of_shape
    wf v op hname hshape hsafety env' hsuccess

private theorem addDefinition.success_natLor_value_shape
    {env env' : Environment} {v : DefinitionVal}
    (hname : v.name = ``Nat.lor) (hsafety : v.safety = .safe)
    (hsuccess : addDefinition env v = .ok env') :
    ∃ op, v.value = .app (.const ``Nat.bitwise []) op := by
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  split at hrun <;> cases hrun
  rename_i _ _ _ _ hrun
  simp [(· >>= ·), ReaderT.bind] at hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i hprimitive
      clear hrun hbody
      simp only [Environment.checkPrimitiveDef, hname] at hprimitive
      simp [TypeChecker.getEnv, (· >>= ·), ReaderT.bind,
        MonadReader.read, readThe, MonadReaderOf.read, Pure.pure,
        ReaderT.read, ReaderT.pure, StateT.bind, StateT.pure,
        Except.pure, Except.bind] at hprimitive
      split at hprimitive
      · split at hprimitive
        · rename_i or hshape
          exact ⟨or, hshape⟩
        · exfalso
          change Except.error _ = Except.ok _ at hprimitive
          cases hprimitive
      · exfalso
        change Except.error _ = Except.ok _ at hprimitive
        cases hprimitive

theorem addDefinition.WF_safe_natLor
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.lor)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  obtain ⟨op, hshape⟩ :=
    addDefinition.success_natLor_value_shape hname hsafety hsuccess
  exact addDefinition.WF_safe_natLor_of_shape
    wf v op hname hshape hsafety env' hsuccess

private theorem addDefinition.success_natXor_value_shape
    {env env' : Environment} {v : DefinitionVal}
    (hname : v.name = ``Nat.xor) (hsafety : v.safety = .safe)
    (hsuccess : addDefinition env v = .ok env') :
    ∃ op, v.value = .app (.const ``Nat.bitwise []) op := by
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  split at hrun <;> cases hrun
  rename_i _ _ _ _ hrun
  simp [(· >>= ·), ReaderT.bind] at hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i hprimitive
      clear hrun hbody
      simp only [Environment.checkPrimitiveDef, hname] at hprimitive
      simp [TypeChecker.getEnv, (· >>= ·), ReaderT.bind,
        MonadReader.read, readThe, MonadReaderOf.read, Pure.pure,
        ReaderT.read, ReaderT.pure, StateT.bind, StateT.pure,
        Except.pure, Except.bind] at hprimitive
      split at hprimitive
      · split at hprimitive
        · rename_i xor hshape
          exact ⟨xor, hshape⟩
        · exfalso
          change Except.error _ = Except.ok _ at hprimitive
          cases hprimitive
      · exfalso
        change Except.error _ = Except.ok _ at hprimitive
        cases hprimitive

theorem addDefinition.WF_safe_natXor
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.xor)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  obtain ⟨op, hshape⟩ :=
    addDefinition.success_natXor_value_shape hname hsafety hsuccess
  exact addDefinition.WF_safe_natXor_of_shape
    wf v op hname hshape hsafety env' hsuccess

theorem addDefinition.WF_safe_inductiveName
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hname : v.name = ``Bool ∨ v.name = ``Bool.false ∨
      v.name = ``Bool.true ∨ v.name = ``Nat ∨
      v.name = ``Nat.zero ∨ v.name = ``Nat.succ) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  have hrun : ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ => False := by
    refine (checkDefinitionBody.WF wf v).bind fun _ state' _ _ => ?_
    refine (Environment.checkPrimitiveDef.WF_of_inductive_name
      (c := .mk' wf .safe v.levelParams) (s := state') hname).bind
      fun allow _ _ hallow => ?_
    refine (TypeChecker.M.WF.liftExcept
      (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
      fun _ _ _ hcheckedName => ?_
    have : allow = true := hcheckedName.2 (by
      rcases hname with hname | hname | hname | hname | hname | hname
      all_goals
        rw [hname]
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    simp_all
  exact hrun.run wf |>.map fun _ h => False.elim h

set_option maxRecDepth 4000 in
theorem addDefinition.WF_safe
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  by_cases hn : ¬Lean.Kernel.Environment.primitives.contains v.name
  · exact addDefinition.WF_safe_of_not_primitive wf v hsafety hn
  · have hp₀ : Lean.Kernel.Environment.primitives.contains v.name :=
      Classical.byContradiction fun h => hn h
    have hp : v.name = ``Bool ∨ v.name = ``Bool.false ∨
        v.name = ``Bool.true ∨ v.name = ``Nat ∨
        v.name = ``Nat.zero ∨ v.name = ``Nat.succ ∨
        v.name = ``Nat.add ∨ v.name = ``Nat.pred ∨
        v.name = ``Nat.sub ∨ v.name = ``Nat.mul ∨
        v.name = ``Nat.pow ∨ v.name = ``Nat.gcd ∨
        v.name = ``Nat.mod ∨ v.name = ``Nat.div ∨
        v.name = ``Nat.beq ∨ v.name = ``Nat.ble ∨
        v.name = ``Nat.bitwise ∨ v.name = ``Nat.land ∨
        v.name = ``Nat.lor ∨ v.name = ``Nat.xor ∨
        v.name = ``Nat.shiftLeft ∨ v.name = ``Nat.shiftRight ∨
        v.name = ``String.ofList ∨ v.name = ``Char.ofNat := by
      simp [Lean.Kernel.Environment.primitives,
        NameSet.contains, NameSet.ofList] at hp₀
      simpa only [eq_comm] using hp₀
    rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h
    · exact addDefinition.WF_safe_inductiveName wf v hsafety (.inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety (.inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inr <| .inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inr <| .inr <| .inr h)
    · exact addDefinition.WF_safe_natAdd wf v h hsafety
    · exact addDefinition.WF_safe_natPred wf v h hsafety
    · exact addDefinition.WF_safe_natSub wf v h hsafety
    · exact addDefinition.WF_safe_natMul wf v h hsafety
    · exact addDefinition.WF_safe_natPow wf v h hsafety
    · exact addDefinition.WF_safe_natGcd wf v h hsafety
    · exact addDefinition.WF_safe_natMod wf v h hsafety
    · exact addDefinition.WF_safe_natDiv wf v h hsafety
    · exact addDefinition.WF_safe_natBEq wf v h hsafety
    · exact addDefinition.WF_safe_natBLE wf v h hsafety
    · exact addDefinition.WF_safe_natBitwise wf v h hsafety
    · exact addDefinition.WF_safe_natLand wf v h hsafety
    · exact addDefinition.WF_safe_natLor wf v h hsafety
    · exact addDefinition.WF_safe_natXor wf v h hsafety
    · exact addDefinition.WF_safe_natShiftLeft wf v h hsafety
    · exact addDefinition.WF_safe_natShiftRight wf v h hsafety
    · exact addDefinition.WF_safe_stringOfList wf v h hsafety
    · exact addDefinition.WF_safe_charOfNat wf v h hsafety

theorem addDefinition.WF_partial
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  by_cases hn : ¬Lean.Kernel.Environment.primitives.contains v.name
  · exact addDefinition.WF_partial_of_not_primitive wf v hsafety hn
  · exact addDefinition.WF_partial_of_primitive wf v hsafety
      (Classical.byContradiction fun h => hn h)

theorem addDefinition.WF_unsafe
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .unsafe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkConstantVal.WF
    (c := .mk' wf .unsafe v.levelParams) (s := {})
    (env := env) (v := v.toConstantVal)
    (wf.tr (safety := .unsafe)).map_wf).run wf |>.bind
      fun _ hchecked => ?_
  obtain ⟨hfresh, hreserved, type', htype, htypeWF⟩ := hchecked
  have hn : ¬Lean.Kernel.Environment.primitives.contains v.name := by
    intro hp
    have := hreserved hp
    contradiction
  let header : AxiomVal := { v.toConstantVal with isUnsafe := true }
  let vconst : VConstant := {
    uvars := v.levelParams.length
    type := type' }
  have hheaderTr : TrConstant .unsafe (ves.venv .unsafe)
      (.axiomInfo header) vconst := by
    exact ⟨by
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial, header], rfl, htype⟩
  have hheaderWF : vconst.WF (ves.venv .unsafe) := htypeWF
  obtain ⟨vesH, wfH, hmonoH, haddH⟩ :=
    wf.addUnsafeAxiom_of_not_primitive (v := header) (v' := vconst)
      (by simp [header]) hfresh hheaderTr hheaderWF hn
  refine checkNoMVarNoFVar.WF.bind fun _ hclosed => ?_
  have htypeH : TrExprS (vesH.venv .unsafe) v.levelParams []
      v.type type' := htype.mono (hmonoH .unsafe)
  have hbodyRun := (checkBodyCore.WF
    (env := env.add (.axiomInfo header)) wfH
    (.defnDecl v) v.name v.levelParams v.type v.value type'
    htypeH hclosed).run wfH
  simp only [header, Bool.not_eq_true'] at hbodyRun
  refine hbodyRun.map fun _ hbody => ?_
  obtain ⟨value', hvalue, hvalueWF⟩ := hbody
  let v' : VDefVal := {
    name := v.name
    uvars := v.levelParams.length
    type := type'
    value := value' }
  have hfinalHeader : TrConstVal .unsafe (ves.venv .unsafe)
      (.defnInfo v) v'.toVConstVal := by
    exact ⟨⟨by
      rw [ConstantInfo.defnInfo_safety, hsafety]
      exact DefinitionSafety.le_rfl,
      rfl, htype⟩, rfl⟩
  have hfinalHeaderWF : v'.toVConstant.WF (ves.venv .unsafe) :=
    htypeWF
  exact wf.addUnsafeDefinition_of_not_primitive hsafety hfresh
    hfinalHeader hfinalHeaderWF (by simpa [v', vconst] using haddH)
    (by simpa [v'] using hvalue) (by simpa [v'] using hvalueWF) hn

theorem addDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases hsafety : v.safety with
  | «unsafe» => exact addDefinition.WF_unsafe wf v hsafety
  | safe => exact addDefinition.WF_safe wf v hsafety
  | «partial» => exact addDefinition.WF_partial wf v hsafety

theorem addAxiom.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : AxiomVal) :
    (addAxiom env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases hunsafe : v.isUnsafe with
  | false =>
    unfold addAxiom
    simp [hunsafe]
    refine (checkConstantVal.WF
      (c := .mk' wf .safe v.levelParams) (s := {})
      (env := env) (v := v.toConstantVal)
      (wf.tr (safety := .safe)).map_wf).run wf |>.map
        fun _ hchecked => ?_
    obtain ⟨hfresh, hreserved, type', htype, htypeWF⟩ := hchecked
    have hn : ¬Lean.Kernel.Environment.primitives.contains v.name := by
      intro hp
      have := hreserved hp
      contradiction
    let v' : VConstant := {
      uvars := v.levelParams.length
      type := type' }
    have htr : TrConstant .safe (ves.venv .safe) (.axiomInfo v) v' := by
      exact ⟨by
        simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
          ConstantInfo.isPartial, hunsafe], rfl, htype⟩
    exact wf.addSafeAxiom_of_not_primitive hunsafe hfresh htr
      (by simpa [v'] using htypeWF) hn
  | true =>
    unfold addAxiom
    simp [hunsafe]
    refine (checkConstantVal.WF
      (c := .mk' wf .unsafe v.levelParams) (s := {})
      (env := env) (v := v.toConstantVal)
      (wf.tr (safety := .unsafe)).map_wf).run wf |>.map
        fun _ hchecked => ?_
    obtain ⟨hfresh, hreserved, type', htype, htypeWF⟩ := hchecked
    have hn : ¬Lean.Kernel.Environment.primitives.contains v.name := by
      intro hp
      have := hreserved hp
      contradiction
    let v' : VConstant := {
      uvars := v.levelParams.length
      type := type' }
    have htr : TrConstant .unsafe (ves.venv .unsafe) (.axiomInfo v) v' := by
      exact ⟨DefinitionSafety.unsafe_le, rfl, htype⟩
    obtain ⟨ves', hwf, hmono, _⟩ :=
      wf.addUnsafeAxiom_of_not_primitive hunsafe hfresh htr
        (by simpa [v'] using htypeWF) hn
    exact ⟨ves', hwf, hmono⟩

theorem addTheorem.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : TheoremVal) :
    (addTheorem env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addTheorem
  simp
  have hrun := (checkTheorem.WF wf v).run wf
  simp only [Bool.not_eq_true'] at hrun
  refine hrun.map fun _ hchecked => ?_
  obtain ⟨v', htr, hvWF, hfresh, hn⟩ := hchecked
  exact wf.addSafeTheorem_of_not_primitive hfresh htr hvWF hn

theorem addOpaque.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : OpaqueVal) :
    (addOpaque env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases hunsafe : v.isUnsafe with
  | false =>
    unfold addOpaque
    simp [hunsafe]
    have hrun := (checkOpaque.WF wf v .safe (by simp [hunsafe])).run wf
    simp only [Bool.not_eq_true'] at hrun
    refine hrun.map fun _ hchecked => ?_
    obtain ⟨v', htr, hvWF, hfresh, hn⟩ := hchecked
    exact wf.addSafeOpaque_of_not_primitive hfresh htr hvWF hn
  | true =>
    unfold addOpaque
    simp [hunsafe]
    have hrun := (checkOpaque.WF wf v .unsafe (by simp [hunsafe])).run wf
    simp only [Bool.not_eq_true'] at hrun
    refine hrun.map fun _ hchecked => ?_
    obtain ⟨v', htr, hvWF, hfresh, hn⟩ := hchecked
    exact wf.addUnsafeOpaque_of_not_primitive hunsafe hfresh htr hvWF hn

theorem addMutualRuns.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v₀ : DefinitionVal) (tail : List DefinitionVal)
    (safety : DefinitionSafety) (hsafety : v₀.safety = safety)
    (hunique : mutualNamesUnique (v₀ :: tail) = true) :
    (do
      M.run env safety (lctx := {}) (lparams := v₀.levelParams) (fuel := {}) <|
        checkMutualHeaders env v₀ (v₀ :: tail)
      let checkEnv := addMutualCheckEnv env (v₀ :: tail)
      M.run checkEnv safety (lctx := {}) (lparams := v₀.levelParams) (fuel := {}) <|
        checkMutualBodies checkEnv (v₀ :: tail) (v₀ :: tail)
      pure (addMutualFinalEnv env (v₀ :: tail))).WF fun env' =>
        ∃ ves' : VEnvs, ves'.WF env' ∧
          ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let all := v₀ :: tail
  have hheadersRun :=
    (checkMutualHeaders.WF wf v₀ all safety hsafety).run wf
  refine hheadersRun.bind fun _ hchecked => ?_
  obtain ⟨headerVals, hheaders⟩ := hchecked
  have hfresh := Lean4Lean.List.Forall₂.mutualHeader_fresh hheaders
  have hnodup : (all.map (fun v => v.name)).Nodup := by
    simpa [all] using mutualNamesUnique_nodup hunique
  have htypes := Lean4Lean.List.Forall₂.mutualHeader_types hheaders
  obtain ⟨headers, hadd, hbase, hcontains⟩ :=
    VEnv.addMutualHeaders_spec
      (Lean4Lean.List.Forall₂.mutualHeader_target_fresh hheaders
        (wf.tr (safety := safety)))
      (Lean4Lean.List.Forall₂.mutualHeader_names_nodup hheaders hnodup)
  have hcheckTr : TrEnv safety (addMutualCheckEnv env all) headers :=
    (wf.tr (safety := safety)).addMutualCheckHeaders
      (Lean4Lean.List.Forall₂.mutualHeader_toOpaque hheaders)
      hfresh hnodup htypes hadd
  have hcheckPrimitives : headers.HasPrimitives :=
    (wf.hasPrimitives (safety := safety)).addMutualHeaders
      (Lean4Lean.List.Forall₂.mutualHeader_target_notPrimitive hheaders) hadd
  have hcheckSafePrimitives : ∀ {n : Name} {ci : ConstantInfo},
      (addMutualCheckEnv env all).find? n = some ci →
        Lean.Kernel.Environment.primitives.contains n →
        ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci
    exact Environment.safePrimitives_addMutualCheckEnv
      (n := n) (ci := ci) (wf.tr (safety := .safe)).map_wf
      hfresh hnodup
      (Lean4Lean.List.Forall₂.mutualHeader_notPrimitive hheaders)
      wf.safePrimitives
  let c : TypeChecker.VContext := {
    env := addMutualCheckEnv env all
    safety := safety
    lctx := {}
    lparams := v₀.levelParams
    fuel := {}
    venv := headers
    hasPrimitives := hcheckPrimitives
    safePrimitives := hcheckSafePrimitives
    trenv := hcheckTr
    mlctx := .nil
    mlctx_wf := trivial
    lctx_eq := rfl }
  have hc : c.toContext = {
      env := addMutualCheckEnv env all
      safety := safety
      lctx := {}
      lparams := v₀.levelParams
      fuel := {} } := rfl
  have hstate : TypeChecker.VState.WF c {} := {
    trctx := .nil
    ngen_wf := nofun
    ectx := ⟨[], .refl, trivial, .refl, .empty, nofun⟩
    inferTypeI_wf := .empty
    inferTypeC_wf := .empty
    whnfCore_wf := .empty
    whnf_wf := .empty
    unfold_wf _ := by simp }
  have hbodiesRun := (checkMutualBodies.WF c env all v₀
    (ves.venv safety) hbase rfl rfl hheaders).runContext hc hstate
  refine hbodiesRun.map fun _ hcheckedBodies => ?_
  obtain ⟨finalVals, hbodies, hsame⟩ := hcheckedBodies
  have hfinal := Lean4Lean.List.Forall₂.mutualBody_toFinal hbodies
  have hfinalFresh := Lean4Lean.List.Forall₂.trConst_target_fresh hfinal
    (fun _ => rfl) (wf.tr (safety := safety)) hfresh
  have hfinalNames := Lean4Lean.List.Forall₂.trConst_names_eq
    hfinal (fun _ => rfl)
  have hfinalNodup : (finalVals.map (fun v => v.name)).Nodup := by
    rw [← hfinalNames]
    exact hnodup
  obtain ⟨finalHeaders, hfinalAdd, _, hfinalContains⟩ :=
    VEnv.addMutualHeaders_spec hfinalFresh hfinalNodup
  have hsameAdd := VEnv.addMutualHeaders_congr (env := ves.venv safety) hsame
  have hfinalHeadersEq : finalHeaders = headers := by
    rw [hadd, hfinalAdd] at hsameAdd
    exact Option.some.inj hsameAdd.symm
  subst finalHeaders
  have hfinalNotPrimitive : ∀ v' ∈ finalVals,
      ¬Lean.Kernel.Environment.primitives.contains v'.name := by
    intro w hw hprim
    have hwname : w.name ∈ finalVals.map (fun v => v.name) :=
      List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [← hfinalNames] at hwname
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hwname
    exact (Lean4Lean.List.Forall₂.mutualHeader_notPrimitive hheaders)
      v hv (hvw ▸ hprim)
  exact wf.addMutual
    (Lean4Lean.List.Forall₂.mutualHeader_sameSafety hheaders)
    hfresh hnodup
    (Lean4Lean.List.Forall₂.mutualHeader_notPrimitive hheaders)
    hfinalNotPrimitive hfinal
    (Lean4Lean.List.Forall₂.mutualBody_types hbodies)
    hfinalAdd hfinalContains
    (Lean4Lean.List.Forall₂.mutualBody_bodies hbodies)
    (Lean4Lean.List.Forall₂.mutualBody_wfs hbodies)

theorem addMutual.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (vs : List DefinitionVal) :
    (addMutual env vs).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases vs with
  | nil =>
    simp only [addMutual]
    exact .throw
  | cons v₀ tail =>
    cases hsafety : v₀.safety with
    | safe =>
      simp only [addMutual, hsafety, ↓reduceIte]
      exact .throw
    | «unsafe» =>
      by_cases hunique : mutualNamesUnique (v₀ :: tail) = true
      · simpa only [addMutual, hsafety, hunique, ↓reduceIte, pure_bind] using
          addMutualRuns.WF wf v₀ tail .unsafe hsafety hunique
      · have hunique' : mutualNamesUnique (v₀ :: tail) = false := by
          simpa using hunique
        simp only [addMutual, hsafety, hunique', ↓reduceIte]
        exact .throw
    | «partial» =>
      by_cases hunique : mutualNamesUnique (v₀ :: tail) = true
      · simpa only [addMutual, hsafety, hunique, ↓reduceIte, pure_bind] using
          addMutualRuns.WF wf v₀ tail .partial hsafety hunique
      · have hunique' : mutualNamesUnique (v₀ :: tail) = false := by
          simpa using hunique
        simp only [addMutual, hsafety, hunique', ↓reduceIte]
        exact .throw

theorem checkEqType.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => False := by
  intro _ h
  unfold checkEqType at h
  simp only [Environment.get] at h
  split at h <;> try contradiction
  rename_i ci hfind
  cases ci with
  | inductInfo info =>
    have hfind' : env.constants.find? ``Eq = some (.inductInfo info) := by
      rw [← (wf.tr (safety := .unsafe)).map_wf.find?'_eq_find?]
      exact hfind
    exact False.elim <|
      (wf.tr (safety := .unsafe)).no_inductInfo hfind'
  | _ =>
    simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]

theorem addQuot.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold Environment.addQuot
  split
  · exact .pure ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  · exact (checkEqType.WF wf).bind fun _ h => False.elim h

def _root_.Lean.Declaration.NonInductive : Declaration → Prop
  | .inductDecl .. => False
  | _ => True

/- Successful checked declaration addition preserves verified environments for
the non-inductive fragment.  Inductives require the separate `VInductDecl`
model, which is not yet implemented. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (hdecl : decl.NonInductive) :
    (addDecl env decl).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | axiomDecl v => exact addAxiom.WF wf v
  | defnDecl v => exact addDefinition.WF wf v
  | thmDecl v => exact addTheorem.WF wf v
  | opaqueDecl v => exact addOpaque.WF wf v
  | mutualDefnDecl vs => exact addMutual.WF wf vs
  | quotDecl => exact addQuot.WF wf
  | inductDecl _ _ _ _ => exact False.elim hdecl
