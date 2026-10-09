import Lean4Lean.Verify.Inductive.Recursor.Signature.RecursiveShapes
import Lean4Lean.Verify.Inductive.Recursor.Signature.Models
import Lean4Lean.Verify.Inductive.Recursor.Signature.Admissible
import Lean4Lean.Verify.Inductive.Recursor.Context.TelescopeUniqueness
import Lean4Lean.Theory.Inductive.HypothesisTyping

/-! The signature of the recursor construction (`RecursorConstruction.signature`), assembled
from the inverted recursor telescope.

The recursive shapes of the signature are read off the checked recursor type
(`recursorTelescope_hypothesisUnlift`) and returned to the declaration's universes by the
universe un-shift. The constructor fields are the unannotated field domains, marked recursive
exactly at the recursive positions of the minor pass's constructor traversal. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-! ### Universe un-shift without context well-formedness -/

/-- `TrExprS.substLevelParamsCore` without the (unused) context invariant. -/
theorem TrExprS.substLevelParamsCore_of_levels
    {env : VEnv} {ps Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    {ls : List VLevel} {F : Name → Level}
    (hls : ∀ level ∈ ls, level.WF Us.length)
    (hlevels : ∀ u u', VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (u.substParams' F false) = some (u'.inst ls))
    (H : TrExprS env ps Δ e e') :
    TrExprS env Us (Δ.instL ls) (Expr.instantiateLevelParamsCore' false F e)
      (e'.instL ls) := by
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (hlevels _ _ hlevel)
  | @const _ _ sourceLevels targetLevels info hlookup hlevel harity =>
    apply TrExprS.const hlookup ?_ (by simpa using harity)
    have Hmap := List.mapM_eq_some.mp hlevel
    apply List.mapM_eq_some.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.imp (fun u u' hu => hlevels u u' hu) Hmap
  | app hfn harg _ _ ihFn ihArg =>
    exact .app (VLCtx.instL_toCtx _ ▸ hfn.instL hls)
      (VLCtx.instL_toCtx _ ▸ harg.instL hls) ihFn ihArg
  | lam hdom _ _ ihDom ihBody =>
    exact .lam (VLCtx.instL_toCtx _ ▸ hdom.instL hls) ihDom ihBody
  | forallE hdom hbody _ _ ihDom ihBody =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (VLCtx.instL_toCtx _ ▸ hbody.instL hls) ihDom ihBody
  | letE hval _ _ _ ihTy ihVal ihBody =>
    exact .letE (VLCtx.instL_toCtx _ ▸ hval.instL hls) ihTy ihVal ihBody
  | lit hlit _ ih =>
    exact .lit hlit (Expr.instantiateLevelParamsCore_eq_self
      Literal.toConstructor_hasLevelParam ▸ ih)
  | mdata _ ih => exact .mdata ih
  | proj _ hproj ih =>
    exact .proj ih (VLCtx.instL_toCtx _ ▸ hproj.instL hls)

/-- `TrExprS.prependLevelParam` without the (unused) context invariant. -/
theorem TrExprS.prependLevelParam_of_fresh
    {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr} {fresh : Name}
    (hfresh : fresh ∉ Us) (H : TrExprS env Us Δ e e') :
    TrExprS env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e
      (e'.instL (VLevel.prependShift Us.length)) := by
  have hshift : ∀ level ∈ VLevel.prependShift Us.length, level.WF (fresh :: Us).length := by
    simpa using VLevel.prependShift_wf (n := Us.length)
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (VLevel.ofLevel_fresh_cons hfresh hlevel)
  | const hlookup hlevels harity =>
    exact .const hlookup (VLevel.mapM_ofLevel_fresh_cons hfresh hlevels) harity
  | app hfn harg _ _ ihFn ihArg =>
    exact .app (VLCtx.instL_toCtx _ ▸ hfn.instL hshift)
      (VLCtx.instL_toCtx _ ▸ harg.instL hshift) ihFn ihArg
  | lam hdom _ _ ihDom ihBody =>
    exact .lam (VLCtx.instL_toCtx _ ▸ hdom.instL hshift) ihDom ihBody
  | forallE hdom hbody _ _ ihDom ihBody =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ hdom.instL hshift)
      (VLCtx.instL_toCtx _ ▸ hbody.instL hshift) ihDom ihBody
  | letE hval _ _ _ ihTy ihVal ihBody =>
    exact .letE (VLCtx.instL_toCtx _ ▸ hval.instL hshift) ihTy ihVal ihBody
  | lit hlit _ ih => exact .lit hlit ih
  | mdata _ ih => exact .mdata ih
  | proj _ hproj ih =>
    exact .proj ih (VLCtx.instL_toCtx _ ▸ hproj.instL hshift)

/-- Levels returning recursor-universe syntax to the declaration's
universes: the fresh elimination universe is dropped to zero, or nothing
happens when there is none. -/
def recursorToDeclLevels (n : Nat) : Level → List VLevel
  | .param _ => recursorDropLevels n
  | _ => VLevel.params n

theorem recursorToDeclLevels_roundtrip
    (ha : AddInductive.AdmissibleElimLevel Us elim) :
    ((recursorDeclarationAbstractLevels Us ha).map
        (VLevel.inst (recursorToDeclLevels Us.length elim))).map
      (VLevel.inst (recursorDeclarationAbstractLevels Us ha)) =
      recursorDeclarationAbstractLevels Us ha := by
  cases elim with
  | zero =>
    rw [recursorDeclarationAbstractLevels_zero ha rfl]
    simp only [recursorToDeclLevels]
    rw [VLevel.inst_map_id VLevel.params_length, VLevel.inst_map_id VLevel.params_length]
  | param fresh =>
    rw [recursorDeclarationAbstractLevels_param ha rfl]
    simp only [recursorToDeclLevels]
    rw [recursorDropLevels_prependShift, VLevel.inst_map_id VLevel.prependShift_length]
  | succ | max | imax | mvar => simp [AddInductive.AdmissibleElimLevel] at ha

/-- Recursor-universe syntax that is the image of declaration-universe syntax. -/
def IsDeclUnivImage (L Q : List VLevel) (e : VExpr) : Prop :=
  (e.instL Q).instL L = e

theorem isDeclUnivImage_instL
    (ha : AddInductive.AdmissibleElimLevel Us elim) (e : VExpr) :
    IsDeclUnivImage (recursorDeclarationAbstractLevels Us ha) (recursorToDeclLevels Us.length elim)
      (e.instL (recursorDeclarationAbstractLevels Us ha)) := by
  unfold IsDeclUnivImage
  rw [VExpr.instL_instL (e := e), VExpr.instL_instL, recursorToDeclLevels_roundtrip]

theorem VLCtx.instL_abstractForallContext_nil (domains : List VExpr) (levels : List VLevel) :
    (abstractForallContext domains []).instL levels =
      abstractForallContext (domains.map (VExpr.instL levels)) [] := by
  rw [VLCtx.instL_abstractForallContext]
  rfl

theorem isDeclUnivImage_context {L Q : List VLevel} {domains : List VExpr}
    (h : ∀ d ∈ domains, IsDeclUnivImage L Q d) :
    ((abstractForallContext domains []).instL Q).instL L = abstractForallContext domains [] := by
  rw [VLCtx.instL_abstractForallContext_nil, VLCtx.instL_abstractForallContext_nil, List.map_map]
  congr 1
  conv => rhs; rw [← List.map_id domains]
  apply List.map_congr_left
  intro d hd
  exact h d hd

/-- Universe un-shift of a recursor-universe translation: a translation of
declaration-universe syntax, in a context which is the image of a
declaration-universe context, is itself such an image. -/
theorem TrExprS.isDeclUnivImage
    {env : VEnv} {Us : List Name} {elim : Level}
    (ha : AddInductive.AdmissibleElimLevel Us elim)
    {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (hΔ : (Δ.instL (recursorToDeclLevels Us.length elim)).instL
      (recursorDeclarationAbstractLevels Us ha) = Δ)
    (hsrc : e.levelParamsIn Us = true)
    (Htr : TrExprS env (AddInductive.getRecLevelParams elim Us) Δ e e') :
    IsDeclUnivImage (recursorDeclarationAbstractLevels Us ha) (recursorToDeclLevels Us.length elim) e' := by
  unfold IsDeclUnivImage
  cases elim with
  | zero =>
    rw [recursorDeclarationAbstractLevels_zero ha rfl] at hΔ ⊢
    simp only [recursorToDeclLevels, AddInductive.getRecLevelParams] at hΔ Htr ⊢
    have hid : (Δ.instL (VLevel.params Us.length)) = Δ := by
      have h := hΔ
      rw [VLCtx.instL_instL, VLevel.inst_map_id VLevel.params_length] at h
      exact h
    have H1 := TrExprS.substLevelParamsCore_of_levels (F := Level.param)
      (ls := VLevel.params Us.length) (fun level hlevel => VLevel.params_wf hlevel)
      (fun u u' hu => by
        simpa [Level.substParams_id, VLevel.inst_id (VLevel.WF.of_ofLevel hu)] using hu) Htr
    rw [Expr.instantiateLevelParamsCore_id, hid] at H1
    have heq := Htr.uniqueS H1
    rw [VExpr.instL_instL, VLevel.inst_map_id VLevel.params_length, ← heq]
  | param fresh =>
    have hfresh : fresh ∉ Us := by
      simpa [AddInductive.AdmissibleElimLevel] using ha
    rw [recursorDeclarationAbstractLevels_param ha rfl] at hΔ ⊢
    simp only [recursorToDeclLevels, AddInductive.getRecLevelParams] at hΔ Htr ⊢
    have H1 := TrExprS.substLevelParamsCore_of_levels (Us := Us) (F := recursorDropLevel fresh)
      (ls := recursorDropLevels Us.length) recursorDropLevels_wf
      (fun _ _ hu => ofLevel_dropFresh hu) Htr
    rw [levelParamsIn_fixed_dropFresh hsrc hfresh] at H1
    have H2 := TrExprS.prependLevelParam_of_fresh hfresh H1
    rw [hΔ] at H2
    exact (Htr.uniqueS H2).symm
  | succ | max | imax | mvar => simp [AddInductive.AdmissibleElimLevel] at ha

theorem TrExprS.isDeclUnivImage_forall₂
    {env : VEnv} {Us : List Name} {elim : Level}
    (ha : AddInductive.AdmissibleElimLevel Us elim) {Δ : VLCtx}
    (hΔ : (Δ.instL (recursorToDeclLevels Us.length elim)).instL
      (recursorDeclarationAbstractLevels Us ha) = Δ)
    {srcs : List Expr} {targets : List VExpr}
    (hsrc : ∀ e ∈ srcs, e.levelParamsIn Us = true)
    (Htr : List.Forall₂ (TrExprS env (AddInductive.getRecLevelParams elim Us) Δ) srcs targets) :
    ∀ d ∈ targets, IsDeclUnivImage (recursorDeclarationAbstractLevels Us ha)
      (recursorToDeclLevels Us.length elim) d := by
  induction Htr with
  | nil => intro d hd; simp at hd
  | @cons a b as bs hab _ ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact TrExprS.isDeclUnivImage ha hΔ (hsrc a (by simp)) hab
    · exact ih (fun e he => hsrc e (by simp [he])) d hd

/-- A telescope of recursor-universe translations of declaration-universe
syntax, over a base which is the image of declaration-universe domains, is
pointwise the image of declaration-universe domains. -/
theorem TrExprS.isDeclUnivImage_telescope
    {env : VEnv} {Us : List Name} {elim : Level}
    (ha : AddInductive.AdmissibleElimLevel Us elim)
    {base binders : List VExpr} {srcs : Nat → Expr}
    (hbase : ∀ d ∈ base, IsDeclUnivImage (recursorDeclarationAbstractLevels Us ha)
      (recursorToDeclLevels Us.length elim) d)
    (hsrc : ∀ i, i < binders.length → (srcs i).levelParamsIn Us = true)
    (Htr : ∀ i (hi : i < binders.length),
      TrExprS env (AddInductive.getRecLevelParams elim Us)
        (abstractForallContext (base ++ binders.take i) []) (srcs i) (binders[i]'hi)) :
    ∀ d ∈ binders, IsDeclUnivImage (recursorDeclarationAbstractLevels Us ha)
      (recursorToDeclLevels Us.length elim) d := by
  have key : ∀ n, n ≤ binders.length → ∀ d ∈ binders.take n,
      IsDeclUnivImage (recursorDeclarationAbstractLevels Us ha)
        (recursorToDeclLevels Us.length elim) d := by
    intro n
    induction n with
    | zero => intro _ d hd; simp at hd
    | succ n ih =>
      intro hn d hd
      have hn' : n < binders.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hn'] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact ih (by omega) d hd
      · have hd' : d = binders[n] := by simpa using hd
        subst hd'
        apply TrExprS.isDeclUnivImage ha _ (hsrc n hn') (Htr n hn')
        apply isDeclUnivImage_context
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hbase x hx
        · exact ih (by omega) x hx
  intro d hd
  exact key binders.length (Nat.le_refl _) d (by rw [List.take_of_length_le (Nat.le_refl _)]; exact hd)

/-- A recursor-universe translation of declaration-universe syntax, returned
to the declaration's universes: the target and the context are un-shifted by
`recursorToDeclLevels`. -/
theorem TrExprS.unshift
    {env : VEnv} {Us : List Name} {elim : Level}
    (ha : AddInductive.AdmissibleElimLevel Us elim)
    {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (hsrc : e.levelParamsIn Us = true)
    (Htr : TrExprS env (AddInductive.getRecLevelParams elim Us) Δ e e') :
    TrExprS env Us (Δ.instL (recursorToDeclLevels Us.length elim)) e
      (e'.instL (recursorToDeclLevels Us.length elim)) := by
  cases elim with
  | zero =>
    simp only [recursorToDeclLevels, AddInductive.getRecLevelParams] at Htr ⊢
    have H1 := TrExprS.substLevelParamsCore_of_levels (F := Level.param)
      (ls := VLevel.params Us.length) (fun level hlevel => VLevel.params_wf hlevel)
      (fun u u' hu => by
        simpa [Level.substParams_id, VLevel.inst_id (VLevel.WF.of_ofLevel hu)] using hu) Htr
    rwa [Expr.instantiateLevelParamsCore_id] at H1
  | param fresh =>
    have hfresh : fresh ∉ Us := by
      simpa [AddInductive.AdmissibleElimLevel] using ha
    simp only [recursorToDeclLevels, AddInductive.getRecLevelParams] at Htr ⊢
    have H1 := TrExprS.substLevelParamsCore_of_levels (Us := Us) (F := recursorDropLevel fresh)
      (ls := recursorDropLevels Us.length) recursorDropLevels_wf
      (fun _ _ hu => ofLevel_dropFresh hu) Htr
    rwa [levelParamsIn_fixed_dropFresh hsrc hfresh] at H1
  | succ | max | imax | mvar => simp [AddInductive.AdmissibleElimLevel] at ha

theorem TrExprS.unshift_forall₂
    {env : VEnv} {Us : List Name} {elim : Level}
    (ha : AddInductive.AdmissibleElimLevel Us elim) {Δ : VLCtx}
    {srcs : List Expr} {targets : List VExpr}
    (hsrc : ∀ e ∈ srcs, e.levelParamsIn Us = true)
    (Htr : List.Forall₂ (TrExprS env (AddInductive.getRecLevelParams elim Us) Δ) srcs targets) :
    List.Forall₂ (TrExprS env Us (Δ.instL (recursorToDeclLevels Us.length elim))) srcs
      (targets.map (VExpr.instL (recursorToDeclLevels Us.length elim))) := by
  induction Htr with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (TrExprS.unshift ha (hsrc _ (by simp)) hab)
      (ih fun e he => hsrc e (by simp [he]))

theorem recursorToDeclLevels_abstract
    (ha : AddInductive.AdmissibleElimLevel Us elim) :
    (recursorDeclarationAbstractLevels Us ha).map
        (VLevel.inst (recursorToDeclLevels Us.length elim)) = VLevel.params Us.length := by
  cases elim with
  | zero =>
    rw [recursorDeclarationAbstractLevels_zero ha rfl]
    simp only [recursorToDeclLevels]
    rw [VLevel.inst_map_id VLevel.params_length]
  | param fresh =>
    rw [recursorDeclarationAbstractLevels_param ha rfl]
    simp only [recursorToDeclLevels]
    rw [recursorDropLevels_prependShift]
  | succ | max | imax | mvar => simp [AddInductive.AdmissibleElimLevel] at ha

theorem List.map_unshift_abstract
    (ha : AddInductive.AdmissibleElimLevel Us elim) {xs : List VExpr}
    (h : ∀ x ∈ xs, x.LevelWF Us.length) :
    (xs.map (VExpr.instL (recursorDeclarationAbstractLevels Us ha))).map
      (VExpr.instL (recursorToDeclLevels Us.length elim)) = xs := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id xs]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply, id]
  rw [VExpr.instL_instL, recursorToDeclLevels_abstract ha, (h x hx).instL_id]

theorem OnCtx.levelWF_mem {env : VEnv} {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → ∀ x ∈ Γ, x.LevelWF U
  | [], _, _, hx => by simp at hx
  | _ :: _, H, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ((Classical.choose_spec H.2).levelWF (OnCtx.levelWF_of_isType H.1)).1
    · exact OnCtx.levelWF_mem H.1 x hx

/-! ### Marking recursive fields -/

theorem List.filterMap_congr_of_mem {α β : Type _} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (by simp)]
    rw [List.filterMap_congr_of_mem (fun x hx => h x (by simp [hx]))]

theorem List.filterMap_find?_zipIdx {β γ : Type _} :
    ∀ (types : List β) (k : Nat) (shapes : List (Nat × γ)),
      (shapes.map Prod.fst).Pairwise (· < ·) →
      (∀ p ∈ shapes, k ≤ p.1 ∧ p.1 < k + types.length) →
      (types.zipIdx k).filterMap
          (fun x => (shapes.find? (fun p => p.1 == x.2)).map (fun p => (x.2, p.2))) = shapes
  | [], k, shapes, _, hbound => by
    cases shapes with
    | nil => rfl
    | cons p ps => have := hbound p (by simp); simp at this; omega
  | t :: ts, k, [], _, _ => by
    simp only [List.find?_nil, Option.map_none]
    simp
  | t :: ts, k, p :: ps, hsorted, hbound => by
    have hsorted' : (ps.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
    have hgt : ∀ q ∈ ps, p.1 < q.1 := by
      intro q hq
      exact (List.pairwise_cons.mp hsorted).1 q.1 (List.mem_map_of_mem hq)
    have hp := hbound p (by simp)
    rw [List.zipIdx_cons, List.filterMap_cons]
    by_cases hpk : p.1 = k
    · have hfind : (p :: ps).find? (fun q => q.1 == k) = some p := by
        simp [hpk]
      rw [hfind]
      simp only [Option.map_some]
      have hrest : (ts.zipIdx (k + 1)).filterMap
          (fun x => ((p :: ps).find? (fun q => q.1 == x.2)).map (fun q => (x.2, q.2))) =
          (ts.zipIdx (k + 1)).filterMap
          (fun x => (ps.find? (fun q => q.1 == x.2)).map (fun q => (x.2, q.2))) := by
        apply List.filterMap_congr_of_mem
        intro x hx
        have hx' := List.mem_zipIdx (x := x.1) (i := x.2) (by simpa using hx)
        have hne : (p.1 == x.2) = false := by simp; omega
        simp [hne]
      rw [hrest, List.filterMap_find?_zipIdx ts (k + 1) ps hsorted' (by
        intro q hq
        have := hgt q hq
        have := hbound q (by simp [hq])
        simp at this ⊢
        omega)]
      rw [← hpk]
    · have hfind : (p :: ps).find? (fun q => q.1 == k) = none := by
        rw [List.find?_eq_none]
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simpa using hpk
        · have := hgt q hq
          simp
          omega
      rw [hfind, Option.map_none]
      exact List.filterMap_find?_zipIdx ts (k + 1) (p :: ps) hsorted (by
        intro q hq
        have hq' := hbound q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simp at hq' ⊢; omega
        · have := hgt q hq
          simp at hq' ⊢
          omega)

/-- The constructor fields with the given domains, marked recursive exactly
at the positions listed in `shapes`, with the listed shapes. -/
def InductiveSignature.markFields {n : Nat} (types : List VExpr)
    (shapes : List (Nat × InductiveSignature.Recursive n)) : List (InductiveSignature.Field n) :=
  types.zipIdx.map fun x =>
    match shapes.find? (fun p => p.1 == x.2) with
    | some p => .recursive x.1 p.2
    | none => .external x.1

@[simp] theorem InductiveSignature.markFields_length {n : Nat} (types : List VExpr)
    (shapes : List (Nat × InductiveSignature.Recursive n)) :
    (InductiveSignature.markFields types shapes).length = types.length := by
  simp [InductiveSignature.markFields]

theorem InductiveSignature.fieldTypes_markFields (s : InductiveSignature)
    (ctor : InductiveSignature.Constructor s.families.size) (types : List VExpr)
    (shapes : List (Nat × InductiveSignature.Recursive s.families.size))
    (h : ctor.fields = InductiveSignature.markFields types shapes) :
    s.fieldTypes ctor = types := by
  apply List.ext_getElem
  · simp [InductiveSignature.fieldTypes, h]
  · intro i h1 h2
    simp only [InductiveSignature.fieldTypes, h, InductiveSignature.markFields, List.getElem_map,
      List.getElem_zipIdx, Nat.zero_add]
    split <;> rfl

theorem InductiveSignature.recursiveFields_markFields {s : InductiveSignature}
    (ctor : InductiveSignature.Constructor s.families.size) (types : List VExpr)
    (shapes : List (Nat × InductiveSignature.Recursive s.families.size))
    (h : ctor.fields = InductiveSignature.markFields types shapes)
    (hsorted : (shapes.map Prod.fst).Pairwise (· < ·))
    (hbound : ∀ p ∈ shapes, p.1 < types.length) :
    InductiveSignature.Instance.recursiveFields (s := s) ctor = shapes := by
  unfold InductiveSignature.Instance.recursiveFields
  have hz : ∀ {α β : Type} (l : List α) (f : α × Nat → β),
      (l.zipIdx.map f).zipIdx = l.zipIdx.map (fun x => (f x, x.2)) := by
    intro α β l f
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [h, InductiveSignature.markFields, hz, List.filterMap_map]
  conv => rhs; rw [← List.filterMap_find?_zipIdx types 0 shapes hsorted
    (fun p hp => ⟨Nat.zero_le _, by simpa using hbound p hp⟩)]
  apply List.filterMap_congr_of_mem
  intro x _
  simp only [Function.comp_apply]
  cases List.find? (fun p => p.fst == x.snd) shapes <;> rfl

/-! ### Induction hypotheses at the declaration's universes -/

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The argument telescope and the target indices of every recursive call recorded in the rule
templates mention only the declaration's universe parameters (never the fresh elimination
universe). Each typed call template records this fact (`TypedCallTemplate.universes`); see
`RecursorConstruction.argumentUniverses`. -/
def RecursorConstruction.ArgumentUniverses (H : RecursorConstruction R) : Prop :=
  ∀ owner (_howner : owner < H.recInfos.size) localIndex
    (_hlocal : localIndex < H.origins.minorTypes[owner]!.size),
    let B := H.recInfos[owner]!.ruleTemplates[localIndex]!
    ∀ j < B.recursiveCalls.size,
      (B.recursiveCalls[j]!.lctx.mkForall B.recursiveCalls[j]!.args
          (.sort .zero)).levelParamsIn c.lparams = true ∧
        ∀ e ∈ B.recursiveCalls[j]!.targetIndices.toList, e.levelParamsIn c.lparams = true

theorem Expr.forallDomainList_levelParamsIn {Us : List Name} :
    ∀ (n : Nat) {e : Expr}, e.levelParamsIn Us = true →
      ∀ d ∈ Expr.forallDomainList n e, d.levelParamsIn Us = true
  | 0, _, _ => by simp [Expr.forallDomainList]
  | n + 1, e, h => by
    cases e with
    | forallE name dom body bi =>
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at h
      intro d hd
      simp only [Expr.forallDomainList, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact Expr.forallDomainList_levelParamsIn n h.2 d hd
    | _ => simp [Expr.forallDomainList]

/-- The argument domains of an induction hypothesis type (`InductionHypothesisType`) mention
only `Us` when its argument telescope and exposed indices do. -/
theorem InductionHypothesisType.argDomains_levelParamsIn
    {stats : AddInductive.InductiveStats} {recInfos : Array AddInductive.RecInfo}
    {root : AddInductive.Context} {field type : Expr}
    (O : InductionHypothesisType stats recInfos root field type) {Us : List Name}
    (htel : (O.current.lctx.mkForall O.args (.sort .zero)).levelParamsIn Us = true)
    (hidx : ∀ e ∈ (O.exposedType.getAppArgs[stats.params.size:] : Array Expr).toList,
      e.levelParamsIn Us = true) :
    ∀ d ∈ O.argDomains, d.levelParamsIn Us = true := by
  have hargTypes := O.arguments_bound.toFVarArrayIn.mkForall_levelParamsIn_types
    O.current_wf O.arguments_bound.nodup htel
  obtain ⟨fv, hfv, _⟩ := O.field_fvar
  have hmotiveApp : (Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive O.exposedType.getAppArgs[stats.params.size:])
      (mkAppN field O.args)).levelParamsIn Us = true := by
    obtain ⟨m, hm, _⟩ := O.motive_is_fvar
    subst hfv
    simp only [Expr.levelParamsIn, Bool.and_eq_true, Expr.mkAppN_eq_mkAppList]
    refine ⟨Expr.levelParamsIn_mkAppList (by rw [hm]; rfl) hidx,
      Expr.levelParamsIn_mkAppList rfl ?_⟩
    intro a ha
    rw [O.arguments_bound.expressions] at ha
    simp only [List.mem_map] at ha
    obtain ⟨y, _, rfl⟩ := ha
    rfl
  have htypeU : type.levelParamsIn Us = true := by
    rw [O.type_eq]
    exact O.arguments_bound.toFVarArrayIn.mkForall_levelParamsIn O.current_wf
      O.arguments_bound.nodup hargTypes hmotiveApp
  exact Expr.forallDomainList_levelParamsIn _ htypeU

/-- The generator's induction hypothesis (`InductiveSignature.Instance.hypothesis`)
as a function of the raw recursive-shape data. -/
def hypothesisForm (levels : List VLevel) (nf nfam prior j pos target : Nat)
    (binders indices : List VExpr) : VExpr :=
  let embed := fun (e : VExpr) localDepth =>
    InductiveSignature.Instance.underFields (e.instL levels) pos nf j (nfam + prior) localDepth
  let domains := binders.zipIdx.map fun (e, i) => embed e i
  let depth := domains.length
  let major := VExpr.mkApps (.bvar (nf - 1 - pos + j + depth)) (InductiveSignature.vars depth 0)
  let motive := VExpr.bvar (nf + j + depth + prior + (nfam - 1 - target))
  VExpr.wrapForalls domains <|
    VExpr.mkApps motive (indices.map (fun e => embed e depth) ++ [major])

theorem InductiveSignature.Instance.hypothesis_eq_form {s : InductiveSignature}
    (g : InductiveSignature.Instance s) (ctor : InductiveSignature.Constructor s.families.size)
    (prior j pos : Nat) (r : InductiveSignature.Recursive s.families.size) :
    g.hypothesis ctor prior j pos r =
      hypothesisForm g.levels ctor.fields.length s.families.size prior j pos r.target.val
        r.binders r.indices := rfl

/-- The declaration-universe sources of the `j`-th recursive shape
`(pos, target, binders, indices)` of a minor, stated against the recursive call `C` of that
induction hypothesis in the rule template (the call from which `RecRuleTemplate.build`
produces the installed rule's recursive value).

* the shape's target and arity are those of `C`, and `C`'s template is the
  closure of its own fields;
* `binders[i]` translates, at the declaration's universes, in
  `parameters ++ sourceFields.take pos ++ binders.take i`, the `i`-th literal
  domain of `C`'s argument telescope `C.lctx.mkForall C.args (.sort .zero)`
  (already closed over the earlier arguments, so its loose variables
  `0, …, i - 1` are those arguments), closed over the fields before `pos` at
  depth `i` and the parameters at depth `pos + i`;
* the indices translate `C.targetIndices` closed over the arguments
  (`abstractN (ExprArrayFVarIds C.args)`), then over the fields before `pos`
  and the parameters at depths `C.args.size` and `pos + C.args.size`, in
  `parameters ++ sourceFields.take pos ++ binders`. -/
def RecursorConstruction.RecursiveShapeDomains
    (H : RecursorConstruction R)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (j pos target : Nat) (binders indices : List VExpr) : Prop :=
  let S := H.origins.minorShapes mowner hmowner localIndex hlocal
  let C := H.recInfos[mowner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!
  let base := R.parameterScope.toCtx.reverse ++
    (H.declFieldDomains mowner hmowner localIndex hlocal).take pos
  let fvs := S.fields_bound.fvars.take pos
  j < (H.recInfos[mowner]!.ruleTemplates[localIndex]!).recursiveCalls.size ∧
  target = C.targetTypeIdx ∧
  binders.length = C.args.size ∧
  C.major = S.recursiveFields[j]! ∧
  C.template = C.lctx.mkLambda C.args
    ((mkAppN (.bvar C.args.size) C.targetIndices).app (mkAppN C.major C.args)) ∧
  (∀ i (hi : i < binders.length),
    TrExprS R.context.venv c.lparams (abstractForallContext (base ++ binders.take i) [])
      (((Expr.forallDomainList C.args.size (C.lctx.mkForall C.args (.sort .zero)))[i]!.abstractList
        fvs i).abstractList H.params.fvars (pos + i))
      (binders[i]'hi)) ∧
  List.Forall₂ (TrExprS R.context.venv c.lparams (abstractForallContext (base ++ binders) []))
    (C.targetIndices.toList.map fun e =>
      ((e.abstractN (ExprArrayFVarIds C.args)).abstractList fvs C.args.size).abstractList
        H.params.fvars (pos + C.args.size))
    indices

/-- `recursorTelescope_hypothesisUnlift`, returned to the declaration's
universes: the `j`-th induction hypothesis of a flat minor slot is the
generator's hypothesis for some declaration-universe binders and indices. -/
theorem RecursorConstruction.recursorTelescope_hypothesisHeader
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D₀ : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D₀.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let L := recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
    let nmot := (H.recInfos.map (·.motive)).size
    let fields := InductiveSignature.insertBinders
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map (VExpr.instL L)) (nmot + minorIdx)
    ∀ (hyps : List VExpr) (res : VExpr) (hhyps : hyps.length = S.hypotheses.size),
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D₀.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
      ∀ (j : Nat) (hj : j < S.hypotheses.size),
      ∃ (pos : Nat) (hpos : pos < S.fields_bound.fvars.length) (t : Nat)
        (binders indices : List VExpr),
        t < H.recInfos.size ∧
        S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) ∧
        hyps[j]'(by rw [hhyps]; exact hj) =
          hypothesisForm L S.fields.size nmot minorIdx j pos t binders indices ∧
        H.RecursiveShapeDomains mowner hmowner localIndex hlocal j pos t binders indices := by
  intro S L nmot fields hyps res hhyps hminorEq j hj
  obtain ⟨origins, root, sourceType, O, pos, hpos, binders, indices, horig, _hstats, _hmotives,
    hfield, hblen, howner', heq, Hbinders, Hindices, hcallArgs, hcallLctx, hcallIdx, hcallT,
    hcallMajor, hcallTemplate, hdomEq, hfvIds⟩ :=
    H.recursorTelescope_hypothesisUnlift howner T minorIdx D₀ mowner hmowner localIndex hlocal hD
      hyps res hhyps hminorEq j hj
  have hjCalls : j < (H.recInfos[mowner]!.ruleTemplates[localIndex]!).recursiveCalls.size := by
    obtain ⟨-, -, -, -, -, _, -, -, -, -, Hcalls⟩ :=
      H.templates.entry mowner hmowner localIndex hlocal
    rw [Hcalls.size_eq]
    exact hj
  obtain ⟨htelU, hidxU⟩ := HU mowner hmowner localIndex hlocal j hjCalls
  rw [hcallLctx, hcallArgs] at htelU
  rw [hcallIdx] at hidxU
  have hdomU := O.argDomains_levelParamsIn htelU hidxU
  let Q := recursorToDeclLevels c.lparams.length H.elimLevel
  have hbase : ∀ d ∈ H.parameterSuffix.parameterDecls.toCtx.reverse ++
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map (VExpr.instL L)).take pos,
      IsDeclUnivImage L Q d := by
    intro d hd
    rw [H.parameterDomains] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
      exact isDeclUnivImage_instL H.elimLevelAdmissible x
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hd)
      exact isDeclUnivImage_instL H.elimLevelAdmissible x
  have hsrcB : ∀ i, i < binders.length →
      ((O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
        H.params.fvars (pos + i)).levelParamsIn c.lparams = true := by
    intro i hi
    simp only [Expr.levelParamsIn_abstractList]
    have hi' : i < O.argDomains.length := by rw [O.argDomains_length]; omega
    rw [getElem!_pos O.argDomains i hi']
    exact hdomU _ (List.getElem_mem hi')
  have hsrcI : ∀ e ∈ ((O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList.map
      fun e => ((e.abstractN O.arguments_bound.fvars).abstractList
        (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
          (pos + O.args.size)), e.levelParamsIn c.lparams = true := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    simp only [Expr.levelParamsIn_abstractList, Expr.levelParamsIn_abstractN]
    exact hidxU e₀ he₀
  have hbinders : ∀ d ∈ binders, IsDeclUnivImage L Q d :=
    TrExprS.isDeclUnivImage_telescope H.elimLevelAdmissible hbase hsrcB Hbinders
  have hindices : ∀ d ∈ indices, IsDeclUnivImage L Q d := by
    refine TrExprS.isDeclUnivImage_forall₂ H.elimLevelAdmissible ?_ hsrcI Hindices
    apply isDeclUnivImage_context
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hbase x hx
    · exact hbinders x hx
  -- The declaration-universe sources, against the template's recursive call.
  have henvR : R.context.venv.WF := R.context.checking.tr.wf
  have hP : OnCtx R.parameterScope.toCtx (R.context.venv.IsType c.lparams.length) := by
    simpa [VLCtx.toCtx] using R.sourceAnonymousParameterWF.toCtx
  have hFctx := (VEnv.IsType.wrapForalls_inv henvR.ordered hP
    (H.sourceFields_replay mowner hmowner localIndex hlocal).2.1).1
  have hwf := OnCtx.levelWF_mem hFctx
  have hPwf : ∀ x ∈ R.parameterScope.toCtx.reverse, x.LevelWF c.lparams.length :=
    fun x hx => hwf x (List.mem_append_right _ (List.mem_reverse.mp hx))
  have hFwf : ∀ x ∈ (H.declFieldDomains mowner hmowner localIndex hlocal).take pos,
      x.LevelWF c.lparams.length :=
    fun x hx => hwf x (List.mem_append_left _ (List.mem_reverse.mpr (List.mem_of_mem_take hx)))
  have hctx : ∀ X : List VExpr,
      (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
        ((H.declFieldDomains mowner hmowner localIndex hlocal).map (VExpr.instL L)).take pos ++ X)
          []).instL Q =
      abstractForallContext (R.parameterScope.toCtx.reverse ++
        (H.declFieldDomains mowner hmowner localIndex hlocal).take pos ++ X.map (VExpr.instL Q)) [] := by
    intro X
    rw [VLCtx.instL_abstractForallContext_nil, H.parameterDomains, ← List.map_take,
      List.map_append, List.map_append, List.map_unshift_abstract H.elimLevelAdmissible hPwf,
      List.map_unshift_abstract H.elimLevelAdmissible hFwf]
  have Hsources : H.RecursiveShapeDomains mowner hmowner localIndex hlocal j pos O.ownerIdx
      (binders.map (VExpr.instL Q)) (indices.map (VExpr.instL Q)) := by
    dsimp only [RecursiveShapeDomains]
    refine ⟨hjCalls, hcallT.symm, by rw [List.length_map, hblen, hcallArgs], hcallMajor, ?_, ?_, ?_⟩
    · rw [hcallTemplate, hcallLctx, hcallArgs, hcallIdx, hcallMajor]
    · intro i hi
      have hi' : i < binders.length := by simpa using hi
      have h := TrExprS.unshift H.elimLevelAdmissible (hsrcB i hi') (Hbinders i hi')
      rw [hctx, List.map_take] at h
      simp only [List.getElem_map]
      rw [hcallArgs, hcallLctx, ← hdomEq]
      exact h
    · have h := TrExprS.unshift_forall₂ H.elimLevelAdmissible hsrcI Hindices
      rw [hctx] at h
      rw [hcallArgs, hcallIdx, hfvIds]
      exact h
  refine ⟨pos, hpos, O.ownerIdx, binders.map (VExpr.instL Q), indices.map (VExpr.instL Q),
    howner', hfield, ?_, Hsources⟩
  rw [heq]
  have hfixB : (binders.map (VExpr.instL Q)).map (VExpr.instL L) = binders := by
    conv => rhs; rw [← List.map_id binders]
    rw [List.map_map]
    exact List.map_congr_left (fun d hd => hbinders d hd)
  have hfixI : (indices.map (VExpr.instL Q)).map (VExpr.instL L) = indices := by
    conv => rhs; rw [← List.map_id indices]
    rw [List.map_map]
    exact List.map_congr_left (fun d hd => hindices d hd)
  have hdom : ((binders.map (VExpr.instL Q)).zipIdx.map fun x =>
      InductiveSignature.Instance.underFields (x.1.instL L) pos S.fields.size j
        (nmot + minorIdx) x.2) =
      binders.zipIdx.map fun x =>
        InductiveSignature.Instance.underFields x.1 pos S.fields.size j (nmot + minorIdx) x.2 := by
    rw [List.zipIdx_map, List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
    rw [show (x.1.instL Q).instL L = x.1 from hbinders x.1 (List.fst_mem_of_mem_zipIdx hx)]
  have hidx : (indices.map (VExpr.instL Q)).map (fun e =>
      InductiveSignature.Instance.underFields (e.instL L) pos S.fields.size j
        (nmot + minorIdx) binders.length) =
      indices.map fun e =>
        InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx)
          binders.length := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
    rw [show (x.instL Q).instL L = x from hindices x hx]
  simp only [hypothesisForm, hdom, List.length_map, List.length_zipIdx, hidx, VExpr.mkApps_append]
  rw [hblen]
  simp only [VExpr.mkApps, List.foldl_cons, List.foldl_nil]
  rw [show S.fields.size - 1 - pos + j + O.args.size =
    j + O.args.size + (S.fields.size - 1 - pos) by omega]

/-! ### Flat minor positions -/

theorem RecursorConstruction.minorPrefixLength_eq
    (H : RecursorConstruction R) (owner : Nat)
    (howner : owner ≤ H.recInfos.size) :
    ((H.recInfos.toList.take owner).flatMap (fun info => info.minors.toList)).length =
      recursorMinorOffset indTypes owner := by
  have hsizes : H.recInfos.size = indTypes.size := H.sourceFamilyCount
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
      have hrec : owner < H.recInfos.size := by omega
      have hind : owner < indTypes.size := by omega
      rw [recursorMinorOffset_step indTypes owner hind]
      simp [List.take_add_one, hrec, ih (by omega)]
      simpa [getElem!_pos H.recInfos owner hrec,
        getElem!_pos indTypes owner hind] using H.minorCounts owner hrec

/-- The flattened minor declaration at offset `recursorMinorOffset indTypes owner + localIndex`
has the recorded binder type of minor `localIndex` of family `owner`. -/
theorem RecursorConstruction.flatMinorDeclaration
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    ∃ D : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors))
        (recursorMinorOffset indTypes owner + localIndex),
      D.type = H.origins.minorTypes[owner]![localIndex]! := by
  let minorIdx := recursorMinorOffset indTypes owner + localIndex
  have hsizes : H.recInfos.size = indTypes.size := H.sourceFamilyCount
  have hflatSize : (H.recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size :=
    mkRecInfos.flatMinors_size hsizes H.minorCounts
  have hbound := H.sourceMinorOffsetBound owner howner localIndex hlocal
  have hminorArray : minorIdx < (H.recInfos.flatMap (·.minors)).size := by
    rw [hflatSize, ← ownedConstructors_length_eq_flattened_size]
    have h1 := H.ownedConstructors_length_offset
    rw [recursorMinorOffset_size] at h1
    have h2 : (ownedConstructors indTypes.toList).length =
        (indTypes.toList.flatMap (fun type => type.ctors)).length := by
      simp [ownedConstructors, List.length_flatMap]
    omega
  obtain ⟨D⟩ := H.bindings.flatMinors.declarationAt H.localWF minorIdx hminorArray
  obtain ⟨O⟩ := H.origins.flatMinorBinderType D
  let originIdx := recursorMinorOffset indTypes O.owner + O.localIndex
  have horiginOwner : O.owner < indTypes.size := by rw [← hsizes]; exact O.owner_lt
  have horiginRoom := recursorMinorOffset_room indTypes O.owner horiginOwner
  have horiginLocal : O.localIndex < indTypes[O.owner]!.ctors.length := by
    rw [← H.minorCounts O.owner O.owner_lt]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  have horiginIdx : originIdx < (H.recInfos.flatMap (·.minors)).size := by
    have hconcrete : originIdx < (indTypes.toList.flatMap (fun type => type.ctors)).length := by
      dsimp only [originIdx]
      omega
    rw [hflatSize, ← ownedConstructors_length_eq_flattened_size]
    simpa [ownedConstructors, List.length_flatMap] using hconcrete
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hminorNodup : H.bindings.flatMinors.fvars.Nodup := (List.nodup_append.mp houter).2.1
  have hflatNodup : (H.recInfos.flatMap (·.minors)).toList.Nodup := by
    rw [H.bindings.flatMinors.expressions]
    have mapFVarNodup : ∀ xs : List FVarId, xs.Nodup → (xs.map Expr.fvar).Nodup := by
      intro xs hxs
      induction hxs with
      | nil => exact .nil
      | @cons fv xs hnotmem _ ih => exact .cons (by simpa using hnotmem) ih
    simpa using mapFVarNodup _ hminorNodup
  have htoListFlatMap : (H.recInfos.flatMap (·.minors)).toList =
      H.recInfos.toList.flatMap (fun info => info.minors.toList) := Array.toList_flatMap
  have horiginIdxRows : originIdx <
      (H.recInfos.toList.flatMap (fun info => info.minors.toList)).length := by
    rw [← htoListFlatMap, Array.length_toList]
    exact horiginIdx
  have horiginIdxList : originIdx < (H.recInfos.flatMap (·.minors)).toList.length := by
    rw [Array.length_toList]; exact horiginIdx
  have hminorIdxList : minorIdx < (H.recInfos.flatMap (·.minors)).toList.length := by
    rw [Array.length_toList]; exact hminorArray
  have horiginLocalList : O.localIndex < H.recInfos[O.owner].minors.toList.length := by
    simpa using O.local_lt
  have HoriginGet := List.flatMap_getElem_prefix H.recInfos.toList
    (fun info => info.minors.toList) O.owner O.localIndex
    (by simpa using O.owner_lt)
    (by simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt)
    (by
      rw [H.minorPrefixLength_eq O.owner (Nat.le_of_lt O.owner_lt)]
      simpa [originIdx] using horiginIdxRows)
  have HoriginGet' : (H.recInfos.flatMap (·.minors)).toList[originIdx]'horiginIdxList =
      H.recInfos[O.owner].minors.toList[O.localIndex]'horiginLocalList := by
    simpa [Array.toList_flatMap, originIdx,
      H.minorPrefixLength_eq O.owner (Nat.le_of_lt O.owner_lt)] using HoriginGet
  have hvalue : (H.recInfos.flatMap (·.minors)).toList[originIdx]'horiginIdxList =
      (H.recInfos.flatMap (·.minors)).toList[minorIdx]'hminorIdxList := by
    calc
      _ = H.recInfos[O.owner].minors.toList[O.localIndex]'horiginLocalList := HoriginGet'
      _ = (H.recInfos.flatMap (·.minors)).toList[minorIdx]'hminorIdxList := by
        simpa only [Array.getElem_toList] using O.expression_eq
  have hposition : originIdx = minorIdx :=
    (List.getElem_inj (h₀ := horiginIdxList) (h₁ := hminorIdxList) hflatNodup).mp hvalue
  have hlocal' : localIndex < indTypes[owner]!.ctors.length := by
    rw [← H.minorTypes_size owner howner]; exact hlocal
  have horiginLocal' : O.localIndex < H.origins.minorTypes[O.owner]!.size := by
    rw [H.minorTypes_size O.owner O.owner_lt]; exact horiginLocal
  obtain ⟨hownerEq, hlocalEq⟩ := H.flatMinorIndex_unique O.owner_lt howner horiginLocal' hlocal
    hposition
  refine ⟨D, ?_⟩
  rw [O.originType_eq, hownerEq, hlocalEq]

/-! ### The minor group is shared by all recursors -/

theorem abstractForallContext_append_nil (A B : List VExpr) :
    abstractForallContext (A ++ B) [] = abstractForallContext B (abstractForallContext A []) := by
  simp [abstractForallContext, List.reverse_append, List.map_append]

/-- The signature with the source parameters and the construction's families, and no
constructors. -/
noncomputable def RecursorConstruction.familySignature
    (H : RecursorConstruction R) : InductiveSignature where
  uvars := decl.uvars
  params := R.parameterScope.toCtx.reverse
  families := H.families
  constructors := #[]

theorem RecursorConstruction.recursorTelescope_motives_eq
    (H : RecursorConstruction R) {owner₁ owner₂ : Nat}
    {target₁ target₂ : VExpr}
    (T₁ : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner₁)
      target₁ stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner₁]!.indices.size owner₁)
    (T₂ : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner₂)
      target₂ stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner₂]!.indices.size owner₂) :
    T₁.params = T₂.params ∧ T₁.motives = T₂.motives := by
  refine ⟨(H.recursorTelescope_params T₁).trans (H.recursorTelescope_params T₂).symm, ?_⟩
  have h₁ := H.recursorTelescope_motives T₁ (H.generatedInstance H.familySignature) rfl rfl rfl
    (H.generatedInstance_target _)
  have h₂ := H.recursorTelescope_motives T₂ (H.generatedInstance H.familySignature) rfl rfl rfl
    (H.generatedInstance_target _)
  exact h₁.trans h₂.symm

theorem RecursorConstruction.recursorTelescope_minors_eq
    (H : RecursorConstruction R) {owner₁ owner₂ : Nat}
    (howner₁ : owner₁ < H.recInfos.size) (howner₂ : owner₂ < H.recInfos.size)
    {target₁ target₂ : VExpr}
    (T₁ : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner₁)
      target₁ stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner₁]!.indices.size owner₁)
    (T₂ : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner₂)
      target₂ stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner₂]!.indices.size owner₂) :
    T₁.minors = T₂.minors := by
  obtain ⟨hp, hm⟩ := H.recursorTelescope_motives_eq T₁ T₂
  let n := (H.recInfos.flatMap (·.minors)).size
  let D : (i : Fin n) → FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) i.val :=
    fun i => Classical.choice (H.bindings.flatMinors.declarationAt H.localWF i.val i.isLt)
  let sources : List Expr := List.ofFn fun i : Fin n =>
    (D i).type.abstractList (H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take i.val)
  have hsrc : sources.length = n := by simp [sources]
  apply TrExprS.telescope_unique (abstractForallContext (T₁.params ++ T₁.motives) []) sources
    T₁.minors T₂.minors (by rw [T₁.minors_length, hsrc]) (by rw [T₂.minors_length, hsrc])
  · intro i hi
    have hi' : i < n := by rw [← hsrc]; exact hi
    have Ht := H.recursorTelescope_minor howner₁ T₁ i (D ⟨i, hi'⟩)
    rw [abstractForallContext_append_nil] at Ht
    simpa [sources] using Ht
  · intro i hi
    have hi' : i < n := by rw [← hsrc]; exact hi
    have Ht := H.recursorTelescope_minor howner₂ T₂ i (D ⟨i, hi'⟩)
    rw [abstractForallContext_append_nil, ← hp, ← hm] at Ht
    simpa [sources] using Ht

/-! ### Comparing induction hypothesis shapes -/

theorem VExpr.forallArity_app (f a : VExpr) : (VExpr.app f a).forallArity = 0 := rfl

theorem hypothesisForm_app (levels : List VLevel) (nf nfam prior j pos target : Nat)
    (binders indices : List VExpr) :
    hypothesisForm levels nf nfam prior j pos target binders indices =
      VExpr.wrapForalls
        (binders.zipIdx.map fun x =>
          InductiveSignature.Instance.underFields (x.1.instL levels) pos nf j (nfam + prior) x.2)
        (.app (VExpr.mkApps (.bvar (nf + j + binders.length + prior + (nfam - 1 - target)))
            (indices.map fun e => InductiveSignature.Instance.underFields (e.instL levels) pos nf j
              (nfam + prior) binders.length))
          (VExpr.mkApps (.bvar (nf - 1 - pos + j + binders.length))
            (InductiveSignature.vars binders.length 0))) := by
  simp only [hypothesisForm, List.length_map, List.length_zipIdx, VExpr.mkApps_append]
  rfl

/-- Two presentations of the same induction hypothesis have the same number of
higher-order binders and the same motive variable. -/
theorem hypothesisForm_compare {levels : List VLevel} {nf nfam prior j pos target : Nat}
    {binders indices A I : List VExpr} {a : Nat} {Y : VExpr}
    (h : VExpr.wrapForalls A (.app (VExpr.mkApps (.bvar a) I) Y) =
      hypothesisForm levels nf nfam prior j pos target binders indices) :
    A.length = binders.length ∧
      a = nf + j + binders.length + prior + (nfam - 1 - target) := by
  rw [hypothesisForm_app] at h
  have harity := congrArg VExpr.forallArity h
  simp only [VExpr.forallArity_wrapForalls, VExpr.forallArity_app, List.length_map,
    List.length_zipIdx, Nat.add_zero] at harity
  refine ⟨harity, ?_⟩
  obtain ⟨_, hbody⟩ := VExpr.wrapForalls_inj_of_length (by simpa using harity) h
  simp only [VExpr.app.injEq] at hbody
  have := congrArg VExpr.getAppFnArgs hbody.1
  rw [VExpr.getAppFnArgs_mkApps_bvar, VExpr.getAppFnArgs_mkApps_bvar] at this
  simp only [Prod.mk.injEq, VExpr.bvar.injEq] at this
  exact this.1

theorem exists_list_of_forall_lt {X : Type} {n : Nat} {P : Nat → X → Prop}
    (h : ∀ j, j < n → ∃ x, P j x) :
    ∃ l : List X, l.length = n ∧ ∀ j (hj : j < l.length), P j l[j] := by
  classical
  refine ⟨List.ofFn fun j : Fin n => Classical.choose (h j.val j.isLt), by simp, ?_⟩
  intro j hj
  simp only [List.getElem_ofFn]
  exact Classical.choose_spec (h j (by simpa using hj))

theorem InductionHypothesisType.ownerIdx_lt
    (O : InductionHypothesisType stats recInfos root field type) :
    O.ownerIdx < recInfos.size := by
  by_contra hge
  obtain ⟨fv, hfv, _⟩ := O.motive_is_fvar
  rw [getElem!_neg recInfos O.ownerIdx (by omega)] at hfv
  cases hfv

/-! ### Recursive shapes of the constructor of one minor -/

/-- The recursive shapes of the constructor of one minor: positions are the traversal's
recursive positions, each induction hypothesis of the checked recursor type is the generator's
hypothesis for its shape, and each shape's target and arity are those of the recorded
induction hypothesis type. -/
def RecursorConstruction.RecursiveShapesSpec
    (H : RecursorConstruction R)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (shapes : List (Nat × InductiveSignature.Recursive H.families.size)) : Prop :=
  let S := H.origins.minorShapes mowner hmowner localIndex hlocal
  let L := recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
  let nmot := (H.recInfos.map (·.motive)).size
  let minorIdx := recursorMinorOffset indTypes mowner + localIndex
  let fields := InductiveSignature.insertBinders
    ((H.declFieldDomains mowner hmowner localIndex hlocal).map (VExpr.instL L)) (nmot + minorIdx)
  (∀ traversal, S.traversal = some traversal →
    shapes.map Prod.fst = traversal.recursivePositions) ∧
  shapes.length = S.hypotheses.size ∧
  (∀ owner (_howner : owner < H.recInfos.size) (target : VExpr)
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (hm : minorIdx < T.minors.length) (hyps : List VExpr) (res : VExpr)
    (hhyps : hyps.length = shapes.length),
    T.minors[minorIdx]'hm = VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
    ∀ j (hj : j < shapes.length),
      hyps[j]'(by omega) = hypothesisForm L S.fields.size nmot minorIdx j shapes[j].1
        shapes[j].2.target.val shapes[j].2.binders shapes[j].2.indices) ∧
  (∀ origins, S.hypothesis_type_origins = some origins → ∀ j (hj : j < shapes.length),
    ∃ root sourceType,
      ∃ O : InductionHypothesisType origins.stats origins.recInfos
        root S.recursiveFields[j]! sourceType,
      ∃ _D : FVarDeclAt S.sourceFullContext S.hypotheses j,
        BindingContextLE origins.fieldRoot root ∧
        _D.type = (sourceType.consumeTypeAnnotationsVerified
          S.sourceFullContext.env.isTypeAnnotationWrapper) ∧
        shapes[j].2.target.val = O.ownerIdx ∧
        shapes[j].2.binders.length = O.args.size) ∧
  (∀ j (hj : j < shapes.length),
    ∃ hpos : shapes[j].1 < S.fields_bound.fvars.length,
      S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[shapes[j].1]'hpos) ∧
      H.RecursiveShapeDomains mowner hmowner localIndex hlocal j shapes[j].1
        shapes[j].2.target.val shapes[j].2.binders shapes[j].2.indices)

theorem RecursorConstruction.minorShapes_exist
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size) :
    ∃ shapes, H.RecursiveShapesSpec mowner hmowner localIndex hlocal shapes := by
  let S := H.origins.minorShapes mowner hmowner localIndex hlocal
  let L := recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
  let nmot := (H.recInfos.map (·.motive)).size
  let minorIdx := recursorMinorOffset indTypes mowner + localIndex
  have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, hHas, traversal, htrav, _, hfieldsT, hrecT, _, _, _, _, _, _⟩ :=
    H.minorSources.rows mowner hmowner hsourceOwner localIndex hlocal
  obtain ⟨origins, horig, _hstats, hmotives⟩ :=
    S.hypothesisTypeOrigins_exists stats H.recInfos hHas
  obtain ⟨D₀, hD⟩ := H.flatMinorDeclaration mowner hmowner localIndex hlocal
  obtain ⟨_, _, ⟨T⟩⟩ := H.recursorTelescope mowner hmowner
  obtain ⟨hyps, _, hhyps, hminorEq, _⟩ :=
    H.recursorTelescope_minorResidual hmowner T minorIdx D₀ mowner hmowner localIndex hlocal hD
  have hsizeRec : origins.recInfos.size = H.recInfos.size := by
    have h := congrArg Array.size hmotives
    simpa using h
  let P : Nat → (Nat × InductiveSignature.Recursive H.families.size) → Prop :=
    fun j x => ∀ (hj : j < hyps.length),
      ∃ hpos : x.1 < S.fields_bound.fvars.length,
        S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[x.1]'hpos) ∧
        hyps[j] = hypothesisForm L S.fields.size nmot minorIdx j x.1 x.2.target.val
          x.2.binders x.2.indices ∧
        H.RecursiveShapeDomains mowner hmowner localIndex hlocal j x.1 x.2.target.val
          x.2.binders x.2.indices ∧
        ∃ root sourceType,
          ∃ O : InductionHypothesisType origins.stats origins.recInfos
            root S.recursiveFields[j]! sourceType,
          ∃ _D : FVarDeclAt S.sourceFullContext S.hypotheses j,
            BindingContextLE origins.fieldRoot root ∧
            _D.type = (sourceType.consumeTypeAnnotationsVerified
          S.sourceFullContext.env.isTypeAnnotationWrapper) ∧
            x.2.target.val = O.ownerIdx ∧ x.2.binders.length = O.args.size
  have hP : ∀ j, j < S.hypotheses.size → ∃ x, P j x := by
    intro j hj
    obtain ⟨pos, hpos, t, binders, indices, ht, hfield, hform, hsources⟩ :=
      H.recursorTelescope_hypothesisHeader HU hmowner T minorIdx D₀ mowner hmowner localIndex
        hlocal hD hyps _ hhyps hminorEq j hj
    obtain ⟨root, sourceType, hLE, ⟨O⟩, D, hDtype⟩ := origins.entry j hj
    have hO : O.ownerIdx < H.recInfos.size := hsizeRec ▸ O.ownerIdx_lt
    obtain ⟨A, I, hA, hEq, _⟩ := H.recursorTelescope_hypothesisShape hmowner T minorIdx D₀ mowner
      hmowner localIndex hlocal hD hyps _ hhyps hminorEq j origins hmotives O D hDtype hO
      pos hpos hfield
    obtain ⟨hlen, hidx⟩ := hypothesisForm_compare (hEq.symm.trans hform)
    have hnmot : nmot = H.recInfos.size := by simp [nmot]
    have htO : t = O.ownerIdx := by omega
    have ht' : t < H.families.size := by rw [H.families_size]; exact ht
    refine ⟨(pos, ⟨binders, ⟨t, ht'⟩, indices⟩), fun _ => ⟨hpos, hfield, hform, hsources, root,
      sourceType, O, D, hLE, hDtype, htO, hlen.symm.trans hA⟩⟩
  obtain ⟨shapes, hlen, hshapes⟩ := exists_list_of_forall_lt hP
  have hlenH : shapes.length = hyps.length := by rw [hlen, hhyps]
  refine ⟨shapes, ?_, hlen, ?_, ?_, ?_⟩
  · intro traversal' htrav'
    have htt : traversal' = traversal := Option.some.inj (htrav'.symm.trans htrav)
    subst htt
    have hposLen : traversal'.recursivePositions.length = shapes.length := by
      rw [traversal'.recursivePositions_length, hrecT, ← S.hypotheses_size, hlen]
    apply List.ext_getElem (by simp [hposLen])
    intro j h1 h2
    have hj : j < shapes.length := by simpa using h1
    obtain ⟨hpos, hfield, _⟩ := hshapes j hj (by omega)
    have hjR : j < traversal'.recursiveFields.size := by
      rw [traversal'.recursivePositions_length.symm]; omega
    obtain ⟨hplt, hsel⟩ := traversal'.decisions.selected_at j hjR
    rw [hfieldsT, hrecT] at hsel
    rw [hfieldsT] at hplt
    have hexpr := S.fields_bound.expressions
    have hplt' : traversal'.recursivePositions[j]! < S.fields_bound.fvars.length := by
      rw [← S.fields_bound.length_fvars] at hplt
      exact hplt
    have hget : S.fields[traversal'.recursivePositions[j]!]! =
        .fvar (S.fields_bound.fvars[traversal'.recursivePositions[j]!]'hplt') := by
      have key : ∀ (xs : Array Expr) (p : Nat) (hp : p < S.fields_bound.fvars.length),
          xs = (S.fields_bound.fvars.map Expr.fvar).toArray →
          xs[p]! = .fvar (S.fields_bound.fvars[p]'hp) := by
        intro xs p hp hxs; subst hxs; simp [hp]
      exact key _ _ hplt' hexpr
    rw [hfield, hget] at hsel
    have hfv := Expr.fvar.inj hsel
    have hidx := (List.getElem_inj (h₀ := hpos) (h₁ := hplt') S.fields_nodup).mp hfv
    simp only [List.getElem_map]
    rw [hidx, getElem!_pos traversal'.recursivePositions j (by omega)]
  · intro owner' howner' target' T' hm hyps' res' hhyps' heq' j hj
    have hTT := H.recursorTelescope_minors_eq howner' hmowner T' T
    have hm' : minorIdx < T.minors.length := by rw [← hTT]; exact hm
    have h1 : T.minors[minorIdx]'hm' = _ := (List.getElem_of_eq hTT hm).symm.trans heq'
    rw [hminorEq, ← VExpr.wrapForalls_append, ← VExpr.wrapForalls_append] at h1
    have hyy := (VExpr.wrapForalls_inj_of_length
      (by simp [InductiveSignature.insertBinders, hhyps', hlenH]) h1).1
    have hyy' : hyps = hyps' := List.append_cancel_left hyy
    subst hyy'
    obtain ⟨_, _, hform, _⟩ := hshapes j hj (by omega)
    exact hform
  · intro origins' horig' j hj
    have hoo : origins' = origins := Option.some.inj (horig'.symm.trans horig)
    subst hoo
    obtain ⟨_, _, _, _, hrest⟩ := hshapes j hj (by omega)
    exact hrest
  · intro j hj
    obtain ⟨hpos, hfield, _, hsources, _⟩ := hshapes j hj (by omega)
    exact ⟨hpos, hfield, hsources⟩

/-! ### The signature of the construction -/

/-- The recursive shapes of the constructor of one minor, chosen to satisfy
`RecursiveShapesSpec`. -/
noncomputable def RecursorConstruction.recursiveShapes
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    List (Nat × InductiveSignature.Recursive H.families.size) :=
  Classical.choose (H.minorShapes_exist HU owner howner localIndex hlocal)

theorem RecursorConstruction.recursiveShapes_spec
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    H.RecursiveShapesSpec owner howner localIndex hlocal
      (H.recursiveShapes HU owner howner localIndex hlocal) :=
  Classical.choose_spec (H.minorShapes_exist HU owner howner localIndex hlocal)

/-- The signature constructor of minor `localIndex` of family `owner`: the minor's constructor
name, its field domains marked recursive by `recursiveShapes`, and its result indices. -/
noncomputable def RecursorConstruction.constructorAt
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    InductiveSignature.Constructor H.families.size where
  name := (H.origins.minorShapes owner howner localIndex hlocal).constructor.name
  owner := ⟨owner, by rw [H.families_size]; exact howner⟩
  fields := InductiveSignature.markFields (H.declFieldDomains owner howner localIndex hlocal)
    (H.recursiveShapes HU owner howner localIndex hlocal)
  indices := H.declConstructorIndices owner howner localIndex hlocal

/-- The signature constructor at a flattened constructor position. -/
noncomputable def RecursorConstruction.constructor
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (k : Fin decl.ownedConstructors.length) :
    InductiveSignature.Constructor H.families.size :=
  let h := H.flatMinorIndex k.val k.isLt
  let howner := Classical.choose_spec h
  let hlocal := Classical.choose_spec (Classical.choose_spec howner)
  H.constructorAt HU (Classical.choose h) (Classical.choose howner)
    (Classical.choose (Classical.choose_spec howner)) (Classical.choose hlocal)

theorem RecursorConstruction.constructorAt_congr
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    {owner owner' : Nat} (howner : owner < H.recInfos.size) (howner' : owner' < H.recInfos.size)
    {localIndex localIndex' : Nat} (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hlocal' : localIndex' < H.origins.minorTypes[owner']!.size)
    (h1 : owner = owner') (h2 : localIndex = localIndex') :
    H.constructorAt HU owner howner localIndex hlocal =
      H.constructorAt HU owner' howner' localIndex' hlocal' := by
  subst h1 h2
  rfl

theorem RecursorConstruction.constructor_eq
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hk : recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length) :
    H.constructor HU ⟨recursorMinorOffset indTypes owner + localIndex, hk⟩ =
      H.constructorAt HU owner howner localIndex hlocal := by
  unfold constructor
  dsimp only
  have h := H.flatMinorIndex (recursorMinorOffset indTypes owner + localIndex) hk
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec h)))
  obtain ⟨h1, h2⟩ := H.flatMinorIndex_unique (Classical.choose (Classical.choose_spec h)) howner
    (Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))))
    hlocal hspec.symm
  exact H.constructorAt_congr HU _ _ _ _ h1 h2

/-- The signature of the recursor construction: source universes and parameter scope, the
construction's families, and one constructor per minor with its unannotated field domains,
marked recursive at the traversal's recursive positions. -/
@[reducible] noncomputable def RecursorConstruction.signature
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses) : InductiveSignature where
  uvars := decl.uvars
  params := R.parameterScope.toCtx.reverse
  families := H.families
  constructors := Array.ofFn (H.constructor HU)
  isUnsafe := decl.isUnsafe

theorem RecursorConstruction.signature_constructor
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hk : recursorMinorOffset indTypes owner + localIndex < (H.signature HU).constructors.size) :
    (H.signature HU).constructors[recursorMinorOffset indTypes owner + localIndex] =
      H.constructorAt HU owner howner localIndex hlocal := by
  simp only [signature, Array.getElem_ofFn]
  exact H.constructor_eq HU owner howner localIndex hlocal _

theorem RecursorConstruction.constructorAt_fieldTypes
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (H.signature HU).fieldTypes (H.constructorAt HU owner howner localIndex hlocal) =
      H.declFieldDomains owner howner localIndex hlocal :=
  InductiveSignature.fieldTypes_markFields _ _ _ _ rfl

theorem RecursorConstruction.constructorAt_recursiveFields
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    InductiveSignature.Instance.recursiveFields (s := H.signature HU)
        (H.constructorAt HU owner howner localIndex hlocal) =
      H.recursiveShapes HU owner howner localIndex hlocal := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, traversal, htrav, _, hfieldsT, _, _, _, _, _, _, _⟩ :=
    H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hspec := H.recursiveShapes_spec HU owner howner localIndex hlocal
  have hpos := hspec.1 traversal htrav
  apply InductiveSignature.recursiveFields_markFields _ _ _ rfl
  · have := traversal.recursivePositions_ordered
    rw [← hpos] at this
    exact this
  · intro p hp
    have hmem : p.1 ∈ traversal.recursivePositions := by
      rw [← hpos]; exact List.mem_map_of_mem hp
    have := traversal.recursivePositions_lt p.1 hmem
    rw [hfieldsT] at this
    rw [H.sourceFields_length]
    exact this

/-- The fields of a minor's constructor marked recursive are those whose rule-template entry
receives a recursive call (`RecRuleTemplate.recursiveMask`). -/
theorem RecursorConstruction.constructorAt_recursiveMask
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (H.constructorAt HU owner howner localIndex hlocal).fields.map
        InductiveSignature.Field.isRecursive =
      (H.recInfos[owner]!.ruleTemplates[localIndex]!).recursiveMask := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  have hspec := H.recursiveShapes_spec HU owner howner localIndex hlocal
  obtain ⟨_, hfieldsB, _, _, _, _, _, _, _, _, hcalls⟩ :=
    H.templates.entry owner howner localIndex hlocal
  have hsizeCalls : (H.recInfos[owner]!.ruleTemplates[localIndex]!).recursiveCalls.size = (H.recursiveShapes HU owner howner localIndex hlocal).length := by
    rw [hspec.2.1]
    exact hcalls.size_eq
  have hlenFields : (H.declFieldDomains owner howner localIndex hlocal).length = S.fields.size :=
    H.sourceFields_length owner howner localIndex hlocal
  apply List.ext_getElem
  · simp [RecursorConstruction.constructorAt, AddInductive.RecRuleTemplate.recursiveMask,
      hfieldsB, hlenFields, S]
  intro i h1 h2
  simp only [List.getElem_map, RecursorConstruction.constructorAt,
    InductiveSignature.markFields, List.getElem_zipIdx, Nat.zero_add,
    AddInductive.RecRuleTemplate.recursiveMask, Array.getElem_toList]
  have hexpr := S.fields_bound.expressions
  have hnodup := S.fields_nodup
  have hiF : i < S.fields_bound.fvars.length := by
    have : i < S.fields.size := by
      simpa [AddInductive.RecRuleTemplate.recursiveMask, hfieldsB] using h2
    simpa [hexpr] using this
  have hBi : (H.recInfos[owner]!.ruleTemplates[localIndex]!).fields[i]'(by
      simpa [AddInductive.RecRuleTemplate.recursiveMask] using h2) =
      .fvar (S.fields_bound.fvars[i]'hiF) := by
    have : (H.recInfos[owner]!.ruleTemplates[localIndex]!).fields = S.fields := hfieldsB
    simp only [this, hexpr]
    simp
  have hmajor : ∀ j (hj : j < (H.recursiveShapes HU owner howner localIndex hlocal).length),
      ∃ hpos : (H.recursiveShapes HU owner howner localIndex hlocal)[j].1 <
          S.fields_bound.fvars.length,
        ((H.recInfos[owner]!.ruleTemplates[localIndex]!).recursiveCalls[j]'(by omega)).major =
          .fvar (S.fields_bound.fvars[(H.recursiveShapes HU owner howner localIndex hlocal)[j].1]'hpos) := by
    intro j hj
    obtain ⟨hpos, hrec, hdom⟩ := hspec.2.2.2.2 j hj
    refine ⟨hpos, ?_⟩
    have hmaj := hdom.2.2.2.1
    have hbang : (H.recInfos[owner]!.ruleTemplates[localIndex]!).recursiveCalls[j]! = (H.recInfos[owner]!.ruleTemplates[localIndex]!).recursiveCalls[j]'(by omega) := by
      simp [getElem!_pos (H.recInfos[owner]!.ruleTemplates[localIndex]!).recursiveCalls j (by omega)]
    rw [← hbang]
    exact hmaj.trans hrec
  have hBi' : (H.recInfos[owner]!.ruleTemplates[localIndex]!).fields[i]'(by
      simpa [AddInductive.RecRuleTemplate.recursiveMask] using h2) =
      .fvar (S.fields_bound.fvars[i]'hiF) := hBi
  rw [hBi']
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hfind
    cases hf : List.find? (fun p => p.fst == i) (H.recursiveShapes HU owner howner localIndex hlocal) with
    | none => rw [hf] at hfind; simp [InductiveSignature.Field.isRecursive] at hfind
    | some p =>
      have hmem := List.mem_of_find?_eq_some hf
      have hpi : p.1 = i := by simpa using List.find?_some hf
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
      obtain ⟨hpos, hmaj⟩ := hmajor j hj
      rw [Array.any_eq_true]
      refine ⟨j, by omega, ?_⟩
      rw [hmaj]
      simp [hpi]
  · intro hany
    rw [Array.any_eq_true] at hany
    obtain ⟨j, hj, hbeq⟩ := hany
    have hj' : j < (H.recursiveShapes HU owner howner localIndex hlocal).length := by omega
    obtain ⟨hpos, hmaj⟩ := hmajor j hj'
    rw [hmaj] at hbeq
    have hfv : S.fields_bound.fvars[(H.recursiveShapes HU owner howner localIndex hlocal)[j].1]'hpos =
        S.fields_bound.fvars[i]'hiF := by
      have := Expr.eqv_fvar_eq hbeq
      simpa using this.symm
    have hidx := (List.getElem_inj (h₀ := hpos) (h₁ := hiF) hnodup).mp hfv
    have hsome : (List.find? (fun p => p.fst == i)
        (H.recursiveShapes HU owner howner localIndex hlocal)).isSome := by
      rw [List.find?_isSome]
      exact ⟨_, List.getElem_mem hj', by simp [hidx]⟩
    cases hf : List.find? (fun p => p.fst == i) (H.recursiveShapes HU owner howner localIndex hlocal) with
    | none => rw [hf] at hsome; cases hsome
    | some p => simp [InductiveSignature.Field.isRecursive]

theorem RecursorConstruction.signatureSpec
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses) :
    H.SignatureSpec (H.signature HU) where
  uvars := rfl
  params := rfl
  families := rfl
  safety := rfl
  size := Array.size_ofFn
  constructor owner howner localIndex hlocal := by
    have hk : recursorMinorOffset indTypes owner + localIndex <
        (H.signature HU).constructors.size := by
      simp only [signature, Array.size_ofFn]
      exact H.sourceMinorOffsetBound owner howner localIndex hlocal
    refine ⟨hk, ?_⟩
    rw [H.signature_constructor HU owner howner localIndex hlocal hk]
    exact ⟨rfl, rfl, H.constructorAt_fieldTypes HU owner howner localIndex hlocal, rfl⟩
  classified hsafe owner howner localIndex hlocal hk := by
    rw [H.signature_constructor HU owner howner localIndex hlocal hk,
      H.constructorAt_recursiveMask HU owner howner localIndex hlocal]
    have hunsafe : isUnsafe = false := by
      cases h : isUnsafe
      · rfl
      · exact absurd (R.core.isUnsafe.trans h) hsafe
    have hchk := congrArg (fun l : List (List (List Bool)) => l[owner]![localIndex]!)
      (H.recursiveFieldsChecked hunsafe)
    have hrows := H.templates.rows_size owner howner
    have hlocal' : localIndex < (H.recInfos[owner]!).ruleTemplates.size := by
      rw [hrows]; exact hlocal
    have hbang : H.recInfos[owner]! = H.recInfos[owner] := getElem!_pos H.recInfos owner howner
    rw [hbang] at hlocal' ⊢
    rw [← hchk, getElem!_pos (H.recInfos.toList.map _) owner (by simpa using howner),
      List.getElem_map, getElem!_pos (List.map _ _) localIndex (by simpa using hlocal'),
      List.getElem_map, getElem!_pos _ localIndex hlocal']
    simp

/-! ### The minor group of the checked recursor type -/

theorem RecursorConstruction.recursorTelescope_minor_eq
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    {owner : Nat} (howner : owner < H.recInfos.size) {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hm : recursorMinorOffset indTypes mowner + localIndex < T.minors.length) :
    T.minors[recursorMinorOffset indTypes mowner + localIndex]'hm =
      (H.generatedInstance (H.signature HU)).minor
        (H.constructorAt HU mowner hmowner localIndex hlocal)
        (recursorMinorOffset indTypes mowner + localIndex) := by
  let minorIdx := recursorMinorOffset indTypes mowner + localIndex
  obtain ⟨D₀, hD⟩ := H.flatMinorDeclaration mowner hmowner localIndex hlocal
  obtain ⟨hyps, idx, hhyps, hminorEq, Hidx⟩ :=
    H.recursorTelescope_minorResidual howner T minorIdx D₀ mowner hmowner localIndex hlocal hD
  have hidx := H.recursorTelescope_minorIndices T minorIdx D₀.inBounds mowner hmowner localIndex
    hlocal hyps idx hhyps Hidx
  have hspec := H.recursiveShapes_spec HU mowner hmowner localIndex hlocal
  have hlenShapes : (H.recursiveShapes HU mowner hmowner localIndex hlocal).length =
      (H.origins.minorShapes mowner hmowner localIndex hlocal).hypotheses.size := hspec.2.1
  have hforms := hspec.2.2.1 owner howner target T hm hyps _
    (hhyps.trans hlenShapes.symm) hminorEq
  have hrec := H.constructorAt_recursiveFields HU mowner hmowner localIndex hlocal
  have hft := H.constructorAt_fieldTypes HU mowner hmowner localIndex hlocal
  have hnf : (H.constructorAt HU mowner hmowner localIndex hlocal).fields.length =
      (H.origins.minorShapes mowner hmowner localIndex hlocal).fields.size := by
    simp [constructorAt, H.sourceFields_length]
  have hfam : (H.signature HU).families.size = (H.recInfos.map (·.motive)).size := by
    simp [H.families_size]
  have hihs : ((InductiveSignature.Instance.recursiveFields (s := H.signature HU)
      (H.constructorAt HU mowner hmowner localIndex hlocal)).zipIdx.map fun x =>
        (H.generatedInstance (H.signature HU)).hypothesis
          (H.constructorAt HU mowner hmowner localIndex hlocal) minorIdx x.2 x.1.1 x.1.2) =
      hyps := by
    rw [hrec]
    apply List.ext_getElem (by simp [hlenShapes, hhyps])
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    refine (InductiveSignature.Instance.hypothesis_eq_form _ _ _ _ _ _).trans ?_
    rw [hforms j (by simpa using h1)]
    simp only [hnf, hfam]
    rfl
  have hihsLen : ((InductiveSignature.Instance.recursiveFields (s := H.signature HU)
      (H.constructorAt HU mowner hmowner localIndex hlocal)).zipIdx.map fun x =>
        (H.generatedInstance (H.signature HU)).hypothesis
          (H.constructorAt HU mowner hmowner localIndex hlocal) minorIdx x.2 x.1.1 x.1.2).length =
      (H.origins.minorShapes mowner hmowner localIndex hlocal).hypotheses.size := by
    rw [hihs, hhyps]
  rw [hminorEq]
  unfold InductiveSignature.Instance.minor
  rw [hihs, hft, hidx]
  have hlev : (H.generatedInstance (H.signature HU)).levels =
      recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible := rfl
  have hind : (H.constructorAt HU mowner hmowner localIndex hlocal).indices =
      H.declConstructorIndices mowner hmowner localIndex hlocal := rfl
  have hown : ((H.constructorAt HU mowner hmowner localIndex hlocal).owner : Nat) =
      mowner := rfl
  have hname : (H.constructorAt HU mowner hmowner localIndex hlocal).name =
      (H.origins.minorShapes mowner hmowner localIndex hlocal).constructor.name := rfl
  have hpl : (H.signature HU).params.length = stats.params.size := by
    simp [H.sourceParameterCount]
  simp only [hlev, hnf, hhyps, hind, hown, hname, hpl, VExpr.wrapForalls_append, VExpr.mkApps_append,
    InductiveSignature.Instance.constructorApp, H.families_size, Array.size_map]
  rw [show ∀ (f a : VExpr), VExpr.mkApps f [a] = .app f a from fun _ _ => rfl]
  have hidxs : (H.declConstructorIndices mowner hmowner localIndex hlocal).map (fun e =>
      ((e.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)).liftN
        (H.origins.minorShapes mowner hmowner localIndex hlocal).hypotheses.size).liftN (H.recInfos.size + minorIdx) ((H.origins.minorShapes mowner hmowner localIndex hlocal).fields.size + (H.origins.minorShapes mowner hmowner localIndex hlocal).hypotheses.size)) =
      (H.declConstructorIndices mowner hmowner localIndex hlocal).map (fun e =>
      ((e.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)).liftN
        (H.recInfos.size + minorIdx) (H.origins.minorShapes mowner hmowner localIndex hlocal).fields.size).liftN (H.origins.minorShapes mowner hmowner localIndex hlocal).hypotheses.size) :=
    List.map_congr_left (fun e _ => (VExpr.liftN_liftN_comm _ _ _ _ _ (Nat.zero_le _)).symm)
  rw [hidxs]

theorem RecursorConstruction.flatMinors_size_eq
    (H : RecursorConstruction R) :
    (H.recInfos.flatMap (·.minors)).size = decl.ownedConstructors.length := by
  have hflatSize : (H.recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size :=
    mkRecInfos.flatMinors_size H.sourceFamilyCount H.minorCounts
  rw [hflatSize, ← ownedConstructors_length_eq_flattened_size]
  have h1 := H.ownedConstructors_length_offset
  rw [recursorMinorOffset_size] at h1
  have h2 : (ownedConstructors indTypes.toList).length =
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
    simp [ownedConstructors, List.length_flatMap]
  omega

/-- The minor group of every checked recursor type is the generator's minor list for the
construction's signature. -/
theorem RecursorConstruction.recursorTelescope_minors_unannotated
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    {owner : Nat} (howner : owner < H.recInfos.size) {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner) :
    T.minors = (H.generatedInstance (H.signature HU)).minors := by
  have hlen : T.minors.length = (H.generatedInstance (H.signature HU)).minors.length := by
    rw [T.minors_length, InductiveSignature.Instance.length_minors, H.flatMinors_size_eq]
    simp [signature]
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi : i < decl.ownedConstructors.length := by
    rw [T.minors_length, H.flatMinors_size_eq] at h1; exact h1
  obtain ⟨mowner, hmowner, localIndex, hlocal, rfl⟩ := H.flatMinorIndex i hi
  rw [H.recursorTelescope_minor_eq HU howner T mowner hmowner localIndex hlocal h1,
    InductiveSignature.Instance.getElem_minors]
  have hk : recursorMinorOffset indTypes mowner + localIndex <
      (H.signature HU).constructors.size := by
    simpa [signature] using hi
  rw [H.signature_constructor HU mowner hmowner localIndex hlocal hk]

/-! ### The parameter, motive and minor prefix of the recursor type -/

theorem LocalContext.forallDomainsOnly_foldN_add
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (k : Nat) (body : Expr) :
    Expr.forallDomainsOnly (fvars.length + k)
      (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) body) =
      fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) (Expr.forallDomainsOnly k body) := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl fv (by simp)
    rw [List.length_cons, Nat.add_right_comm]
    simp only [List.foldr_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.forallDomainsOnly, Expr.forallDomainsOnly_abstractN]
    simpa only [LocalContext.mkBindingList1N, Bool.false_eq_true, ↓reduceIte] using
      congrArg (fun e => Expr.forallE name (type.abstractN []) (e.abstractN [fv]) bi)
        (ih (fun other hother => hdecl other (by simp [hother])))

theorem FVarArrayIn.forallDomainsOnly_add
    (H : FVarArrayIn c xs) (Hc : BindingContextWF c)
    (hnodup : H.fvars.Nodup) (k : Nat) (body : Expr) :
    Expr.forallDomainsOnly (xs.size + k) (c.lctx.mkForall xs body) =
      c.lctx.mkForall xs (Expr.forallDomainsOnly k body) := by
  have hdecl : ∀ fv ∈ H.fvars, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    exact Hc.findCDecl fv (H.members fv hfv)
  have hfind : ∀ fv ∈ H.fvars, ∃ decl, c.lctx.find? fv = some decl := by
    intro fv hfv
    obtain ⟨index, name, type, bi, kind, h⟩ := hdecl fv hfv
    exact ⟨_, h⟩
  conv => lhs; rw [H.expressions]
  conv => rhs; rw [H.expressions]
  simp only [List.size_toArray, List.length_map]
  rw [LocalContext.mkForall, LocalContext.mkForall,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  exact LocalContext.forallDomainsOnly_foldN_add hdecl k body

theorem RecursorConstruction.recursorType_forallDomainsOnly
    (H : RecursorConstruction R) (owner : Nat) :
    Expr.forallDomainsOnly
        (stats.params.size + (H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size)
        (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner) =
      H.localContext.lctx.mkForall stats.params
        (H.localContext.lctx.mkForall (H.recInfos.map (·.motive))
          (H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) (.sort .zero))) := by
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams : H.params.fvars.Nodup := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have hmotives : H.bindings.motives.fvars.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp houter).1).2.1
  have hminors : H.bindings.flatMinors.fvars.Nodup := (List.nodup_append.mp houter).2.1
  unfold AddInductive.declareRecursors.recursorType
  rw [Nat.add_assoc, H.params.forallDomainsOnly_add H.localWF hparams,
    H.bindings.motives.forallDomainsOnly_add H.localWF hmotives,
    ← Nat.add_zero (H.recInfos.flatMap (·.minors)).size,
    H.bindings.flatMinors.forallDomainsOnly_add H.localWF hminors]
  rfl

theorem RecursorConstruction.recursorType_prefixTelescope
    (H : RecursorConstruction R) (owner : Nat) :
    ∃ residual, Expr.ForallTelescope
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      (stats.params.size + (H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size)
      residual := by
  unfold AddInductive.declareRecursors.recursorType
  have H1 := H.params.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
      H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
      H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
      H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] <|
      .app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  have H2 := (H.bindings.motives.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
      H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
      H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] <|
      .app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
        H.recInfos[owner]!.major)).abstractN H.params.fvars
  have H3 := ((H.bindings.flatMinors.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
      H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] <|
      .app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
        H.recInfos[owner]!.major)).abstractN H.bindings.motives.fvars).abstractN H.params.fvars
      (0 + (H.recInfos.map (·.motive)).size)
  exact ⟨_, (H1.trans H2).trans H3⟩

/-! ### The generated recursor types of the construction's signature -/

theorem RecursorConstruction.signature_types
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < (H.signature HU).families.size) :
    TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      ((H.generatedInstance (H.signature HU)).recursorType ⟨owner, howner⟩) := by
  have howner' : owner < H.recInfos.size := by
    simpa [signature, H.families_size] using howner
  obtain ⟨target, Htr, ⟨T⟩⟩ := H.recursorTelescope owner howner'
  have heq := H.recursorTarget_eq_of_minors howner' T (H.generatedInstance (H.signature HU))
    rfl rfl rfl (H.generatedInstance_target _)
    (by simp [signature, H.flatMinors_size_eq])
    (H.recursorTelescope_minors_unannotated HU howner' T)
  rw [heq] at Htr
  exact Htr

theorem RecursorConstruction.signature_minorTranslation
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses) :
    TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (H.localContext.lctx.mkForall stats.params <|
        H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
        H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) (.sort .zero))
      (VExpr.wrapForalls ((H.generatedInstance (H.signature HU)).params ++
        (H.generatedInstance (H.signature HU)).motives ++
        (H.generatedInstance (H.signature HU)).minors) (.sort .zero)) := by
  by_cases hempty : H.recInfos.size = 0
  · have hrec : H.recInfos = #[] := Array.eq_empty_of_size_eq_zero hempty
    have hminors : (H.generatedInstance (H.signature HU)).minors = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [InductiveSignature.Instance.length_minors]
      simp only [signature, Array.size_ofFn]
      rw [← H.flatMinors_size_eq, hrec]
      rfl
    have Hpm := H.generatedParametersMotivesTranslation (H.generatedInstance (H.signature HU))
      rfl rfl rfl (H.generatedInstance_target _)
    rw [hminors, List.append_nil]
    have hflat : H.recInfos.flatMap (·.minors) = #[] := by rw [hrec]; rfl
    rw [hflat, LocalContext.mkForall_empty]
    exact Hpm
  · obtain ⟨target, Htr, ⟨T⟩⟩ := H.recursorTelescope 0 (by omega)
    obtain ⟨residual, Htel⟩ := H.recursorType_prefixTelescope 0
    have hp := H.recursorTelescope_params T
    have hm := H.recursorTelescope_motives T (H.generatedInstance (H.signature HU))
      rfl rfl rfl (H.generatedInstance_target _)
    have hmi := H.recursorTelescope_minors_unannotated HU (by omega) T
    have hp' : (H.generatedInstance (H.signature HU)).params =
        H.parameterSuffix.parameterDecls.toCtx.reverse := by
      rw [InductiveSignature.Instance.params, H.parameterDomains]
      rfl
    rw [T.target_eq, show T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major =
      (T.params ++ T.motives ++ T.minors) ++ (T.indices ++ T.major) by simp,
      VExpr.wrapForalls_append] at Htr
    have hlen : (T.params ++ T.motives ++ T.minors).length =
        stats.params.size + (H.recInfos.map (·.motive)).size +
          (H.recInfos.flatMap (·.minors)).size := by
      simp only [List.length_append, T.params_length, T.motives_length, T.minors_length]
    have Hd := (TrExprS.forallDomainsOnly Htel hlen Htr).1
    rw [H.recursorType_forallDomainsOnly, hp, hm, hmi, ← hp'] at Hd
    exact Hd

theorem RecursorConstruction.signature_generatedIHsWellTyped
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses) :
    (H.generatedInstance (H.signature HU)).GeneratedIHsWellTyped R.context.venv := by
  by_cases hempty : H.recInfos.size = 0
  · intro index
    have hsize : (H.signature HU).constructors.size = 0 := by
      simp only [signature, Array.size_ofFn]
      rw [← H.flatMinors_size_eq, Array.eq_empty_of_size_eq_zero hempty]
      rfl
    exact absurd index.isLt (by omega)
  · have h0 : 0 < H.recInfos.size := by omega
    have hsrc : 0 < indTypes.size := by rw [← H.sourceFamilyCount]; exact h0
    have hf : 0 < (H.signature HU).families.size := by
      simp [H.families_size]; omega
    obtain ⟨type, Htr, Htype⟩ := H.recursorTypeTranslation 0 hsrc
    have heq := Htr.uniqueS (H.signature_types HU 0 hf)
    rw [heq] at Htype
    exact InductiveSignature.Instance.generatedIHsWellTyped_of_recursorType _
      R.context.checking.tr.wf ⟨0, hf⟩ Htype

end Lean4Lean.VerifyInductive
