import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean
open Lean4Lean

theorem InductiveSignature.CaseSchema.Permission.congr
    {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size}
    (H : schema.Permission U owner levels target)
    (hwf : ∀ l ∈ target' :: levels', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) (target :: levels) (target' :: levels')) :
    schema.Permission U owner levels' target' := by
  let .cons ht hls := heq
  refine ⟨hls.length_eq.symm.trans H.length, fun l h => hwf l (.tail _ h),
    hwf _ (.head _), ?_⟩
  rcases H.admissible with h | h
  · exact .inl (h.of_equiv (VLevel.inst_congr rfl hls))
  · exact .inr (ht.symm.trans h)

theorem InductiveSignature.CaseSchema.Permission.packedWF
    {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size}
    (H : schema.Permission U owner levels target) :
    ∀ l ∈ target :: levels, l.WF U :=
  List.forall_mem_cons.mpr ⟨H.target_wf, H.levels_wf⟩

namespace VEnv

open VExpr

section
set_option hygiene false
variable (env : VEnv) (uvars : Nat)

section
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEqStrong Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEqStrong Γ e1 e2 A

inductive IsDefEqStrong : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    u.WF uvars →
    [] ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | elimDF {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size} :
    env.eliminators block schema →
    schema.genericType owner = some type →
    type.Closed →
    schema.Permission uvars owner levels target →
    (∀ level ∈ target' :: levels', level.WF uvars) →
    List.Forall₂ (· ≈ ·) (target :: levels) (target' :: levels') →
    typeLevel.WF uvars →
    Γ ⊢ type.instL (target :: levels) ≡ type.instL (target' :: levels') : .sort typeLevel →
    Γ ⊢ .elim block owner.val (target :: levels) ≡
      .elim block owner.val (target' :: levels') : type.instL (target :: levels)
  | appDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | projDF :
    env.projections typeName info →
    (∀ l ∈ levels, l.WF uvars) →
    levels.length = info.uvars →
    params.length = info.nparams →
    indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    fieldLevel.WF uvars →
    Γ ⊢ fieldType : .sort fieldLevel →
    Γ ⊢ sourceMajor ≡ major :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    Γ ⊢ sourceMajor ≡ major' :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    info.ctorType.Closed →
    (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero →
    Γ ⊢ .proj typeName index major ≡
      .proj typeName index major' : fieldType
  | lamDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B : .sort v →
    A'::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B →
    A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF :
    u.WF uvars → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    u.WF uvars → v.WF uvars → Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ B.inst e' : .sort v →
    Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    A.lift::A::Γ ⊢ B.liftN 1 1 : .sort v →
    Γ ⊢ e : .forallE A B →
    A::Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) →
    A::Γ ⊢ A.lift : .sort u →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    u.WF uvars →
    [] ⊢ df.type.instL ls : .sort u →
    [] ⊢ df.lhs.instL ls : df.type.instL ls →
    [] ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls : df.type.instL ls →
    Γ ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls
  | elimIota {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size} :
    env.eliminators block schema →
    schema.genericEquations block owner = some rules →
    df ∈ rules →
    InductiveSignature.CaseSchema.RuleClosed df →
    schema.Permission uvars owner levels target →
    typeLevel.WF uvars →
    Γ ⊢ df.type.instL (target :: levels) : .sort typeLevel →
    Γ ⊢ df.lhs.instL (target :: levels) : df.type.instL (target :: levels) →
    Γ ⊢ df.rhs.instL (target :: levels) : df.type.instL (target :: levels) →
    Γ ⊢ df.lhs.instL (target :: levels) ≡ df.rhs.instL (target :: levels) :
      df.type.instL (target :: levels)
  | projIota :
    env.projections typeName info →
    Γ ⊢ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) : fieldType →
    args[info.nparams + index]? = some field →
    Γ ⊢ field : fieldType →
    Γ ⊢ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) ≡ field :
      fieldType
  | structEta :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) :
      VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) ≡ e :
      VExpr.mkApps (.const typeName levels) params
  | unitLike :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    info.numFields = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ e' : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ e ≡ e' : VExpr.mkApps (.const typeName levels) params

end

section
local notation:65 Γ " ⊢ " e " : " A:30 => HasTypeStrong Γ e A true
local notation:65 Γ " ⊢ " e " :! " A:30 => HasTypeStrong Γ e A false
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEqStrong env uvars Γ e1 e2 A

/--
This is functionally a mutual inductive type,
but using a bool index makes it easier to do induction in lean.
The defeq rule is separated from the structural rules for easy inversion.
-/
inductive HasTypeStrong : List VExpr → VExpr → VExpr → Bool → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i :! A
  | sort' : l.WF uvars → l'.WF uvars → l ≈ l' → Γ ⊢ .sort l :! .sort (.succ l')
  | const :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = ci.uvars →
    u.WF uvars →
    [] ⊢ ci.type.instL ls : .sort u →
    Γ ⊢ ci.type.instL ls : .sort u →
    Γ ⊢ .const c ls :! ci.type.instL ls
  | elim {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size} :
    env.eliminators block schema →
    schema.genericType owner = some type →
    type.Closed →
    schema.Permission uvars owner levels target →
    typeLevel.WF uvars →
    Γ ⊢ type.instL (target :: levels) : .sort typeLevel →
    Γ ⊢ .elim block owner.val (target :: levels) :! type.instL (target :: levels)
  | app :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    Γ ⊢ .forallE A B : .sort (.imax u v) →
    Γ ⊢ f : .forallE A B →
    Γ ⊢ a : A →
    Γ ⊢ B.inst a : .sort v →
    Γ ⊢ .app f a :! B.inst a
  | proj :
    env.projections typeName info →
    (∀ l ∈ levels, l.WF uvars) →
    levels.length = info.uvars →
    params.length = info.nparams →
    indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    fieldLevel.WF uvars →
    Γ ⊢ fieldType : .sort fieldLevel →
    Γ ⊢ sourceMajor ≡ major :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    Γ ⊢ major : VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    info.ctorType.Closed →
    (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero →
    Γ ⊢ .proj typeName index major :! fieldType
  | lam :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body : B →
    Γ ⊢ .forallE A B : .sort (.imax u v) →
    Γ ⊢ .lam A body :! .forallE A B
  | forallE :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ body : .sort v →
    Γ ⊢ .forallE A body :! .sort (.imax u v)
  | base : Γ ⊢ e :! A → Γ ⊢ e : A
  | defeq : u.WF uvars → Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u → Γ ⊢ B : .sort u → Γ ⊢ e : A → Γ ⊢ e : B
end

end

theorem IsDefEqStrong.hasType {env : VEnv}
    (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e1 A ∧ env.IsDefEqStrong U Γ e2 e2 A :=
  ⟨H.trans H.symm, H.symm.trans H⟩

variable! (henv : Ordered env) in
theorem IsDefEqStrong.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h1 h2 _ ih3 => refine .bvar (h1.weakN W) h2 (ih3 W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ ih2 =>
    simp [(henv.closedC h1).instL.liftN_eq (Nat.zero_le _)] at ih2 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 (ih2 W)
  | elimDF h1 h2 h3 h4 h5 h6 h7 _ ih =>
    have ih := ih W
    simpa [VExpr.liftN, h3.instL.liftN_eq (Nat.zero_le _)] using
      (IsDefEqStrong.elimDF h1 h2 h3 h4 h5 h6 h7
        (by simpa [VExpr.liftN, h3.instL.liftN_eq (Nat.zero_le _)] using ih))
  | elimIota h1 h2 h3 h4 h5 h6 _ _ _ ihT ihL ihR =>
    simp only [h4.1.instL.liftN_eq (Nat.zero_le _),
      h4.2.1.instL.liftN_eq (Nat.zero_le _), h4.2.2.instL.liftN_eq (Nat.zero_le _)] at ihT ihL ihR ⊢
    exact .elimIota h1 h2 h3 h4 h5 h6 (ihT W) (ihL W) (ihR W)
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine liftN_inst_hi .. ▸ .appDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W) (ih4 W) ?_
    exact liftN_inst_hi .. ▸ liftN_inst_hi .. ▸ ih5 W
  | @projDF typeName info levels params index sourceMajor fieldType _ fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield hwf
      _ _ _ hclosed hguard ihField ihLeft ihRight =>
    have hfield' := VProjectionInfo.fieldType_liftN
      (typeName := typeName) (levels := levels) (params := params)
      (index := index) (major := sourceMajor) (n := n) (k := k) info hclosed
    rw [hfield] at hfield'
    have hleft := ihLeft W
    have hright := ihRight W
    simp only [VExpr.liftN_mkApps, List.map_append, VExpr.liftN] at hleft hright
    simpa [VExpr.liftN] using
      (.projDF (info := info) (params := params.map fun param => param.liftN n k)
        (indexArgs := indexArgs.map fun arg => arg.liftN n k)
        hinfo hlevels huvars (by simpa using hparams) (by simpa using hindices)
        hfield' hwf (ihField W) hleft hright hclosed hguard)
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W.succ) (ih5 W.succ)
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W) (ih2 W)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine liftN_inst_hi .. ▸ liftN_instN_hi .. ▸ .beta h1 h2
      (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W)
      (liftN_instN_hi .. ▸ ih5 W :)
      (liftN_instN_hi .. ▸ liftN_instN_hi .. ▸ ih6 W :)
  | @eta Γ a u B v e h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have := IsDefEqStrong.eta h1 h2 (ih1 W) (ih2 W.succ) ?_ (ih4 W) ?_ ?_
    · simp [liftN]; rwa [← lift_liftN']
    · specialize ih3 W.succ.succ
      have := liftN'_comm B n 1 (k+1) 1 (Nat.le_add_left ..)
      rw [Nat.add_comm 1] at this; rwa [← this, ← lift_liftN'] at ih3
    · have ih5 : IsDefEqStrong _ _ _ _ _ (liftN n (lift (forallE ..)) _) := ih5 W.succ
      rwa [← lift_liftN', ← lift_liftN'] at ih5
    · have ih6 := ih6 W.succ
      rwa [← lift_liftN'] at ih6
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    simp [
      hA1.instL.liftN_eq (Nat.zero_le _),
      hA2.instL.liftN_eq (Nat.zero_le _),
      hA3.instL.liftN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact IsDefEqStrong.extra h1 h2 h3 h4 h5 h6 h7 (ih4 W) (ih5 W)
  | projIota h1 _ h3 _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at ih1 ⊢
    exact .projIota h1 ih1 (by simp [h3]) ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map,
      Function.comp_def] at ih1 ih2 ⊢
    exact .structEta h1 (by simpa using h2) h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at ih1 ih2 ⊢
    exact .unitLike h1 (by simpa using h2) h3 h4 ih1 ih2

theorem IsDefEqStrong.defeq (H : IsDefEqStrong env U Γ e1 e2 A) : env.IsDefEq U Γ e1 e2 A := by
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | elimDF h1 h2 h3 h4 h5 h6 _ _ ih =>
    exact .elimDF h1 h2 h3 h4 h5 h6 ih.hasType.1
  | elimIota h1 h2 h3 h4 h5 _ _ _ _ _ ihL ihR =>
    exact .elimIota h1 h2 h3 h4 h5 ihL ihR
  | appDF _ _ _ _ _ _ _ _ _ ih1 ih2 => exact .appDF ih1 ih2
  | projDF h1 h2 h3 h4 h5 h6 _ _ _ _ hclosed hguard
      ihField ihLeft ihRight =>
    exact .projDF h1 h2 h3 h4 h5 h6 ihField ihLeft ihRight hclosed hguard
  | lamDF _ _ _ _ _ _ _ ih1 _ _ ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ _ _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ _ _ _ _ _ _ _ _ _ _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra h1 h2 h3
  | projIota h1 _ h3 _ ih1 ih2 => exact .projIota h1 ih1 h3 ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 => exact .structEta h1 h2 h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 => exact .unitLike h1 h2 h3 h4 ih1 ih2

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem IsDefEqStrong.mono
    (H : env.IsDefEqStrong U Γ e1 e2 A) : env'.IsDefEqStrong U Γ e1 e2 A := by
  induction H with
  | bvar h1 h2 _ ih => exact .bvar h1 h2 ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 _ _ ih1 ih2 =>
    exact .constDF (henv.1 h1) h2 h3 h4 h5 h6 ih1 ih2
  | elimDF h1 h2 h3 h4 h5 h6 h7 _ ih =>
    exact .elimDF (henv.eliminators h1) h2 h3 h4 h5 h6 h7 ih
  | elimIota h1 h2 h3 h4 h5 h6 _ _ _ ihT ihL ihR =>
    exact .elimIota (henv.eliminators h1) h2 h3 h4 h5 h6 ihT ihL ihR
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .appDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | projDF h1 h2 h3 h4 h5 h6 h7 _ _ _ hclosed hguard
      ihField ihLeft ihRight =>
    exact .projDF (henv.projections h1) h2 h3 h4 h5 h6 h7
      ihField ihLeft ihRight hclosed hguard
  | lamDF h1 h2  _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .lamDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 ih1 ih2 ih3
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 ih1 ih2
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .beta h1 h2 ih1 ih2 ih3 ih4 ih5 ih6
  | eta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .eta h1 h2 ih1 ih2 ih3 ih4 ih5 ih6
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 h4 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .extra (henv.2 h1) h2 h3 h4 ih1 ih2 ih3 ih4 ih5
  | projIota h1 _ h3 _ ih1 ih2 => exact .projIota (henv.projections h1) ih1 h3 ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 => exact .structEta (henv.projections h1) h2 h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 => exact .unitLike (henv.projections h1) h2 h3 h4 ih1 ih2

variable! (henv : Ordered env) in
theorem IsDefEqStrong.weak0 (H : env.IsDefEqStrong U [] e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e2 A := by
  have ⟨h1, h2, h3⟩ := H.defeq.closedN' henv.closed ⟨⟩
  simpa [h1.liftN_eq (Nat.zero_le _), h2.liftN_eq (Nat.zero_le _),
    h3.liftN_eq (Nat.zero_le _)] using H.weakN henv (.zero Γ rfl)

inductive EqUpToLevels (U : Nat) : VExpr → VExpr → Prop
  | bvar : EqUpToLevels U (.bvar i) (.bvar i)
  | const : (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    EqUpToLevels U (.const c ls) (.const c ls')
  | elim : (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    EqUpToLevels U (.elim block owner ls) (.elim block owner ls')
  | sort : l.WF U → l'.WF U → l ≈ l' → EqUpToLevels U (.sort l) (.sort l')
  | app : EqUpToLevels U f f' → EqUpToLevels U a a' → EqUpToLevels U (.app f a) (.app f' a')
  | proj : EqUpToLevels U e e' →
      EqUpToLevels U (.proj typeName index e) (.proj typeName index e')
  | lam : EqUpToLevels U A A' → EqUpToLevels U e e' → EqUpToLevels U (.lam A e) (.lam A' e')
  | forallE : EqUpToLevels U A A' → EqUpToLevels U B B' → EqUpToLevels U (.forallE A B) (.forallE A' B')

theorem EqUpToLevels.instL_expr (e : VExpr)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) ls ls') :
    EqUpToLevels U (e.instL ls) (e.instL ls') := by
  induction e with
  | bvar => exact .bvar
  | sort => exact .sort (.inst hls) (.inst hls') (VLevel.inst_congr rfl heq)
  | const | elim =>
    constructor
    · exact List.forall_mem_map.2 fun _ _ => .inst hls
    · exact List.forall_mem_map.2 fun _ _ => .inst hls'
    · exact List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
        .rfl fun _ _ => VLevel.inst_congr rfl heq
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ _ _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

variable! {env : VEnv} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') in
theorem EqUpToLevels.instL (H : env.IsDefEqStrong U' Γ e1 e2 A) :
    EqUpToLevels U (e1.instL ls) (e1.instL ls') ∧ EqUpToLevels U (e2.instL ls) (e2.instL ls') := by
  induction H with
  | bvar => exact ⟨.bvar, .bvar⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 | proofIrrel _ _  _ _ ih1 ih2
  | extra _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | sortDF h1 h2 h3 =>
    constructor <;> exact .sort (.inst hls) (.inst hls') (VLevel.inst_congr rfl heq)
  | constDF h1 h2 h3 h4 h5 =>
    constructor <;> exact .const
      (List.forall_mem_map.2 fun _ _ => .inst hls)
      (List.forall_mem_map.2 fun _ _ => .inst hls')
      (List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
        .rfl fun _ _ => VLevel.inst_congr rfl heq)
  | elimDF => exact ⟨instL_expr _ hls hls' heq, instL_expr _ hls hls' heq⟩
  | elimIota _ _ _ _ _ _ _ _ _ _ ihL ihR => exact ⟨ihL.1, ihR.2⟩
  | appDF _ _ _ _ _ _ _ _ _ ih1 ih2 => exact ⟨.app ih1.1 ih2.1, .app ih1.2 ih2.2⟩
  | projDF _ _ _ _ _ _ _ _ _ _ _ _ _ ihLeft ihRight =>
    exact ⟨.proj ihLeft.2, .proj ihRight.2⟩
  | lamDF _ _ _ _ _ _ _ ih1 _ _ ih2 => exact ⟨.lam ih1.1 ih2.1, .lam ih1.2 ih2.2⟩
  | forallEDF _ _ _ _ _ ih1 ih2 => exact ⟨.forallE ih1.1 ih2.1, .forallE ih1.2 ih2.2⟩
  | defeqDF _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ ih1 _ ih3 ih4 _ ih6 => exact ⟨.app (.lam ih1.1 ih3.1) ih4.1, ih6.2⟩
  | eta _ _ _ _ _ _ _ _ ih1 _ _ ih4 ih5 => exact ⟨.lam ih1.1 (.app ih5.1 .bvar), ih4.1⟩
  | projIota _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩
  | structEta _ _ _ _ _ ih1 ih2 => exact ⟨ih2.1, ih1.1⟩
  | unitLike _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩


variable! {env : VEnv} (W : OnCtx Γ fun _ A => A.LevelWF U) in
theorem EqUpToLevels.refl (H : env.IsDefEqStrong U Γ e1 e2 A) :
    EqUpToLevels U e1 e1 ∧ EqUpToLevels U e2 e2 := by
  have := IsDefEq.levelWF H.defeq W
  exact LevelWF.instL_id this.1 ▸ LevelWF.instL_id this.2.1 ▸
    EqUpToLevels.instL VLevel.params_wf VLevel.params_wf (.rfl fun _ _ => rfl) H

theorem EqUpToLevels.weakN (H : EqUpToLevels U e e') :
    EqUpToLevels U (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k with
  | bvar => exact .bvar
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | const h1 h2 h3 => exact .const h1 h2 h3
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ihMajor => exact .proj ihMajor
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

variable! (h₀ : EqUpToLevels U e₀ e₀') in
theorem EqUpToLevels.instN (H : EqUpToLevels U e e') :
    EqUpToLevels U (e.inst e₀ k) (e'.inst e₀' k) := by
  induction H generalizing k with
  | bvar => simp [inst, instVar]; split <;> [exact .bvar; split] <;> [exact h₀.weakN; exact .bvar]
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | const h1 h2 h3 => exact .const h1 h2 h3
    | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ihMajor => exact .proj ihMajor
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

def EnvStrong (env : VEnv) (U : Nat) (e A : VExpr) : Prop :=
  env.IsDefEqStrong U [] e e A ∧
  (∃ u, env.IsDefEqStrong U [] A A (.sort u)) ∧
  (∀ U' ls ls', (∀ l ∈ ls, l.WF U') → (∀ l ∈ ls', l.WF U') → List.Forall₂ (· ≈ ·) ls ls' →
    env.IsDefEqStrong U' [] (e.instL ls) (e.instL ls') (A.instL ls)) ∧
  ∀ A B, e = A.forallE B →
    (∃ u, env.IsDefEqStrong U [] A A (.sort u)) ∧
    (∃ u, env.IsDefEqStrong U [A] B B (.sort u))

variable! {env : VEnv} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') in
theorem IsDefEqStrong.instL (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U' (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls) (A.instL ls) := by
  induction H with
  | bvar h _ _ ih =>
    exact .bvar h.instL (.inst hls) ih
  | constDF h1 h2 h3 h4 h5 _ _ _ ih1 ih2 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ⊢
    exact .constDF h1
      (by simp [VLevel.WF.inst hls]) (by simp [VLevel.WF.inst hls]) (by simp [h4])
      (by simpa using h5.imp fun _ _ => VLevel.inst_congr_l) (.inst hls) ih1 ih2
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF _ _ h3 =>
    exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls) (VLevel.inst_congr_l h3)
  | elimDF h1 h2 h3 h4 h5 h6 _ _ ih =>
    simpa [VExpr.instL, VExpr.instL_instL, List.map_cons] using
      (IsDefEqStrong.elimDF h1 h2 h3 (h4.instL hls)
        (by simp [VLevel.WF.inst hls])
        (by simpa using h6.imp fun _ _ => VLevel.inst_congr_l)
        (.inst hls) (by simpa [VExpr.instL_instL, VExpr.instL] using ih))
  | elimIota h1 h2 h3 h4 h5 _ _ _ _ ihT ihL ihR =>
    simpa [VExpr.instL, VExpr.instL_instL, List.map_cons] using
      (IsDefEqStrong.elimIota h1 h2 h3 h4 (h5.instL hls) (.inst hls)
        (by simpa [VExpr.instL_instL, VExpr.instL] using ihT)
        (by simpa [VExpr.instL_instL, VExpr.instL] using ihL)
        (by simpa [VExpr.instL_instL, VExpr.instL] using ihR))
  | appDF _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact instL_instN ▸ .appDF (.inst hls) (.inst hls)
      ih1 ih2 ih3 ih4 (instL_instN ▸ instL_instN ▸ ih5)
  | @projDF typeName info levels params index sourceMajor fieldType _ fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield _
      _ _ _ hclosed hguard ihField ihLeft ihRight =>
    have hfield' := VProjectionInfo.fieldType_instL
      (typeName := typeName) (levels := levels) (params := params)
      (index := index) (major := sourceMajor) (substitution := ls) info
    rw [hfield] at hfield'
    have hleft := ihLeft
    have hright := ihRight
    simp only [VExpr.instL_mkApps, List.map_append, VExpr.instL] at hleft hright
    simpa [VExpr.instL] using
      (.projDF (info := info) (params := params.map (VExpr.instL ls))
        (indexArgs := indexArgs.map (VExpr.instL ls)) hinfo
        (by simp [VLevel.WF.inst hls]) (by simpa using huvars)
        (by simpa using hparams) (by simpa using hindices) hfield'
        (.inst hls) ihField hleft hright hclosed
        (by
          rcases hguard with hnever | hprop
          · left
            rw [← VLevel.inst_inst]
            exact hnever.inst
          · right
            simpa [VLevel.inst] using VLevel.inst_congr_l (ls := ls) hprop))
  | lamDF _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF (.inst hls) (.inst hls) ih1 ih2 ih3 ih4 ih5
  | forallEDF _ _ _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF (.inst hls) (.inst hls) ih1 ih2 ih3
  | defeqDF _ _ _ ih1 ih2 =>
    exact .defeqDF (.inst hls) ih1 ih2
  | beta _ _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    simpa using .beta (.inst hls) (.inst hls) ih1 ih2 ih3 ih4
      (by simpa [VExpr.instL] using ih5) (by simpa [VExpr.instL] using ih6)
  | eta _ _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    simpa [VExpr.instL] using .eta (.inst hls) (.inst hls) ih1 ih2
      (by simpa [VExpr.instL] using ih3) ih4
      (by simpa [VExpr.instL] using ih5) (by simpa [VExpr.instL] using ih6)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ih3 ih4 ih5 ⊢
    exact .extra h1 (by simp [VLevel.WF.inst hls]) (by simp [h3])
      (.inst hls) ih1 ih2 ih3 ih4 ih5
  | projIota h1 _ h3 _ ih1 ih2 =>
    simp only [VExpr.instL_mkApps, VExpr.instL] at ih1 ⊢
    exact .projIota h1 ih1 (by simp [h3]) ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_map,
      Function.comp_def] at ih1 ih2 ⊢
    exact .structEta h1 (by simpa using h2) h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    simp only [VExpr.instL_mkApps, VExpr.instL] at ih1 ih2 ⊢
    exact .unitLike h1 (by simpa using h2) h3 h4 ih1 ih2

def CtxStrong (env : VEnv) (U Γ) :=
  OnCtx Γ fun Γ A => ∃ u, env.IsDefEqStrong U Γ A A (.sort u)

variable! (henv : Ordered env) in
nonrec theorem CtxStrong.lookup {Γ} (H : CtxStrong env U Γ) (h : Lookup Γ i A) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) :=
  H.lookup h fun ⟨_, h⟩ => ⟨_, h.weakN henv .one⟩

theorem CtxStrong.defeq {Γ} (H : CtxStrong env U Γ) : OnCtx Γ (env.IsType U) :=
  H.mono fun ⟨_, h⟩ => ⟨_, h.defeq⟩

theorem CtxStrong.levelWF : ∀ {Γ}, CtxStrong env U Γ → OnCtx Γ fun _ A => A.LevelWF U
  | [], h => h
  | _::_, ⟨h1, _, h2⟩ => ⟨levelWF h1, (h2.defeq.levelWF (levelWF h1)).1⟩

variable! (henv : Ordered env) (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) (hΓ₀ : CtxStrong env U Γ₀) in
theorem IsDefEqStrong.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : env.IsDefEqStrong U Γ₁ e1 e2 A)
    (hΓ : CtxStrong env U Γ) :
    env.IsDefEqStrong U Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  induction H generalizing Γ k with
  | @bvar _ i ty _ h _ h2 ih =>
    dsimp [inst]; clear h2 ih
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h =>
        let ⟨u, hty⟩ := hΓ₀.lookup henv h
        exact .bvar h (hty.defeq.sort_r henv hΓ₀.defeq) hty
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← liftN_instN_lo (hj := Nat.zero_le _)])
      | zero =>
        let ⟨u, hty⟩ := hΓ.lookup henv .zero
        exact .bvar .zero (hty.defeq.sort_r henv hΓ.defeq) hty
      | succ h => exact (ih h hΓ.1).weakN henv .one
  | symm _ ih => exact .symm (ih W hΓ)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W hΓ) (ih2 W hΓ)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ ih2 =>
    simp [(henv.closedC h1).instL.instN_eq (Nat.zero_le _)] at ih2 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 (ih2 W hΓ)
  | elimDF h1 h2 h3 h4 h5 h6 h7 _ ih =>
    simp only [h3.instL.instN_eq (Nat.zero_le _)] at ih ⊢
    exact .elimDF h1 h2 h3 h4 h5 h6 h7 (ih W hΓ)
  | elimIota h1 h2 h3 h4 h5 h6 _ _ _ ihT ihL ihR =>
    simp only [h4.1.instL.instN_eq (Nat.zero_le _),
      h4.2.1.instL.instN_eq (Nat.zero_le _), h4.2.2.instL.instN_eq (Nat.zero_le _)] at ihT ihL ihR ⊢
    exact .elimIota h1 h2 h3 h4 h5 h6 (ihT W hΓ) (ihL W hΓ) (ihR W hΓ)
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact inst0_inst_hi .. ▸ .appDF h1 h2
      (ih1 W hΓ) (ih2 W.succ ⟨hΓ, _, ih1 W hΓ⟩)
      (ih3 W hΓ) (ih4 W hΓ) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih5 W hΓ)
  | @projDF typeName info levels params index sourceMajor fieldType _ fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield hwf
      _ _ _ hclosed hguard ihField ihLeft ihRight =>
    have hfield' := VProjectionInfo.fieldType_inst_some
      (typeName := typeName) (levels := levels) (params := params)
      (index := index) (major := sourceMajor) (result := fieldType)
      (value := e₀) (k := k) info hclosed hfield
    have hleft := ihLeft W hΓ
    have hright := ihRight W hΓ
    simp only [VExpr.inst_mkApps, List.map_append, VExpr.inst] at hleft hright
    simpa [VExpr.inst] using
      (.projDF (info := info) (params := params.map fun param => param.inst e₀ k)
        (indexArgs := indexArgs.map fun arg => arg.inst e₀ k)
        hinfo hlevels huvars (by simpa using hparams) (by simpa using hindices)
        hfield' hwf (ihField W hΓ) hleft hright hclosed hguard)
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact
      have hΓ' := ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩
      have hΓ'' := ⟨hΓ, _, (ih1 W hΓ).hasType.2⟩
      .lamDF h1 h2 (ih1 W hΓ) (ih2 W.succ hΓ') (ih3 W.succ hΓ'') (ih4 W.succ hΓ') (ih5 W.succ hΓ'')
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF h1 h2 (ih1 W hΓ)
      (ih2 W.succ ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩) (ih3 W.succ ⟨hΓ, _, (ih1 W hΓ).hasType.2⟩)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W hΓ) (ih2 W hΓ)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    rw [inst0_inst_hi, inst0_inst_hi]; exact
      have hΓ' := ⟨hΓ, _, ih1 W hΓ⟩
      .beta h1 h2
        (ih1 W hΓ) (ih2 W.succ hΓ') (ih3 W.succ hΓ') (ih4 W hΓ)
        (inst0_inst_hi .. ▸ ih5 W hΓ) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih6 W hΓ)
  | eta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have :=
      have hΓ' := ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩
      IsDefEqStrong.eta h1 h2 (ih1 W hΓ) (ih2 W.succ hΓ')
        (by
          have := ih3 W.succ.succ ⟨hΓ', _, by
            rw [← lift_instN_lo]; exact (ih1 W hΓ).hasType.1.weakN henv .one⟩
          rwa [lift_instN_lo, liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
        (ih4 W hΓ)
        (by
          have := ih5 W.succ hΓ'
          simp only [inst, ← lift_instN_lo] at this
          rwa [liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
        (by simpa [inst, ← lift_instN_lo] using ih6 W.succ hΓ')
    rw [lift, liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W hΓ) (ih2 W hΓ) (ih3 W hΓ)
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    simp [
      hA1.instL.instN_eq (Nat.zero_le _),
      hA2.instL.instN_eq (Nat.zero_le _),
      hA3.instL.instN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact .extra h1 h2 h3 h4 h5 h6 h7 (ih4 W hΓ) (ih5 W hΓ)
  | projIota h1 _ h3 _ ih1 ih2 =>
    have ih1 := ih1 W hΓ
    have ih2 := ih2 W hΓ
    simp only [VExpr.inst_mkApps, VExpr.inst] at ih1 ⊢
    exact .projIota h1 ih1 (by simp [h3]) ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    have ih1 := ih1 W hΓ
    have ih2 := ih2 W hΓ
    simp only [VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
      Function.comp_def] at ih1 ih2 ⊢
    exact .structEta h1 (by simpa using h2) h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    have ih1 := ih1 W hΓ
    have ih2 := ih2 W hΓ
    simp only [VExpr.inst_mkApps, VExpr.inst] at ih1 ih2 ⊢
    exact .unitLike h1 (by simpa using h2) h3 h4 ih1 ih2

theorem IsDefEqStrong.defeqDF_l (henv : Ordered env) (hΓ : CtxStrong env U Γ)
    (h1 : env.IsDefEqStrong U Γ A A' (.sort u))
    (h2 : env.IsDefEqStrong U (A::Γ) e1 e2 B) : env.IsDefEqStrong U (A'::Γ) e1 e2 B := by
  simpa [VExpr.inst_liftN_bvar] using
    have hu := h1.defeq.sort_r henv hΓ.defeq
    have hΓ' := ⟨hΓ, _, h1.hasType.2⟩
    h1.weakN henv (.one (A := A'))
      |>.symm.defeqDF hu (.bvar .zero hu (h1.hasType.2.weakN henv .one))
      |>.instN henv hΓ' .zero (h2.weakN henv (.succ (.one (A := A')))) hΓ'

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
theorem IsDefEqStrong.forallE_inv' (hΓ : CtxStrong env U Γ)
    (H : env.IsDefEqStrong U Γ e1 e2 V) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    (∃ u, env.IsDefEqStrong U Γ A A (.sort u)) ∧ ∃ v, env.IsDefEqStrong U (A::Γ) B B (.sort v) := by
  induction H generalizing A B with
  | symm _ ih => exact ih hΓ eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 hΓ (.inl eq)
    · exact ih2 hΓ (.inr eq)
  | forallEDF _ _ h1 h2 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasType.1⟩, _, h2.hasType.1⟩
    · exact ⟨⟨_, h1.hasType.2⟩, _, h1.defeqDF_l henv hΓ h2.hasType.2⟩
  | defeqDF _ _ _ _ ih2 => exact ih2 hΓ eq
  | @beta _ _ _ _ _ e _ _ _ h1 _ _ h4 _ _ _ _ ih3 ih4 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih4 hΓ (.inl eq)
    | forallE A B =>
      cases eq
      let ⟨⟨_, A1⟩, _, A2⟩ := ih3 ⟨hΓ, _, h1⟩ (.inl rfl)
      refine ⟨⟨_, h4.instN henv hΓ .zero A1 hΓ⟩, _, h4.instN henv hΓ (.succ .zero) A2 ?_⟩
      exact ⟨hΓ, _, h4.instN henv hΓ .zero A1 hΓ⟩
    | _ => cases eq
  | eta _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inl eq)
  | @extra df ls _ Γ h1 h2 =>
    suffices ∀ e, VExpr.instL ls e = VExpr.forallE A B →
        EnvStrong env df.uvars e df.type →
        (∃ u, IsDefEqStrong env U Γ A A (.sort u)) ∧
        (∃ u, IsDefEqStrong env U (A :: Γ) B B (.sort u)) by
      have ⟨A1, A2⟩ := envIH.2 h1
      cases eq <;> exact this _ ‹_› ‹_›
    intro e eq IH
    cases e <;> cases eq; rename_i A B
    let ⟨⟨_, A1⟩, v, A2⟩ := IH.2.2.2 _ _ rfl
    refine ⟨⟨_, (A1.instL h2).weak0 henv⟩, v.inst ls, ?_⟩
    have := (A2.instL h2).weakN henv (.succ (.zero Γ))
    have C1 := (A1.instL h2).defeq.closedN henv ⟨⟩
    have C2 := (A2.instL h2).defeq.closedN henv ⟨⟨⟩, C1⟩
    rw [C1.liftN_eq (Nat.zero_le _), C2.liftN_eq (by exact Nat.le_refl _)] at this
    simpa [liftN]
  | elimIota _ _ _ _ _ _ _ _ _ _ ihL ihR =>
    obtain eq | eq := eq
    · exact ihL hΓ (.inl eq)
    · exact ihR hΓ (.inl eq)
  | projIota _ _ _ _ _ ih2 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih2 hΓ (.inl eq)
  | structEta _ _ _ _ _ ih1 _ =>
    obtain eq | eq := eq
    · exact (VExpr.mkApps_ne_forallE (fn := .const _ _) (fun _ _ h => nomatch h) _ eq).elim
    · exact ih1 hΓ (.inl eq)
  | unitLike _ _ _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 hΓ (.inl eq)
    · exact ih2 hΓ (.inl eq)
  | _ => nomatch eq

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
theorem IsDefEqStrong.isType' (hΓ : CtxStrong env U Γ) (H : env.IsDefEqStrong U Γ e1 e2 A) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) := by
  induction H with
  | bvar h => exact hΓ.lookup henv h
  | symm _ ih => exact ih hΓ
  | trans _ _ ih1 => exact ih1 hΓ
  | sortDF h1 => exact ⟨_, .sortDF h1 h1 rfl⟩
  | constDF h1 h2 =>
    let ⟨_, h⟩ := envIH.1 h1
    exact ⟨_, (h.1.instL h2).weak0 henv⟩
  | elimDF _ _ _ _ _ _ _ h => exact ⟨_, h.hasType.1⟩
  | elimIota _ _ _ _ _ _ h => exact ⟨_, h⟩
  | appDF _ _ _ _ _ h4 _ _ _ ih3 =>
    let ⟨_, ih3⟩ := ih3 hΓ
    have ⟨_, _, ih3⟩ := ih3.forallE_inv' henv envIH hΓ (.inl rfl)
    exact ⟨_, h4.hasType.1.instN henv hΓ .zero ih3 hΓ⟩
  | projDF _ _ _ _ _ _ _ hfieldType _ _ _ _ _ _ _ =>
    exact ⟨_, hfieldType.hasType.2⟩
  | lamDF h1 h2 h3 h4 => exact ⟨_, .forallEDF h1 h2 h3.hasType.1 h4 h4⟩
  | forallEDF h1 h2 => exact ⟨_, .sortDF ⟨h1, h2⟩ ⟨h1, h2⟩ rfl⟩
  | defeqDF _ h2 => exact ⟨_, h2.hasType.2⟩
  | beta _ _ _ h4 _ h6 => exact ⟨_, h6.hasType.1.instN henv hΓ .zero h4 hΓ⟩
  | eta _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hΓ
  | proofIrrel h1 => exact ⟨_, h1⟩
  | extra h1 h2 =>
    have ⟨_, h⟩ := (envIH.2 h1).2.2.1
    exact ⟨_, (h.instL h2).weak0 henv⟩
  | projIota _ _ _ _ ih1 => exact ih1 hΓ
  | structEta _ _ _ _ _ ih1 => exact ih1 hΓ
  | unitLike _ _ _ _ _ _ ih1 => exact ih1 hΓ

theorem IsDefEqStrong.instDF
    (henv : Ordered env) (hΓ : CtxStrong env U Γ) (hu : u.WF U) (hv : v.WF U)
    (hA : env.IsDefEqStrong U Γ A A (.sort u))
    (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v))
    (hf : env.IsDefEqStrong U (A::Γ) f f' B)
    (ha : env.IsDefEqStrong U Γ a a' A) :
    env.IsDefEqStrong U Γ (f.inst a) (f'.inst a') (B.inst a) :=
  have H2 {f f' B v}
      (hv : v.WF U)
      (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v))
      (hf : env.IsDefEqStrong U (A::Γ) f f' B)
      (hi : IsDefEqStrong env U Γ (inst B a) (inst B a') (sort v)) :
      env.IsDefEqStrong U Γ (f.inst a) (f'.inst a') (B.inst a) :=
    have H1 {a f}
        (hf : env.IsDefEqStrong U (A::Γ) f f' B)
        (ha : IsDefEqStrong env U Γ a a A) :
        env.IsDefEqStrong U Γ (.app (.lam A f) a) (f.inst a) (B.inst a) :=
      IsDefEqStrong.beta hu hv hA hB hf.hasType.1 ha
        (ha.hasType.1.instN henv hΓ .zero hB hΓ)
        (ha.hasType.1.instN henv hΓ .zero hf.hasType.1 hΓ)
    (H1 hf ha.hasType.1).symm.trans <|
      .trans (.appDF hu hv hA hB (.lamDF hu hv hA hB hB hf hf) ha hi) <|
      .defeqDF hv (.symm hi) (H1 hf.hasType.2 ha.hasType.2)
  H2 hv hB hf <| H2 (v := v.succ) hv (.sortDF hv hv rfl) hB (.sortDF hv hv rfl)

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env))
  (W : CtxStrong env U Γ) in
theorem EqUpToLevels.defeq (H : env.IsDefEqStrong U Γ e1 e2 A)
    (H1 : EqUpToLevels U e1 e1') (H2 : EqUpToLevels U e2 e2') :
    env.IsDefEqStrong U Γ e1' e2' A := by
  induction H generalizing e1' e2' with
  | bvar h1 h2 h3 => let .bvar := H1; let .bvar := H2; exact .bvar h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 _ _ ih1 ih2 =>
    let .const a1 a2 a3 := H1
    let .const b1 b2 b3 := H2
    let ⟨_, c1⟩ := envIH.1 h1
    have c2 := a3.flip.trans (T := (· ≈ ·)) (fun _ _ _  => (·.symm.trans)) <|
      h5.trans (T := (· ≈ ·)) (fun _ _ _ => Eq.trans) b3
    have := c1.2.2.1 _ _ _ a2 b2 c2
    exact .defeqDF (.inst a1) (.symm ((c1.2.2.1 _ _ _ a1 a2 a3).weak0 henv)) <|
      .constDF h1 a2 b2 (a3.length_eq.symm.trans h4) c2 (.inst a2) this (this.weak0 henv)
  | elimDF h1 h2 h3 h4 h5 h6 h7 ht ih =>
    let .elim a1 a2 a3 := H1
    let .elim b1 b2 b3 := H2
    cases a3 with
    | cons ha tla =>
      cases b3 with
      | cons hb tlb =>
        have aeq := List.Forall₂.cons ha tla
        have beq := List.Forall₂.cons hb tlb
        have cross := aeq.flip.trans (T := (· ≈ ·)) (fun _ _ _ => (·.symm.trans)) <|
          h6.trans (T := (· ≈ ·)) (fun _ _ _ => Eq.trans) beq
        have typeCross := ih W (instL_expr _ a1 a2 aeq) (instL_expr _ h5 b2 beq)
        have typeLeft := ih W (instL_expr _ a1 a2 aeq)
          (instL_expr _ h5 a1 (h6.flip.imp fun _ _ h => h.symm))
        exact .defeqDF h7 typeLeft <|
          .elimDF h1 h2 h3 (h4.congr a2 aeq) b2 cross h7 typeCross
  | elimIota h1 h2 h3 h4 h5 h6 hT hL hR _ ihL ihR =>
    exact (ihL W H1 (EqUpToLevels.refl W.levelWF hL).1).trans <|
      (IsDefEqStrong.elimIota h1 h2 h3 h4 h5 h6 hT hL hR).trans
        (ihR W (EqUpToLevels.refl W.levelWF hR).1 H2)
  | symm _ ih => exact (ih W H2 H1).symm
  | trans h1 _ ih1 ih2 =>
    have H3 := (EqUpToLevels.refl W.levelWF h1).2; exact (ih1 W H1 H3).trans (ih2 W H3 H2)
  | sortDF h1 h2 h3 =>
    let .sort a1 a2 a3 := H1
    let .sort b1 b2 b3 := H2
    exact .defeqDF (by exact a1)
      (.symm <| .sortDF (by exact a1) (by exact a2) (VLevel.succ_congr a3))
      (.sortDF a2 b2 (a3.symm.trans <| h3.trans b3))
  | appDF h1 h2 h3 h4 h5 h6 _ ih1 ih2 ih3 ih4 ih5 =>
    let .app a1 a2 := H1
    let .app b1 b2 := H2
    have := ih4 W a2 (EqUpToLevels.refl W.levelWF h6).2 |>.trans h6.symm
    exact .defeqDF h2 (.instDF henv W h1 (by exact h2) h3 (.sortDF h2 h2 rfl) h4 this) <|
      .appDF h1 h2 h3 h4 (ih3 W a1 b1) (ih4 W a2 b2) <|
      .instDF henv W h1 (by exact h2) h3 (.sortDF h2 h2 rfl) h4 (ih4 W a2 b2)
  | projDF h1 h2 h3 h4 h5 h6 h7 hField hLeft hRight
      hclosed hguard ihField ihLeft ihRight =>
    let .proj aMajor := H1
    let .proj bMajor := H2
    have sourceEq := (EqUpToLevels.refl W.levelWF hLeft).1
    exact IsDefEqStrong.projDF h1 h2 h3 h4 h5 h6 h7 hField
      (ihLeft W sourceEq aMajor) (ihRight W sourceEq bMajor) hclosed hguard
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih1 ih2 ih3 ih4 =>
    let .lam a1 a2 := H1
    let .lam b1 b2 := H2
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := ih1 W (EqUpToLevels.refl W.levelWF h3).1 b1
    have h4' := c1.symm.defeqDF_l henv W h4
    exact have ih := ih4 ⟨W, _, h3.hasType.1⟩ a2 b2
      .defeqDF (by exact ⟨h1, h2⟩) (.forallEDF h1 h2 c1 h4' h4) <|
      .lamDF h1 h2 (ih1 W a1 b1) h4' (.defeqDF_l henv W c2 h4)
        (.defeqDF_l henv W c1.symm ih) (.defeqDF_l henv W c2 ih)
  | forallEDF h1 h2 h3 _ _ ih1 ih2 =>
    let .forallE a1 a2 := H1
    let .forallE b1 b2 := H2
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := ih1 W (EqUpToLevels.refl W.levelWF h3).1 b1
    exact .forallEDF h1 h2 (ih1 W a1 b1)
      (.defeqDF_l henv W c1.symm <| ih2 ⟨W, _, h3.hasType.1⟩ a2 b2)
      (.defeqDF_l henv W c2 <| ih2 ⟨W, _, h3.hasType.1⟩ a2 b2)
  | defeqDF h1 h2 _ _ ih => exact .defeqDF h1 h2 (ih W H1 H2)
  | beta h1 h2 h3 h4 h5 h6 h7 _ ih1 _ ih3 ih4 ih5 ih6 =>
    let .app a1 a3 := H1; let .lam a1 a2 := a1
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := ih4 W a3 (EqUpToLevels.refl W.levelWF h6).2 |>.trans h6.symm
    have c3 := ih3 ⟨W, _, h3⟩ a2 a2
    have hb := (EqUpToLevels.refl (CtxStrong.levelWF (by exact ⟨W, _, h3⟩)) h4).2
    have c4 := ih5 W (.instN a3 hb) (EqUpToLevels.refl W.levelWF h7).2
    refine .trans ?_ (ih6 W (.instN a3 a2) H2)
    refine .defeqDF h2 (.instDF henv W h1 (by exact h2) h3 (.sortDF h2 h2 rfl) h4 c2) ?_
    exact .beta h1 h2 c1.hasType.1 (.defeqDF_l henv W c1.symm h4)
      (.defeqDF_l henv W c1.symm c3) (.defeqDF h1 c1.symm c2.hasType.1)
      c4.hasType.1 (.instN henv c2.hasType.1 W .zero c3 W)
  | eta h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 ih3 ih4 ih5 =>
    let .lam a1 a3 := H1; let .app a2 a3 := a3; let .bvar := a3
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := have W' := ⟨W, _, h3⟩; ih5 W' a2 (EqUpToLevels.refl W'.levelWF h7).2
    have c3 := IsDefEqStrong.appDF h1 h2 h8 h5 c2 (.bvar .zero h1 h8)
    rw [VExpr.inst_liftN_bvar] at c3; specialize c3 h4
    refine .trans
      (.symm <| .lamDF h1 h2 c1.symm h4 (.defeqDF_l henv W c1.symm h4) c3.symm
        (.defeqDF_l henv W c1.symm c3.symm)) ?_
    exact .trans (.eta h1 h2 h3 h4 h5 h6 h7 h8) (ih4 W (EqUpToLevels.refl W.levelWF h6).1 H2)
  | proofIrrel h1 _ _ _ ih1 ih2 => exact .proofIrrel h1 (ih1 W H1 H1) (ih2 W H2 H2)
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ ih1 ih2 =>
    have c1 := ih1 trivial H1 (EqUpToLevels.refl (by trivial) h6).2
    have c2 := ih2 trivial H2 (EqUpToLevels.refl (by trivial) h7).2
    refine .weak0 henv <| c1.trans <| .trans ?_ c2.symm
    exact .extra h1 h2 h3 h4 h5 h6 h7 h6 h7
  | projIota h1 h2 h3 h4 ih1 ih2 =>
    exact (ih1 W H1 (EqUpToLevels.refl W.levelWF h2).1).trans <|
      (IsDefEqStrong.projIota h1 h2 h3 h4).trans (ih2 W (EqUpToLevels.refl W.levelWF h4).1 H2)
  | structEta h1 h2 h3 h4 h5 ih1 ih2 =>
    exact (ih2 W H1 (EqUpToLevels.refl W.levelWF h5).1).trans <|
      (IsDefEqStrong.structEta h1 h2 h3 h4 h5).trans (ih1 W (EqUpToLevels.refl W.levelWF h4).1 H2)
  | unitLike h1 h2 h3 h4 h5 h6 ih1 ih2 =>
    exact (ih1 W H1 (EqUpToLevels.refl W.levelWF h5).1).trans <|
      (IsDefEqStrong.unitLike h1 h2 h3 h4 h5 h6).trans (ih2 W (EqUpToLevels.refl W.levelWF h6).1 H2)

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
theorem IsDefEq.strong' (hΓ : CtxStrong env U Γ)
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsDefEqStrong U Γ e1 e2 A := by
  have hctx {Γ} (H : OnCtx Γ fun Γ A => ∃ u, env.IsDefEqStrong U Γ A A (.sort u)) :
     OnCtx Γ (env.IsType U) := H.mono fun ⟨_, h⟩ => ⟨_, h.defeq⟩
  induction H with
  | bvar h =>
    let ⟨u, hA⟩ := hΓ.lookup henv h
    exact .bvar h (hA.defeq.sort_r henv (hctx hΓ)) hA
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih1 ih2 => exact (ih1 hΓ).trans (ih2 hΓ)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | @constDF _ _ ls₁ ls₂ _ h1 h2 h3 h4 h5 =>
    let ⟨u, h6⟩ := envIH.1 h1
    have := h6.2.2.1 _ _ _ h2 h3 h5
    exact .constDF h1 h2 h3 h4 h5 (.inst h2) this (this.weak0 henv)
  | elimDF h1 h2 h3 h4 h5 h6 hT ih =>
    have hwf := hT.sort_r henv hΓ.defeq
    have hleft := h4.packedWF
    have ht := ih hΓ
    have ht' := EqUpToLevels.defeq henv envIH hΓ ht
      (EqUpToLevels.refl hΓ.levelWF ht).1 (EqUpToLevels.instL_expr _ hleft h5 h6)
    exact .elimDF h1 h2 h3 h4 h5 h6 hwf ht'
  | elimIota h1 h2 h3 h4 h5 _ _ ihL ihR =>
    have hl := ihL hΓ
    have ⟨u, ht⟩ := hl.isType' henv envIH hΓ
    exact .elimIota h1 h2 h3 h4 h5 (ht.defeq.sort_r henv hΓ.defeq) ht hl (ihR hΓ)
  | appDF _ _ ih1 ih2 =>
    let ⟨_, h3⟩ := (ih1 hΓ).isType' henv envIH hΓ
    let ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := h3.forallE_inv' henv envIH hΓ (.inl rfl)
    have hu := hA.defeq.sort_r henv hΓ.defeq
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, hA⟩
    have hv := hB.defeq.sort_r henv hΓ'.defeq
    exact .appDF hu hv hA hB (ih1 hΓ) (ih2 hΓ) <|
      .instDF (v := v.succ) henv hΓ hu hv hA (.sortDF hv hv rfl) hB (ih2 hΓ)
  | projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
      hLeft hRight hclosed hguard ihField ihLeft ihRight =>
    have hwf := hfieldTyping.sort_r henv hΓ.defeq
    exact .projDF hinfo hlevels huvars hparams hindices hfield hwf
      (ihField hΓ) (ihLeft hΓ) (ihRight hΓ) hclosed hguard
  | lamDF hA _ ih1 ih2 =>
    have hu := hA.sort_r henv hΓ.defeq
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, (ih1 hΓ).hasType.1⟩
    let ⟨_, hB⟩ := (ih2 hΓ').isType' henv envIH hΓ'
    exact .lamDF hu (hB.defeq.sort_r henv hΓ'.defeq) (ih1 hΓ)
      hB ((ih1 hΓ).defeqDF_l henv hΓ hB) (ih2 hΓ') ((ih1 hΓ).defeqDF_l henv hΓ (ih2 hΓ'))
  | forallEDF hA hb ih1 ih2 =>
    have hu := hA.sort_r henv hΓ.defeq
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, (ih1 hΓ).hasType.1⟩
    exact .forallEDF hu (hb.sort_r henv hΓ'.defeq)
      (ih1 hΓ) (ih2 hΓ') ((ih1 hΓ).defeqDF_l henv hΓ (ih2 hΓ'))
  | defeqDF hAB _ ih1 ih2 =>
    exact .defeqDF (hAB.sort_r henv hΓ.defeq) (ih1 hΓ) (ih2 hΓ)
  | beta _ _ ih1 ih2 =>
    have he' := ih2 hΓ
    have ⟨_, hA⟩ := he'.isType' henv envIH hΓ
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, hA⟩
    have he := ih1 hΓ'
    have ⟨_, hB⟩ := he.isType' henv envIH hΓ'
    exact .beta (hA.defeq.sort_r henv hΓ.defeq) (hB.defeq.sort_r henv hΓ'.defeq)
      hA hB he he' (he'.instN henv hΓ .zero hB hΓ) (he'.instN henv hΓ .zero he hΓ)
  | eta _ ih =>
    have he := ih hΓ
    let ⟨_, hAB⟩ := he.isType' henv envIH hΓ
    let ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := hAB.forallE_inv' henv envIH hΓ (.inl rfl)
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, hA⟩
    exact .eta (hA.defeq.sort_r henv hΓ.defeq) (hB.defeq.sort_r henv hΓ'.defeq)
      hA hB (hB.weakN henv (.succ .one)) he (he.weakN henv .one) (hA.weakN henv .one)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | extra h1 h2 h3 =>
    let ⟨⟨hl, ⟨_, ht⟩, _⟩, hr, _, _⟩ := envIH.2 h1
    exact .extra h1 h2 h3 (.inst h2) (ht.instL h2)
      (hl.instL h2) (hr.instL h2) ((hl.instL h2).weak0 henv) ((hr.instL h2).weak0 henv)
  | projIota h1 _ h3 _ ih1 ih2 => exact .projIota h1 (ih1 hΓ) h3 (ih2 hΓ)
  | structEta h1 h2 h3 _ _ ih1 ih2 => exact .structEta h1 h2 h3 (ih1 hΓ) (ih2 hΓ)
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 => exact .unitLike h1 h2 h3 h4 (ih1 hΓ) (ih2 hΓ)

theorem CtxStrong.strong' (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env))
    (hΓ : OnCtx Γ (env.IsType U)) : CtxStrong env U Γ := by
  induction Γ with
  | nil => trivial
  | cons _ _ ih => let ⟨hΓ, _, hA⟩ := hΓ; exact ⟨ih hΓ, _, hA.strong' henv envIH (ih hΓ)⟩

theorem Ordered.strong (henv : Ordered env) : OnTypes env (EnvStrong env) := by
  refine henv.induction _ (fun le ⟨h1, ⟨_, h2⟩, h3, h4⟩ => ?_) (fun henv IH H => ?_)
  · refine ⟨h1.mono le, ⟨_, h2.mono le⟩, ?_, ?_⟩
    · exact fun _ _ _ h4 h5 h6 => (h3 _ _ _ h4 h5 h6).mono le
    · exact fun _ _ eq => let ⟨⟨_, h4⟩, ⟨_, h5⟩⟩ := h4 _ _ eq; ⟨⟨_, h4.mono le⟩, ⟨_, h5.mono le⟩⟩
  · have H' := H.strong' henv IH (Γ := []) ⟨⟩
    refine ⟨H', H'.isType' henv IH ⟨⟩, fun _ _ _ h1 h2 h3 => ?_, ?_⟩
    · exact EqUpToLevels.defeq henv IH (by trivial) (.instL h1 H')
        (EqUpToLevels.refl (by trivial) (.instL h1 H')).1 (EqUpToLevels.instL h1 h2 h3 H').1
    · exact fun _ _ eq => H'.forallE_inv' henv IH ⟨⟩ (.inl eq)

theorem CtxStrong.strong (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) : CtxStrong env U Γ :=
  .strong' henv henv.strong hΓ

theorem IsDefEq.strong (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsDefEqStrong U Γ e1 e2 A :=
  H.strong' henv henv.strong (.strong henv hΓ)

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.eqUpToLevels (H : env.IsDefEq U Γ e1 e2 A)
    (H1 : EqUpToLevels U e2 e2') : env.IsDefEq U Γ e1 e2' A :=
  have W := .strong' henv henv.strong hΓ
  have := H.strong henv hΓ
  (EqUpToLevels.defeq henv henv.strong W (H.strong henv hΓ)
    (EqUpToLevels.refl W.levelWF this).1 H1).defeq

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U')) {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') in
theorem IsDefEq.instL_r (H : env.IsDefEq U' Γ e1 e2 A) :
    env.IsDefEq U (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls') (A.instL ls) :=
  have := H.strong henv hΓ
  IsDefEq.eqUpToLevels henv (hΓ.instL hls) (this.instL hls).defeq
    (EqUpToLevels.instL hls hls' heq this).2

theorem IsDefEqStrong.hasType' {env : VEnv}
    (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.HasTypeStrong U Γ e1 A true ∧ env.HasTypeStrong U Γ e2 A true := by
  induction H with
  | bvar h1 h2 _ ih3 => refine and_self_iff.2 <| .base <| .bvar h1 h2 ih3.1
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 | proofIrrel _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | sortDF h1 h2 h3 => exact ⟨.base <| .sort' h1 h1 rfl, .base <| .sort' h2 h1 h3.symm⟩
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    exact ⟨.base <| .const h1 h2 h4 h6 ih1.1 ih2.1,
      .defeq h6 h8.symm ih2.2 ih2.1 <| .base <|
      .const h1 h3 (h5.length_eq.symm.trans h4) h6 ih1.2 ih2.2⟩
  | elimDF h1 h2 h3 h4 h5 h6 h7 ht ih =>
    exact ⟨.base <| .elim h1 h2 h3 h4 h7 ih.1,
      .defeq h7 ht.symm ih.2 ih.1 <| .base <|
        .elim h1 h2 h3 (h4.congr h5 h6) h7 ih.2⟩
  | elimIota _ _ _ _ _ _ _ _ _ _ ihL ihR => exact ⟨ihL.1, ihR.1⟩
  | appDF h1 h2 h3 h4 h5 h6 h7 ih1 ih2 ih3 ih4 ih5 =>
    have := HasTypeStrong.base <| .forallE h1 h2 ih1.1 ih2.1
    exact ⟨.base <| .app h1 h2 ih1.1 ih2.1 this ih3.1 ih4.1 ih5.1,
      .defeq h2 h7.symm ih5.2 ih5.1 <| .base <| .app h1 h2 ih1.2 ih2.2 this ih3.2 ih4.2 ih5.2⟩
  | projDF h1 h2 h3 h4 h5 h6 h7 hField hLeft hRight
      hclosed hguard ihField ihLeft ihRight =>
    exact ⟨.base <| .proj h1 h2 h3 h4 h5 h6 h7 ihField.1
        hLeft ihLeft.2 hclosed hguard,
      .base <| .proj h1 h2 h3 h4 h5 h6 h7 ihField.2
        hRight ihRight.2 hclosed hguard⟩
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih1 ih2 ih3 ih4 ih5 =>
    refine ⟨.base <| .lam h1 h2 ih1.1 ih2.1 ih4.1 ?a,
      .defeq (by exact ⟨h1, h2⟩) (.symm <| .forallEDF h1 h2 h3 h4 h5) ?b ?a ?_⟩
    · exact .base <| .forallE h1 h2 ih1.1 ih2.1
    · exact .base <| .forallE h1 h2 ih1.2 ih3.1
    · exact .base <| .lam h1 h2 ih1.2 ih3.1 ih5.2 ?b
  | forallEDF h1 h2 h3 h4 h5 ih1 ih2 ih3 =>
    exact ⟨.base <| .forallE h1 h2 ih1.1 ih2.1, .base <| .forallE h1 h2 ih1.2 ih3.2⟩
  | defeqDF h1 h2 h3 ih1 ih2 =>
    exact ⟨.defeq h1 h2 ih1.1 ih1.2 ih2.1, .defeq h1 h2 ih1.1 ih1.2 ih2.2⟩
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have := HasTypeStrong.base <| .forallE h1 h2 ih1.1 ih2.1
    refine ⟨.base <| .app h1 h2 ih1.1 ih2.1 this ?_ ih4.1 ih5.1, ih6.1⟩
    refine .base <| .lam h1 h2 ih1.1 ih2.1 ih3.1 ?_
    exact .base <| .forallE h1 h2 ih1.1 ih2.1
  | @eta Γ A u B v e h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine have a1 := .base <| .forallE h1 h2 ih6.1 ih3.1
      have := ih6.1.app h1 h2 ih3.1 a1 ih5.1 (.base <| .bvar .zero h1 ih6.1); ?_
    rw [VExpr.inst_liftN_bvar] at this; specialize this ih2.1
    refine ⟨.base <| .lam h1 h2 ih1.1 ih2.1 (.base this) ?_, ih4.1⟩
    exact .base <| .forallE h1 h2 ih1.1 ih2.1
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 => exact ⟨ih4.1, ih5.1⟩
  | projIota _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩
  | structEta _ _ _ _ _ ih1 ih2 => exact ⟨ih2.1, ih1.1⟩
  | unitLike _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩

theorem HasTypeStrong.refl {env : VEnv}
    (H : env.HasTypeStrong U Γ e A b) : env.IsDefEqStrong U Γ e e A := by
  induction H with
  | bvar h1 h2 _ ih1 => refine .bvar h1 h2 ih1
  | sort' h1 h2 h3 =>
    refine .defeqDF ?_ (.sortDF ?_ ?_ (VLevel.succ_congr h3)) (.sortDF h1 h1 rfl) <;> assumption
  | const h1 h2 h3 h4 h5 h6 ih1 ih2 =>
    exact .constDF h1 h2 h2 h3 (.rfl fun _ _ => rfl) h4 ih1 ih2
  | elim h1 h2 h3 h4 h5 _ ih =>
    exact .elimDF h1 h2 h3 h4 h4.packedWF
      (.rfl fun _ _ => rfl) h5 ih
  | app h1 h2 h3 h4 _ h5 h6 h7 ih1 ih2 _ ih3 ih4 ih5 =>
    exact .appDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | proj h1 h2 h3 h4 h5 h6 h7 _ hMajorEq _ hclosed hguard
      ihField ihMajor =>
    exact .projDF h1 h2 h3 h4 h5 h6 h7 ihField
      hMajorEq hMajorEq hclosed hguard
  | lam h1 h2 h3 h4 h5 _ ih1 ih2 ih3 =>
    exact .lamDF h1 h2 ih1 ih2 ih2 ih3 ih3
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    exact .forallEDF h1 h2 ih1 ih2 ih2
  | base _ ih => exact ih
  | defeq h1 h2 h3 h4 h5 ih1 ih2 ih3 => exact .defeqDF h1 h2 ih3

theorem HasTypeStrong.hasType {env : VEnv}
    (H : env.HasTypeStrong U Γ e A b) :  env.HasType U Γ e A := H.refl.defeq.hasType.1

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.app_inv (H : env.HasType U Γ (.app f a) V) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : f.app a = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H =>
    subst eq'; let .app _ _ _ _ _ h1 h2 _ := H; exact ⟨_, _, h1.hasType, h2.hasType⟩

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.proj_inv
    (H : env.HasType U Γ (.proj typeName index major) V) :
    ∃ info levels params indexArgs sourceMajor fieldType fieldLevel,
      env.projections typeName info ∧
      (∀ level ∈ levels, level.WF U) ∧
      levels.length = info.uvars ∧
      params.length = info.nparams ∧
      indexArgs.length = info.nindices ∧
      info.fieldType typeName levels params index sourceMajor = some fieldType ∧
      env.HasType U Γ fieldType (.sort fieldLevel) ∧
      env.IsDefEq U Γ sourceMajor major
        (VExpr.mkApps (.const typeName levels) (params ++ indexArgs)) ∧
      info.ctorType.Closed ∧
      ((info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : VExpr.proj typeName index major = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H =>
    subst eq'
    let .proj hinfo hlevels huvars hparams hindices hfield _ hfieldTyping hmajor _
        hclosed hguard := H
    exact ⟨_, _, _, _, _, _, _, hinfo, hlevels, huvars, hparams, hindices,
      hfield, hfieldTyping.hasType, hmajor.defeq,
      hclosed, hguard⟩

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.app_inv (H : VExpr.WF env U Γ (.app f a)) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A :=
  let ⟨_, H⟩ := H; HasType.app_inv henv hΓ H

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.lam_inv (H : env.HasType U Γ (.lam A body) V) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : A.lam body = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H => subst eq'; let .lam _ _ h1 _ h2 _ := H; exact ⟨⟨_, h1.hasType⟩, _, h2.hasType⟩

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.lam_inv (H : VExpr.WF env U Γ (.lam A body)) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) :=
  let ⟨_, H⟩ := H; HasType.lam_inv henv hΓ H

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.const_inv (H : env.HasType U Γ (.const c ls) V) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : VExpr.const c ls = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H => subst eq'; let .const h1 h2 h3 .. := H; exact ⟨_, h1, h2, h3⟩

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.const_inv (H : VExpr.WF env U Γ (.const c ls)) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars :=
  let ⟨_, H⟩ := H; HasType.const_inv henv hΓ H

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
/-- Recover the declaration-derived schema and actual universe specialization
of a typed abstract eliminator, even after conversion of its type. -/
theorem HasType.elim_inv (H : env.HasType U Γ (.elim block slot packed) V) :
    ∃ (schema : InductiveSignature.CaseSchema) (owner : Fin schema.signature.families.size)
      (type : VExpr) (target : VLevel) (levels : List VLevel) (typeLevel : VLevel),
      slot = owner.val ∧ packed = target :: levels ∧
      env.eliminators block schema ∧ schema.genericType owner = some type ∧
      type.Closed ∧ schema.Permission U owner levels target ∧ typeLevel.WF U ∧
      env.HasType U Γ (type.instL (target :: levels)) (.sort typeLevel) := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : VExpr.elim block slot packed = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H =>
    subst eq'
    cases H with
    | elim h1 h2 h3 h4 h5 h6 =>
      exact ⟨_, _, _, _, _, _, rfl, rfl, h1, h2, h3, h4, h5, h6.hasType⟩

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.bvar_inv (H : env.HasType U Γ (.bvar i) V) : ∃ A, Lookup Γ i A := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : VExpr.bvar i = e' at H
  induction H with cases eq
  | defeq _ _ _ _ _ _ _ ih => exact ih hΓ rfl eq'
  | base H => subst eq'; let .bvar h1 .. := H; exact ⟨_, h1⟩

/-- **Simultaneous substitution for the strong judgment**, the three-way left/right/cross bundle. -/
theorem IsDefEqStrong.substEq' (henv : Ordered env)
    (hΓ : CtxStrong env U Γ) (hΓ₀ : CtxStrong env U Γ₀)
    (W : Ctx.SubstEq env U Γ₀ σ σ' Γ) (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ₀ (e1.subst σ) (e1.subst σ') (A.subst σ) ∧
    env.IsDefEqStrong U Γ₀ (e2.subst σ) (e2.subst σ') (A.subst σ) ∧
    env.IsDefEqStrong U Γ₀ (e1.subst σ) (e2.subst σ') (A.subst σ) := by
  induction H generalizing Γ₀ σ σ' with
  | bvar h _ _ =>
    have s := (W.lookup h).strong henv hΓ₀.defeq; exact ⟨s, s, s⟩
  | sortDF hw hw' h =>
    have C : env.IsDefEqStrong U Γ₀ (.sort _) (.sort _) (.sort _) := .sortDF hw hw' h
    exact ⟨C.hasType.1, C.hasType.2, C⟩
  | symm _ ih => let ⟨l, r, c⟩ := ih hΓ hΓ₀ W; exact ⟨r, l, (r.trans c.symm).trans l⟩
  | trans _ _ ih1 ih2 =>
    let ⟨l1, _, c1⟩ := ih1 hΓ hΓ₀ W
    let ⟨l2, r2, c2⟩ := ih2 hΓ hΓ₀ W
    exact ⟨l1, r2, c1.trans (l2.symm.trans c2)⟩
  | defeqDF hu _ _ ih1 ih2 =>
    have hty := (ih1 hΓ hΓ₀ W.left).2.2
    let ⟨l2, r2, c2⟩ := ih2 hΓ hΓ₀ W
    exact ⟨.defeqDF hu hty l2, .defeqDF hu hty r2, .defeqDF hu hty c2⟩
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    let ⟨ihp, _, _⟩ := ih1 hΓ hΓ₀ W
    let ⟨ihh, _, _⟩ := ih2 hΓ hΓ₀ W
    let ⟨ihh', _, _⟩ := ih3 hΓ hΓ₀ W
    exact ⟨ihh, ihh', .proofIrrel ihp.hasType.1 ihh.hasType.1 ihh'.hasType.2⟩
  | @constDF c ci ls ls' u _ h1 hWls hWls' hlen hFf hu hcty _ _ _ =>
    have hcl : (VExpr.instL ls ci.type).ClosedN 0 := (henv.closedC h1).instL
    rw [show (VExpr.instL ls ci.type).subst σ = VExpr.instL ls ci.type from hcl.subst_eq .zero]
    have C : env.IsDefEqStrong U Γ₀ (.const c ls) (.const c ls') (VExpr.instL ls ci.type) :=
      .constDF h1 hWls hWls' hlen hFf hu hcty (hcty.weak0 henv)
    exact ⟨C.hasType.1, C.hasType.2, C⟩
  | elimDF h1 h2 h3 h4 h5 h6 h7 _ ih =>
    have ht := (ih hΓ hΓ₀ W.left).2.2
    simp only [h3.instL.subst_eq .zero] at ht ⊢
    have C := IsDefEqStrong.elimDF h1 h2 h3 h4 h5 h6 h7 ht
    exact ⟨C.hasType.1, C.hasType.2, C⟩
  | elimIota h1 h2 h3 h4 h5 h6 _ _ _ ihT ihL ihR =>
    have ht := (ihT hΓ hΓ₀ W.left).1
    have hl := (ihL hΓ hΓ₀ W.left).1
    have hr := (ihR hΓ hΓ₀ W.left).1
    simp only [h4.1.instL.subst_eq .zero, h4.2.1.instL.subst_eq .zero,
      h4.2.2.instL.subst_eq .zero] at ht hl hr ⊢
    have C := IsDefEqStrong.elimIota h1 h2 h3 h4 h5 h6 ht hl hr
    exact ⟨C.hasType.1, C.hasType.2, C⟩
  | @appDF Γ' A u B v _ _ _ _ hu hv hA hB _ _ _ ihA ihB ihf iha ihBinst =>
    have hA' := (ihA hΓ hΓ₀ W.left).1
    have hΓ_A : CtxStrong env U (A.subst σ :: Γ₀) := ⟨hΓ₀, _, hA'⟩
    have hΓ_A_src : CtxStrong env U (A :: Γ') := ⟨hΓ, _, hA⟩
    have W_A : Ctx.SubstEq env U (A.subst σ :: Γ₀) σ.lift σ.lift (A :: Γ') :=
      W.left.lift henv hA.defeq
    have hB' := (ihB hΓ_A_src hΓ_A W_A).1
    have ⟨ihf_l, ihf_r, ihf_c⟩ := ihf hΓ hΓ₀ W
    have ⟨iha_l, iha_r, iha_c⟩ := iha hΓ hΓ₀ W
    have ⟨_, _, iha_cleft⟩ := iha hΓ hΓ₀ W.left
    have ih2_cons : ∀ {x y : VExpr}, env.IsDefEqStrong U Γ₀ x y (A.subst σ) →
        env.IsDefEqStrong U Γ₀ ((B.subst σ.lift).inst x) ((B.subst σ.lift).inst y) (.sort v) := by
      intro x y hxy
      have W_cons : Ctx.SubstEq env U Γ₀ (σ.cons x) (σ.cons y) (A :: Γ') := by
        refine .cons (by simpa using W.left) hA.defeq (by simpa using hxy.defeq)
      have := (ihB hΓ_A_src hΓ₀ W_cons).1
      rwa [← inst_lift_cons, ← inst_lift_cons] at this
    refine subst_inst ▸ ⟨?_, .defeqDF hv (ih2_cons iha_cleft.symm) ?_, ?_⟩
    · exact .appDF hu hv hA' hB' ihf_l iha_l (ih2_cons iha_l)
    · exact .appDF hu hv hA' hB' ihf_r iha_r (ih2_cons iha_r)
    · exact .appDF hu hv hA' hB' ihf_c iha_c (ih2_cons iha_c)
  | @projDF typeName info levels params index sourceMajor fieldType Γ' fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield hwf
      hField hLeft hRight hclosed hguard ihField ihLeft ihRight =>
    have hfield' := VProjectionInfo.fieldType_subst_some
      (typeName := typeName) (levels := levels) (params := params)
      (index := index) (major := sourceMajor) (result := fieldType)
      (substitution := σ) info hclosed hfield
    have hFieldσ := (ihField hΓ hΓ₀ W.left).1.hasType.1
    have leftσ := (ihLeft hΓ hΓ₀ W.left).2.2
    have leftσ' := (ihLeft hΓ hΓ₀ W).2.2
    have rightσ := (ihRight hΓ hΓ₀ W.left).2.2
    have rightσ' := (ihRight hΓ hΓ₀ W).2.2
    simp only [VExpr.subst_mkApps, List.map_append, VExpr.subst] at leftσ leftσ' rightσ rightσ'
    have mkProjection {left right : VExpr}
        (hleft : env.IsDefEqStrong U Γ₀ (sourceMajor.subst σ) left
          (VExpr.mkApps (.const typeName levels)
            (params.map (VExpr.subst · σ) ++ indexArgs.map (VExpr.subst · σ))))
        (hright : env.IsDefEqStrong U Γ₀ (sourceMajor.subst σ) right
          (VExpr.mkApps (.const typeName levels)
            (params.map (VExpr.subst · σ) ++ indexArgs.map (VExpr.subst · σ)))) :
        env.IsDefEqStrong U Γ₀
          (.proj typeName index left)
          (.proj typeName index right)
          (fieldType.subst σ) :=
      .projDF (info := info) (params := params.map (VExpr.subst · σ))
        (indexArgs := indexArgs.map (VExpr.subst · σ))
        hinfo hlevels huvars (by simpa using hparams) (by simpa using hindices)
        hfield' hwf hFieldσ hleft hright hclosed hguard
    exact ⟨mkProjection leftσ leftσ',
      mkProjection rightσ rightσ',
      mkProjection leftσ rightσ'⟩
  | @lamDF Γ' A A' u B v _ _ hu hv h1 _ _ _ _ ihA ihB ihB' ihbody ihbody' =>
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ihA hΓ hΓ₀ W
    have hA_in_Γ := h1.hasType.1
    have hA'_in_Γ := h1.hasType.2
    have hA_subst := ihA_l.hasType.1
    have hA_σ'_subst := ihA_l.hasType.2
    have hA'_subst := ihA_r.hasType.1
    have hA'_σ'_subst := ihA_r.hasType.2
    have hΓ_A_subst : CtxStrong env U (A.subst σ :: Γ₀) := ⟨hΓ₀, _, hA_subst⟩
    have hΓ_A_σ'_subst : CtxStrong env U (A.subst σ' :: Γ₀) := ⟨hΓ₀, _, hA_σ'_subst⟩
    have hΓ_A'_subst : CtxStrong env U (A'.subst σ :: Γ₀) := ⟨hΓ₀, _, hA'_subst⟩
    have hΓ_A'_σ'_subst : CtxStrong env U (A'.subst σ' :: Γ₀) := ⟨hΓ₀, _, hA'_σ'_subst⟩
    have hΓ_A_src : CtxStrong env U (A :: Γ') := ⟨hΓ, _, hA_in_Γ⟩
    have hΓ_A'_src : CtxStrong env U (A' :: Γ') := ⟨hΓ, _, hA'_in_Γ⟩
    have hAA'_σ := (ihA hΓ hΓ₀ W.left).2.2
    have W_A := W.lift henv hA_in_Γ.defeq
    have W_A_σ' := W.lift_at henv hA_in_Γ.defeq ihA_l.defeq
    have W_A' := W.lift henv hA'_in_Γ.defeq
    have W_A'_σ' := W.lift_at henv hA'_in_Γ.defeq ihA_r.defeq
    have W_A_to_A'σ' := W.lift_at henv hA_in_Γ.defeq ihA_c.defeq
    have W_left_A'σ := W.left.lift_at henv hA_in_Γ.defeq hAA'_σ.defeq
    -- `B` typed (reflexively) at the four domain/substitution variants.
    have B_Aσ := (ihB hΓ_A_src hΓ_A_subst W_A).1.hasType.1
    have B_Aσ' := (ihB hΓ_A_src hΓ_A_σ'_subst W_A_σ').1.hasType.1
    have B_A'σ := (ihB hΓ_A_src hΓ_A'_subst W_left_A'σ).1.hasType.1
    have B_A'σ' := (ihB hΓ_A_src hΓ_A'_σ'_subst W_A_to_A'σ').1.hasType.1
    -- `body`/`body'` congruences at the needed variants.
    have body_Aσ := (ihbody hΓ_A_src hΓ_A_subst W_A).1
    have body_Aσ' := (ihbody hΓ_A_src hΓ_A_σ'_subst W_A_σ').1
    have body_cross_Aσ := (ihbody hΓ_A_src hΓ_A_subst W_A).2.2
    have body_cross_A'σ' := (ihbody hΓ_A_src hΓ_A'_σ'_subst W_A_to_A'σ').2.2
    have body'_A'σ := (ihbody' hΓ_A'_src hΓ_A'_subst W_A').2.1
    have body'_A'σ' := (ihbody' hΓ_A'_src hΓ_A'_σ'_subst W_A'_σ').2.1
    refine ⟨?_, .defeqDF (u := u.imax v) ⟨hu, hv⟩
      (.forallEDF hu hv hAA'_σ.symm B_A'σ B_Aσ) ?_, ?_⟩
    · exact .lamDF hu hv ihA_l B_Aσ B_Aσ' body_Aσ body_Aσ'
    · exact .lamDF hu hv ihA_r B_A'σ B_A'σ' body'_A'σ body'_A'σ'
    · exact .lamDF hu hv ihA_c B_Aσ B_A'σ' body_cross_Aσ body_cross_A'σ'
  | @forallEDF Γ' A A' u _ _ v hu hv h1 _ _ ihA ihbody ihbody' =>
    let ⟨ihA_l, ihA_r, ihA_c⟩ := ihA hΓ hΓ₀ W
    have hA_in_Γ := h1.hasType.1
    have hA'_in_Γ := h1.hasType.2
    have hA_subst := ihA_l.hasType.1
    have hA_σ'_subst := ihA_l.hasType.2
    have hA'_subst := ihA_r.hasType.1
    have hA'_σ'_subst := ihA_r.hasType.2
    have hΓ_A_subst : CtxStrong env U (A.subst σ :: Γ₀) := ⟨hΓ₀, _, hA_subst⟩
    have hΓ_A_σ'_subst : CtxStrong env U (A.subst σ' :: Γ₀) := ⟨hΓ₀, _, hA_σ'_subst⟩
    have hΓ_A'_subst : CtxStrong env U (A'.subst σ :: Γ₀) := ⟨hΓ₀, _, hA'_subst⟩
    have hΓ_A'_σ'_subst : CtxStrong env U (A'.subst σ' :: Γ₀) := ⟨hΓ₀, _, hA'_σ'_subst⟩
    have hΓ_A_src : CtxStrong env U (A :: Γ') := ⟨hΓ, _, hA_in_Γ⟩
    have hΓ_A'_src : CtxStrong env U (A' :: Γ') := ⟨hΓ, _, hA'_in_Γ⟩
    have W_A := W.lift henv hA_in_Γ.defeq
    have W_A_σ' := W.lift_at henv hA_in_Γ.defeq ihA_l.defeq
    have W_A' := W.lift henv hA'_in_Γ.defeq
    have W_A'_σ' := W.lift_at henv hA'_in_Γ.defeq ihA_r.defeq
    have W_A_to_A'σ' := W.lift_at henv hA_in_Γ.defeq ihA_c.defeq
    have body_Aσ := (ihbody hΓ_A_src hΓ_A_subst W_A).1
    have body_Aσ' := (ihbody hΓ_A_src hΓ_A_σ'_subst W_A_σ').1
    have body_cross_Aσ := (ihbody hΓ_A_src hΓ_A_subst W_A).2.2
    have body_cross_A'σ' := (ihbody hΓ_A_src hΓ_A'_σ'_subst W_A_to_A'σ').2.2
    have body'_A'σ := (ihbody' hΓ_A'_src hΓ_A'_subst W_A').2.1
    have body'_A'σ' := (ihbody' hΓ_A'_src hΓ_A'_σ'_subst W_A'_σ').2.1
    exact ⟨.forallEDF hu hv ihA_l body_Aσ body_Aσ',
      .forallEDF hu hv ihA_r body'_A'σ body'_A'σ',
      .forallEDF hu hv ihA_c body_cross_Aσ body_cross_A'σ'⟩
  | @beta Γ' A u B v e e' hu hv hA _ _ _ _ _ ihA ihB ihe ihe' _ iheinst =>
    have hA'σ := (ihA hΓ hΓ₀ W.left).1
    have hΓ_A_src : CtxStrong env U (A :: Γ') := ⟨hΓ, _, hA⟩
    have hΓ_A_subst : CtxStrong env U (A.subst σ :: Γ₀) := ⟨hΓ₀, _, hA'σ⟩
    have hA_σ'_subst := (ihA hΓ hΓ₀ W).1.hasType.2
    have hΓ_A_σ'_subst : CtxStrong env U (A.subst σ' :: Γ₀) := ⟨hΓ₀, _, hA_σ'_subst⟩
    have W_A_left := W.left.lift henv hA.defeq
    have W_A := W.lift henv hA.defeq
    have W_A_σ' := W.lift_at henv hA.defeq (ihA hΓ hΓ₀ W).1.defeq
    have hBσ := (ihB hΓ_A_src hΓ_A_subst W_A_left).1
    have heσ := (ihe hΓ_A_src hΓ_A_subst W_A_left).1
    have he'σ := (ihe' hΓ hΓ₀ W.left).1
    -- `(B.subst σ.lift).inst _`-congruence, as in the `appDF` case.
    have ih2_cons : ∀ {x y : VExpr}, env.IsDefEqStrong U Γ₀ x y (A.subst σ) →
        env.IsDefEqStrong U Γ₀ ((B.subst σ.lift).inst x) ((B.subst σ.lift).inst y) (.sort v) := by
      intro x y hxy
      have W_cons : Ctx.SubstEq env U Γ₀ (σ.cons x) (σ.cons y) (A :: Γ') := by
        refine .cons (by simpa using W.left) hA.defeq (by simpa using hxy.defeq)
      have := (ihB hΓ_A_src hΓ₀ W_cons).1
      rwa [← inst_lift_cons, ← inst_lift_cons] at this
    -- diagonal-σ beta reduction
    have H_σ : env.IsDefEqStrong U Γ₀ ((VExpr.app (VExpr.lam A e) e').subst σ)
        ((e.inst e').subst σ) ((B.inst e').subst σ) := by
      show env.IsDefEqStrong U Γ₀
        (VExpr.app (VExpr.lam (A.subst σ) (e.subst σ.lift)) (e'.subst σ)) _ _
      rw [show ((e.inst e').subst σ) = (e.subst σ.lift).inst (e'.subst σ) from subst_inst,
          show ((B.inst e').subst σ) = (B.subst σ.lift).inst (e'.subst σ) from subst_inst]
      exact .beta hu hv hA'σ hBσ heσ he'σ (ih2_cons he'σ)
        (subst_inst ▸ subst_inst ▸ (iheinst hΓ hΓ₀ W.left).1)
    have R := (iheinst hΓ hΓ₀ W).1
    -- redex congruence for the left diagonal
    have B_Aσ := (ihB hΓ_A_src hΓ_A_subst W_A).1.hasType.1
    have B_Aσ' := (ihB hΓ_A_src hΓ_A_σ'_subst W_A_σ').1.hasType.1
    have e_Aσ := (ihe hΓ_A_src hΓ_A_subst W_A).1
    have e_Aσ' := (ihe hΓ_A_src hΓ_A_σ'_subst W_A_σ').1
    have ⟨iha_l, _, _⟩ := ihA hΓ hΓ₀ W
    have ⟨ihe'_l, _, _⟩ := ihe' hΓ hΓ₀ W
    have L : env.IsDefEqStrong U Γ₀ ((VExpr.app (VExpr.lam A e) e').subst σ)
        ((VExpr.app (VExpr.lam A e) e').subst σ') ((B.inst e').subst σ) := by
      show env.IsDefEqStrong U Γ₀
        (VExpr.app (VExpr.lam (A.subst σ) (e.subst σ.lift)) (e'.subst σ)) _ _
      rw [show ((B.inst e').subst σ) = (B.subst σ.lift).inst (e'.subst σ) from subst_inst]
      exact .appDF hu hv hA'σ hBσ (.lamDF hu hv iha_l B_Aσ B_Aσ' e_Aσ e_Aσ') ihe'_l
        (ih2_cons ihe'_l)
    exact ⟨L, R, H_σ.trans R⟩
  | @eta Γ' A u B v e hu hv hA hB _ he _ _ ihA ihB _ ihe _ _ =>
    -- normal form of substituting into the eta-expanded lambda
    have h_lam_eq : ∀ τ : VExpr.Subst,
        (VExpr.lam A (.app e.lift (.bvar 0))).subst τ =
          .lam (A.subst τ) (.app (e.subst τ).lift (.bvar 0)) := by
      intro τ
      show VExpr.lam (A.subst τ) (.app (e.lift.subst τ.lift) ((VExpr.bvar 0).subst τ.lift)) = _
      rw [lift_subst_lift]; rfl
    have hΓ_A_src : CtxStrong env U (A :: Γ') := ⟨hΓ, _, hA⟩
    have iha_l := (ihA hΓ hΓ₀ W).1
    -- σ-diagonal eta
    have hA_σ := (ihA hΓ hΓ₀ W).1.hasType.1
    have hΓ_A_subst : CtxStrong env U (A.subst σ :: Γ₀) := ⟨hΓ₀, _, hA_σ⟩
    have W_A_σ := W.left.lift henv hA.defeq
    have W_A_cross := W.lift henv hA.defeq
    have hB_σ := (ihB hΓ_A_src hΓ_A_subst W_A_σ).1.hasType.1
    have he_σ := (ihe hΓ hΓ₀ W).1.hasType.1
    have H_σ : env.IsDefEqStrong U Γ₀
        ((VExpr.lam A (.app e.lift (.bvar 0))).subst σ) (e.subst σ) ((A.forallE B).subst σ) :=
      (h_lam_eq σ) ▸ .eta hu hv hA_σ hB_σ (hB_σ.weakN henv (.succ .one))
        he_σ (he_σ.weakN henv .one) (hA_σ.weakN henv .one)
    have R := (ihe hΓ hΓ₀ W).1
    -- σ'-diagonal eta
    have hA_σ' := iha_l.hasType.2
    have hΓ_A_σ'_subst : CtxStrong env U (A.subst σ' :: Γ₀) := ⟨hΓ₀, _, hA_σ'⟩
    have W_A_σ' := W.lift_at henv hA.defeq iha_l.defeq
    have hB_cross_Aσ := (ihB hΓ_A_src hΓ_A_subst W_A_cross).2.2
    have hB_cross_Aσ' := (ihB hΓ_A_src hΓ_A_σ'_subst W_A_σ').2.2
    have hB_σ' := (ihB hΓ_A_src hΓ_A_σ'_subst W_A_σ').1.hasType.2
    -- the two forallE types are defeq; coerce e's σ'-typing across
    have hTeq := IsDefEqStrong.forallEDF hu hv iha_l hB_cross_Aσ hB_cross_Aσ'
    have he_σ' := IsDefEqStrong.defeqDF (u := u.imax v) ⟨hu, hv⟩ hTeq (ihe hΓ hΓ₀ W).1.hasType.2
    have H_σ' : env.IsDefEqStrong U Γ₀
        ((VExpr.lam A (.app e.lift (.bvar 0))).subst σ') (e.subst σ') ((A.forallE B).subst σ') :=
      (h_lam_eq σ') ▸ .eta hu hv hA_σ' hB_σ' (hB_σ'.weakN henv (.succ .one))
        he_σ' (he_σ'.weakN henv .one) (hA_σ'.weakN henv .one)
    exact ⟨H_σ.trans (R.trans
        (IsDefEqStrong.defeqDF (u := u.imax v) ⟨hu, hv⟩ hTeq.symm H_σ'.symm)),
      R, H_σ.trans R⟩
  | @extra df ls u _ h1 hWls hlen hu htype hlhs hrhs _ _ _ _ _ _ _ =>
    have et : ∀ τ, (VExpr.instL ls df.type).subst τ = VExpr.instL ls df.type :=
      fun _ => (htype.defeq.closedN henv ⟨⟩).subst_eq .zero
    have el : ∀ τ, (VExpr.instL ls df.lhs).subst τ = VExpr.instL ls df.lhs :=
      fun _ => (hlhs.defeq.closedN henv ⟨⟩).subst_eq .zero
    have er : ∀ τ, (VExpr.instL ls df.rhs).subst τ = VExpr.instL ls df.rhs :=
      fun _ => (hrhs.defeq.closedN henv ⟨⟩).subst_eq .zero
    simp only [et, el, er]
    have C : env.IsDefEqStrong U Γ₀ (VExpr.instL ls df.lhs) (VExpr.instL ls df.rhs)
        (VExpr.instL ls df.type) :=
      .extra h1 hWls hlen hu htype hlhs hrhs (hlhs.weak0 henv) (hrhs.weak0 henv)
    exact ⟨C.hasType.1, C.hasType.2, C⟩
  | projIota h1 _ h3 _ ih1 ih2 =>
    have l1 := (ih1 hΓ hΓ₀ W).1
    have l2 := (ih2 hΓ hΓ₀ W).1
    have t1 := (ih1 hΓ hΓ₀ W.left).1
    have t2 := (ih2 hΓ hΓ₀ W.left).1
    simp only [VExpr.subst_mkApps, VExpr.subst] at l1 t1 ⊢
    exact ⟨l1, l2, (IsDefEqStrong.projIota h1 t1 (by simp [h3]) t2).trans l2⟩
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    have l1 := (ih1 hΓ hΓ₀ W).1
    have l2 := (ih2 hΓ hΓ₀ W).1
    have t1 := (ih1 hΓ hΓ₀ W.left).1
    have t2 := (ih2 hΓ hΓ₀ W.left).1
    simp only [VExpr.subst_mkApps, VExpr.subst, List.map_append, List.map_map,
      Function.comp_def] at l1 l2 t1 t2 ⊢
    exact ⟨l2, l1, (IsDefEqStrong.structEta h1 (by simpa using h2) h3 t1 t2).trans l1⟩
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    have l1 := (ih1 hΓ hΓ₀ W).1
    have l2 := (ih2 hΓ hΓ₀ W).1
    simp only [VExpr.subst_mkApps, VExpr.subst] at l1 l2 ⊢
    exact ⟨l1, l2, .unitLike h1 (by simpa using h2) h3 h4 l1.hasType.1 l2.hasType.2⟩

/-- Simultaneous substitution of a related pair `σ ≡ σ'` into a strong defeq: the cross
projection of `substEq'`. -/
theorem IsDefEqStrong.subst (henv : Ordered env)
    (hΓ : CtxStrong env U Γ) (hΓ₀ : CtxStrong env U Γ₀)
    (W : Ctx.SubstEq env U Γ₀ σ σ' Γ) (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ₀ (e1.subst σ) (e2.subst σ') (A.subst σ) :=
  (H.substEq' henv hΓ hΓ₀ W).2.2

/-- Simultaneous substitution of a related pair `σ ≡ σ'` into a (weak) defeq, generalizing
`IsDefEq.instDF` from one variable to a whole substitution. Assumes both contexts are well
formed, as elsewhere in `Typing.Lemmas`; proved via the strong judgment. -/
theorem IsDefEq.substDF (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (W : Ctx.SubstEq env U Γ₀ σ σ' Γ) (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U Γ₀ (e1.subst σ) (e2.subst σ') (A.subst σ) :=
  ((H.strong henv hΓ).subst henv (.strong henv hΓ) (.strong henv hΓ₀) W).defeq

variable! (henv : Ordered env) in
theorem IsDefEq.subst (W : Ctx.SubstEq env U Γ₀ σ σ Γ)
    (H : env.IsDefEq U Γ e1 e2 A) (hΓ₀ : OnCtx Γ₀ (env.IsType U) := by trivial) :
    env.IsDefEq U Γ₀ (e1.subst σ) (e2.subst σ) (A.subst σ) := H.substDF henv W.wf hΓ₀ W

variable! (henv : Ordered env) in
theorem HasType.subst (W : Ctx.SubstEq env U Γ₀ σ σ Γ)
    (H : env.HasType U Γ e A) (hΓ₀ : OnCtx Γ₀ (env.IsType U) := by trivial) :
    env.HasType U Γ₀ (e.subst σ) (A.subst σ) := H.substDF henv W.wf hΓ₀ W

variable! (henv : Ordered env) in
theorem IsDefEqU.subst (W : Ctx.SubstEq env U Γ₀ σ σ Γ)
    (H : env.IsDefEqU U Γ e1 e2) (hΓ₀ : OnCtx Γ₀ (env.IsType U) := by trivial) :
    env.IsDefEqU U Γ₀ (e1.subst σ) (e2.subst σ) :=
  let ⟨_, h⟩ := H; ⟨_, h.substDF henv W.wf hΓ₀ W⟩

variable! (henv : Ordered env) in
theorem IsType.subst (W : Ctx.SubstEq env U Γ₀ σ σ Γ)
    (H : env.IsType U Γ A) (hΓ₀ : OnCtx Γ₀ (env.IsType U) := by trivial) :
    env.IsType U Γ₀ (A.subst σ) :=
  let ⟨_, h⟩ := H; ⟨_, h.substDF henv W.wf hΓ₀ W⟩
