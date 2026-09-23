import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)
  /-- Registering a pattern-reduction rule (an ι rule) changes neither the constant
  map nor the model's constants. -/
  | pat : Aligned C venv → Aligned C (venv.addPat p r)
  /-- An inductive block, inserted as a whole: the map gets the block's constants `cis`
  (fresh, with distinct names, in the order the kernel inserts them), the model the
  matching constants `l`, and each constant translates in the model environment holding
  the whole block — the types of a block's recursors mention all of its type formers and
  constructors, so a nested mutual block, which the kernel inserts type by type, cannot
  be aligned one constant at a time. -/
  | block {cis : List ConstantInfo} {l : List (Name × VConstant)} :
    Aligned C venv →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup →
    List.Forall₂ (fun ci b => TrConstant safety venv' ci b.2 ∧ ci.name = b.1) cis l →
    l.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) venv = some venv' →
    Aligned (insertConsts C cis) venv'

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih | pat _ ih => exact ih
  | block _ hfr hnd _ _ ih => exact insertConsts_wf ih hfr hnd

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih | pat _ ih => exact ih
  | block H hfr hnd hblk hfold ih =>
    constructor
    · rintro ⟨ci, hci, hs⟩
      rcases insertConsts_find? H.map_wf hfr hnd hci with h | ⟨hmem, hn⟩
      · obtain ⟨ci', hci'⟩ := ih.1 ⟨ci, h, hs⟩
        exact ⟨ci', (VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold).constants hci'⟩
      · obtain ⟨b, hb, -, hbn⟩ := hblk.forall_exists_l ci hmem
        refine ⟨b.2, ?_⟩
        rw [← hn, hbn]
        exact VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb
    · rintro ⟨ci', hci'⟩
      rcases VEnv.addConst_foldlM_constants_inv (nm := Prod.fst) (ci := Prod.snd) hfold hci'
        with h | ⟨b, hb, hbn, -⟩
      · obtain ⟨ci, hci, hs⟩ := ih.2 ⟨ci', h⟩
        refine ⟨ci, insertConsts_find?_mono H.map_wf.map₂ (fun d hd e => ?_) hci, hs⟩
        have := hfr d hd; rw [e, hci] at this; cases this
      · obtain ⟨ci, hci, htr, hcn⟩ := hblk.forall_exists_r b hb
        refine ⟨ci, ?_, htr.1⟩
        rw [← hbn, ← hcn]; exact insertConsts_find?_self H.map_wf hfr hnd ci hci

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

/-- Registering the ι rules of a declaration keeps `Aligned`: every step is an `addPat`. -/
theorem Aligned.addRules {decl : VInductDecl} (h : Aligned safety C venv)
    (hP : decl.addRules venv = some venv') : Aligned safety C venv' := by
  unfold VInductDecl.addRules at hP
  refine VEnv.foldlM_inv (P := Aligned safety C) (fun r _ _ _ hA hfold => ?_) h hP
  refine VEnv.foldlM_inv (P := Aligned safety C) (fun ru _ _ _ hA' hstep => ?_) hA hfold
  unfold VEnv.addRecRule at hstep; split at hstep
  · cases hstep; exact hA'.pat
  · cases hstep

/-- Adding an inductive block keeps `Aligned`: the constant stages form one `Aligned.block`
step — the kernel inserts the block's constants in `H.order`, the model in stage order
(`VInductDecl.consts`, which `addTypesCtorsRecs` folds over), and an `addConst` fold does
not depend on its order (`VEnv.addConst_foldlM_perm`); each constant translates in the
environment holding the whole block (`H.envR`). The ι-rule stage is `Aligned.addRules`. -/
theorem Aligned.addInduct (H : AddInduct safety C₁ venv₁ decl C₂ venv₂)
    (h : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  have leT : H.envT ≤ H.envR := (VEnv.addCtors_le H.stC).trans (VEnv.addRecs_le H.stR)
  -- the block's constants, kernel side and model side, matched by kind
  have hpair : List.Forall₂ (fun ci (b : Name × VConstant) =>
      TrConstant safety H.envR ci b.2 ∧ ci.name = b.1)
      (AddInduct.consts H.ivals H.rvals) decl.consts := by
    unfold AddInduct.consts VInductDecl.consts
    refine List.Forall₂.append (List.Forall₂.append ?_ ?_) ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact H.types.imp fun _ _ ht =>
        ⟨ht.tr.1.mono ((VEnv.addTypes_le H.stT).trans leT), ht.tr.2⟩
    · rw [← List.map_flatMap, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact (List.Forall₂.flatMap (fun _ _ ht => ht.ctors) H.types).imp fun _ _ hc =>
        ⟨hc.1.1.mono leT, hc.1.2⟩
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact H.recs.imp fun _ _ hr => ⟨hr.tr.1.mono (VEnv.addRecs_le H.stR), hr.tr.2⟩
  -- the same matching, in the kernel's insertion order
  obtain ⟨l', hl', hpair'⟩ := List.Forall₂.perm_left H.order_perm hpair
  have hfold : l'.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) venv₁ = some H.envR := by
    have := H.addTypesCtorsRecs
    rw [VInductDecl.addTypesCtorsRecs_eq] at this
    exact VEnv.addConst_foldlM_perm (nm := Prod.fst) (ci := Prod.snd) hl'.symm this
  rw [H.map_eq]
  exact (h.block H.order_fresh H.order_nodup hpair' hfold).addRules H.stP

theorem Aligned.addDefEqs {C : ConstMap} : ∀ {cis' : List VDefVal} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqs cis')
  | [], _, H => H
  | ci :: cis, venv, H => by
    show Aligned safety C (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis)
    exact Aligned.addDefEqs H.defeq

theorem Aligned.insertDefs : ∀ {cis : List DefinitionVal} {cis' : List VDefVal} {C venv venv'},
    Aligned safety C venv → (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    List.Forall₂ (fun ci ci' => TrConstVal safety venv (.defnInfo ci) ci'.toVConstVal) cis cis' →
    venv.addConsts cis' = some venv' → Aligned safety (insertDefs C cis) venv'
  | [], _, _, _, _, H, _, _, hblk, e => by
    cases hblk; simp [VEnv.addConsts] at e; cases e; exact H
  | ci :: cis, _, C, venv, _, H, hnd, hfr, hblk, e => by
    cases hblk with | @cons _ ci' _ _ htr hblk => ?_
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    have hname := htr.2
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1' : venv.addConst ci.name ci'.toVConstant = some venv₁ := by rw [hname]; exact h1
    show Aligned safety
      (_root_.Lean4Lean.insertDefs (SMap.insert C ci.name (.defnInfo ci)) cis) _
    refine Aligned.insertDefs (H.const (hfr _ (.head _)) htr.1 h1' rfl) hnd.2
      (fun c hc => ?_) (Lean4Lean.List.Forall₂.imp
        (fun _ _ h => h.mono (VEnv.addConst_le h1')) hblk) h2
    rw [H.map_wf.find?_insert]
    have : ¬ (ci.name == c.name) = true := by
      simp only [beq_iff_eq]; intro h
      exact hnd.1 ⟨c, hc, h.symm⟩
    simp [this]
    exact hfr c (.tail _ hc)

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | ignore h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | thm h1 h2 _ _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | mutualDef hblk hnd hfr _ hadd _ _ ih =>
    exact Aligned.addDefEqs <| ih.insertDefs hnd hfr
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) hblk) hadd
  | quot _ h _ ih => exact ih.addQuot h
  | induct _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

/-! ### Recursor lookup across the quotient constants

`pats_iota'` (below) pulls a `recInfo` lookup back across a `quot` step: `addQuot`
registers only `quotInfo` constants. -/

/-- Pull a `recInfo` lookup back across one fresh non-`recInfo` insertion: since
the inserted value is not a `recInfo`, a `recInfo` resolved in the extended map
was already resolved before the insertion. -/
theorem pull_recInfo {m : ConstMap} {name recName : Name} {q : ConstantInfo}
    {rval : RecursorVal} (wf : m.WF) (hq : ∀ v, q ≠ .recInfo v)
    (h : (m.insert name q).find? recName = some (.recInfo rval)) :
    m.find? recName = some (.recInfo rval) := by
  rw [wf.find?_insert] at h; split at h
  · exact absurd (Option.some.inj h) (hq rval)
  · exact h

/-- Pull-back combinator for one `AddQuot1` step: the inserted quotient constant
is a `quotInfo`, so a `recInfo` lookup passes through it. -/
theorem AddQuot1.pull {P : ConstMap → VEnv → Prop} {name kind ci' recName rval}
    (H1 : ∀ m env, m.WF → P m env → m.find? recName = some (.recInfo rval))
    (m env) (wf : m.WF) (H2 : AddQuot1 name kind ci' P m env) :
    m.find? recName = some (.recInfo rval) := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact pull_recInfo wf (fun _ => by nofun) (H1 _ _ (wf.insert _ _ h2) h4)

/-- A `recInfo` resolvable after adding the quotient constants was already
resolvable before: `addQuot` only registers `quotInfo` constants. -/
theorem AddQuot.pull {recName rval} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (hfind : C₂.find? recName = some (.recInfo rval)) :
    C₁.find? recName = some (.recInfo rval) := by
  dsimp [AddQuot] at H
  refine (AddQuot1.pull <| AddQuot1.pull <| AddQuot1.pull <| AddQuot1.pull ?_) _ _ wf H
  rintro m env hwf ⟨rfl, _⟩; exact hfind

/-- A constant other than a `quotInfo` resolvable after adding the quotient constants was
already resolvable before. -/
theorem AddQuot.pull_of {x ci} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (hq : ∀ v, ci ≠ .quotInfo v) (hfind : C₂.find? x = some ci) : C₁.find? x = some ci := by
  have step {P : ConstMap → VEnv → Prop} {name kind ci'}
      (H1 : ∀ m env, m.WF → P m env → m.find? x = some ci) (m env) (wf : m.WF)
      (H2 : AddQuot1 name kind ci' P m env) : m.find? x = some ci := by
    let ⟨_, _, _, _, h2, _, h4⟩ := H2
    have h := H1 _ _ (wf.insert _ _ h2) h4
    rw [wf.find?_insert] at h; split at h
    · exact absurd (Option.some.inj h).symm (hq _)
    · exact h
  dsimp [AddQuot] at H
  refine (step <| step <| step <| step ?_) _ _ wf H
  rintro m env _ ⟨rfl, _⟩; exact hfind

/-- Inserting a whole block of definitions preserves constant-map well-formedness,
provided every name is fresh and the block has no duplicate names. -/
theorem insertDefs_wf : ∀ {cis : List DefinitionVal} {C : ConstMap}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup → (insertDefs C cis).WF
  | [], _, hC, _, _ => hC
  | d :: ds, C, hC, hfr, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine insertDefs_wf (cis := ds) (hC.insert _ _ (hfr _ (.head _))) (fun e he => ?_) hnd.2
    rw [hC.find?_insert, if_neg]; · exact hfr e (.tail _ he)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (List.mem_map.2 ⟨e, he, hh.symm⟩)

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩
  | pat h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addPat_le⟩
  | block H hfr hnd hblk hfold ih =>
    rcases insertConsts_find? H.map_wf hfr hnd h with h' | ⟨hmem, hn⟩
    · exact mono (VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold) (ih h')
    · obtain ⟨b, hb, htr, hbn⟩ := hblk.forall_exists_l ci hmem
      refine ⟨b.2, ?_, htr⟩
      rw [← hn, hbn]
      exact VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩
  | pat h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addPat_le⟩
  | block H hfr hnd hblk hfold ih =>
    rcases insertConsts_find? H.map_wf hfr hnd h with h' | ⟨hmem, hn⟩
    · rcases VEnv.addConst_foldlM_constants_inv (nm := Prod.fst) (ci := Prod.snd) hfold hs
        with hs' | ⟨b, hb, hbn, -⟩
      · obtain ⟨h1, h2⟩ := ih h' hs'
        exact ⟨h1, h2.mono (VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold)⟩
      · exfalso
        obtain ⟨d, hd, -, hdn⟩ := hblk.forall_exists_r b hb
        have := hfr d hd; rw [hdn, hbn, h'] at this; cases this
    · obtain ⟨b, hb, htr, hbn⟩ := hblk.forall_exists_l ci hmem
      have := VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb
      rw [← hbn, hn, hs] at this
      cases this
      exact ⟨hn, htr⟩

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem VEnv.addDefEqs_self : ∀ {cis' : List VDefVal} {venv : VEnv} {ci'}, ci' ∈ cis' →
    (venv.addDefEqs cis').defeqs ci'.toDefEq
  | ci :: cis, venv, _, hc => by
    show (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis).defeqs _
    cases hc with
    | head => exact VEnv.addDefEqs_le.defeqs VEnv.addDefEq_self
    | tail _ hc => exact VEnv.addDefEqs_self hc

theorem insertDefs_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertDefs C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ ConstantInfo.defnInfo d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    have h : (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci := h
    rcases insertDefs_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with h | ⟨e, he, h1, h2⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨d, .head _, by simpa using hb, rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, h1, h2⟩

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    have' le := (VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, rfl, rfl⟩
    · exact (ih h).mono le
    · obtain ⟨d', hd', htr, hval⟩ := Lean4Lean.List.Forall₂.forall_exists_l hblk _ hd
      cases hv
      have hdefeq := VEnv.IsDefEq.extra0 (VEnv.addDefEqs_self hd')
        ((H.mutualDef hblk hnd hfr ‹_› hadd ‹_›).wf.ordered.defEqWF (VEnv.addDefEqs_self hd'))
      let ⟨⟨b1, b2, b3⟩, b4⟩ := htr
      exact ⟨_, hval.mono VEnv.addDefEqs_le, b2.symm ▸ b4.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | thm h2 h3 h4 h5 h1 H ih =>
    have' le := VEnv.addConst_le h1
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      dsimp only [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal] at b2 b4 ⊢
      have hp := h5.mono le
      have hb := h4.mono le
      have hc := VEnv.HasType.const0 (VEnv.addConst_self h1) ⟨_, hp⟩
      rw [b4] at hc
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ?_⟩
      exact ⟨_, .proofIrrel hp hb hc⟩
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | induct _ hadd H ih =>
    -- The registered constants carry no delta-value, so `hv` forces `name` to have
    -- been present already in `C` (`AddInduct.value_find`); then `ih` applies.
    exact (ih (hadd.value_find H.map_wf h hv)).mono hadd.le

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv

/-! ### Forward `find?` transport across fresh insertions

A constant already resolvable stays resolvable, to the same value, across insertions of
names it does not carry (`SMap.find?_insert_of_fresh`, `SMap.insertList_find?_mono`,
`AddInduct.find?_mono` in `Basic.lean`); here for `insertDefs` and `AddQuot`. -/

theorem insertDefs_find?_mono {cis : List DefinitionVal} {C : ConstMap} {x v} (wf : C.WF)
    (hfr : ∀ d ∈ cis, C.find? d.name = none) (h : C.find? x = some v) :
    (insertDefs C cis).find? x = some v := by
  unfold insertDefs
  refine SMap.insertList_find?_mono (nm := (·.name)) (val := (.defnInfo ·)) wf.map₂
    (fun d hd hx => ?_) h
  have := hfr d hd; rw [hx, h] at this; cases this

theorem AddQuot1.find?_mono {P : ConstMap → VEnv → Prop} {Q : Prop} {name kind ci' x v}
    (H1 : ∀ m env, m.WF → m.find? x = some v → P m env → Q)
    (m env) (wf : m.WF) (h : m.find? x = some v) (H2 : AddQuot1 name kind ci' P m env) : Q := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact H1 _ _ (wf.insert _ _ h2) (SMap.find?_insert_of_fresh wf.map₂ h2 h) h4

/-- A constant resolvable before adding the quotient constants is still resolvable, to
the same value, afterwards. -/
theorem AddQuot.find?_mono {x v} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (h : C₁.find? x = some v) : C₂.find? x = some v := by
  dsimp [AddQuot] at H
  refine (AddQuot1.find?_mono <| AddQuot1.find?_mono <| AddQuot1.find?_mono <|
    AddQuot1.find?_mono ?_) _ _ wf h H
  rintro m env _ h ⟨rfl, _⟩; exact h

/-! ### The ι-reduction interface -/

/-- `TrEnv'`-level ι-rule lookup with the registered witness named: the reduct is
`iotaRHS` at the recursor's telescope split and the constructor's parameter count
(`cval.numParams`, read off the constructor's own `ctorInfo`), over a template `rhs`
translating the kernel rule's reduct; the check is trivial (so `iota_defeq` runs with
`chk := []`). -/
theorem TrEnv'.pats_iota' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv' safety C Q venv)
    (hrec : C.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      C.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true) := by
  induction H with
  | empty => simp [SMap.find?] at hrec
  | ignore h1 h2 h3 ih =>
    rw [h3.map_wf.find?_insert] at hrec; split at hrec
    · injection hrec with hrec; subst hrec; exact absurd hsafe h2
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h3.map_wf.map₂ h1 hct, htr, hp⟩
  | thm _ h2 _ _ h5 h6 ih =>
    rw [h6.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h5
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h6.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | mutualDef _ hnd hfr _ hadd _ h7 ih =>
    rcases insertDefs_find? h7.map_wf hfr hnd hrec with hrec' | ⟨d, _, _, hd⟩
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec'
      exact ⟨cval, rhs, hc, insertDefs_find?_mono h7.map_wf hfr hct,
        htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le),
        ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le).pats hp⟩
    · exact absurd hd (by nofun)
  | «axiom» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | defn _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le),
        ((VEnv.addConst_le h4).trans VEnv.addDefEq_le).pats hp⟩
  | «opaque» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | quot _ h2 h3 ih =>
    obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih (h2.pull h3.map_wf hrec)
    exact ⟨cval, rhs, hc, h2.find?_mono h3.map_wf hct, htr.mono h2.le, h2.le.pats hp⟩
  | induct _ hadd h3 ih =>
    rcases hadd.rec_find h3.map_wf hrec with
      hC | ⟨r, hr, hname, _, hpar, hmot, hmin, hind, hrules⟩
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hC
      exact ⟨cval, rhs, hc, hadd.find?_mono h3.map_wf hct, htr.mono hadd.le,
        hadd.le.pats hp⟩
    · obtain ⟨hctor, hmem⟩ : rule.ctor = cName ∧ rule ∈ rval.rules :=
        ⟨by simpa using List.find?_some hrule, List.mem_of_find?_eq_some hrule⟩
      obtain ⟨ru, hru, hructor, hrunf, ⟨cval, hcfind, hcnp⟩, hclosed, hrutr⟩ := hrules rule hmem
      refine ⟨cval, ru.rhs, hclosed, by rw [← hctor]; exact hcfind, hrutr, ?_⟩
      rw [← hname, ← hpar, ← hmot, ← hmin, ← hind, ← hrunf, ← hctor, ← hructor, ← hcnp]
      exact VEnv.addInduct_pat hr hru hclosed hadd.env_eq

/-- `TrEnv'.pats_iota'` against the environment's own `find?`: the ι rule of a recursor
rule resolvable in `env` is registered in the translated environment's `pats`. -/
theorem TrEnv.pats_iota' {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      env.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true) := by
  have h : env.constants.find?' recName = some (.recInfo rval) := hrec
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := TrEnv'.pats_iota' H h hrule hsafe
  refine ⟨cval, rhs, hc, ?_, htr, hp⟩
  show env.constants.find?' cName = _
  rw [(TrEnv'.map_wf H).find?'_eq_find?]; exact hct

/-- Inverse of `pats_iota'`, at the `TrEnv'` level: every registered ι pattern
`SimplePattern.iota recName M cName N` comes from a kernel recursor `rval` (resolvable in
`C` under `recName`) and its rule for `cName` (found by constructor, uniquely by
`VInductDecl.WF.rules_nodup`), whose constructor `cval` is resolvable in `C`; `M` and `N`
are the kernel telescope split and `cval.numParams + rule.nfields`, and the registered
entry is `iotaRHS` at those counts over a translation of the kernel reduct, with the
trivial check. The reduct component is stated with `HEq` because its type mentions `M`
and `N`. -/
theorem TrEnv'.pats_iota_inv' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv' safety C Q venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed),
      C.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      C.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true := by
  induction H with
  | empty => exact (hp : False).elim
  | ignore h1 _ Hprev ih =>
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h1 hrec, hru,
      SMap.find?_insert_of_fresh wf h1 hct, hM, hN, htr, hh1, hh2⟩
  | «axiom» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h4), hh1, hh2⟩
  | defn _ h2 _ h4 Hprev ih =>
    rw [VEnv.addDefEq_pats, VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN,
      htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le), hh1, hh2⟩
  | mutualDef _ hnd hfr _ hadd _ Hprev ih =>
    rw [VEnv.addDefEqs_pats, VEnv.addConsts_pats hadd] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf
    exact ⟨rval, rule, cval, rhs, hc, insertDefs_find?_mono wf hfr hrec, hru,
      insertDefs_find?_mono wf hfr hct, hM, hN,
      htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le), hh1, hh2⟩
  | thm _ h2 _ _ h5 Hprev ih =>
    rw [VEnv.addConst_pats h5] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h5), hh1, hh2⟩
  | «opaque» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h4), hh1, hh2⟩
  | quot _ h2 Hprev ih =>
    rw [VEnv.addQuot_pats h2.to_addQuot] at hp
    obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hp
    have wf := Hprev.map_wf
    exact ⟨rval, rule, cval, rhs, hc, h2.find?_mono wf hrec, hru, h2.find?_mono wf hct, hM, hN,
      htr.mono h2.le, hh1, hh2⟩
  | induct hwf hadd Hprev ih =>
    have wf := Hprev.map_wf
    rcases VEnv.addInduct_pats_origin' hadd.env_eq hp with
      hold | ⟨rec, hrec, ru, hru, hc, e, he⟩
    · obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ := ih hold
      exact ⟨rval, rule, cval, rhs, hc, hadd.find?_mono wf hrec, hru, hadd.find?_mono wf hct,
        hM, hN, htr.mono hadd.le, hh1, hh2⟩
    · obtain ⟨hrn, hm, hcn, hkk⟩ := VEnv.iota_toPattern_inj e
      subst hrn hm hcn hkk
      cases e
      obtain ⟨rval, hrfind, hmaj, hpar, hmot, hmin, hind, hrules⟩ := hadd.rec_reg wf hwf hrec
      obtain ⟨rule, hfind, hnf, ⟨cval, hcfind, hcnp⟩, htr⟩ := hrules ru hru
      refine ⟨rval, rule, cval, ru.rhs, hc, hrfind, hfind, hcfind, ?_, by rw [← hcnp, ← hnf],
        htr, ?_, ?_⟩
      · rw [hmaj]; rfl
      · rw [← hpar, ← hmot, ← hmin, ← hind, ← hcnp, ← hnf]
        exact heq_of_eq (congrArg Prod.fst he)
      · exact congrArg Prod.snd he

/-- Inverse of `pats_iota'`; see `TrEnv'.pats_iota_inv'`. From a registered ι pattern,
recover the kernel recursor and its rule for the constructor, the constructor itself, the
full kernel telescope split behind `M`, the split of `N` into the constructor's parameter
and field counts, and the registered reduct. -/
theorem TrEnv.pats_iota_inv' {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv safety env venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed),
      env.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      env.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true := by
  obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ :=
    TrEnv'.pats_iota_inv' H hp
  have wf := TrEnv'.map_wf H
  refine ⟨rval, rule, cval, rhs, hc, ?_, hru, ?_, hM, hN, htr, hh1, hh2⟩
  · show env.constants.find?' recName = _; rw [wf.find?'_eq_find?]; exact hrec
  · show env.constants.find?' cName = _; rw [wf.find?'_eq_find?]; exact hct

/-! ### The block behind a kernel type former or constructor -/

/-- A type former or constructor resolvable in `C` and visible at `safety` was inserted by an
`induct` step: it is one of the kernel constants of an `AddInduct` block `decl`, well-formed
over the environment `env₀` it extends, whose result `env₁` lies below `venv`. Every other
step inserts only definitions, axioms, theorems, opaques, quotient constants, or (`ignore`)
constants invisible at `safety`. -/
theorem TrEnv'.find?_induct {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {x : Name} {ci : ConstantInfo}
    (H : TrEnv' safety C Q venv) (h : C.find? x = some ci) (hsafe : safety ≤ ci.safety)
    (hk : ci.isInductive ∨ ci.isCtor) :
    ∃ (C₀ C₁ : ConstMap) (env₀ env₁ : VEnv) (decl : VInductDecl),
      decl.WF env₀ ∧ env₁ ≤ venv ∧
      ∃ A : AddInduct safety C₀ env₀ decl C₁ env₁,
        ci ∈ AddInduct.consts A.ivals A.rvals ∧ ci.name = x := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignore _ h2 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; exact absurd hsafe h2
    · exact ih h
  | «axiom» _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans (VEnv.addConst_le h4), A, hA⟩
  | defn _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf,
        hle.trans ((VEnv.addConst_le h4).trans VEnv.addDefEq_le), A, hA⟩
  | mutualDef _ hnd hfr _ hadd _ Hprev ih =>
    rcases insertDefs_find? Hprev.map_wf hfr hnd h with h | ⟨_, _, _, rfl⟩
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf,
        hle.trans ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le), A, hA⟩
    · simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
  | thm _ _ _ _ h5 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans (VEnv.addConst_le h5), A, hA⟩
  | «opaque» _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at h; split at h
    · cases h; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans (VEnv.addConst_le h4), A, hA⟩
  | quot _ h2 Hprev ih =>
    have hq : ∀ v, ci ≠ .quotInfo v := by
      rintro v rfl; simp [ConstantInfo.isInductive, ConstantInfo.isCtor] at hk
    obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih (h2.pull_of Hprev.map_wf hq h)
    exact ⟨_, _, _, _, _, hwf, hle.trans h2.le, A, hA⟩
  | induct hwf hadd Hprev ih =>
    rcases hadd.find? Hprev.map_wf h with h | hA
    · obtain ⟨_, _, _, _, _, hwf, hle, A, hA⟩ := ih h
      exact ⟨_, _, _, _, _, hwf, hle.trans hadd.le, A, hA⟩
    · exact ⟨_, _, _, _, _, hwf, .rfl, hadd, hA⟩

/-- The block that declared a kernel type former `ival` as the model type former `t`: `decl`
is well-formed over `env₀`, its type formers extend `env₀` to `envT` and the whole block to
`env₁ ≤ venv`, and `t ∈ decl.types` translates `ival` with the constructors `cvals`
(`TrIndType`: `ival` translating to `t` in `env₀`, `ival.ctors` the names of `cvals`, each
constructor translating in `envT` with its Π-arity). -/
structure TrEnv'.InductOrigin (safety : DefinitionSafety) (venv : VEnv) (ival : InductiveVal)
    (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
    (cvals : List ConstructorVal) : Prop where
  wf : decl.WF env₀
  addTypes : decl.addTypes env₀ = some envT
  addInduct : env₀.addInduct decl = some env₁
  le : env₁ ≤ venv
  mem : t ∈ decl.types
  tr : TrIndType safety env₀ envT ival cvals t

/-- The type former and block behind an `inductInfo` of `C`: the inverse of `TrEnv'`'s
`induct` clause for type formers. Visibility at `safety` is needed, as for `pats_iota'`: an
`ignore` step inserts a type former of no block. -/
theorem TrEnv'.inductInfo_inv {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {I : Name} {ival : InductiveVal}
    (H : TrEnv' safety C Q venv) (hI : C.find? I = some (.inductInfo ival))
    (hsafe : safety ≤ (Lean.ConstantInfo.inductInfo ival).safety) :
    ∃ (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      t.name = I ∧ InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  obtain ⟨_, _, env₀, env₁, decl, hwf, hle, A, hmem, hn⟩ :=
    H.find?_induct hI hsafe (.inl rfl)
  rcases AddInduct.mem_consts.1 hmem with ⟨iv, hiv, he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, he⟩ <;>
    cases he
  obtain ⟨t, ht, htr⟩ := A.types.forall_exists_l iv hiv
  exact ⟨decl, env₀, A.envT, env₁, t, iv.2, htr.tr.2.symm.trans hn,
    ⟨hwf, A.stT, A.env_eq, hle, ht, htr⟩⟩

/-- The type former and block behind a `ctorInfo` of `C`: `cval` is among the constructors
`cvals` of a type former `t` of a block `decl`, with the data of `InductOrigin`; its model
constructor and translation are the matching entry of `tr.ctors`. -/
theorem TrEnv'.ctorInfo_inv {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {x : Name} {cval : ConstructorVal}
    (H : TrEnv' safety C Q venv) (hc : C.find? x = some (.ctorInfo cval))
    (hsafe : safety ≤ (Lean.ConstantInfo.ctorInfo cval).safety) :
    ∃ (ival : InductiveVal) (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      cval ∈ cvals ∧ cval.name = x ∧ InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  obtain ⟨_, _, env₀, env₁, decl, hwf, hle, A, hmem, hn⟩ :=
    H.find?_induct hc hsafe (.inr rfl)
  rcases AddInduct.mem_consts.1 hmem with ⟨_, _, he⟩ | ⟨iv, hiv, _, hcv, he⟩ | ⟨_, _, he⟩ <;>
    cases he
  obtain ⟨t, ht, htr⟩ := A.types.forall_exists_l iv hiv
  exact ⟨iv.1, decl, env₀, A.envT, env₁, t, iv.2, hcv, hn, ⟨hwf, A.stT, A.env_eq, hle, ht, htr⟩⟩

/-- `TrEnv'.inductInfo_inv` against the environment's own `find?`. -/
theorem TrEnv.inductInfo_inv {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {I : Name} {ival : InductiveVal}
    (H : TrEnv safety env venv) (hI : env.find? I = some (.inductInfo ival))
    (hsafe : safety ≤ (Lean.ConstantInfo.inductInfo ival).safety) :
    ∃ (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      t.name = I ∧ TrEnv'.InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  have h : env.constants.find?' I = some (.inductInfo ival) := hI
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  exact TrEnv'.inductInfo_inv H h hsafe

/-- `TrEnv'.ctorInfo_inv` against the environment's own `find?`. -/
theorem TrEnv.ctorInfo_inv {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {x : Name} {cval : ConstructorVal}
    (H : TrEnv safety env venv) (hc : env.find? x = some (.ctorInfo cval))
    (hsafe : safety ≤ (Lean.ConstantInfo.ctorInfo cval).safety) :
    ∃ (ival : InductiveVal) (decl : VInductDecl) (env₀ envT env₁ : VEnv) (t : VInductiveType)
      (cvals : List ConstructorVal),
      cval ∈ cvals ∧ cval.name = x ∧
      TrEnv'.InductOrigin safety venv ival decl env₀ envT env₁ t cvals := by
  have h : env.constants.find?' x = some (.ctorInfo cval) := hc
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  exact TrEnv'.ctorInfo_inv H h hsafe

/-- A registered ι rule, matched against a well-typed redex with its `Realizes` side
conditions discharged, gives a definitional equality between redex and reduct. Thin
wrapper over `VEnv.IsDefEq.pat`. -/
theorem TrEnv.iota_defeq {venv : VEnv} {U : Nat} {Γ : List VExpr}
    {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 m2 chk}
    (hpat : venv.pats p r) (hm : p.Matches e m1 m2)
    (hty : venv.HasType U Γ e A) (hR : r.2.Realizes m1 m2 chk)
    (hall : ∀ t ∈ chk, venv.IsDefEq U Γ t.1 t.2.1 t.2.2) :
    venv.IsDefEqU U Γ e (r.1.apply m1 m2) :=
  ⟨A, VEnv.IsDefEq.pat hpat hm hty hR hall⟩

/-- The ι reduction step of a translated environment, as `reduceRecursor.WF` needs it: a
well-typed redex matching a recursor's ι pattern (over the constructor `cval` resolved in
`env`) is definitionally equal to the `iotaRHS` reduct, over a template `rhs` translating
the kernel rule's reduct. Composes `pats_iota'` with `iota_defeq` at the trivial check. -/
theorem TrEnv.iota_rec {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule} {cval : ConstructorVal}
    {U : Nat} {Γ : List VExpr} {e A : VExpr} {m1 m2}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety)
    (hctor : env.find? cName = some (.ctorInfo cval))
    (hm : (SimplePattern.iota recName
        (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
        (cval.numParams + rule.nfields)).toPattern.Matches e m1 m2)
    (hty : venv.HasType U Γ e A) :
    ∃ (rhs : VExpr) (hc : rhs.Closed),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.IsDefEqU U Γ e ((SimplePattern.iotaRHS recName cName rval.numParams
        rval.numMotives rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc).apply
          m1 m2) := by
  obtain ⟨cval', rhs, hc, hct, htr, hp⟩ := H.pats_iota' hrec hrule hsafe
  rw [hctor] at hct; cases hct
  exact ⟨rhs, hc, htr, TrEnv.iota_defeq hp hm hty (chk := []) trivial nofun⟩

/-- The head of a well-typed application spine is well-typed. -/
theorem VEnv.HasType.mkApps_inv_head {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {as : List VExpr} {f V : VExpr}, env.HasType U Γ (f.mkApps as) V → ∃ W, env.HasType U Γ f W
  | [], _, V, H => ⟨V, H⟩
  | a :: as, f, _, H => by
    rw [VExpr.mkApps_cons] at H
    obtain ⟨_, H'⟩ := mkApps_inv_head henv hΓ (as := as) (f := f.app a) H
    obtain ⟨_, _, hf, -⟩ := H'.app_inv henv hΓ
    exact ⟨_, hf⟩

/-! ### Rebuilding an application spine in the translation

A head and arguments that translate assemble into a translation of the spine, provided the
model spine is well-typed: each application node needs the typing of its function and
argument, which `HasType.mkApps_inv_head` and `HasType.app_inv` read off the whole spine. -/

theorem TrExpr.mkAppList {env : VEnv} {Us : List Name} {Δ : VLCtx}
    (henv : env.WF) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length))
    {as : List Expr} {as' : List VExpr} (has : List.Forall₂ (TrExpr env Us Δ) as as') :
    ∀ {f f' V}, TrExpr env Us Δ f f' → env.HasType Us.length Δ.toCtx (f'.mkApps as') V →
      TrExpr env Us Δ (f.mkAppList as) (f'.mkApps as') := by
  induction has with
  | nil => exact fun hf _ => hf
  | cons ha _ ih =>
    intro f f' V hf hty
    rw [VExpr.mkApps_cons] at hty ⊢
    obtain ⟨_, hty'⟩ := hty.mkApps_inv_head henv hΔ
    obtain ⟨_, _, h1, h2⟩ := hty'.app_inv henv hΔ
    exact ih (.app henv hΔ h1 h2 hf ha) hty
