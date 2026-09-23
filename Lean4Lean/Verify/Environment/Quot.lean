import Lean4Lean.Verify.Environment.Extension

/-!
# Quotient initialization

`addQuot.WF`: `Environment.addQuot` keeps the environment well-formed. The kernel side
is computed: `checkEqType` establishes that `Eq` is a safe inductive type of the expected shape
(`checkEqType_ok`), and `addQuot` then inserts the four `quotInfo` constants with concrete
types (`addQuot_eq`, with the `mkForall` telescopes evaluated in `T1_eq`…`T4_eq` through
`LocalContext.mkBindingList`). On the model side the `Eq` of the environment translates to
`eqConst` (`QuotReady`), and each quotient constant's type translates to the model's
(`T1_tr`…`T4_tr`), which gives the `AddQuot` step of `TrEnv'.quot` at every safety level.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

theorem withLocalDecl_run {m} [Monad m] (n : Name) (bi : BinderInfo) (ty : Expr)
    (k : Expr → ExprBuildT m α) (lctx : LocalContext) (ngen : NameGenerator) :
    (withLocalDecl n bi ty k : ExprBuildT m α) lctx ngen =
      k (.fvar ⟨ngen.curr⟩) (lctx.mkLocalDecl ⟨ngen.curr⟩ n ty bi) ngen.next := rfl

namespace AddQuotAux

abbrev ng0 : NameGenerator := {}
abbrev x1 : FVarId := ⟨ng0.curr⟩
abbrev x2 : FVarId := ⟨ng0.next.curr⟩
abbrev x3 : FVarId := ⟨ng0.next.next.curr⟩
abbrev x4 : FVarId := ⟨ng0.next.next.next.curr⟩
abbrev x5 : FVarId := ⟨ng0.next.next.next.next.curr⟩
abbrev x6 : FVarId := ⟨ng0.next.next.next.next.next.curr⟩

abbrev u : Level := .param `u
abbrev v : Level := .param `v
abbrev αr : Expr := .arrow (.fvar x1) (.arrow (.fvar x1) .prop)
abbrev quot_r : Expr := mkApp2 (.const ``Quot [u]) (.fvar x1) (.fvar x2)

abbrev L1 : LocalContext := ({} : LocalContext).mkLocalDecl x1 `α (.sort u) .implicit
abbrev L2 : LocalContext := L1.mkLocalDecl x2 `r αr .default
abbrev L3 : LocalContext := L2.mkLocalDecl x3 `a (.fvar x1) .default
abbrev L2' : LocalContext := L1.mkLocalDecl x2 `r αr .implicit
abbrev L3' : LocalContext := L2'.mkLocalDecl x3 `a (.fvar x1) .default
abbrev L4 : LocalContext := L3'.mkLocalDecl x4 `β (.sort v) .implicit
abbrev L5 : LocalContext := L4.mkLocalDecl x5 `f (.arrow (.fvar x1) (.fvar x4)) .default
abbrev L6 : LocalContext := L5.mkLocalDecl x6 `b (.fvar x1) .default
abbrev L4i : LocalContext := L3'.mkLocalDecl x4 `β (.arrow quot_r .prop) .implicit
abbrev L5i : LocalContext := L4i.mkLocalDecl x5 `q quot_r .implicit

abbrev T1 : Expr := L2.mkForall #[.fvar x1, .fvar x2] (.sort u)
abbrev T2 : Expr := L3.mkForall #[.fvar x1, .fvar x2, .fvar x3] quot_r
abbrev sanity : Expr := L6.mkForall #[.fvar x3, .fvar x6] <|
  .arrow (mkApp2 (.fvar x2) (.fvar x3) (.fvar x6))
    (mkApp3 (.const ``Eq [v]) (.fvar x4) (.app (.fvar x5) (.fvar x3)) (.app (.fvar x5) (.fvar x6)))
abbrev T3 : Expr := L6.mkForall #[.fvar x1, .fvar x2, .fvar x4, .fvar x5] <|
  .arrow sanity <| .arrow quot_r (.fvar x4)
abbrev all_quot : Expr := L4i.mkForall #[.fvar x3] <|
  .app (.fvar x4) (mkApp3 (.const ``Quot.mk [u]) (.fvar x1) (.fvar x2) (.fvar x3))
abbrev T4 : Expr := L5i.mkForall #[.fvar x1, .fvar x2, .fvar x4] <|
  .forallE `mk all_quot (L5i.mkForall #[.fvar x5] (.app (.fvar x4) (.fvar x5))) .default

abbrev q1 : ConstantInfo :=
  .quotInfo { name := ``Quot, kind := .type, levelParams := [`u], type := T1 }
abbrev q2 : ConstantInfo :=
  .quotInfo { name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := T2 }
abbrev q3 : ConstantInfo :=
  .quotInfo { name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := T3 }
abbrev q4 : ConstantInfo :=
  .quotInfo { name := ``Quot.ind, kind := .ind, levelParams := [`u], type := T4 }

theorem addQuot_eq (env : Environment) (hq : env.quotInit = false) (h1 : checkEqType env = .ok ())
    (h2 : env.checkName ``Quot = .ok ()) (h3 : env.checkName ``Quot.mk = .ok ())
    (h4 : env.checkName ``Quot.lift = .ok ()) (h5 : env.checkName ``Quot.ind = .ok ()) :
    Environment.addQuot env = .ok (markQuotInit ((((env.add q1).add q2).add q3).add q4)) := by
  unfold Environment.addQuot
  simp only [hq, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  rfl


/-! ### The telescope contexts

Each `L*` is the empty context extended by `mkLocalDecl`s at the distinct generated fvars
`x1`…`x6`, so `LocalContext.find?_mkLocalDecl` — which needs only the underlying map's
well-formedness — turns a lookup into a chain of decidable fvar comparisons. `quot_simp`
performs that rewriting, and closes the membership side conditions of
`LocalContext.mkForall_eq_fold` through `quot_mem`. -/

open LocalContext (empty_map_wf map_wf_mkLocalDecl find?_mkLocalDecl) in
section

theorem L1_mwf : L1.fvarIdToDecl.WF := map_wf_mkLocalDecl empty_map_wf
theorem L1_find (x) : L1.find? x =
    if x = x1 then some (.cdecl ({} : LocalContext).decls.size x1 `α (.sort u) .implicit .default)
    else none := by
  rw [find?_mkLocalDecl empty_map_wf, LocalContext.find?_empty]
theorem L2_mwf : L2.fvarIdToDecl.WF := map_wf_mkLocalDecl L1_mwf
theorem L2_find (x) : L2.find? x =
    if x = x2 then some (.cdecl L1.decls.size x2 `r αr .default .default) else L1.find? x :=
  find?_mkLocalDecl L1_mwf x
theorem L3_find (x) : L3.find? x =
    if x = x3 then some (.cdecl L2.decls.size x3 `a (.fvar x1) .default .default)
    else L2.find? x :=
  find?_mkLocalDecl L2_mwf x

-- the second branch (`Quot.lift`, `Quot.ind`): `r` is implicit there
theorem L2'_mwf : L2'.fvarIdToDecl.WF := map_wf_mkLocalDecl L1_mwf
theorem L2'_find (x) : L2'.find? x =
    if x = x2 then some (.cdecl L1.decls.size x2 `r αr .implicit .default) else L1.find? x :=
  find?_mkLocalDecl L1_mwf x
theorem L3'_mwf : L3'.fvarIdToDecl.WF := map_wf_mkLocalDecl L2'_mwf
theorem L3'_find (x) : L3'.find? x =
    if x = x3 then some (.cdecl L2'.decls.size x3 `a (.fvar x1) .default .default)
    else L2'.find? x :=
  find?_mkLocalDecl L2'_mwf x
theorem L4_mwf : L4.fvarIdToDecl.WF := map_wf_mkLocalDecl L3'_mwf
theorem L4_find (x) : L4.find? x =
    if x = x4 then some (.cdecl L3'.decls.size x4 `β (.sort v) .implicit .default)
    else L3'.find? x :=
  find?_mkLocalDecl L3'_mwf x
theorem L5_mwf : L5.fvarIdToDecl.WF := map_wf_mkLocalDecl L4_mwf
theorem L5_find (x) : L5.find? x =
    if x = x5 then
      some (.cdecl L4.decls.size x5 `f (.arrow (.fvar x1) (.fvar x4)) .default .default)
    else L4.find? x :=
  find?_mkLocalDecl L4_mwf x
theorem L6_find (x) : L6.find? x =
    if x = x6 then some (.cdecl L5.decls.size x6 `b (.fvar x1) .default .default)
    else L5.find? x :=
  find?_mkLocalDecl L5_mwf x
theorem L4i_mwf : L4i.fvarIdToDecl.WF := map_wf_mkLocalDecl L3'_mwf
theorem L4i_find (x) : L4i.find? x =
    if x = x4 then some (.cdecl L3'.decls.size x4 `β (.arrow quot_r .prop) .implicit .default)
    else L3'.find? x :=
  find?_mkLocalDecl L3'_mwf x
theorem L5i_find (x) : L5i.find? x =
    if x = x5 then some (.cdecl L4i.decls.size x5 `q quot_r .implicit .default) else L4i.find? x :=
  find?_mkLocalDecl L4i_mwf x

end

/-- Resolve lookups and bindings along the telescope contexts: rewrite with the `L*_find`
ladder, decide the fvar comparisons, and unfold the binder construction. -/
macro "quot_simp" : tactic => `(tactic|
  simp +decide only [List.foldr, LocalContext.mkBindingList1,
    L1_find, L2_find, L3_find, L2'_find, L3'_find, L4_find, L5_find, L6_find, L4i_find, L5i_find,
    ↓reduceIte, Expr.abstractList, Expr.abstract1, Expr.arrow, Expr.prop, mkApp2, mkApp3, mkApp,
    Nat.zero_add, Nat.reduceAdd])

/-- Every variable of a telescope is declared in its context: the side condition of
`LocalContext.mkForall_eq_fold`. -/
macro "quot_mem" : tactic => `(tactic|
  (simp only [List.forall_mem_cons, List.forall_mem_nil, and_true];
   repeat' (first
     | refine And.intro ?_ ?_
     | (quot_simp; exact ⟨_, rfl⟩)
     | (intro _ h; cases h))))

theorem T1_eq : T1 = .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default) (.sort u) .default)
    .implicit := by
  show LocalContext.mkForall L2 ⟨[x1, x2].map .fvar⟩ _ = _
  rw [LocalContext.mkForall_eq_fold [x1, x2] _ (by quot_mem) (by simp; decide)]
  quot_simp

theorem T2_eq : T2 = .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default)
    (.forallE `a (.bvar 1) (.app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1)) .default) .default)
    .implicit := by
  show LocalContext.mkForall L3 ⟨[x1, x2, x3].map .fvar⟩ _ = _
  rw [LocalContext.mkForall_eq_fold [x1, x2, x3] _ (by quot_mem) (by simp; decide)]
  quot_simp

theorem sanity_eq : sanity = .forallE `a (.fvar x1) (.forallE `b (.fvar x1)
    (.forallE `a (.app (.app (.fvar x2) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [v]) (.fvar x4)) (.app (.fvar x5) (.bvar 2)))
        (.app (.fvar x5) (.bvar 1))) .default) .default) .default := by
  show LocalContext.mkForall L6 ⟨[x3, x6].map .fvar⟩ _ = _
  rw [LocalContext.mkForall_eq_fold [x3, x6] _ (by quot_mem) (by simp; decide)]
  quot_simp

theorem T3_eq : T3 = .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default)
    (.forallE `β (.sort v) (.forallE `f (.forallE `a (.bvar 2) (.bvar 1) .default)
      (.forallE `a
        (.forallE `a (.bvar 3) (.forallE `b (.bvar 4)
          (.forallE `a (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
              (.app (.bvar 3) (.bvar 1))) .default) .default) .default)
        (.forallE `a (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)) (.bvar 3) .default)
        .default) .default) .implicit) .implicit) .implicit := by
  show LocalContext.mkForall L6 ⟨[x1, x2, x4, x5].map .fvar⟩ _ = _
  rw [sanity_eq, LocalContext.mkForall_eq_fold [x1, x2, x4, x5] _ (by quot_mem) (by simp; decide)]
  quot_simp

theorem all_quot_eq : all_quot = .forallE `a (.fvar x1)
    (.app (.fvar x4) (.app (.app (.app (.const ``Quot.mk [u]) (.fvar x1)) (.fvar x2)) (.bvar 0)))
    .default := by
  show LocalContext.mkForall L4i ⟨[x3].map .fvar⟩ _ = _
  rw [LocalContext.mkForall_eq_fold [x3] _ (by quot_mem) (by simp)]
  quot_simp

theorem T4_inner_eq : L5i.mkForall #[.fvar x5] (.app (.fvar x4) (.fvar x5)) =
    .forallE `q quot_r (.app (.fvar x4) (.bvar 0)) .implicit := by
  show LocalContext.mkForall L5i ⟨[x5].map .fvar⟩ _ = _
  rw [LocalContext.mkForall_eq_fold [x5] _ (by quot_mem) (by simp)]
  quot_simp

theorem T4_eq : T4 = .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default)
    (.forallE `β (.forallE `a (.app (.app (.const ``Quot [u]) (.bvar 1)) (.bvar 0)) .prop .default)
      (.forallE `mk
        (.forallE `a (.bvar 2) (.app (.bvar 1)
          (.app (.app (.app (.const ``Quot.mk [u]) (.bvar 3)) (.bvar 2)) (.bvar 0))) .default)
        (.forallE `q (.app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2))
          (.app (.bvar 2) (.bvar 0)) .implicit) .default) .implicit) .implicit) .implicit := by
  show LocalContext.mkForall L5i ⟨[x1, x2, x4].map .fvar⟩ _ = _
  rw [all_quot_eq, T4_inner_eq,
    LocalContext.mkForall_eq_fold [x1, x2, x4] _ (by quot_mem) (by simp; decide)]
  quot_simp

/-! ### `checkEqType` -/

abbrev LE1 (u : Name) : LocalContext :=
  ({} : LocalContext).mkLocalDecl x1 `α (.sort (.param u)) .implicit
abbrev TE (u : Name) : Expr :=
  (LE1 u).mkForall #[.fvar x1] (.arrow (.fvar x1) (.arrow (.fvar x1) .prop))

theorem LE1_find (u : Name) (x) : (LE1 u).find? x =
    if x = x1 then
      some (.cdecl ({} : LocalContext).decls.size x1 `α (.sort (.param u)) .implicit .default)
    else none := by
  rw [LocalContext.find?_mkLocalDecl LocalContext.empty_map_wf, LocalContext.find?_empty]

theorem TE_eq (u : Name) : TE u = .forallE `α (.sort (.param u))
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .implicit := by
  show LocalContext.mkForall (LE1 u) ⟨[x1].map .fvar⟩ _ = _
  rw [LocalContext.mkForall_eq_fold [x1] _ (fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact ⟨_, by rw [LE1_find, if_pos rfl]⟩) (by simp)]
  simp +decide only [List.foldr, LocalContext.mkBindingList1, LE1_find,
    ↓reduceIte, Expr.abstractList, Expr.abstract1, Expr.arrow, Expr.prop, Nat.zero_add]

theorem Environment.get_ok {env : Environment} {n : Name} {ci : ConstantInfo}
    (h : env.get n = .ok ci) : env.find? n = some ci := by
  unfold Environment.get at h
  cases hfind : env.find? n with
  | none => simp [hfind] at h
  | some ci' => simp only [hfind] at h; cases h; rfl

/-- What a successful `checkEqType` establishes: `Eq` is a safe inductive type with one
universe parameter whose type is (up to binder names) `∀ {α : Sort u}, α → α → Prop`. -/
theorem checkEqType_ok (env : Environment) (h : checkEqType env = .ok ()) :
    ∃ info : InductiveVal, env.find? ``Eq = some (.inductInfo info) ∧ info.isUnsafe = false ∧
      ∃ u, info.levelParams = [u] ∧ (info.type == TE u) = true := by
  unfold checkEqType at h
  generalize hg : env.get ``Eq = g at h
  cases g with
  | error e => cases h
  | ok ci =>
    have hfind := Environment.get_ok hg
    cases ci with
    | inductInfo info =>
      simp only [bind, Except.bind] at h
      cases hu : info.isUnsafe with
      | true => rw [hu] at h; cases h
      | false =>
      rw [hu] at h
      simp only [Bool.false_eq_true, ite_false] at h
      cases hlp : info.levelParams with
      | nil => rw [hlp] at h; cases h
      | cons u rest =>
        cases rest with
        | cons _ _ => rw [hlp] at h; cases h
        | nil =>
          rw [hlp] at h
          cases hctors : info.ctors with
          | nil => rw [hctors] at h; cases h
          | cons eqRefl rest =>
            cases rest with
            | cons _ _ => rw [hctors] at h; cases h
            | nil =>
              rw [hctors] at h
              refine ⟨info, hfind, hu, u, hlp, ?_⟩
              cases hb : (info.type == TE u)
              · exfalso
                have hb' : (info.type != TE u) = true := by simp [bne, hb]
                simp only [ExprBuildT.run, bind, ReaderT.bind, withLocalDecl_run, read,
                  MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read, pure,
                  ReaderT.pure, Except.pure, Except.bind] at h
                split at h
                · cases h
                · rename_i heq
                  split at heq
                  · cases heq
                  · rename_i hc
                    exact hc hb'
              · rfl
    | _ => cases h


/-! ### Model side: the translations of the quotient constants -/

/-- The concrete kernel types (`T1_eq`…`T4_eq`). -/
abbrev T1' : Expr := .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default) (.sort u) .default)
    .implicit
abbrev T2' : Expr := .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default)
    (.forallE `a (.bvar 1) (.app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1)) .default) .default)
    .implicit
abbrev T3' : Expr := .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default)
    (.forallE `β (.sort v) (.forallE `f (.forallE `a (.bvar 2) (.bvar 1) .default)
      (.forallE `a
        (.forallE `a (.bvar 3) (.forallE `b (.bvar 4)
          (.forallE `a (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
              (.app (.bvar 3) (.bvar 1))) .default) .default) .default)
        (.forallE `a (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)) (.bvar 3) .default)
        .default) .default) .implicit) .implicit) .implicit
abbrev T4' : Expr := .forallE `α (.sort u) (.forallE `r
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default)
    (.forallE `β (.forallE `a (.app (.app (.const ``Quot [u]) (.bvar 1)) (.bvar 0)) .prop .default)
      (.forallE `mk
        (.forallE `a (.bvar 2) (.app (.bvar 1)
          (.app (.app (.app (.const ``Quot.mk [u]) (.bvar 3)) (.bvar 2)) (.bvar 0))) .default)
        (.forallE `q (.app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2))
          (.app (.bvar 2) (.bvar 0)) .implicit) .default) .implicit) .implicit) .implicit

theorem T1_tr {venv : VEnv} : TrExprS venv [`u] [] T1' quotConst.type := by
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.sort rfl) ?_
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ (.sort rfl)
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) (.sort rfl)

theorem T2_tr {venv : VEnv} (hQuot : venv.constants ``Quot = some quotConst) :
    TrExprS venv [`u] [] T2' quotMkConst.type := by
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.sort rfl) ?_
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
    refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) (.sort rfl)
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
    refine .app (by type_tac) (by type_tac) ?_ (.bvar rfl)
    refine .app (by type_tac) (by type_tac) (.const hQuot rfl rfl) (.bvar rfl)

theorem T3_tr {venv : VEnv} (hEq : venv.constants ``Eq = some eqConst)
    (hQuot : venv.constants ``Quot = some quotConst) :
    TrExprS venv [`u, `v] [] T3' quotLiftConst.type := by
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.sort rfl) ?_
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
    refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) (.sort rfl)
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.sort rfl) ?_
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) (.bvar rfl)
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
    refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
    refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
    · refine .app (by type_tac) (by type_tac) ?_ (.bvar rfl)
      exact .app (by type_tac) (by type_tac) (.bvar rfl) (.bvar rfl)
    · refine .app (by type_tac) (by type_tac) ?_ ?_
      · refine .app (by type_tac) (by type_tac) ?_ ?_
        · exact .app (by type_tac) (by type_tac) (.const hEq rfl rfl) (.bvar rfl)
        · exact .app (by type_tac) (by type_tac) (.bvar rfl) (.bvar rfl)
      · exact .app (by type_tac) (by type_tac) (.bvar rfl) (.bvar rfl)
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ (.bvar rfl)
    refine .app (by type_tac) (by type_tac) ?_ (.bvar rfl)
    exact .app (by type_tac) (by type_tac) (.const hQuot rfl rfl) (.bvar rfl)

theorem T4_tr {venv : VEnv} (hQuot : venv.constants ``Quot = some quotConst)
    (hMk : venv.constants ``Quot.mk = some quotMkConst) :
    TrExprS venv [`u] [] T4' quotIndConst.type := by
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.sort rfl) ?_
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
    refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) (.sort rfl)
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ (.sort rfl)
    refine .app (by type_tac) (by type_tac) ?_ (.bvar rfl)
    exact .app (by type_tac) (by type_tac) (.const hQuot rfl rfl) (.bvar rfl)
  refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ (.bvar rfl) ?_
    refine .app (by type_tac) (by type_tac) (.bvar rfl) ?_
    refine .app (by type_tac) (by type_tac) ?_ (.bvar rfl)
    refine .app (by type_tac) (by type_tac) ?_ (.bvar rfl)
    exact .app (by type_tac) (by type_tac) (.const hMk rfl rfl) (.bvar rfl)
  · refine .forallE ⟨_, by type_tac⟩ ⟨_, by type_tac⟩ ?_ ?_
    · refine .app (by type_tac) (by type_tac) ?_ (.bvar rfl)
      exact .app (by type_tac) (by type_tac) (.const hQuot rfl rfl) (.bvar rfl)
    · exact .app (by type_tac) (by type_tac) (.bvar rfl) (.bvar rfl)

/-! ### Model side: `Eq` -/

/-- A safe `Eq` of the shape `checkEqType` accepts is `eqConst` in the model at every safety
level: `VEnv.QuotReady`. -/
theorem quotReady {safety} {env : Environment} {venv : VEnv} (H : TrEnv safety env venv)
    {info : InductiveVal} (hfind : env.find? ``Eq = some (.inductInfo info))
    (hus : info.isUnsafe = false) {u : Name} (hlp : info.levelParams = [u])
    (hty : (info.type == TE u) = true) : venv.QuotReady := by
  have hs : safety ≤ (ConstantInfo.inductInfo info).safety := by
    simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hus,
      Bool.false_eq_true, ↓reduceIte]
    exact DefinitionSafety.le_safe
  obtain ⟨ci', hci', -, hlen, htr⟩ := H.find? hfind hs
  dsimp only [ConstantInfo.levelParams, ConstantInfo.type, ConstantInfo.toConstantVal] at hlen htr
  rw [hlp] at hlen htr
  have htr := htr.eqv hty
  rw [TE_eq] at htr
  obtain ⟨uvars, type⟩ := ci'
  simp only [List.length_cons, List.length_nil] at hlen
  subst hlen
  cases htr with | forallE _ _ h1 h2 =>
  cases h1 with | sort hu =>
  cases h2 with | forallE _ _ h3 h4 =>
  cases h3 with | bvar hb0 =>
  cases h4 with | forallE _ _ h5 h6 =>
  cases h5 with | bvar hb1 =>
  cases h6 with | sort hz =>
  simp [VLevel.ofLevel, VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.depth, VExpr.liftN,
    liftVar] at hu hz hb0 hb1
  subst hu hz
  obtain ⟨rfl, -⟩ := hb0
  obtain ⟨rfl, -⟩ := hb1
  exact hci'

/-! ### The `AddQuot` step and `addQuot.WF` -/

/-- The constant map after quotient initialization. -/
abbrev C' (C : ConstMap) : ConstMap :=
  (((C.insert ``Quot q1).insert ``Quot.mk q2).insert ``Quot.lift q3).insert ``Quot.ind q4

/-- The model-side steps of quotient initialization at one safety level: the four
`addConst`s and the `addDefEq`, packaged as the `AddQuot` witness of `TrEnv'.quot`. -/
theorem exists_addQuot {safety} {env : Environment} {venv : VEnv} (H : TrEnv safety env venv)
    (hEq : venv.QuotReady)
    (h1 : env.find? ``Quot = none) (h2 : env.find? ``Quot.mk = none)
    (h3 : env.find? ``Quot.lift = none) (h4 : env.find? ``Quot.ind = none) :
    ∃ v1 v2 v3 v4 : VEnv,
      venv.addConst ``Quot quotConst = some v1 ∧ v1.addConst ``Quot.mk quotMkConst = some v2 ∧
      v2.addConst ``Quot.lift quotLiftConst = some v3 ∧
      v3.addConst ``Quot.ind quotIndConst = some v4 ∧
      AddQuot env.constants (C' env.constants) venv (v4.addDefEq quotDefEq) := by
  have mapWF := H.map_wf
  have h1' : env.constants.find? ``Quot = none := by rwa [← mapWF.find?'_eq_find?]
  have h2' : env.constants.find? ``Quot.mk = none := by rwa [← mapWF.find?'_eq_find?]
  have h3' : env.constants.find? ``Quot.lift = none := by rwa [← mapWF.find?'_eq_find?]
  have h4' : env.constants.find? ``Quot.ind = none := by rwa [← mapWF.find?'_eq_find?]
  have n1 := H.constants_eq_none h1
  have n2 := H.constants_eq_none h2
  have n3 := H.constants_eq_none h3
  have n4 := H.constants_eq_none h4
  obtain ⟨v1, e1⟩ := VEnv.addConst_eq_none (ci := quotConst) n1
  have n2 : v1.constants ``Quot.mk = none := by
    rw [VEnv.addConst_eq_of_ne e1 (by decide)]; exact n2
  have n3 : v1.constants ``Quot.lift = none := by
    rw [VEnv.addConst_eq_of_ne e1 (by decide)]; exact n3
  have n4 : v1.constants ``Quot.ind = none := by
    rw [VEnv.addConst_eq_of_ne e1 (by decide)]; exact n4
  obtain ⟨v2, e2⟩ := VEnv.addConst_eq_none (ci := quotMkConst) n2
  have n3 : v2.constants ``Quot.lift = none := by
    rw [VEnv.addConst_eq_of_ne e2 (by decide)]; exact n3
  have n4 : v2.constants ``Quot.ind = none := by
    rw [VEnv.addConst_eq_of_ne e2 (by decide)]; exact n4
  obtain ⟨v3, e3⟩ := VEnv.addConst_eq_none (ci := quotLiftConst) n3
  have n4 : v3.constants ``Quot.ind = none := by
    rw [VEnv.addConst_eq_of_ne e3 (by decide)]; exact n4
  obtain ⟨v4, e4⟩ := VEnv.addConst_eq_none (ci := quotIndConst) n4
  have hQuot1 : v1.constants ``Quot = some quotConst := VEnv.addConst_self e1
  have hQuot2 : v2.constants ``Quot = some quotConst := (VEnv.addConst_le e2).constants hQuot1
  have hQuot3 : v3.constants ``Quot = some quotConst := (VEnv.addConst_le e3).constants hQuot2
  have hMk3 : v3.constants ``Quot.mk = some quotMkConst :=
    (VEnv.addConst_le e3).constants (VEnv.addConst_self e2)
  have hEq2 : v2.constants ``Eq = some eqConst :=
    ((VEnv.addConst_le e1).trans (VEnv.addConst_le e2)).constants hEq
  refine ⟨v1, v2, v3, v4, e1, e2, e3, e4, ?_⟩
  refine ⟨[`u], T1, v1, ⟨DefinitionSafety.le_rfl, rfl, ?_⟩, h1', e1, ?_⟩
  · show TrExprS venv [`u] [] T1 quotConst.type; rw [T1_eq]; exact T1_tr
  refine ⟨[`u], T2, v2, ⟨DefinitionSafety.le_rfl, rfl, ?_⟩,
    SMap.find?_insert_none mapWF.map₂ (by decide) h2', e2, ?_⟩
  · show TrExprS v1 [`u] [] T2 quotMkConst.type; rw [T2_eq]; exact T2_tr hQuot1
  refine ⟨[`u, `v], T3, v3, ⟨DefinitionSafety.le_rfl, rfl, ?_⟩,
    SMap.find?_insert_none (SMap.insert_map₂ mapWF.map₂) (by decide)
      (SMap.find?_insert_none mapWF.map₂ (by decide) h3'), e3, ?_⟩
  · show TrExprS v2 [`u, `v] [] T3 quotLiftConst.type; rw [T3_eq]; exact T3_tr hEq2 hQuot2
  refine ⟨[`u], T4, v4, ⟨DefinitionSafety.le_rfl, rfl, ?_⟩,
    SMap.find?_insert_none (SMap.insert_map₂ (SMap.insert_map₂ mapWF.map₂)) (by decide)
      (SMap.find?_insert_none (SMap.insert_map₂ mapWF.map₂) (by decide)
        (SMap.find?_insert_none mapWF.map₂ (by decide) h4')), e4, rfl, rfl⟩
  · show TrExprS v3 [`u] [] T4 quotIndConst.type; rw [T4_eq]; exact T4_tr hQuot3 hMk3

end AddQuotAux

open AddQuotAux in
/-- Quotient initialization keeps the environment well-formed and extends every safety-indexed
model. The initialized branch is immediate; otherwise `checkEqType` has established that `Eq`
is a safe inductive type of the expected shape, which is `eqConst` in the model at every level
(`quotReady`), and the four quotient constants are added by `TrEnv'.quot`. -/
theorem addQuot.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' henv'
  cases hq : env.quotInit with
  | true =>
    rw [Environment.addQuot, if_pos hq] at henv'
    cases henv'
    exact ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  | false =>
  have mapWF := (wf.tr (safety := .safe)).map_wf
  -- the checks
  have hce : checkEqType env = .ok () := by
    rw [Environment.addQuot, if_neg (by simp [hq])] at henv'
    generalize hce : checkEqType env = ce at henv'
    cases ce with
    | error => cases henv'
    | ok x => cases x; rfl
  have hn : ∀ n, env.checkName n = .ok () →
      env.find? n = none ∧ Environment.primitives.contains n = false :=
    fun n h => let ⟨a, b⟩ := checkName.WF mapWF n false _ h; ⟨a, by simpa using b⟩
  have hn1 : env.checkName ``Quot = .ok () := by
    rw [Environment.addQuot, if_neg (by simp [hq]), hce] at henv'
    generalize hc : env.checkName ``Quot = c at henv'
    cases c with
    | error => cases henv'
    | ok x => cases x; rfl
  have hn2 : env.checkName ``Quot.mk = .ok () := by
    rw [Environment.addQuot, if_neg (by simp [hq]), hce] at henv'
    simp only [hn1, bind, Except.bind] at henv'
    generalize hc : env.checkName ``Quot.mk = c at henv'
    cases c with
    | error => cases henv'
    | ok x => cases x; rfl
  have hn3 : env.checkName ``Quot.lift = .ok () := by
    rw [Environment.addQuot, if_neg (by simp [hq]), hce] at henv'
    simp only [hn1, hn2, bind, Except.bind] at henv'
    generalize hc : env.checkName ``Quot.lift = c at henv'
    cases c with
    | error => cases henv'
    | ok x => cases x; rfl
  have hn4 : env.checkName ``Quot.ind = .ok () := by
    rw [Environment.addQuot, if_neg (by simp [hq]), hce] at henv'
    simp only [hn1, hn2, hn3, bind, Except.bind] at henv'
    generalize hc : env.checkName ``Quot.ind = c at henv'
    cases c with
    | error => cases henv'
    | ok x => cases x; rfl
  rw [addQuot_eq env hq hce hn1 hn2 hn3 hn4] at henv'
  cases henv'
  obtain ⟨info, hfind, hsafe, u, hlp, hty⟩ := checkEqType_ok env hce
  have hEq {safety} : (ves.venv safety).QuotReady :=
    quotReady wf.tr hfind hsafe hlp hty
  obtain ⟨f1, p1⟩ := hn _ hn1; obtain ⟨f2, p2⟩ := hn _ hn2
  obtain ⟨f3, p3⟩ := hn _ hn3; obtain ⟨f4, p4⟩ := hn _ hn4
  have hex := fun safety => exists_addQuot (wf.tr (safety := safety)) hEq f1 f2 f3 f4
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice (P := fun safety venv' =>
    ∃ v1 v2 v3 v4 : VEnv,
      (ves.venv safety).addConst ``Quot quotConst = some v1 ∧
      v1.addConst ``Quot.mk quotMkConst = some v2 ∧
      v2.addConst ``Quot.lift quotLiftConst = some v3 ∧
      v3.addConst ``Quot.ind quotIndConst = some v4 ∧
      venv' = v4.addDefEq quotDefEq ∧
      AddQuot env.constants (C' env.constants) (ves.venv safety) venv')
    fun safety => by
      obtain ⟨v1, v2, v3, v4, e1, e2, e3, e4, hA⟩ := hex safety
      exact ⟨_, v1, v2, v3, v4, e1, e2, e3, e4, rfl, hA⟩
  have hle (safety) : ves.venv safety ≤ ves'.venv safety := by
    obtain ⟨v1, v2, v3, v4, e1, e2, e3, e4, heq, -⟩ := hves' safety
    rw [heq]
    exact (VEnv.addConst_le e1).trans <| (VEnv.addConst_le e2).trans <|
      (VEnv.addConst_le e3).trans <| (VEnv.addConst_le e4).trans VEnv.addDefEq_le
  refine ⟨ves', ?_, hle⟩
  exact {
    tr {safety} := by
      obtain ⟨v1, v2, v3, v4, e1, e2, e3, e4, heq, hA⟩ := hves' safety
      have htr := wf.tr (safety := safety)
      unfold TrEnv at htr; rw [hq] at htr
      exact TrEnv'.quot hEq hA htr
    hasPrimitives {safety} := by
      obtain ⟨v1, v2, v3, v4, e1, e2, e3, e4, heq, -⟩ := hves' safety
      rw [heq]
      exact ((((wf.hasPrimitives.addConst p1 e1).addConst p2 e2).addConst p3 e3).addConst
        p4 e4).addDefEq
    safePrimitives {n ci} hfind hp := by
      have m1 := mapWF
      have m2 := m1.insert ``Quot q1 (by rwa [← m1.find?'_eq_find?])
      have m3 := m2.insert ``Quot.mk q2
        (SMap.find?_insert_none m1.map₂ (by decide) (by rwa [← m1.find?'_eq_find?]))
      have m4 := m3.insert ``Quot.lift q3 (SMap.find?_insert_none m2.map₂ (by decide)
        (SMap.find?_insert_none m1.map₂ (by decide) (by rwa [← m1.find?'_eq_find?])))
      refine safePrimitives_add' m4 (fun h hp => ?_) q4 ?_
        (fun h => nomatch p4.symm.trans h) hfind hp
      · refine safePrimitives_add' m3 (fun h hp => ?_) q3 ?_
          (fun h => nomatch p3.symm.trans h) h hp
        · refine safePrimitives_add' m2 (fun h hp => ?_) q2 ?_
            (fun h => nomatch p2.symm.trans h) h hp
          · exact safePrimitives_add' m1 wf.safePrimitives q1 f1
              (fun h => nomatch p1.symm.trans h) h hp
          · exact Environment.find?_add_of_ne m1 q1 f1 (by decide) f2
        · exact Environment.find?_add_of_ne m2 q2
            (Environment.find?_add_of_ne m1 q1 f1 (by decide) f2)
            (by decide) (Environment.find?_add_of_ne m1 q1 f1 (by decide) f3)
      · exact Environment.find?_add_of_ne m3 q3
          (Environment.find?_add_of_ne m2 q2 (Environment.find?_add_of_ne m1 q1 f1 (by decide) f2)
            (by decide) (Environment.find?_add_of_ne m1 q1 f1 (by decide) f3)) (by decide)
          (Environment.find?_add_of_ne m2 q2 (Environment.find?_add_of_ne m1 q1 f1 (by decide) f2)
            (by decide) (Environment.find?_add_of_ne m1 q1 f1 (by decide) f4))
    mono {safety safety'} hsf := by
      obtain ⟨v1, v2, v3, v4, e1, e2, e3, e4, heq, -⟩ := hves' safety
      obtain ⟨w1, w2, w3, w4, g1, g2, g3, g4, heq', -⟩ := hves' safety'
      rw [heq, heq']
      exact VEnv.addDefEq_mono <| VEnv.addConst_mono (VEnv.addConst_mono (VEnv.addConst_mono
        (VEnv.addConst_mono (wf.mono hsf) g1 e1) g2 e2) g3 e3) g4 e4 }

end Lean4Lean
