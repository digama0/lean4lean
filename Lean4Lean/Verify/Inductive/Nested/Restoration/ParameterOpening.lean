import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace

/-! Opening of the common parameter telescope by nested restoration (`openRestoreParams`):
the opening relation `ParamOpening`, the cancellation of opening and closing, and the
transfer of translations across identical forall prefixes (`Expr.SameForallPrefix`), up to
the abstract relation `NestedRestoration` for one restored expression. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact context/free-variable opening relation for `openRestoreParams`. -/
inductive ParamOpening : LocalContext → Array Expr → Expr → Nat →
    LocalContext → Array Expr → Expr → Prop
  | done : ParamOpening lctx As e 0 lctx As e
  | forallE {id : FVarId} :
      ParamOpening
        (lctx.mkLocalDecl id name dom bi) (As.push (.fvar id))
        (body.instantiate1 (.fvar id)) n outLctx outAs tail →
      ParamOpening lctx As (.forallE name dom body bi) (n + 1)
        outLctx outAs tail
  | lam {id : FVarId} :
      ParamOpening
        (lctx.mkLocalDecl id name dom bi) (As.push (.fvar id))
        (body.instantiate1 (.fvar id)) n outLctx outAs tail →
      ParamOpening lctx As (.lam name dom body bi) (n + 1)
        outLctx outAs tail

/-- Nested lowering's parameter traversal is the forall-only fragment of the
restoration traversal.  Sharing this relation gives both phases one audited
telescope-substitution model. -/
theorem LoweringParamOpening.toParamOpening
    (H : LoweringParamOpening lctx As e n outLctx tail outAs) :
    ParamOpening lctx As e n outLctx outAs tail := by
  induction H with
  | done => exact .done
  | step Hnext ih => exact .forallE ih

theorem ParamOpening.params_size
    (H : ParamOpening lctx As e n outLctx outAs tail) :
    outAs.size = As.size + n := by
  induction H with
  | done => simp
  | forallE _ ih | lam _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

/-- The free-variable-ID fragment of `FVarsIn`.  Unlike `FVarsIn`, this
predicate intentionally says nothing about universe or expression
metavariables; binder opening/closing cancellation depends only on free
variable capture. -/
def _root_.Lean.Expr.FVarIdsIn (e : Expr) (P : FVarId → Prop) : Prop :=
  match e with
  | .fvar fv => P fv
  | .app fn arg => fn.FVarIdsIn P ∧ arg.FVarIdsIn P
  | .lam _ dom body _ | .forallE _ dom body _ =>
      dom.FVarIdsIn P ∧ body.FVarIdsIn P
  | .letE _ type value body _ =>
      type.FVarIdsIn P ∧ value.FVarIdsIn P ∧ body.FVarIdsIn P
  | .mdata _ body | .proj _ _ body => body.FVarIdsIn P
  | .bvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => True

theorem _root_.Lean.Expr.FVarIdsIn.mono
    {e : Expr} {P Q : FVarId → Prop}
    (H : e.FVarIdsIn P) (hmono : ∀ fv, P fv → Q fv) :
    e.FVarIdsIn Q := by
  induction e <;> simp_all [Expr.FVarIdsIn]

theorem FVarsIn_to_FVarIdsIn {e : Expr} {P : FVarId → Prop}
    (H : e.FVarsIn P) : e.FVarIdsIn P := by
  induction e <;> simp_all [FVarsIn, Expr.FVarIdsIn]

theorem _root_.Lean.Expr.FVarIdsIn.liftLooseBVars
    {e : Expr} {P : FVarId → Prop} {s d : Nat}
    (H : e.FVarIdsIn P) : (e.liftLooseBVars' s d).FVarIdsIn P := by
  induction e generalizing s <;>
    simp_all [Expr.FVarIdsIn, Expr.liftLooseBVars']

theorem _root_.Lean.Expr.FVarIdsIn.instantiate1_go
    {e a : Expr} {P : FVarId → Prop} {k : Nat}
    (He : e.FVarIdsIn P) (Ha : a.FVarIdsIn P) :
    (e.instantiate1' a k).FVarIdsIn P := by
  induction e generalizing k <;>
    simp_all [Expr.FVarIdsIn, Expr.instantiate1']
  case bvar =>
    split
    · simp [Expr.FVarIdsIn]
    · split
      · exact Ha.liftLooseBVars
      · simp [Expr.FVarIdsIn]

theorem _root_.Lean.Expr.FVarIdsIn.instantiate1
    {e a : Expr} {P : FVarId → Prop}
    (He : e.FVarIdsIn P) (Ha : a.FVarIdsIn P) :
    (e.instantiate1 a).FVarIdsIn P := by
  rw [Expr.instantiate1_eq]
  exact He.instantiate1_go Ha

theorem _root_.Lean.Expr.FVarIdsIn.abstract_instantiate1
    {e : Expr} {fv : FVarId} {k : Nat}
    (H : e.FVarIdsIn (· ≠ fv)) :
    (e.instantiate1' (.fvar fv) k).abstract1 fv k = e := by
  induction e generalizing k with
    simp_all [Expr.FVarIdsIn, Expr.instantiate1', Expr.abstract1]
  | bvar i =>
    split <;> [skip; split]
    · simp [Expr.abstract1, *]
    · simp [Expr.abstract1, Expr.liftLooseBVars', *]
    · obtain _ | i := i <;> simp [Expr.abstract1] <;> omega
  | fvar other => exact Ne.symm H

/-- Exact-model form of `FVarIdsIn.abstract_instantiate1`, for bodies closed below the opened
binder. -/
theorem _root_.Lean.Expr.FVarIdsIn.abstractN_instantiate1
    {e : Expr} {fv : FVarId} {k : Nat}
    (H : e.FVarIdsIn (· ≠ fv)) (hc : Closed e (k + 1)) :
    (e.instantiate1' (.fvar fv) k).abstractN [fv] k = e := by
  rw [Expr.abstractN_singleton (hc.instantiate1 (a := Expr.fvar fv) trivial).looseBVarRange_le]
  exact H.abstract_instantiate1

theorem _root_.Lean.Expr.FVarIdsIn.abstractN_of
    {e : Expr} {selected : FVarId} {P : FVarId → Prop} {k : Nat}
    (H : e.FVarIdsIn (fun fv => fv = selected ∨ P fv)) :
    (e.abstractN [selected] k).FVarIdsIn P := by
  induction e generalizing k <;>
    simp_all [Expr.FVarIdsIn, Expr.abstractN, Expr.lastRevIdx?]
  case fvar fv =>
    split
    next => trivial
    next hne =>
      rcases H with heq | hP
      · subst fv
        simp at hne
      · exact hP

theorem _root_.Lean.Expr.FVarIdsIn.mkAppList
    {fn : Expr} {args : List Expr} {P : FVarId → Prop} :
    (fn.mkAppList args).FVarIdsIn P ↔
      fn.FVarIdsIn P ∧ ∀ arg ∈ args, arg.FVarIdsIn P := by
  induction args generalizing fn <;>
    simp_all [Expr.mkAppList, Expr.FVarIdsIn, and_assoc]

theorem _root_.Lean.Expr.FVarIdsIn.getAppArgsList
    {e a : Expr} {P : FVarId → Prop}
    (H : e.FVarIdsIn P) (ha : a ∈ e.getAppArgsList) :
    a.FVarIdsIn P := by
  have H' : (e.getAppFn.mkAppList e.getAppArgsList).FVarIdsIn P := by
    rw [Expr.mkAppList_getAppArgsList]
    exact H
  exact (Expr.FVarIdsIn.mkAppList.mp H').2 a ha

/-- Exact local-declaration extension performed alongside parameter opening.
Declarations are recorded in binder order; `LocalContext.toList` stores the
same suffix in reverse because newer declarations are at the front. -/
theorem ParamOpening.context_extension
    (H : ParamOpening lctx As e n outLctx outAs tail) :
    ∃ decls : List LocalDecl,
      outLctx.toList = decls.reverse ++ lctx.toList ∧
      outAs.toList = As.toList ++ decls.map (fun d => .fvar d.fvarId) ∧
      decls.length = n := by
  induction H with
  | done => exact ⟨[], by simp⟩
  | forallE Hnext ih | lam Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    rcases ih with ⟨decls, hlctx, hparams, hlength⟩
    let decl : LocalDecl :=
      .cdecl lctx'.decls.size id name dom bi .default
    refine ⟨decl :: decls, ?_, ?_, by simp [hlength]⟩
    · simp [hlctx, decl, LocalContext.mkLocalDecl_toList]
    · simp [hparams, decl, List.append_assoc, LocalDecl.fvarId]

/-- A positional free-variable declaration (`FVarDeclAt`) and a declaration occurring at the
same free-variable identifier in a well-formed context are the same local
declaration. -/
theorem FVarDeclAt.declaration_eq_of_mem
    (D : FVarDeclAt c xs i)
    (Hc : BindingContextWF c)
    (d : LocalDecl) (hd : d ∈ c.lctx.toList)
    (hfv : d.fvarId = D.fvar) :
    d = .cdecl D.index D.fvar D.userName D.type D.binderInfo D.kind := by
  have hfind := LocalContextWF_find?_eq_some_of_mem Hc.wf hd
  rw [hfv] at hfind
  exact Option.some.inj (hfind.symm.trans D.declaration)

/-- At a root opening, the parameter array is in binder order while the
local-context free-variable list is in the reverse (most-recent-first) order.
This is the ordering convention required by `MLCtx.mkForall`. -/
theorem ParamOpening.root_params_reverse_fvars
    (Hopen : ParamOpening {} #[] e n outLctx outAs tail) :
    outAs.toList.reverse = outLctx.fvars.map Expr.fvar := by
  rcases Hopen.context_extension with
    ⟨decls, hlctx, hparams, _hlength⟩
  have hparams' : outAs.toList =
      decls.map (fun d => Expr.fvar d.fvarId) := by
    simpa using hparams
  have hlctx' : outLctx.toList = decls.reverse := by
    change outLctx.toList = decls.reverse ++ [] at hlctx
    simpa using hlctx
  rw [hparams', LocalContext.fvars, hlctx']
  simp [Function.comp_def]

/-- A forall-only restoration opening records enough information to cancel
its substitutions binder by binder.  The freshness hypothesis is deliberately
relative to the declarations introduced by this opening, so recursive calls
may still mention parameters introduced by earlier calls. -/
theorem ParamOpening.forall_rebuilding_data
    (Hopen : ParamOpening lctx As e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.ForallTelescope e n residual) :
    ∃ decls : List LocalDecl,
      outLctx.toList = decls.reverse ++ lctx.toList ∧
      outAs.toList = As.toList ++
        decls.map (fun d => Expr.fvar d.fvarId) ∧
      decls.length = n ∧
      (decls.map (fun d => d.fvarId)).Nodup ∧
      (∀ d ∈ decls, outLctx.find? d.fvarId = some d) ∧
      (Closed e → e.FVarIdsIn (fun fv => fv ∉ decls.map (fun d => d.fvarId)) →
        (decls.map (fun d => d.fvarId)).foldr
          (fun fv result =>
            LocalContext.mkBindingList1N false outLctx [] fv
              (result.abstractN [fv])) tail = e) := by
  induction Hopen generalizing residual with
  | done =>
    cases Htel
    exact ⟨[], by simp⟩
  | forallE Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Hbody =>
      have HbodyInst : Expr.ForallTelescope
          (body.instantiate1 (.fvar id)) n'
          (residual.instantiate1' (.fvar id) n') := by
        simpa [Expr.instantiate1_eq] using
          Hbody.instantiate1' (.fvar id) 0
      rcases ih Hwf HbodyInst with
        ⟨decls, hlctx, hparams, hlength, hnodup, hfind, hrebuild⟩
      let decl : LocalDecl :=
        .cdecl lctx'.decls.size id name dom bi .default
      have hlctx' : outLctx'.toList =
          (decl :: decls).reverse ++ lctx'.toList := by
        simp [hlctx, decl, LocalContext.mkLocalDecl_toList]
      have hparams' : outAs'.toList = As'.toList ++
          (decl :: decls).map (fun d => Expr.fvar d.fvarId) := by
        simp [hparams, decl, List.append_assoc, LocalDecl.fvarId]
      have hallNodup :
          ((decl :: decls).map (fun d => d.fvarId)).Nodup := by
        have hall := Hwf.nodup
        rw [hlctx', List.map_append] at hall
        have hrev := (List.nodup_append.mp hall).1
        rw [List.map_reverse] at hrev
        exact List.nodup_reverse.mp hrev
      have hfind' : ∀ d ∈ decl :: decls,
          outLctx'.find? d.fvarId = some d := by
        intro d hd
        apply LocalContextWF_find?_eq_some_of_mem Hwf
        rw [hlctx']
        exact List.mem_append_left _ (List.mem_reverse.mpr hd)
      refine ⟨decl :: decls, hlctx', hparams', by simp [hlength],
        hallNodup, hfind', ?_⟩
      intro hclosed hfree
      have hclosedBody : Closed body 1 := hclosed.2
      have hopenClosed : Closed (body.instantiate1 (.fvar id)) := by
        rw [Expr.instantiate1_eq]; exact hclosedBody.instantiate1 (a := .fvar id) trivial
      simp only [Expr.FVarIdsIn] at hfree
      simp only [List.map_cons, List.mem_cons, not_or, decl,
        LocalDecl.fvarId] at hfree
      have hbodyNoId : body.FVarIdsIn (fun fv => fv ≠ id) :=
        hfree.2.mono fun _ hfv => hfv.1
      have hbodyNoRest : body.FVarIdsIn
          (fun fv => fv ∉ decls.map (fun d => d.fvarId)) :=
        hfree.2.mono fun _ hfv => hfv.2
      have hallNodup' : id ∉ decls.map (fun d => d.fvarId) ∧
          (decls.map (fun d => d.fvarId)).Nodup := by
        simpa [decl, LocalDecl.fvarId] using hallNodup
      have hidNotRest : id ∉ decls.map (fun d => d.fvarId) := by
        exact hallNodup'.1
      have hopenFree : (body.instantiate1 (.fvar id)).FVarIdsIn
          (fun fv => fv ∉ decls.map (fun d => d.fvarId)) := by
        apply hbodyNoRest.instantiate1
        simpa [Expr.FVarIdsIn] using hidNotRest
      have hinner := hrebuild hopenClosed hopenFree
      simp only [List.map_cons, List.foldr_cons]
      rw [hinner]
      have hhead := hfind' decl (by simp)
      have hheadId : outLctx'.find? id = some decl := by
        simpa [decl, LocalDecl.fvarId] using hhead
      simp [LocalContext.mkBindingList1N, hheadId, decl, LocalDecl.fvarId,
        Expr.instantiate1_eq, hbodyNoId.abstractN_instantiate1 hclosedBody, Expr.abstractN_nil]
  | lam Hnext ih => cases Htel

/-- Lambda counterpart of `forall_rebuilding_data`.  Equation restoration
opens an initial lambda prefix and later closes the selected declarations
with `mkLambda`; this certificate proves that the round trip uses the
literal source binder prefix and is not merely alpha-equivalent to it. -/
theorem ParamOpening.lambda_rebuilding_data
    (Hopen : ParamOpening lctx As e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.LambdaTelescope e n residual) :
    ∃ decls : List LocalDecl,
      outLctx.toList = decls.reverse ++ lctx.toList ∧
      outAs.toList = As.toList ++
        decls.map (fun d => Expr.fvar d.fvarId) ∧
      decls.length = n ∧
      (decls.map (fun d => d.fvarId)).Nodup ∧
      (∀ d ∈ decls, outLctx.find? d.fvarId = some d) ∧
      (Closed e → e.FVarIdsIn (fun fv => fv ∉ decls.map (fun d => d.fvarId)) →
        (decls.map (fun d => d.fvarId)).foldr
          (fun fv result =>
            LocalContext.mkBindingList1N true outLctx [] fv
              (result.abstractN [fv])) tail = e) := by
  induction Hopen generalizing residual with
  | done =>
    cases Htel
    exact ⟨[], by simp⟩
  | forallE Hnext ih => cases Htel
  | lam Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Hbody =>
      have HbodyInst : Expr.LambdaTelescope
          (body.instantiate1 (.fvar id)) n'
          (residual.instantiate1' (.fvar id) n') := by
        simpa [Expr.instantiate1_eq] using
          Hbody.instantiate1' (.fvar id) 0
      rcases ih Hwf HbodyInst with
        ⟨decls, hlctx, hparams, hlength, hnodup, hfind, hrebuild⟩
      let decl : LocalDecl :=
        .cdecl lctx'.decls.size id name dom bi .default
      have hlctx' : outLctx'.toList =
          (decl :: decls).reverse ++ lctx'.toList := by
        simp [hlctx, decl, LocalContext.mkLocalDecl_toList]
      have hparams' : outAs'.toList = As'.toList ++
          (decl :: decls).map (fun d => Expr.fvar d.fvarId) := by
        simp [hparams, decl, List.append_assoc, LocalDecl.fvarId]
      have hallNodup :
          ((decl :: decls).map (fun d => d.fvarId)).Nodup := by
        have hall := Hwf.nodup
        rw [hlctx', List.map_append] at hall
        have hrev := (List.nodup_append.mp hall).1
        rw [List.map_reverse] at hrev
        exact List.nodup_reverse.mp hrev
      have hfind' : ∀ d ∈ decl :: decls,
          outLctx'.find? d.fvarId = some d := by
        intro d hd
        apply LocalContextWF_find?_eq_some_of_mem Hwf
        rw [hlctx']
        exact List.mem_append_left _ (List.mem_reverse.mpr hd)
      refine ⟨decl :: decls, hlctx', hparams', by simp [hlength],
        hallNodup, hfind', ?_⟩
      intro hclosed hfree
      have hclosedBody : Closed body 1 := hclosed.2
      have hopenClosed : Closed (body.instantiate1 (.fvar id)) := by
        rw [Expr.instantiate1_eq]; exact hclosedBody.instantiate1 (a := .fvar id) trivial
      simp only [Expr.FVarIdsIn] at hfree
      simp only [List.map_cons, List.mem_cons, not_or, decl,
        LocalDecl.fvarId] at hfree
      have hbodyNoId : body.FVarIdsIn (fun fv => fv ≠ id) :=
        hfree.2.mono fun _ hfv => hfv.1
      have hbodyNoRest : body.FVarIdsIn
          (fun fv => fv ∉ decls.map (fun d => d.fvarId)) :=
        hfree.2.mono fun _ hfv => hfv.2
      have hallNodup' : id ∉ decls.map (fun d => d.fvarId) ∧
          (decls.map (fun d => d.fvarId)).Nodup := by
        simpa [decl, LocalDecl.fvarId] using hallNodup
      have hopenFree : (body.instantiate1 (.fvar id)).FVarIdsIn
          (fun fv => fv ∉ decls.map (fun d => d.fvarId)) := by
        apply hbodyNoRest.instantiate1
        simpa [Expr.FVarIdsIn] using hallNodup'.1
      have hinner := hrebuild hopenClosed hopenFree
      simp only [List.map_cons, List.foldr_cons]
      rw [hinner]
      have hhead := hfind' decl (by simp)
      have hheadId : outLctx'.find? id = some decl := by
        simpa [decl, LocalDecl.fvarId] using hhead
      simp [LocalContext.mkBindingList1N, hheadId, decl, LocalDecl.fvarId,
        Expr.instantiate1_eq, hbodyNoId.abstractN_instantiate1 hclosedBody, Expr.abstractN_nil]

/-- Closing a root lambda opening with its unchanged exposed body reproduces
the input equation right-hand side exactly. -/
theorem ParamOpening.root_mkLambda_tail
    (Hopen : ParamOpening {} #[] e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.LambdaTelescope e n residual)
    (Hclosed : e.FVarIdsIn fun _ => False) (hclosed : Closed e) :
    outLctx.mkLambda outAs tail = e := by
  rcases Hopen.lambda_rebuilding_data Hwf Htel with
    ⟨decls, _hlctx, hparams, _hlength, hnodup, hfind, hrebuild⟩
  have harray :
      outAs = (decls.map (fun d => Expr.fvar d.fvarId)).toArray := by
    apply Array.toList_inj.mp
    simpa using hparams
  rw [harray, LocalContext.mkLambda]
  rw [show decls.map (fun d => Expr.fvar d.fvarId) =
      (decls.map (fun d => d.fvarId)).map Expr.fvar by simp]
  rw [LocalContext.mkBinding_eqN]
  rw [LocalContext.mkBindingListN_eq_fold]
  · apply hrebuild hclosed
    exact Hclosed.mono fun fv hfalse => False.elim hfalse
  · intro fv hfv
    rcases List.mem_map.mp hfv with ⟨d, hd, rfl⟩
    exact ⟨d, hfind d hd⟩
  · exact hnodup

/-- Folding the declarations copied by a forall opening removes exactly the
new parameter IDs.  `P` describes the free variables allowed before the
opening; the root specialization uses `P := False`. -/
theorem ParamOpening.forall_closing_data
    (Hopen : ParamOpening lctx As e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.ForallTelescope e n residual)
    (Hsource : e.FVarIdsIn P) :
    ∃ decls : List LocalDecl,
      outLctx.toList = decls.reverse ++ lctx.toList ∧
      outAs.toList = As.toList ++
        decls.map (fun d => Expr.fvar d.fvarId) ∧
      decls.length = n ∧
      (decls.map (fun d => d.fvarId)).Nodup ∧
      (∀ d ∈ decls, outLctx.find? d.fvarId = some d) ∧
      ∀ newBody,
        newBody.FVarIdsIn
          (fun fv => P fv ∨ fv ∈ decls.map (fun d => d.fvarId)) →
        ((decls.map (fun d => d.fvarId)).foldr
          (fun fv result =>
            LocalContext.mkBindingList1N false outLctx [] fv
              (result.abstractN [fv])) newBody).FVarIdsIn P := by
  induction Hopen generalizing residual P with
  | done =>
    cases Htel
    refine ⟨[], by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro newBody Hnew
    exact Hnew.mono fun fv h => by simpa using h
  | forallE Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Hbody =>
      simp only [Expr.FVarIdsIn] at Hsource
      have HbodyInst : Expr.ForallTelescope
          (body.instantiate1 (.fvar id)) n'
          (residual.instantiate1' (.fvar id) n') := by
        simpa [Expr.instantiate1_eq] using
          Hbody.instantiate1' (.fvar id) 0
      have HopenedSource : (body.instantiate1 (.fvar id)).FVarIdsIn
          (fun fv => P fv ∨ fv = id) := by
        have HbodyScope : body.FVarIdsIn
            (fun fv => P fv ∨ fv = id) :=
          Hsource.2.mono fun fv hP => Or.inl hP
        apply HbodyScope.instantiate1
        simp [Expr.FVarIdsIn]
      rcases ih Hwf HbodyInst HopenedSource with
        ⟨decls, hlctx, hparams, hlength, hnodup, hfind, hclose⟩
      let decl : LocalDecl :=
        .cdecl lctx'.decls.size id name dom bi .default
      have hlctx' : outLctx'.toList =
          (decl :: decls).reverse ++ lctx'.toList := by
        simp [hlctx, decl, LocalContext.mkLocalDecl_toList]
      have hparams' : outAs'.toList = As'.toList ++
          (decl :: decls).map (fun d => Expr.fvar d.fvarId) := by
        simp [hparams, decl, List.append_assoc, LocalDecl.fvarId]
      have hallNodup :
          ((decl :: decls).map (fun d => d.fvarId)).Nodup := by
        have hall := Hwf.nodup
        rw [hlctx', List.map_append] at hall
        have hrev := (List.nodup_append.mp hall).1
        rw [List.map_reverse] at hrev
        exact List.nodup_reverse.mp hrev
      have hfind' : ∀ d ∈ decl :: decls,
          outLctx'.find? d.fvarId = some d := by
        intro d hd
        apply LocalContextWF_find?_eq_some_of_mem Hwf
        rw [hlctx']
        exact List.mem_append_left _ (List.mem_reverse.mpr hd)
      refine ⟨decl :: decls, hlctx', hparams', by simp [hlength],
        hallNodup, hfind', ?_⟩
      intro newBody Hnew
      have HnewInner : newBody.FVarIdsIn
          (fun fv => (P fv ∨ fv = id) ∨
            fv ∈ decls.map (fun d => d.fvarId)) := by
        apply Hnew.mono
        intro fv hfv
        rcases hfv with hP | hnew
        · exact Or.inl (Or.inl hP)
        · simp only [List.map_cons, List.mem_cons, decl,
            LocalDecl.fvarId] at hnew
          rcases hnew with hid | hrest
          · exact Or.inl (Or.inr hid)
          · exact Or.inr hrest
      have Hinner := hclose newBody HnewInner
      have Habstract :
          ((decls.map (fun d => d.fvarId)).foldr
            (fun fv result =>
              LocalContext.mkBindingList1N false outLctx' [] fv
                (result.abstractN [fv])) newBody).abstractN [id] |>.FVarIdsIn P := by
        apply Expr.FVarIdsIn.abstractN_of
        exact Hinner.mono fun fv hfv => by
          rcases hfv with hP | hid
          · exact Or.inr hP
          · exact Or.inl hid
      simp only [List.map_cons, List.foldr_cons]
      have hhead := hfind' decl (by simp)
      have hheadId : outLctx'.find? id = some decl := by
        simpa [decl, LocalDecl.fvarId] using hhead
      simpa [LocalContext.mkBindingList1N, hheadId, decl,
        LocalDecl.fvarId, Expr.FVarIdsIn, Expr.abstractN_nil] using
        And.intro Hsource.1 Habstract
  | lam Hnext ih => cases Htel
/-- Full-scoping twin of `forall_closing_data`: the same closing fold also preserves
level metavariable freedom recorded by `FVarsIn`.  `P` describes the free variables allowed before the
opening; the root specialization uses `P := False`. -/
theorem ParamOpening.forall_closing_data_fvarsIn
    (Hopen : ParamOpening lctx As e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.ForallTelescope e n residual)
    (Hsource : e.FVarsIn P) :
    ∃ decls : List LocalDecl,
      outLctx.toList = decls.reverse ++ lctx.toList ∧
      outAs.toList = As.toList ++
        decls.map (fun d => Expr.fvar d.fvarId) ∧
      decls.length = n ∧
      (decls.map (fun d => d.fvarId)).Nodup ∧
      (∀ d ∈ decls, outLctx.find? d.fvarId = some d) ∧
      ∀ newBody,
        newBody.FVarsIn
          (fun fv => P fv ∨ fv ∈ decls.map (fun d => d.fvarId)) →
        ((decls.map (fun d => d.fvarId)).foldr
          (fun fv result =>
            LocalContext.mkBindingList1N false outLctx [] fv
              (result.abstractN [fv])) newBody).FVarsIn P := by
  induction Hopen generalizing residual P with
  | done =>
    cases Htel
    refine ⟨[], by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro newBody Hnew
    exact Hnew.mono fun fv h => by simpa using h
  | forallE Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Hbody =>
      simp only [Lean4Lean.FVarsIn] at Hsource
      have HbodyInst : Expr.ForallTelescope
          (body.instantiate1 (.fvar id)) n'
          (residual.instantiate1' (.fvar id) n') := by
        simpa [Expr.instantiate1_eq] using
          Hbody.instantiate1' (.fvar id) 0
      have HopenedSource : (body.instantiate1 (.fvar id)).FVarsIn
          (fun fv => P fv ∨ fv = id) := by
        have HbodyScope : body.FVarsIn
            (fun fv => P fv ∨ fv = id) :=
          Hsource.2.mono fun fv hP => Or.inl hP
        rw [Expr.instantiate1_eq]
        apply HbodyScope.instantiate1
        simp [Lean4Lean.FVarsIn]
      rcases ih Hwf HbodyInst HopenedSource with
        ⟨decls, hlctx, hparams, hlength, hnodup, hfind, hclose⟩
      let decl : LocalDecl :=
        .cdecl lctx'.decls.size id name dom bi .default
      have hlctx' : outLctx'.toList =
          (decl :: decls).reverse ++ lctx'.toList := by
        simp [hlctx, decl, LocalContext.mkLocalDecl_toList]
      have hparams' : outAs'.toList = As'.toList ++
          (decl :: decls).map (fun d => Expr.fvar d.fvarId) := by
        simp [hparams, decl, List.append_assoc, LocalDecl.fvarId]
      have hallNodup :
          ((decl :: decls).map (fun d => d.fvarId)).Nodup := by
        have hall := Hwf.nodup
        rw [hlctx', List.map_append] at hall
        have hrev := (List.nodup_append.mp hall).1
        rw [List.map_reverse] at hrev
        exact List.nodup_reverse.mp hrev
      have hfind' : ∀ d ∈ decl :: decls,
          outLctx'.find? d.fvarId = some d := by
        intro d hd
        apply LocalContextWF_find?_eq_some_of_mem Hwf
        rw [hlctx']
        exact List.mem_append_left _ (List.mem_reverse.mpr hd)
      refine ⟨decl :: decls, hlctx', hparams', by simp [hlength],
        hallNodup, hfind', ?_⟩
      intro newBody Hnew
      have HnewInner : newBody.FVarsIn
          (fun fv => (P fv ∨ fv = id) ∨
            fv ∈ decls.map (fun d => d.fvarId)) := by
        apply Hnew.mono
        intro fv hfv
        rcases hfv with hP | hnew
        · exact Or.inl (Or.inl hP)
        · simp only [List.map_cons, List.mem_cons, decl,
            LocalDecl.fvarId] at hnew
          rcases hnew with hid | hrest
          · exact Or.inl (Or.inr hid)
          · exact Or.inr hrest
      have Hinner := hclose newBody HnewInner
      have Habstract :
          ((decls.map (fun d => d.fvarId)).foldr
            (fun fv result =>
              LocalContext.mkBindingList1N false outLctx' [] fv
                (result.abstractN [fv])) newBody).abstractN [id] |>.FVarsIn P := by
        apply FVarsIn.abstractN_of
        exact Hinner.mono fun fv hfv => by
          rcases hfv with hP | hid
          · exact Or.inr hP
          · exact Or.inl (by simp [hid])
      simp only [List.map_cons, List.foldr_cons]
      have hhead := hfind' decl (by simp)
      have hheadId : outLctx'.find? id = some decl := by
        simpa [decl, LocalDecl.fvarId] using hhead
      simpa [LocalContext.mkBindingList1N, hheadId, decl,
        LocalDecl.fvarId, Lean4Lean.FVarsIn, Expr.abstractN_nil] using
        And.intro Hsource.1 Habstract
  | lam Hnext ih => cases Htel


/-- Closing a root forall opening with its unchanged exposed body reproduces
the input telescope exactly. -/
theorem ParamOpening.root_mkForall_tail
    (Hopen : ParamOpening {} #[] e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.ForallTelescope e n residual)
    (Hclosed : e.FVarIdsIn fun _ => False) (hclosed : Closed e) :
    outLctx.mkForall outAs tail = e := by
  rcases Hopen.forall_rebuilding_data Hwf Htel with
    ⟨decls, _hlctx, hparams, _hlength, hnodup, hfind, hrebuild⟩
  have harray :
      outAs = (decls.map (fun d => Expr.fvar d.fvarId)).toArray := by
    apply Array.toList_inj.mp
    simpa using hparams
  rw [harray, LocalContext.mkForall]
  rw [show decls.map (fun d => Expr.fvar d.fvarId) =
      (decls.map (fun d => d.fvarId)).map Expr.fvar by simp]
  rw [LocalContext.mkBinding_eqN]
  rw [LocalContext.mkBindingListN_eq_fold]
  · apply hrebuild hclosed
    exact Hclosed.mono fun fv hfalse => False.elim hfalse
  · intro fv hfv
    rcases List.mem_map.mp hfv with ⟨d, hd, rfl⟩
    exact ⟨d, hfind d hd⟩
  · exact hnodup

/-- Closing an arbitrary body scoped by a root opening's selected parameters
produces an expression with no free-variable IDs. -/
theorem ParamOpening.root_mkForall_fvarIdsClosed
    (Hopen : ParamOpening {} #[] e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.ForallTelescope e n residual)
    (Hsource : e.FVarIdsIn fun _ => False)
    (Hselection : CDeclArray outLctx outAs)
    (Hbody : body.FVarIdsIn (· ∈ Hselection.fvars)) :
    (outLctx.mkForall outAs body).FVarIdsIn fun _ => False := by
  rcases Hopen.forall_closing_data Hwf Htel Hsource with
    ⟨decls, _hlctx, hparams, _hlength, hnodup, hfind, hclose⟩
  have harray :
      outAs = (decls.map (fun d => Expr.fvar d.fvarId)).toArray := by
    apply Array.toList_inj.mp
    simpa using hparams
  have hselectionIds :
      Hselection.fvars = decls.map (fun d => d.fvarId) := by
    have harr : (Hselection.fvars.map Expr.fvar).toArray =
        ((decls.map (fun d => d.fvarId)).map Expr.fvar).toArray := by
      rw [← Hselection.expressions, harray]
      simp
    have hlist : Hselection.fvars.map Expr.fvar =
        (decls.map (fun d => d.fvarId)).map Expr.fvar := by
      simpa using congrArg Array.toList harr
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist
  have Hbody' : body.FVarIdsIn
      (fun fv => False ∨ fv ∈ decls.map (fun d => d.fvarId)) := by
    apply Hbody.mono
    intro fv hfv
    exact Or.inr (by simpa [hselectionIds] using hfv)
  rw [harray, LocalContext.mkForall]
  rw [show decls.map (fun d => Expr.fvar d.fvarId) =
      (decls.map (fun d => d.fvarId)).map Expr.fvar by simp]
  rw [LocalContext.mkBinding_eqN]
  rw [LocalContext.mkBindingListN_eq_fold]
  · exact hclose body Hbody'
  · intro fv hfv
    rcases List.mem_map.mp hfv with ⟨d, hd, rfl⟩
    exact ⟨d, hfind d hd⟩
  · exact hnodup
/-- Closing an arbitrary body scoped by a root opening's selected parameters
produces an expression with no free variables and no level metavariables,
provided the opened source had none. -/
theorem ParamOpening.root_mkForall_fvarsClosed
    (Hopen : ParamOpening {} #[] e n outLctx outAs tail)
    (Hwf : outLctx.WF)
    (Htel : Expr.ForallTelescope e n residual)
    (Hsource : e.FVarsIn fun _ => False)
    (Hselection : CDeclArray outLctx outAs)
    (Hbody : body.FVarsIn (· ∈ Hselection.fvars)) :
    (outLctx.mkForall outAs body).FVarsIn fun _ => False := by
  rcases Hopen.forall_closing_data_fvarsIn Hwf Htel Hsource with
    ⟨decls, _hlctx, hparams, _hlength, hnodup, hfind, hclose⟩
  have harray :
      outAs = (decls.map (fun d => Expr.fvar d.fvarId)).toArray := by
    apply Array.toList_inj.mp
    simpa using hparams
  have hselectionIds :
      Hselection.fvars = decls.map (fun d => d.fvarId) := by
    have harr : (Hselection.fvars.map Expr.fvar).toArray =
        ((decls.map (fun d => d.fvarId)).map Expr.fvar).toArray := by
      rw [← Hselection.expressions, harray]
      simp
    have hlist : Hselection.fvars.map Expr.fvar =
        (decls.map (fun d => d.fvarId)).map Expr.fvar := by
      simpa using congrArg Array.toList harr
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist
  have Hbody' : body.FVarsIn
      (fun fv => False ∨ fv ∈ decls.map (fun d => d.fvarId)) := by
    apply Hbody.mono
    intro fv hfv
    exact Or.inr (by simpa [hselectionIds] using hfv)
  rw [harray, LocalContext.mkForall]
  rw [show decls.map (fun d => Expr.fvar d.fvarId) =
      (decls.map (fun d => d.fvarId)).map Expr.fvar by simp]
  rw [LocalContext.mkBinding_eqN]
  rw [LocalContext.mkBindingListN_eq_fold]
  · exact hclose body Hbody'
  · intro fv hfv
    rcases List.mem_map.mp hfv with ⟨d, hd, rfl⟩
    exact ⟨d, hfind d hd⟩
  · exact hnodup


/-- Two expressions have the same concrete leading forall binders, while
their residual bodies may differ.  This is the exact syntactic relation
between a source constructor and its nested-lowered constructor. -/
inductive Expr.SameForallPrefix : Nat → Expr → Expr → Prop
  | nil : Expr.SameForallPrefix 0 left right
  | cons : Expr.SameForallPrefix n left right →
      Expr.SameForallPrefix (n + 1)
        (.forallE name dom left bi) (.forallE name dom right bi)

theorem Expr.SameForallPrefix.symm
    (H : Expr.SameForallPrefix n left right) :
    Expr.SameForallPrefix n right left := by
  induction H with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem Expr.SameForallPrefix.trans
    (H₁ : Expr.SameForallPrefix n left middle)
    (H₂ : Expr.SameForallPrefix n middle right) :
    Expr.SameForallPrefix n left right := by
  induction H₁ generalizing right with
  | nil => cases H₂; exact .nil
  | cons _ ih =>
    cases H₂ with
    | cons H₂ => exact .cons (ih H₂)

/-- The common concrete binder domains of two forall telescopes transfer a
free-variable bound from the right telescope to the left once the left
residual satisfies that same bound.  This is useful when replay identifies
the binder prefix but the two passes deliberately build different result
expressions. -/
theorem Expr.SameForallPrefix.leftFVarsIn
    (H : Expr.SameForallPrefix n left right)
    (Hleft : Expr.ForallTelescope left n leftResidual)
    (HrightScope : right.FVarsIn P)
    (HleftResidualScope : leftResidual.FVarsIn P) :
    left.FVarsIn P := by
  induction H generalizing leftResidual with
  | nil =>
    cases Hleft
    exact HleftResidualScope
  | cons _ ih =>
    cases Hleft with
    | cons Hleft =>
      exact ⟨HrightScope.1,
        ih Hleft HrightScope.2 HleftResidualScope⟩

/-- Closedness obeys the same prefix transfer principle.  The residual is
checked beneath the complete prefix, while every shared binder domain is
read from the closed right telescope. -/
theorem Expr.SameForallPrefix.leftClosed
    (H : Expr.SameForallPrefix n left right)
    (Hleft : Expr.ForallTelescope left n leftResidual)
    (HrightClosed : Closed right k)
    (HleftResidualClosed : Closed leftResidual (k + n)) :
    Closed left k := by
  induction H generalizing leftResidual k with
  | nil =>
    cases Hleft
    simpa using HleftResidualClosed
  | @cons n left right name dom bi H ih =>
    cases Hleft with
    | cons Hleft =>
      refine ⟨HrightClosed.1, ih Hleft HrightClosed.2 ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        HleftResidualClosed

/-- Identical concrete forall prefixes are complete once their residual
bodies are identified.  Keeping both telescope witnesses explicit avoids
relying on a syntactic `isForall` loop when the prefix was produced by two
independent executable passes. -/
theorem Expr.SameForallPrefix.eq_of_residual_eq
    (H : Expr.SameForallPrefix n left right)
    (Hleft : Expr.ForallTelescope left n leftResidual)
    (Hright : Expr.ForallTelescope right n rightResidual)
    (hresidual : leftResidual = rightResidual) :
    left = right := by
  induction H generalizing leftResidual rightResidual with
  | nil =>
    cases Hleft
    cases Hright
    exact hresidual
  | cons _ ih =>
    cases Hleft with
    | cons Hleft =>
      cases Hright with
      | cons Hright =>
        exact congrArg
          (fun body => Expr.forallE _ _ body _)
          (ih Hleft Hright hresidual)

/-- Reuse the binder-domain part of one translated forall telescope with a
different residual.  This is the dependent-type counterpart of
`SameLambdaPrefix.replaceTranslatedResidual`: the template supplies the
exact translated domains, while an independently translated and well-formed
residual supplies the new codomain. -/
theorem Expr.SameForallPrefix.replaceTranslatedResidual
    (Hsame : Expr.SameForallPrefix n template replacement)
    (HtemplateTelescope : Expr.ForallTelescope template n templateResidual)
    (HreplacementTelescope :
      Expr.ForallTelescope replacement n replacementResidual)
    (henv : VEnv.WF env)
    (Hctx : OnCtx Delta.toCtx (env.IsType Us.length))
    (hdomains : domains.length = n)
    (Htemplate : TrExprS env Us Delta template
      (VExpr.wrapForalls domains templateTarget))
    (HreplacementResidual :
      TrExprS env Us (abstractForallContext domains Delta)
        replacementResidual replacementTarget)
    (HreplacementResidualType : env.IsType Us.length
      (abstractForallContext domains Delta).toCtx replacementTarget) :
    TrExprS env Us Delta replacement
      (VExpr.wrapForalls domains replacementTarget) := by
  induction Hsame generalizing domains Delta templateResidual
      replacementResidual templateTarget replacementTarget with
  | nil =>
    cases HtemplateTelescope
    cases HreplacementTelescope
    have hnil : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using
      HreplacementResidual
  | @cons n left right name dom bi Hsame ih =>
    cases HtemplateTelescope with
    | cons HtemplateTail =>
      cases HreplacementTelescope with
      | cons HreplacementTail =>
        cases domains with
        | nil => simp at hdomains
        | cons domain domains =>
          cases Htemplate with
          | forallE HdomainType HtemplateBodyType HdomainTr HtemplateBody =>
            have htail : domains.length = n := by simpa using hdomains
            have Hctx' : OnCtx (domain :: Delta.toCtx)
                (env.IsType Us.length) := ⟨Hctx, HdomainType⟩
            have Hopened := VEnv.IsType.wrapForalls_inv henv.ordered Hctx'
              HtemplateBodyType
            have HreplacementResidualType' : env.IsType Us.length
                (domains.reverse ++ domain :: Delta.toCtx)
                replacementTarget := by
              rw [abstractForallContext_toCtx] at HreplacementResidualType
              simpa [VLCtx.toCtx] using HreplacementResidualType
            have HreplacementBodyType : env.IsType Us.length
                (domain :: Delta.toCtx)
                (VExpr.wrapForalls domains replacementTarget) :=
              VEnv.IsType.wrapForalls Hopened.1
                HreplacementResidualType'
            apply TrExprS.forallE HdomainType HreplacementBodyType HdomainTr
            simpa [abstractForallContext, List.map_append,
              List.append_assoc] using
              ih HtemplateTail HreplacementTail
                (by simpa [VLCtx.toCtx] using Hctx') htail HtemplateBody
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HreplacementResidual)
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HreplacementResidualType)

theorem Expr.SameForallPrefix.instantiate1'
    (H : Expr.SameForallPrefix n left right) (arg : Expr) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.instantiate1' arg k) (right.instantiate1' arg k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.instantiate1']
    exact .cons (ih (k + 1))

theorem Expr.SameForallPrefix.abstract1
    (H : Expr.SameForallPrefix n left right) (fv : FVarId) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.abstract1 fv k) (right.abstract1 fv k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstract1]
    exact .cons (ih (k + 1))

theorem Expr.SameForallPrefix.abstractN
    (H : Expr.SameForallPrefix n left right) (xs : List FVarId) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.abstractN xs k) (right.abstractN xs k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstractN]
    exact .cons (ih (k + 1))

theorem Expr.SameForallPrefix.abstractList
    (H : Expr.SameForallPrefix n left right)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.abstractList fvars k) (right.abstractList fvars k) := by
  induction fvars generalizing left right k with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

theorem Expr.SameForallPrefix.liftLooseBVars'
    (H : Expr.SameForallPrefix n left right)
    (s amount : Nat) :
    Expr.SameForallPrefix n
      (left.liftLooseBVars' s amount) (right.liftLooseBVars' s amount) := by
  induction H generalizing s with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.liftLooseBVars']
    exact .cons (ih (s + 1))

theorem Expr.SameForallPrefix.target_isForall_of_pos
    (H : Expr.SameForallPrefix n source target) (hpos : 0 < n) :
    target.isForall = true := by
  cases H with
  | nil => simp at hpos
  | cons => rfl

/-- Translating two concrete telescopes with an identical forall prefix
produces definitionally equal abstract binder contexts.  Their residual
bodies need not agree: only the shared concrete domain at each layer is
compared, in the context conversion accumulated from the preceding layers. -/
theorem Expr.SameForallPrefix.translatedContexts
    (H : Expr.SameForallPrefix n left right)
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length leftCtx rightCtx)
    (Hleft : TrExprS env Us leftCtx left leftTarget)
    (Hright : TrExprS env Us rightCtx right rightTarget) :
    ∃ leftDomains leftResidual rightDomains rightResidual,
      leftDomains.length = n ∧
      rightDomains.length = n ∧
      leftTarget = VExpr.wrapForalls leftDomains leftResidual ∧
      rightTarget = VExpr.wrapForalls rightDomains rightResidual ∧
      VEnv.IsDefEqCtx env Us.length []
        (leftDomains.reverse ++ leftCtx.toCtx)
        (rightDomains.reverse ++ rightCtx.toCtx) := by
  induction H generalizing leftCtx rightCtx leftTarget rightTarget with
  | nil =>
    exact ⟨[], leftTarget, [], rightTarget, rfl, rfl, rfl, rfl, by
      simpa using hctx.defeqCtx⟩
  | @cons n left right name dom bi H ih =>
    cases Hleft with
    | @forallE leftDom leftBody _ _ _ _ _ HleftDomType HleftBodyType
        HleftDom HleftBody =>
      cases Hright with
      | @forallE rightDom rightBody _ _ _ _ _ HrightDomType
          HrightBodyType HrightDom HrightBody =>
        have hdomU := HleftDom.uniq henv hctx HrightDom
        rcases HleftDomType with ⟨_leftLevel, HleftDomType⟩
        have hdom := hdomU.of_l henv hctx.wf.toCtx HleftDomType
        have hctx' : VLCtx.IsDefEq env Us.length
            ((none, .vlam leftDom) :: leftCtx)
            ((none, .vlam rightDom) :: rightCtx) :=
          .cons hctx nofun (.vlam hdom)
        rcases ih hctx' HleftBody HrightBody with
          ⟨leftTail, leftResidual, rightTail, rightResidual,
            hleftLength, hrightLength, hleftTarget, hrightTarget,
            hcontexts⟩
        refine ⟨leftDom :: leftTail, leftResidual,
          rightDom :: rightTail, rightResidual, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hleftLength]
        · simp [hrightLength]
        · simp [VExpr.wrapForalls, hleftTarget]
        · simp [VExpr.wrapForalls, hrightTarget]
        · simpa [List.reverse_cons, List.append_assoc,
            VLCtx.toCtx] using hcontexts

/-- Exact-domain form of `translatedContexts`.  When the two translated
targets have already been decomposed into caller-selected forall domains,
the anonymous context conversion can be returned over those very lists
rather than over fresh existential decompositions of the same targets. -/
theorem Expr.SameForallPrefix.translatedContextsExact
    (H : Expr.SameForallPrefix n left right)
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length leftCtx rightCtx)
    (Hleft : TrExprS env Us leftCtx left
      (VExpr.wrapForalls leftDomains leftResidual))
    (Hright : TrExprS env Us rightCtx right
      (VExpr.wrapForalls rightDomains rightResidual))
    (hleftLength : leftDomains.length = n)
    (hrightLength : rightDomains.length = n) :
    VEnv.IsDefEqCtx env Us.length []
      (leftDomains.reverse ++ leftCtx.toCtx)
      (rightDomains.reverse ++ rightCtx.toCtx) := by
  rcases H.translatedContexts henv hctx Hleft Hright with
    ⟨actualLeftDomains, actualLeftResidual,
      actualRightDomains, actualRightResidual,
      hactualLeftLength, hactualRightLength,
      hleftTarget, hrightTarget, Hcontexts⟩
  have hleftDomains : leftDomains = actualLeftDomains :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hleftLength hactualLeftLength (by simpa using hleftTarget)
  have hrightDomains : rightDomains = actualRightDomains :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hrightLength hactualRightLength (by simpa using hrightTarget)
  subst actualLeftDomains
  subst actualRightDomains
  exact Hcontexts

/-- Two translated forall telescopes with the same concrete prefix and the same
residual source are definitionally equal, at a sort level, so that a dependent
context conversion can be extended by the resulting domain. -/
theorem Expr.SameForallPrefix.translatedWholeTargetsOfResidualRightSort
    (H : Expr.SameForallPrefix n leftSource rightSource)
    (henv : VEnv.WF env)
    (Hbase : VEnv.IsDefEqCtx env Us.length []
      baseLeft.reverse baseRight.reverse)
    (Hleft : TrExprS env Us
      (abstractForallContext baseLeft []) leftSource
      (VExpr.wrapForalls leftDomains leftTarget))
    (Hright : TrExprS env Us
      (abstractForallContext baseRight []) rightSource
      (VExpr.wrapForalls rightDomains rightTarget))
    (hleftLength : leftDomains.length = n)
    (hrightLength : rightDomains.length = n)
    (HleftResidual : TrExprS env Us
      (abstractForallContext (baseLeft ++ leftDomains) []) residualSource
      leftTarget)
    (HrightResidual : TrExprS env Us
      (abstractForallContext (baseRight ++ rightDomains) []) residualSource
      rightTarget)
    (HrightResidualType : env.IsType Us.length
      (abstractForallContext (baseRight ++ rightDomains) []).toCtx
      rightTarget) :
    ∃ level, env.IsDefEq Us.length baseLeft.reverse
      (VExpr.wrapForalls leftDomains leftTarget)
      (VExpr.wrapForalls rightDomains rightTarget) (.sort level) := by
  have HbaseV := abstractForallContext.isDefEq Hbase
  have Hlocals := H.translatedContextsExact henv HbaseV Hleft Hright
    hleftLength hrightLength
  have Hlocals' : VEnv.IsDefEqCtx env Us.length []
      (baseLeft ++ leftDomains).reverse
      (baseRight ++ rightDomains).reverse := by
    simpa [List.reverse_append, VLCtx.toCtx] using Hlocals
  have HresidualU := TrExprS.uniqAbstractForallContext
    HleftResidual HrightResidual henv Hlocals'
  rcases HrightResidualType with ⟨residualLevel, HrightResidualType⟩
  have HrightResidualType' : env.HasType Us.length
      (baseRight ++ rightDomains).reverse rightTarget
      (.sort residualLevel) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
      HrightResidualType
  have HrightResidualTypeLeft : env.HasType Us.length
      (baseLeft ++ leftDomains).reverse rightTarget
      (.sort residualLevel) :=
    HrightResidualType'.defeqDFC henv.ordered
      (Hlocals'.symm henv.ordered)
  have Hresidual : env.IsDefEq Us.length
      (baseLeft ++ leftDomains).reverse leftTarget rightTarget
      (.sort residualLevel) :=
    HresidualU.of_r henv Hlocals'.isType HrightResidualTypeLeft
  have Hclosed :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads Hlocals'
      n (by simp [hleftLength]) Hresidual
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  exact ⟨closedLevel, by
    simpa [hleftLength, hrightLength] using Hclosed⟩

/-- Closing two residual bodies with the same ordinary declarations creates
the same concrete forall prefix around both. -/
theorem LocalContext.sameForallPrefixN_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (left right : Expr) :
    Expr.SameForallPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N false lctx [] fv
            (result.abstractN [fv])) left)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N false lctx [] fv
            (result.abstractN [fv])) right) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1N, hfind]
    exact Expr.SameForallPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstractN [fv])

/-- Closing two bodies over the same duplicate-free local selection gives
the same concrete forall prefix, independently of the bodies. -/
theorem CDeclArray.sameForallPrefix
    (H : CDeclArray lctx xs)
    (hnodup : H.fvars.Nodup) (left right : Expr) :
    Expr.SameForallPrefix xs.size
      (lctx.mkForall xs left) (lctx.mkForall xs right) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkForall, LocalContext.mkForall,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  simpa using LocalContext.sameForallPrefixN_fold hdecl left right

/-- A concrete restoration opening transfers across an identical forall
prefix, retaining exactly the same generated context and parameter array. -/
theorem Expr.SameForallPrefix.transferRestoreOpening
    (Hsame : Expr.SameForallPrefix n source target)
    (Hopen : ParamOpening lctx As target n outLctx outAs targetTail) :
    ∃ sourceTail,
      ParamOpening lctx As source n outLctx outAs sourceTail := by
  induction n generalizing source target lctx As with
  | zero =>
    cases Hsame with
    | nil =>
      cases Hopen with
      | done => exact ⟨source, .done⟩
  | succ n ih =>
    cases Hsame with
    | @cons _ sourceBody targetBody name dom bi Hinner =>
      cases Hopen with
      | forallE Hnext =>
        rename_i id
        have Hinst : Expr.SameForallPrefix n
            (sourceBody.instantiate1 (.fvar id))
            (targetBody.instantiate1 (.fvar id)) := by
          simpa [Expr.instantiate1_eq] using
            Hinner.instantiate1' (.fvar id) 0
        rcases ih Hinst Hnext with ⟨sourceTail, Hsource⟩
        exact ⟨sourceTail, .forallE Hsource⟩

/-- Lean expression equivalence of residual bodies is preserved when both
are closed by the same selected forall declarations. -/
theorem CDeclArray.mkForall_eqv
    (Hselection : CDeclArray lctx As)
    (hnodup : Hselection.fvars.Nodup)
    (Hbody : (left == right) = true) :
    ((lctx.mkForall As left == lctx.mkForall As right)) = true := by
  rcases Hselection with ⟨fvars, rfl, hdecl⟩
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkForall, LocalContext.mkBinding_eqN]
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hlookup⟩
    exact ⟨.cdecl index fv name type bi kind, hlookup⟩
  rw [LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  induction fvars with
  | nil => exact Hbody
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hlookup⟩
    simp only [List.foldr_cons, LocalContext.mkBindingList1N, hlookup, Bool.false_eq_true,
      ↓reduceIte]
    apply Expr.forallE_eqv (Expr.eqv_refl _)
    exact Expr.abstractN_eqv (ih (fun other hother => hdecl other (by
      simp [hother])) (List.nodup_cons.mp hnodup).2
      (fun other hother => hfind other (by simp [hother])))

/-- The suffix created by restoration opening consists exactly of the fresh
free variables introduced by its telescope traversal. -/
theorem ParamOpening.params_fvars_extension
    (H : ParamOpening lctx As e n outLctx outAs tail) :
    ∃ fvars : List FVarId,
      outAs.toList = As.toList ++ fvars.map Expr.fvar ∧
      fvars.length = n := by
  induction H with
  | done => exact ⟨[], by simp⟩
  | forallE H ih | lam H ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    rcases ih with ⟨fvars, heq, hlength⟩
    refine ⟨id :: fvars, ?_, by simp [hlength]⟩
    simp [heq, List.append_assoc]

/-- Jointly opening a generated forall telescope substitutes precisely the
fresh restoration variables into its residual body. -/
theorem ParamOpening.forallResidualData
    (Hopen : ParamOpening lctx As outer n outLctx outAs tail)
    (Htel : Expr.ForallTelescope outer n residual) :
    ∃ fvars : List FVarId,
      outAs.toList = As.toList ++ fvars.map Expr.fvar ∧
      fvars.length = n ∧
      tail = residual.instantiateRevList (fvars.map Expr.fvar) := by
  induction Hopen generalizing residual with
  | done =>
    cases Htel
    exact ⟨[], by simp⟩
  | forallE Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Hbody =>
      have Hbody' := Hbody.instantiate1' (.fvar id) 0
      rcases ih (residual := residual.instantiate1' (.fvar id) n')
        (by simpa [Expr.instantiate1_eq] using Hbody') with
        ⟨fvars, heq, hlength, htail⟩
      refine ⟨id :: fvars, ?_, by simp [hlength], ?_⟩
      · simp [heq, List.append_assoc]
      · rw [htail]
        have hcomm := Expr.instantiateRevList_instantiate1'_fvars
          residual id fvars 0 0
        simp only [Nat.zero_add, Nat.add_zero] at hcomm
        rw [hlength] at hcomm
        simpa using hcomm
  | lam Hnext ih => cases Htel

/-- Jointly opening a generated lambda telescope substitutes precisely the
fresh restoration variables into its residual body. -/
theorem ParamOpening.lambdaResidualData
    (Hopen : ParamOpening lctx As outer n outLctx outAs tail)
    (Htel : Expr.LambdaTelescope outer n residual) :
    ∃ fvars : List FVarId,
      outAs.toList = As.toList ++ fvars.map Expr.fvar ∧
      fvars.length = n ∧
      tail = residual.instantiateRevList (fvars.map Expr.fvar) := by
  induction Hopen generalizing residual with
  | done =>
    cases Htel
    exact ⟨[], by simp⟩
  | forallE Hnext ih => cases Htel
  | lam Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Hbody =>
      have Hbody' := Hbody.instantiate1' (.fvar id) 0
      rcases ih (residual := residual.instantiate1' (.fvar id) n')
        (by simpa [Expr.instantiate1_eq] using Hbody') with
        ⟨fvars, heq, hlength, htail⟩
      refine ⟨id :: fvars, ?_, by simp [hlength], ?_⟩
      · simp [heq, List.append_assoc]
      · rw [htail]
        have hcomm := Expr.instantiateRevList_instantiate1'_fvars
          residual id fvars 0 0
        simp only [Nat.zero_add, Nat.add_zero] at hcomm
        rw [hlength] at hcomm
        simpa using hcomm

/-- Root specialization of `forallResidualData`, stated with Lean's
`Array` operations. -/
theorem ParamOpening.forallResidual
    (Hopen : ParamOpening {} #[] outer n outLctx outAs tail)
    (Htel : Expr.ForallTelescope outer n residual) :
    tail = residual.instantiateRev outAs := by
  rcases Hopen.forallResidualData Htel with
    ⟨fvars, hAs, _hlength, htail⟩
  have hAs' : outAs = (fvars.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa using hAs
  rw [htail, Expr.instantiateRev_eq, Expr.instantiate_eq, hAs']
  simp [Expr.instantiateList_reverse]

/-- If the residual refers only to the unopened suffix, opening an outer
prefix preserves that residual literally.  Generated recursor results have
exactly this property: they mention motives, indices, and the major premise,
but never the common parameter binders outside them. -/
theorem ParamOpening.forallSuffix_sameResidual
    (Hopen : ParamOpening lctx As outer n outLctx outAs tail)
    (Htelescope : Expr.ForallTelescope outer (n + suffixArity) residual)
    (Hrange : residual.looseBVarRange' ≤ suffixArity) :
    Expr.ForallTelescope tail suffixArity residual := by
  induction Hopen generalizing residual with
  | done => simpa using Htelescope
  | forallE Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    rw [show (n' + 1) + suffixArity = (n' + suffixArity) + 1 by omega]
      at Htelescope
    cases Htelescope with
    | cons Hbody =>
      have Hbody' := Hbody.instantiate1' (.fvar id) 0
      have hresidual :
          residual.instantiate1' (.fvar id) (n' + suffixArity) = residual :=
        Expr.instantiate1'_eq_self (by omega)
      exact ih (residual := residual)
        (by simpa [Expr.instantiate1_eq, hresidual] using Hbody') Hrange
  | lam Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    rw [show (n' + 1) + suffixArity = (n' + suffixArity) + 1 by omega]
      at Htelescope
    cases Htelescope

theorem ParamOpening.initial_size
    (H : ParamOpening {} #[] e n outLctx outAs tail) :
    outAs.size = n := by
  simpa using H.params_size

/-- Restoration opening together with the duplicate-free local-variable
selection produced by its concrete name generator. -/
def ParamOpeningSelected
    (lctx : LocalContext) (As : Array Expr) (e : Expr) (n : Nat)
    (outLctx : LocalContext) (outAs : Array Expr) (tail : Expr) : Prop :=
  ParamOpening lctx As e n outLctx outAs tail ∧
  outLctx.WF ∧
  ∃ Hselection : CDeclArray outLctx outAs,
    Hselection.fvars.Nodup

theorem openRestoreParams_refinesSelected
    (H : RestoreTelescope e n)
    (Hctx : NestedBindingContextWF lctx ngen)
    (Hparams : NestedBoundParams lctx As) :
    ∀ (out : LocalContext × Array Expr × Expr) outNgen,
      Lean4Lean.ElimNestedInductive.Result.openRestoreParams n lctx As e ngen =
        (out, outNgen) →
      ParamOpeningSelected lctx As e n out.1 out.2.1 out.2.2 := by
  induction n generalizing e lctx As ngen with
  | zero =>
    intro out outNgen hout
    simp [Lean4Lean.ElimNestedInductive.Result.openRestoreParams] at hout
    cases hout
    exact ⟨.done, Hctx.wf, Hparams.toSelection Hctx, Hparams.nodup⟩
  | succ n ih =>
    cases H with
    | @forallE body _ name dom bi Hbody =>
      intro out outNgen hout
      simp only [Lean4Lean.ElimNestedInductive.Result.openRestoreParams,
        mkFreshId, getNGen, setNGen,
        bind, StateT.bind, pure, StateT.pure] at hout
      have Hnext := ih (Hbody.instantiate1 (.fvar ⟨ngen.curr⟩))
        (Hctx := Hctx.withLocalDecl name dom bi)
        (Hparams := Hparams.push Hctx name dom bi) out outNgen hout
      exact ⟨.forallE Hnext.1, Hnext.2⟩
    | @lam body _ name dom bi Hbody =>
      intro out outNgen hout
      simp only [Lean4Lean.ElimNestedInductive.Result.openRestoreParams,
        mkFreshId, getNGen, setNGen,
        bind, StateT.bind, pure, StateT.pure] at hout
      have Hnext := ih (Hbody.instantiate1 (.fvar ⟨ngen.curr⟩))
        (Hctx := Hctx.withLocalDecl name dom bi)
        (Hparams := Hparams.push Hctx name dom bi) out outNgen hout
      exact ⟨.lam Hnext.1, Hnext.2⟩

/-- End-to-end abstract relation for nested restoration: open exactly the
recorded parameter telescope, restore every body node, then rebuild the same
outer forall/lambda kind selected by the source root. -/
def NestedRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
  (input output : Expr) : Prop :=
  ∃ lctx As body restoredBody,
    ParamOpeningSelected {} #[] input result.nparams lctx As body ∧
    ExprReplacement (result.restoreNestedNode env As auxRec)
      body restoredBody ∧
    output = if input.isForall then lctx.mkForall As restoredBody
      else lctx.mkLambda As restoredBody

/-- The concrete parameter-opening data hidden by `NestedRestoration`, with
the exact binder-order selection and its length exposed for alpha-invariant
transport of translations. -/
structure NestedRestorationOpening
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (input output : Expr) where
  lctx : LocalContext
  params : Array Expr
  body : Expr
  restoredBody : Expr
  opening : ParamOpening {} #[] input result.nparams lctx params body
  lctxWF : lctx.WF
  selection : CDeclArray lctx params
  selectionNodup : selection.fvars.Nodup
  selectionLength : selection.fvars.length = result.params.size
  replacement : ExprReplacement (result.restoreNestedNode env params auxRec)
    body restoredBody
  output_eq : output = if input.isForall then
    lctx.mkForall params restoredBody else lctx.mkLambda params restoredBody

theorem NestedRestoration.opening
    (H : NestedRestoration result env auxRec input output)
    (hparams : result.params.size = result.nparams) :
    Nonempty (NestedRestorationOpening result env auxRec input output) := by
  rcases H with ⟨lctx, params, body, restoredBody,
    ⟨Hopening, Hlctx, Hselection, Hnodup⟩, Hreplacement, houtput⟩
  have hselectionSize : Hselection.fvars.length = result.params.size := by
    rw [← Hselection.size, Hopening.initial_size, ← hparams]
  exact ⟨{
    lctx := lctx
    params := params
    body := body
    restoredBody := restoredBody
    opening := Hopening
    lctxWF := Hlctx
    selection := Hselection
    selectionNodup := Hnodup
    selectionLength := hselectionSize
    replacement := Hreplacement
    output_eq := houtput }⟩

/-- Nested restoration changes only the body below the common parameter
prefix.  The rebuilt output therefore has literally the same leading forall
domains as the generated input. -/
theorem NestedRestorationOpening.sameForallPrefix
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htelescope : Expr.ForallTelescope input result.nparams suffix)
    (Hinput : input.FVarIdsIn fun _ => False) (hclosed : Closed input) :
    Expr.SameForallPrefix result.nparams input output := by
  by_cases hzero : result.nparams = 0
  · simpa [hzero] using (Expr.SameForallPrefix.nil (left := input)
      (right := output))
  have hinput : Hopen.lctx.mkForall Hopen.params Hopen.body = input :=
    Hopen.opening.root_mkForall_tail Hopen.lctxWF Htelescope Hinput hclosed
  have hfor : input.isForall = true :=
    Htelescope.isForall_of_pos (Nat.zero_lt_of_ne_zero hzero)
  have houtput : output =
      Hopen.lctx.mkForall Hopen.params Hopen.restoredBody := by
    simpa [hfor] using Hopen.output_eq
  have Hsame : Expr.SameForallPrefix result.nparams
      (Hopen.lctx.mkForall Hopen.params Hopen.body)
      (Hopen.lctx.mkForall Hopen.params Hopen.restoredBody) := by
    simpa only [Hopen.opening.initial_size] using
      Hopen.selection.sameForallPrefix Hopen.selectionNodup Hopen.body
        Hopen.restoredBody
  simpa only [hinput, ← houtput] using Hsame

/-- The rebuilt output exposes the exact residual obtained by
abstracting restoration's fresh parameter variables.  This is stronger than
mere arity preservation: the transport of translations can type that very
residual and then close it under the unchanged concrete parameter prefix. -/
theorem NestedRestorationOpening.outputPrefixTelescope
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htelescope : Expr.ForallTelescope input result.nparams suffix) :
    Expr.ForallTelescope output result.nparams
      (Hopen.restoredBody.abstractN Hopen.selection.fvars) := by
  rcases Hopen with ⟨lctx, params, body, restoredBody, Hopening, _HlctxWF,
    Hselection, _Hnodup, _HselectionLength, _Hreplacement, houtput⟩
  have Hrebuilt := Hselection.forallTelescope restoredBody
  rw [Hopening.initial_size] at Hrebuilt
  have houtputForall : output =
      lctx.mkForall params restoredBody := by
    cases hparams : result.nparams with
    | zero =>
        have hsize : params.size = 0 := by
          simpa [hparams] using Hopening.initial_size
        have hnil : params = #[] := Array.size_eq_zero_iff.mp hsize
        have hlambda : lctx.mkLambda #[] restoredBody = restoredBody := by
          rw [LocalContext.mkLambda]
          change LocalContext.mkBinding true lctx
            (([] : List FVarId).map Expr.fvar).toArray restoredBody =
              restoredBody
          rw [LocalContext.mkBinding_eqN]
          exact LocalContext.mkBindingListN_nil
        simpa [hnil, LocalContext.mkForall_empty, hlambda] using houtput
    | succ n =>
        have hfor : input.isForall = true :=
          Htelescope.isForall_of_pos (by omega)
        simpa [hfor] using houtput
  change Expr.ForallTelescope output result.nparams
    (restoredBody.abstractN Hselection.fvars)
  simpa only [houtputForall] using Hrebuilt

/-- Closing the fresh parameter variables exposed by a root
opening recovers the de Bruijn suffix of the input closed forall telescope. -/
theorem NestedRestorationOpening.abstractBody_eq_suffix
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htelescope : Expr.ForallTelescope input result.nparams suffix)
    (Hinput : input.FVarsIn fun _ => False) (hclosed : Closed input) :
    Hopen.body.abstractList Hopen.selection.fvars = suffix := by
  have hbody := Hopen.opening.forallResidual Htelescope
  have Hsuffix : suffix.FVarsIn (fun _ => False) :=
    Htelescope.resultFVarsIn Hinput
  have Haway : suffix.FVarsIn (fun fv => fv ∉ Hopen.selection.fvars) :=
    Hsuffix.mono fun _ hfalse => False.elim hfalse
  have hlength : Hopen.selection.fvars.length = result.nparams :=
    Hopen.selection.size.symm.trans Hopen.opening.initial_size
  have hlb : suffix.looseBVarRange' ≤ Hopen.selection.fvars.length := by
    rw [hlength]
    simpa using (Htelescope.closed_result hclosed).looseBVarRange_le
  have Hcancel := Haway.abstract_instantiateRev_fvarArray Hopen.params
    Hopen.selection.fvars Hopen.selection.expressions Hopen.selectionNodup hlb
  have hbodyClosed : Hopen.body.looseBVarRange' = 0 := by
    rw [hbody, Expr.instantiateRev_eq, Expr.instantiate_eq, Hopen.selection.expressions]
    have hinst : (Expr.instantiateList suffix
        ((Hopen.selection.fvars.map Expr.fvar).toArray.reverse.toList) 0).looseBVarRange'
        ≤ 0 + 0 :=
      Expr.instantiateList_looseBVarRange (by simpa using hlb)
        (by intro a ha; simp at ha; obtain ⟨_, _, rfl⟩ := ha; exact Nat.le_refl 0)
    simpa using hinst
  calc
    Hopen.body.abstractList Hopen.selection.fvars =
        Hopen.body.abstract
          (Hopen.selection.fvars.map Expr.fvar).toArray :=
      (Expr.abstract_eq_of_closed _ _ Hopen.selectionNodup hbodyClosed).symm
    _ = Hopen.body.abstract Hopen.params :=
      congrArg Hopen.body.abstract Hopen.selection.expressions.symm
    _ = suffix := by simpa [hbody] using Hcancel

@[simp] theorem restoreNestedNode_forall
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) :
    result.restoreNestedNode env As auxRec (.forallE name dom body bi) =
      none := by
  simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
    Expr.getAppFn]

/-- After restoration opens the common-parameter prefix, the remaining
generated recursor telescope is a binder-aligned replacement
(`ForallTelescopeReplacement`). The residual remains literal when it only refers
to that suffix. -/
theorem NestedRestorationOpening.suffixTelescopeReplacement
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htelescope : Expr.ForallTelescope input
      (result.nparams + suffixArity) residual)
    (Hrange : residual.looseBVarRange' ≤ suffixArity) :
    ∃ restoredResidual,
      ExprReplacement.ForallTelescopeReplacement
        (result.restoreNestedNode env Hopen.params auxRec)
        Hopen.body Hopen.restoredBody suffixArity residual
        restoredResidual := by
  have Hsuffix := Hopen.opening.forallSuffix_sameResidual Htelescope Hrange
  exact Hopen.replacement.forallTelescopeReplacement
    (fun _name _dom _body _bi =>
      restoreNestedNode_forall result env Hopen.params auxRec) Hsuffix

theorem restoreNestedNode_of_bvar_head
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name)
    (hhead : input.getAppFn = .bvar index) :
    result.restoreNestedNode env As auxRec input = none := by
  cases input <;>
    simp_all [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
      Expr.getAppFn]

theorem ExprReplacement.restoreNested_bvarApps
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (root : Nat) :
    ∀ args : List Nat,
      ExprReplacement (result.restoreNestedNode env As auxRec)
        (args.foldl (fun fn index => .app fn (.bvar index)) (.bvar root))
        (args.foldl (fun fn index => .app fn (.bvar index)) (.bvar root)) := by
  intro args
  have go : ∀ (tail : List Nat) (fn : Expr) (headIndex : Nat),
      fn.getAppFn = .bvar headIndex →
      ExprReplacement (result.restoreNestedNode env As auxRec) fn fn →
      ExprReplacement (result.restoreNestedNode env As auxRec)
        (tail.foldl (fun fn index => .app fn (.bvar index)) fn)
        (tail.foldl (fun fn index => .app fn (.bvar index)) fn) := by
    intro tail
    induction tail with
    | nil => exact fun fn headIndex hhead Hfn => Hfn
    | cons index tail ih =>
      intro fn headIndex hhead Hfn
      simp only [List.foldl_cons]
      have happHead : (Expr.app fn (.bvar index)).getAppFn =
          Expr.bvar headIndex := by
        simpa [Expr.getAppFn] using hhead
      have Happ : ExprReplacement (result.restoreNestedNode env As auxRec)
          (.app fn (.bvar index)) (.app fn (.bvar index)) := by
        apply ExprReplacement.app
        · exact restoreNestedNode_of_bvar_head result env As auxRec happHead
        · exact Hfn
        · exact .bvar
            (restoreNestedNode_of_bvar_head result env As auxRec rfl)
      exact ih _ _ happHead Happ
  exact go args (.bvar root) root rfl <|
    .bvar (restoreNestedNode_of_bvar_head result env As auxRec rfl)

theorem Closed.foldl_bvarApps
    {fn : Expr} {args : List Nat} {arity : Nat}
    (Hfn : Closed fn arity)
    (Hargs : ∀ index ∈ args, index < arity) :
    Closed (args.foldl (fun fn index => .app fn (.bvar index)) fn) arity := by
  induction args generalizing fn with
  | nil => exact Hfn
  | cons index args ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact ⟨Hfn, Hargs index (by simp)⟩
    · intro other hother
      exact Hargs other (by simp [hother])

theorem FVarsIn.foldl_bvarApps
    {fn : Expr} {args : List Nat} {predicate : FVarId → Prop}
    (Hfn : fn.FVarsIn predicate) :
    (args.foldl (fun fn index => .app fn (.bvar index)) fn
      ).FVarsIn predicate := by
  induction args generalizing fn with
  | nil => exact Hfn
  | cons index args ih =>
    simp only [List.foldl_cons]
    exact ih ⟨Hfn, True.intro⟩

/-- The generated recursor result contains only an application spine of bound
variables.  Nested restoration therefore leaves it literally unchanged. -/
theorem ExprReplacement.restoreNested_concreteRecursorResult
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name)
    (numMotives numMinors numIndices ownerIdx : Nat) :
    ExprReplacement (result.restoreNestedNode env As auxRec)
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx)
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx) := by
  let motiveOffset :=
    1 + numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indices : List Nat := List.ofFn fun i : Fin numIndices =>
    1 + (numIndices - 1 - i)
  have Hfn := ExprReplacement.restoreNested_bvarApps result env As auxRec
    motiveOffset indices
  have Hfn' : ExprReplacement (result.restoreNestedNode env As auxRec)
      (mkAppN (.bvar motiveOffset) (indices.map Expr.bvar).toArray)
      (mkAppN (.bvar motiveOffset) (indices.map Expr.bvar).toArray) := by
    simpa [mkAppN, List.foldl_map, Function.comp_def] using Hfn
  have hindices :
      List.ofFn (fun i : Fin numIndices =>
        Expr.bvar (1 + (numIndices - 1 - i))) = indices.map Expr.bvar := by
    apply List.ext_getElem
    · simp [indices]
    · intro i hleft hright
      simp [indices]
  unfold concreteRecursorResult
  rw [hindices]
  change ExprReplacement (result.restoreNestedNode env As auxRec)
    (.app (mkAppN (.bvar motiveOffset) (indices.map Expr.bvar).toArray)
      (.bvar 0))
    (.app (mkAppN (.bvar motiveOffset) (indices.map Expr.bvar).toArray)
      (.bvar 0))
  apply ExprReplacement.app
  · apply restoreNestedNode_of_bvar_head result env As auxRec
    rw [Expr.getAppFn, Expr.getAppFn_mkAppN]
    rfl
  · exact Hfn'
  · exact .bvar
      (restoreNestedNode_of_bvar_head result env As auxRec rfl)

theorem concreteRecursorResult_closed
    (howner : ownerIdx < numMotives) :
    Closed (concreteRecursorResult numMotives numMinors numIndices ownerIdx)
      (numMotives + numMinors + numIndices + 1) := by
  let arity := numMotives + numMinors + numIndices + 1
  let motiveOffset :=
    1 + numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indices : List Nat := List.ofFn fun i : Fin numIndices =>
    1 + (numIndices - 1 - i)
  have hoffset : motiveOffset < arity := by
    dsimp [motiveOffset, arity]
    omega
  have hindicesBound : ∀ index ∈ indices, index < arity := by
    intro index hindex
    simp only [indices, List.mem_ofFn] at hindex
    rcases hindex with ⟨i, rfl⟩
    dsimp [arity]
    omega
  have Hfn := Closed.foldl_bvarApps
    (fn := .bvar motiveOffset) (args := indices) (arity := arity)
    hoffset hindicesBound
  have hindices :
      List.ofFn (fun i : Fin numIndices =>
        Expr.bvar (1 + (numIndices - 1 - i))) = indices.map Expr.bvar := by
    apply List.ext_getElem
    · simp [indices]
    · intro i hleft hright
      simp [indices]
  unfold concreteRecursorResult
  rw [hindices]
  change Closed
    (.app (mkAppN (.bvar motiveOffset) (indices.map Expr.bvar).toArray)
      (.bvar 0)) arity
  constructor
  · simpa [mkAppN, List.foldl_map, Function.comp_def] using Hfn
  · dsimp [arity]
    exact Nat.zero_lt_succ _

theorem concreteRecursorResult_noFVars :
    (concreteRecursorResult numMotives numMinors numIndices ownerIdx).FVarsIn
      (fun _ => False) := by
  let motiveOffset :=
    1 + numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indices : List Nat := List.ofFn fun i : Fin numIndices =>
    1 + (numIndices - 1 - i)
  have Hfn := FVarsIn.foldl_bvarApps (predicate := fun _ => False)
    (fn := .bvar motiveOffset) (args := indices) (by trivial)
  have hindices :
      List.ofFn (fun i : Fin numIndices =>
        Expr.bvar (1 + (numIndices - 1 - i))) = indices.map Expr.bvar := by
    apply List.ext_getElem
    · simp [indices]
    · intro i hleft hright
      simp [indices]
  unfold concreteRecursorResult
  rw [hindices]
  change (Expr.app
    (mkAppN (.bvar motiveOffset) (indices.map Expr.bvar).toArray)
    (.bvar 0)).FVarsIn (fun _ => False)
  constructor
  · simpa [mkAppN, List.foldl_map, Function.comp_def] using Hfn
  · trivial

theorem concreteRecursorResult_looseBVarRange
    (howner : ownerIdx < numMotives) :
    (concreteRecursorResult numMotives numMinors numIndices ownerIdx
      ).looseBVarRange' ≤
      numMotives + numMinors + numIndices + 1 :=
  (concreteRecursorResult_closed howner).looseBVarRange_le

/-- Strong recursor specialization: restoration preserves not only the total
telescope arity but its de Bruijn result expression. -/
theorem NestedRestoration.concreteRecursorResult_forallTelescope
    (H : NestedRestoration result env auxRec input output)
    (howner : ownerIdx < numMotives)
    (Htelescope : Expr.ForallTelescope input
      (result.nparams +
        (numMotives + numMinors + numIndices + 1))
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx)) :
    Expr.ForallTelescope output
      (result.nparams +
        (numMotives + numMinors + numIndices + 1))
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx) := by
  rcases H with ⟨lctx, As, body, restoredBody,
    ⟨Hopening, _Hlctx, Hselection, _Hnodup⟩, Hreplacement, houtput⟩
  let recResult :=
    concreteRecursorResult numMotives numMinors numIndices ownerIdx
  have Hbody : Expr.ForallTelescope body
      (numMotives + numMinors + numIndices + 1) recResult :=
    Hopening.forallSuffix_sameResidual Htelescope
      (concreteRecursorResult_looseBVarRange howner)
  rcases Hreplacement.forallTelescope_residual
      (fun name dom body bi => restoreNestedNode_forall
        (result := result) (env := env) (As := As) (auxRec := auxRec))
      Hbody with ⟨restoredResidual, Hrestored, Hresidual⟩
  have Hidentity := ExprReplacement.restoreNested_concreteRecursorResult
    result env As auxRec numMotives numMinors numIndices ownerIdx
  have hresidual : restoredResidual = recResult := by
    calc
      restoredResidual = recResult.replace
          (result.restoreNestedNode env As auxRec) := Hresidual.eq_replace
      _ = recResult := by
        simpa [recResult] using Hidentity.eq_replace.symm
  subst restoredResidual
  have hfor : input.isForall = true :=
    Htelescope.isForall_of_pos (by omega)
  rw [houtput, hfor]
  have Hcombined := Hselection.prependTelescope Hrestored
  rw [Hopening.initial_size] at Hcombined
  have habstract : recResult.abstractN Hselection.fvars
      (numMotives + numMinors + numIndices + 1) = recResult :=
    FVarsIn.abstractN_eq_self concreteRecursorResult_noFVars _ _
  rw [habstract] at Hcombined
  simpa [recResult] using Hcombined

theorem restoreNested_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name) (input : Expr)
    (Htelescope : RestoreTelescope input result.nparams) :
    NestedRestoration result env auxRec input
      (result.restoreNested env input auxRec) := by
  unfold Lean4Lean.ElimNestedInductive.Result.restoreNested
  generalize hopen :
    Lean4Lean.ElimNestedInductive.Result.openRestoreParams result.nparams
      {} #[] input ({ namePrefix := `_nested_fresh } : NameGenerator) = opened
  rcases opened with ⟨⟨lctx, As, body⟩, outNGen⟩
  have Hopening := openRestoreParams_refinesSelected Htelescope
    (NestedBindingContextWF.empty
      ({ namePrefix := `_nested_fresh } : NameGenerator))
    NestedBoundParams.empty (lctx, As, body) outNGen hopen
  simp
  exact ⟨lctx, As, body,
    body.replace (result.restoreNestedNode env As auxRec),
    Hopening, restoreNested_body result env As auxRec body,
    by simp only [Expr.replace_eq]⟩


end VerifyInductive
end Lean4Lean
