import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Quot

/-! # Verification of quotient initialization

`Environment.addQuot` (Lean4Lean/Quot.lean) checks `Eq` and installs `Quot`,
`Quot.mk`, `Quot.lift` and `Quot.ind`, building their types with
`withLocalDecl`/`mkForall` from a fresh name generator.  This file computes the
four installed types exactly (`QuotInit.tQuot_eq` and siblings), translates
them to the abstract constants `quotConst`, `quotMkConst`, `quotLiftConst` and
`quotIndConst` of `Theory/Quot.lean`, and extends every safety-indexed abstract
environment by `VEnv.addQuot` (`VEnvs.WF.addQuot`).  The abstract rule
`VDecl.WF.quot` needs `VEnv.QuotReady` (abstract `Eq` with its canonical type)
at every safety level; the executable's `checkEqType` does not check the
safety of `Eq`, so this is a hypothesis of `addQuot.WF`, discharged at the top
level by canonical equality (`VEnv.HasCanonicalEq.quotReady`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open Lean4Lean VEnv
open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

/-- Translation of the syntax fragment (bound variables, sorts, constants,
applications and foralls) used by the quotient constants, at binder depth `d`. -/
def plainTr (Us : List Name) : Nat → Expr → Option VExpr
  | d, .bvar i => if i < d then some (.bvar i) else none
  | _, .sort u => (VLevel.ofLevel Us u).map .sort
  | _, .const c us => (us.mapM (VLevel.ofLevel Us)).map (.const c)
  | d, .app f a => do some (.app (← plainTr Us d f) (← plainTr Us d a))
  | d, .forallE _ ty body _ => do some (.forallE (← plainTr Us d ty) (← plainTr Us (d+1) body))
  | _, _ => none

theorem plainTr_find? {As : List VExpr} {i : Nat} (h : i < As.length) :
    ∃ A, VLCtx.find? (As.map fun A => ((none : Option (FVarId × List FVarId)), VLocalDecl.vlam A))
      (.inl i) = some (.bvar i, A) := by
  induction As generalizing i with
  | nil => cases h
  | cons A As ih =>
    cases i with
    | zero => exact ⟨_, rfl⟩
    | succ i =>
      obtain ⟨B, hB⟩ := ih (Nat.lt_of_succ_lt_succ h)
      refine ⟨B.liftN 1, ?_⟩
      simp [VLCtx.find?, VLCtx.next, hB, VLocalDecl.depth, VExpr.liftN]

theorem TrExprS.ofPlainTr {env : VEnv} {Us : List Name} (henv : env.Ordered) :
    ∀ {e : Expr} {e' : VExpr} {As : List VExpr},
      plainTr Us As.length e = some e' →
      OnCtx As (env.IsType Us.length) →
      VExpr.WF env Us.length As e' →
      TrExprS env Us (As.map fun A => (none, .vlam A)) e e'
  | .bvar i, e', As, h, _, _ => by
    simp only [plainTr] at h
    split at h <;> cases h
    obtain ⟨A, hA⟩ := plainTr_find? ‹i < As.length›
    exact .bvar hA
  | .sort u, e', As, h, _, _ => by
    simp only [plainTr, Option.map_eq_some_iff] at h
    obtain ⟨u', hu, rfl⟩ := h
    exact .sort hu
  | .const c us, e', As, h, hΓ, hwf => by
    simp only [plainTr, Option.map_eq_some_iff] at h
    obtain ⟨us', hus, rfl⟩ := h
    obtain ⟨ci, hci, -, hlen⟩ := hwf.const_inv henv hΓ
    exact .const hci hus ((List.mapM_eq_some.1 hus).length_eq.trans hlen)
  | .app f a, e', As, h, hΓ, hwf => by
    simp only [plainTr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨f', hf, a', ha, rfl⟩ := h
    obtain ⟨A, B, h1, h2⟩ := hwf.app_inv henv hΓ
    have := VLCtx.toCtx_map_anonymousLams As
    refine .app (by rwa [this]) (by rwa [this]) (ofPlainTr henv hf hΓ ⟨_, h1⟩)
      (ofPlainTr henv ha hΓ ⟨_, h2⟩)
  | .forallE _ ty body _, e', As, h, hΓ, hwf => by
    simp only [plainTr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty', hty, body', hbody, rfl⟩ := h
    obtain ⟨T, hT⟩ := hwf
    obtain ⟨h1, h2⟩ := HasType.forallE_inv henv hT
    have := VLCtx.toCtx_map_anonymousLams As
    refine .forallE (by rwa [this]) (by rwa [this]) (ofPlainTr henv hty hΓ ?_) ?_
    · obtain ⟨_, h⟩ := h1; exact ⟨_, h⟩
    · have := ofPlainTr (As := ty' :: As) henv hbody ⟨hΓ, h1⟩ (by obtain ⟨_, h⟩ := h2; exact ⟨_, h⟩)
      simpa using this
  | .fvar _, _, _, h, _, _ | .mvar _, _, _, h, _, _ | .lam .., _, _, h, _, _
  | .letE .., _, _, h, _, _ | .lit _, _, _, h, _, _ | .mdata .., _, _, h, _, _
  | .proj .., _, _, h, _, _ => by simp [plainTr] at h

/-! ### The executable's quotient constants

`Environment.addQuot` runs in `ExprBuildT` from the empty local context and
the default name generator, so its free variables are `_uniq.1`, `_uniq.2`,
... in binding order.  The definitions below replay its local contexts and
`mkForall` calls literally (`tQuot`, `tMk`, `tLift`, `tInd`), and the `*C`
definitions are the closed results, proved equal in `tQuot_eq` and siblings. -/

namespace QuotInit

/-- The `k`-th free variable produced by the default name generator. -/
def fid (k : Nat) : FVarId := ⟨Name.mkNum `_uniq k⟩
def u : Level := .param `u
def v : Level := .param `v
def α : Expr := .fvar (fid 1)
def r : Expr := .fvar (fid 2)
def a : Expr := .fvar (fid 3)
def β : Expr := .fvar (fid 4)
def f : Expr := .fvar (fid 5)
def b : Expr := .fvar (fid 6)
def q : Expr := .fvar (fid 5)
def L1 : LocalContext := ({} : LocalContext).mkLocalDecl (fid 1) `α (.sort u) .implicit
def L2 : LocalContext :=
  L1.mkLocalDecl (fid 2) `r (Expr.arrow α (Expr.arrow α Expr.prop)) .default
def L3 : LocalContext := L2.mkLocalDecl (fid 3) `a α .default
def L2' : LocalContext :=
  L1.mkLocalDecl (fid 2) `r (Expr.arrow α (Expr.arrow α Expr.prop)) .implicit
def L3' : LocalContext := L2'.mkLocalDecl (fid 3) `a α .default
def quot_r : Expr := mkApp2 (.const ``Quot [u]) α r
def L4 : LocalContext := L3'.mkLocalDecl (fid 4) `β (.sort v) .implicit
def L5 : LocalContext := L4.mkLocalDecl (fid 5) `f (Expr.arrow α β) .default
def L6 : LocalContext := L5.mkLocalDecl (fid 6) `b α .default
def L4' : LocalContext := L3'.mkLocalDecl (fid 4) `β (Expr.arrow quot_r Expr.prop) .implicit
def L5' : LocalContext := L4'.mkLocalDecl (fid 5) `q quot_r .default
def sanity : Expr := L6.mkForall #[a, b]
  (Expr.arrow (mkApp2 r a b) (mkApp3 (.const ``Eq [v]) β (.app f a) (.app f b)))
def quotMk_a : Expr := mkApp3 (.const ``Quot.mk [u]) α r a
def all_quot : Expr := L4'.mkForall #[a] (.app β quotMk_a)
def tQuot : Expr := L2.mkForall #[α, r] (.sort u)
def tMk : Expr := L3.mkForall #[α, r, a] quot_r
def tLift : Expr := L6.mkForall #[α, r, β, f] (Expr.arrow sanity (Expr.arrow quot_r β))
def tInd : Expr :=
  L5'.mkForall #[α, r, β] (.forallE `mk all_quot (L5'.mkForall #[q] (.app β q)) .default)
def tQuotC : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.sort (.param `u)) .default) .implicit
def tMkC : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.forallE `a (.bvar 1) (.app (.app (.const ``Quot [.param `u]) (.bvar 2)) (.bvar 1)) .default)
      .default) .implicit
def tLiftC : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.forallE `β (.sort (.param `v))
        (.forallE `f (.forallE `a (.bvar 2) (.bvar 1) .default)
          (.forallE `a
            (.forallE `a (.bvar 3)
              (.forallE `b (.bvar 4)
                (.forallE `a (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const ``Eq [.param `v]) (.bvar 4))
                    (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1)))
                  .default) .default) .default)
            (.forallE `a (.app (.app (.const ``Quot [.param `u]) (.bvar 4)) (.bvar 3))
              (.bvar 3) .default)
            .default) .default) .implicit) .implicit) .implicit
def tIndC : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.forallE `β
        (.forallE `a (.app (.app (.const ``Quot [.param `u]) (.bvar 1)) (.bvar 0))
          (.sort .zero) .default)
        (.forallE `mk
          (.forallE `a (.bvar 2)
            (.app (.bvar 1) (.app (.app (.app (.const ``Quot.mk [.param `u]) (.bvar 3))
              (.bvar 2)) (.bvar 0))) .default)
          (.forallE `q (.app (.app (.const ``Quot [.param `u]) (.bvar 3)) (.bvar 2))
            (.app (.bvar 2) (.bvar 0)) .default)
          .default) .implicit) .implicit) .implicit


theorem find?_mkLocalDecl {lctx : LocalContext} (h : lctx.fvarIdToDecl.WF)
    {fv x : FVarId} {n : Name} {t : Expr} {bi : BinderInfo} :
    (lctx.mkLocalDecl fv n t bi).find? x =
      if fv == x then some (.cdecl lctx.decls.size fv n t bi .default) else lctx.find? x := by
  simp only [LocalContext.mkLocalDecl, LocalContext.find?, h.find?_insert]

theorem wf0 : ({} : LocalContext).fvarIdToDecl.WF := .empty

theorem mkForall_eq_fold {lctx : LocalContext} {xs : List FVarId} {b : Expr}
    (hex : ∀ x ∈ xs, ∃ d, lctx.find? x = some d)
    (nd : xs.Nodup) (hb : Closed b) (hdecl : LocalContext.DeclsClosed lctx xs) :
    lctx.mkForall (xs.map .fvar).toArray b =
      xs.foldr (fun a e => LocalContext.mkBindingList1 false lctx [] a (e.abstract1 a)) b := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq' hex nd hb hdecl,
    LocalContext.mkBindingList_eq_fold hex nd]

theorem wf1 : L1.fvarIdToDecl.WF := wf0.insert
theorem wf2 : L2.fvarIdToDecl.WF := wf1.insert
theorem wf2' : L2'.fvarIdToDecl.WF := wf1.insert
theorem wf3' : L3'.fvarIdToDecl.WF := wf2'.insert
theorem wf4 : L4.fvarIdToDecl.WF := wf3'.insert
theorem wf5 : L5.fvarIdToDecl.WF := wf4.insert
theorem wf4' : L4'.fvarIdToDecl.WF := wf3'.insert

theorem tQuot_eq : tQuot = tQuotC := by
  have hf : ∀ x, L2.find? x = if fid 2 == x then some (.cdecl L1.decls.size (fid 2) `r
      (Expr.arrow α (Expr.arrow α Expr.prop)) .default .default)
      else if fid 1 == x then some (.cdecl 0 (fid 1) `α (.sort u) .implicit .default)
      else none := by
    intro x
    rw [L2, find?_mkLocalDecl wf1, L1, find?_mkLocalDecl wf0, LocalContext.find?_empty]
  unfold tQuot
  rw [show #[α, r] = ([fid 1, fid 2].map Expr.fvar).toArray from rfl, mkForall_eq_fold]
  · simp [hf, LocalContext.mkBindingList1, Expr.abstract1, fid, α, Expr.arrow, Expr.prop, tQuotC, u]
  · intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [hf, fid]
  · simp [fid]
  · trivial
  · intro x hx d hd; simp at hx
    rcases hx with rfl | rfl <;> simp [hf, fid] at hd <;> subst hd <;> trivial

theorem fL1 (x) : L1.find? x =
    if fid 1 == x then some (.cdecl 0 (fid 1) `α (.sort u) .implicit .default) else none := by
  rw [L1, find?_mkLocalDecl wf0, LocalContext.find?_empty]
theorem fL2 (x) : L2.find? x = if fid 2 == x then some (.cdecl L1.decls.size (fid 2) `r
    (Expr.arrow α (Expr.arrow α Expr.prop)) .default .default) else L1.find? x := by
  rw [L2, find?_mkLocalDecl wf1]
theorem fL3 (x) : L3.find? x = if fid 3 == x then some (.cdecl L2.decls.size (fid 3) `a
    α .default .default) else L2.find? x := by
  rw [L3, find?_mkLocalDecl wf2]
theorem fL2' (x) : L2'.find? x = if fid 2 == x then some (.cdecl L1.decls.size (fid 2) `r
    (Expr.arrow α (Expr.arrow α Expr.prop)) .implicit .default) else L1.find? x := by
  rw [L2', find?_mkLocalDecl wf1]
theorem fL3' (x) : L3'.find? x = if fid 3 == x then some (.cdecl L2'.decls.size (fid 3) `a
    α .default .default) else L2'.find? x := by
  rw [L3', find?_mkLocalDecl wf2']
theorem fL4 (x) : L4.find? x = if fid 4 == x then some (.cdecl L3'.decls.size (fid 4) `β
    (.sort v) .implicit .default) else L3'.find? x := by
  rw [L4, find?_mkLocalDecl wf3']
theorem fL5 (x) : L5.find? x = if fid 5 == x then some (.cdecl L4.decls.size (fid 5) `f
    (Expr.arrow α β) .default .default) else L4.find? x := by
  rw [L5, find?_mkLocalDecl wf4]
theorem fL6 (x) : L6.find? x = if fid 6 == x then some (.cdecl L5.decls.size (fid 6) `b
    α .default .default) else L5.find? x := by
  rw [L6, find?_mkLocalDecl wf5]
theorem fL4' (x) : L4'.find? x = if fid 4 == x then some (.cdecl L3'.decls.size (fid 4) `β
    (Expr.arrow quot_r Expr.prop) .implicit .default) else L3'.find? x := by
  rw [L4', find?_mkLocalDecl wf3']
theorem fL5' (x) : L5'.find? x = if fid 5 == x then some (.cdecl L4'.decls.size (fid 5) `q
    quot_r .default .default) else L4'.find? x := by
  rw [L5', find?_mkLocalDecl wf4']

theorem tMk_eq : tMk = tMkC := by
  unfold tMk
  rw [show #[α, r, a] = ([fid 1, fid 2, fid 3].map Expr.fvar).toArray from rfl, mkForall_eq_fold]
  · simp [fL3, fL2, fL1, LocalContext.mkBindingList1, Expr.abstract1, fid, α, r, quot_r,
      Expr.arrow, Expr.prop, tMkC, u]
  · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [fL3, fL2, fL1, fid]
  · simp [fid]
  · simp [quot_r, Closed, α, r]
  · intro x hx d hd; simp at hx
    rcases hx with rfl | rfl | rfl <;> simp [fL3, fL2, fL1, fid] at hd <;> subst hd <;>
      simp [LocalContext.DeclClosed, Closed, α, Expr.arrow, Expr.prop]

def sanityC : Expr :=
  .forallE `a α
    (.forallE `b α
      (.forallE `a (.app (.app r (.bvar 1)) (.bvar 0))
        (.app (.app (.app (.const ``Eq [v]) β) (.app f (.bvar 2))) (.app f (.bvar 1)))
        .default) .default) .default

theorem sanity_eq : sanity = sanityC := by
  unfold sanity
  rw [show #[a, b] = ([fid 3, fid 6].map Expr.fvar).toArray from rfl, mkForall_eq_fold]
  · simp [fL6, fL5, fL4, fL3', fL2', fL1, LocalContext.mkBindingList1, Expr.abstract1, fid,
      α, r, a, b, β, f, Expr.arrow, Expr.prop, sanityC, mkApp2, mkApp3]
  · intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [fL6, fL5, fL4, fL3', fid]
  · simp [fid]
  · simp [Closed, Expr.arrow, mkApp2, mkApp3, r, a, b, β, f]
  · intro x hx d hd; simp at hx
    rcases hx with rfl | rfl <;> simp [fL6, fL5, fL4, fL3', fid] at hd <;> subst hd <;>
      simp [LocalContext.DeclClosed, Closed, α]

theorem tLift_eq : tLift = tLiftC := by
  unfold tLift
  rw [sanity_eq, show #[α, r, β, f] = ([fid 1, fid 2, fid 4, fid 5].map Expr.fvar).toArray from rfl,
    mkForall_eq_fold]
  · simp [fL6, fL5, fL4, fL3', fL2', fL1, LocalContext.mkBindingList1, Expr.abstract1, fid,
      α, r, β, f, Expr.arrow, Expr.prop, sanityC, tLiftC, quot_r, u, v, mkApp2]
  · intro x hx; simp at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [fL6, fL5, fL4, fL3', fL2', fL1, fid]
  · simp [fid]
  · simp [Closed, Expr.arrow, sanityC, quot_r, mkApp2, α, r, β, f]
  · intro x hx d hd; simp at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [fL6, fL5, fL4, fL3', fL2', fL1, fid] at hd <;>
      subst hd <;> simp [LocalContext.DeclClosed, Closed, α, β, Expr.arrow, Expr.prop]

def allQuotC : Expr :=
  .forallE `a α (.app β (.app (.app (.app (.const ``Quot.mk [u]) α) r) (.bvar 0))) .default

theorem allQuot_eq : all_quot = allQuotC := by
  unfold all_quot
  rw [show #[a] = ([fid 3].map Expr.fvar).toArray from rfl, mkForall_eq_fold]
  · simp [fL4', fL3', LocalContext.mkBindingList1, Expr.abstract1, fid,
      α, r, a, β, allQuotC, quotMk_a, mkApp3]
  · intro x hx; simp at hx; subst hx; simp [fL4', fL3', fid]
  · simp
  · simp [Closed, quotMk_a, mkApp3, α, r, a, β]
  · intro x hx d hd; simp at hx; subst hx
    simp [fL4', fL3', fid] at hd; subst hd; simp [LocalContext.DeclClosed, Closed, α]

theorem qbody_eq :
    L5'.mkForall #[q] (.app β q) = .forallE `q quot_r (.app β (.bvar 0)) .default := by
  rw [show #[q] = ([fid 5].map Expr.fvar).toArray from rfl, mkForall_eq_fold]
  · simp [fL5', LocalContext.mkBindingList1, Expr.abstract1, fid, β, q, quot_r, mkApp2, α, r]
  · intro x hx; simp at hx; subst hx; simp [fL5', fid]
  · simp
  · simp [Closed, β, q]
  · intro x hx d hd; simp at hx; subst hx
    simp [fL5', fid] at hd; subst hd; simp [LocalContext.DeclClosed, Closed, quot_r, mkApp2, α, r]

theorem tInd_eq : tInd = tIndC := by
  unfold tInd
  rw [allQuot_eq, qbody_eq,
    show #[α, r, β] = ([fid 1, fid 2, fid 4].map Expr.fvar).toArray from rfl,
    mkForall_eq_fold]
  · simp [fL5', fL4', fL3', fL2', fL1, LocalContext.mkBindingList1, Expr.abstract1, fid,
      α, r, β, Expr.arrow, Expr.prop, allQuotC, tIndC, quot_r, u, mkApp2]
  · intro x hx; simp at hx
    rcases hx with rfl | rfl | rfl <;> simp [fL5', fL4', fL3', fL2', fL1, fid]
  · simp [fid]
  · simp [Closed, allQuotC, quot_r, mkApp2, α, r, β]
  · intro x hx d hd; simp at hx
    rcases hx with rfl | rfl | rfl <;> simp [fL5', fL4', fL3', fL2', fL1, fid] at hd <;>
      subst hd <;>
      simp [LocalContext.DeclClosed, Closed, α, quot_r, mkApp2, r, Expr.arrow, Expr.prop]

def ciQuot : ConstantInfo :=
  .quotInfo { name := ``Quot, kind := .type, levelParams := [`u], type := tQuotC }
def ciMk : ConstantInfo :=
  .quotInfo { name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := tMkC }
def ciLift : ConstantInfo :=
  .quotInfo { name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := tLiftC }
def ciInd : ConstantInfo :=
  .quotInfo { name := ``Quot.ind, kind := .ind, levelParams := [`u], type := tIndC }

theorem plain_quot : plainTr [`u] 0 tQuotC = some quotConst.type := rfl
theorem plain_mk : plainTr [`u] 0 tMkC = some quotMkConst.type := rfl
theorem plain_lift : plainTr [`u, `v] 0 tLiftC = some quotLiftConst.type := rfl
theorem plain_ind : plainTr [`u] 0 tIndC = some quotIndConst.type := rfl

end QuotInit
open QuotInit

/-- The executable's quotient initialization, on a not-yet-initialized
environment, is `checkEqType`, four name checks, and the installation of the
four constants with the exact types computed above. -/
theorem Environment.addQuot_eq (env : Environment) (h : env.quotInit = false) :
    Environment.addQuot env = (do
      checkEqType env
      env.checkName ``Quot
      env.checkName ``Quot.mk
      env.checkName ``Quot.lift
      env.checkName ``Quot.ind
      pure <| markQuotInit <| (((env.add ciQuot).add ciMk).add ciLift).add ciInd) := by
  have : ciQuot =
      .quotInfo { name := ``Quot, kind := .type, levelParams := [`u], type := tQuot } := by
    rw [tQuot_eq]; rfl
  have : ciMk =
      .quotInfo { name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := tMk } := by
    rw [tMk_eq]; rfl
  have : ciLift =
      .quotInfo { name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := tLift } := by
    rw [tLift_eq]; rfl
  have : ciInd =
      .quotInfo { name := ``Quot.ind, kind := .ind, levelParams := [`u], type := tInd } := by
    rw [tInd_eq]; rfl
  simp only [*]
  unfold Environment.addQuot
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem VEnv.addConst_some {env : VEnv} {n : Name} (ci : VConstant)
    (h : env.constants n = none) :
    ∃ env', env.addConst n ci = some env' ∧ env'.constants n = some ci ∧
      ∀ m, n ≠ m → env'.constants m = env.constants m := by
  refine ⟨{ env with constants := fun m => if n = m then some ci else env.constants m },
    by simp [VEnv.addConst, h], by simp, fun m hm => by simp [hm]⟩

theorem trConstant_quot {venv : VEnv} (henv : venv.Ordered) {lps : List Name} {t : Expr}
    {ci' : VConstant} (hlen : lps.length = ci'.uvars)
    (hp : plainTr lps 0 t = some ci'.type) (hwf : ci'.WF venv) (n k) :
    TrConstant .safe venv (.quotInfo { name := n, kind := k, levelParams := lps, type := t }) ci' :=
  ⟨DefinitionSafety.le_rfl, hlen, by
    show TrExprS venv lps [] t ci'.type
    have hwf' : VExpr.WF venv lps.length [] ci'.type := by
      obtain ⟨_, h⟩ := hwf; exact ⟨_, hlen ▸ h⟩
    exact TrExprS.ofPlainTr (As := []) henv hp trivial hwf'⟩

/-- One abstract environment can be extended by the quotient constants, and the
extension is aligned with the executable's installation. -/
theorem AddQuot.exists {C : ConstMap} {venv : VEnv} (hC : C.WF) (henv : venv.Ordered)
    (hq : venv.QuotReady)
    (hv1 : venv.constants ``Quot = none) (hv2 : venv.constants ``Quot.mk = none)
    (hv3 : venv.constants ``Quot.lift = none) (hv4 : venv.constants ``Quot.ind = none)
    (hc1 : C.find? ``Quot = none) (hc2 : C.find? ``Quot.mk = none)
    (hc3 : C.find? ``Quot.lift = none) (hc4 : C.find? ``Quot.ind = none) :
    ∃ venv', AddQuot C ((((C.insert ``Quot ciQuot).insert ``Quot.mk ciMk).insert
      ``Quot.lift ciLift).insert ``Quot.ind ciInd) venv venv' := by
  have hwf1 : quotConst.WF venv := ⟨_, by type_tac⟩
  obtain ⟨e1, h1, q1, k1⟩ := VEnv.addConst_some quotConst hv1
  have o1 : e1.Ordered := .const henv hwf1 h1
  have hwf2 : quotMkConst.WF e1 := ⟨_, by type_tac⟩
  obtain ⟨e2, h2, q2, k2⟩ := VEnv.addConst_some (env := e1) quotMkConst
    (by rw [k1 ``Quot.mk (by decide)]; exact hv2)
  have o2 : e2.Ordered := .const o1 hwf2 h2
  have eq2 : e2.constants ``Eq = some eqConst := by
    rw [k2 ``Eq (by decide), k1 ``Eq (by decide)]; exact hq
  have quot2 : e2.constants ``Quot = some quotConst := by rw [k2 ``Quot (by decide)]; exact q1
  have hwf3 : quotLiftConst.WF e2 := ⟨_, by type_tac⟩
  obtain ⟨e3, h3, q3, k3⟩ := VEnv.addConst_some (env := e2) quotLiftConst
    (by rw [k2 ``Quot.lift (by decide), k1 ``Quot.lift (by decide)]; exact hv3)
  have o3 : e3.Ordered := .const o2 hwf3 h3
  have quot3 : e3.constants ``Quot = some quotConst := by rw [k3 ``Quot (by decide)]; exact quot2
  have mk3 : e3.constants ``Quot.mk = some quotMkConst := by
    rw [k3 ``Quot.mk (by decide)]; exact q2
  have hwf4 : quotIndConst.WF e3 := ⟨_, by type_tac⟩
  obtain ⟨e4, h4, -, -⟩ := VEnv.addConst_some (env := e3) quotIndConst
    (by
      rw [k3 ``Quot.ind (by decide), k2 ``Quot.ind (by decide), k1 ``Quot.ind (by decide)]
      exact hv4)
  have hC1 := hC.insert ``Quot ciQuot hc1
  have m2 : (C.insert ``Quot ciQuot).find? ``Quot.mk = none := by
    rw [hC.find?_insert]; simpa using hc2
  have hC2 := hC1.insert ``Quot.mk ciMk m2
  have m3 : ((C.insert ``Quot ciQuot).insert ``Quot.mk ciMk).find? ``Quot.lift = none := by
    rw [hC1.find?_insert, hC.find?_insert]; simpa using hc3
  have hC3 := hC2.insert ``Quot.lift ciLift m3
  have m4 : (((C.insert ``Quot ciQuot).insert ``Quot.mk ciMk).insert ``Quot.lift ciLift).find?
      ``Quot.ind = none := by
    rw [hC2.find?_insert, hC1.find?_insert, hC.find?_insert]; simpa using hc4
  refine ⟨e4.addDefEq quotDefEq, [`u], tQuotC, e1,
    trConstant_quot henv rfl plain_quot hwf1 _ _, hc1, h1,
    [`u], tMkC, e2, trConstant_quot o1 rfl plain_mk hwf2 _ _, m2, h2,
    [`u, `v], tLiftC, e3, trConstant_quot o2 rfl plain_lift hwf3 _ _, m3, h3,
    [`u], tIndC, e4, trConstant_quot o3 rfl plain_ind hwf4 _ _, m4, h4, rfl, rfl⟩
theorem VEnv.addQuot_cases {venv venv' : VEnv} (h : venv.addQuot = some venv') :
    ∃ e1 e2 e3 e4, venv.addConst ``Quot quotConst = some e1 ∧
      e1.addConst ``Quot.mk quotMkConst = some e2 ∧
      e2.addConst ``Quot.lift quotLiftConst = some e3 ∧
      e3.addConst ``Quot.ind quotIndConst = some e4 ∧ venv' = e4.addDefEq quotDefEq := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, rfl⟩ := h
  exact ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩

theorem VEnv.addQuot_mono {v₁ v₂ w₁ w₂ : VEnv} (H : v₁ ≤ v₂)
    (h₁ : v₁.addQuot = some w₁) (h₂ : v₂.addQuot = some w₂) : w₁ ≤ w₂ := by
  obtain ⟨a1, a2, a3, a4, ha1, ha2, ha3, ha4, rfl⟩ := VEnv.addQuot_cases h₁
  obtain ⟨b1, b2, b3, b4, hb1, hb2, hb3, hb4, rfl⟩ := VEnv.addQuot_cases h₂
  exact VEnv.addDefEq_mono <| VEnv.addConst_mono (VEnv.addConst_mono
    (VEnv.addConst_mono (VEnv.addConst_mono H ha1 hb1) ha2 hb2) ha3 hb3) ha4 hb4

theorem VEnv.HasPrimitives.addQuot {venv venv' : VEnv} (H : venv.HasPrimitives)
    (h : venv.addQuot = some venv')
    (p1 : Environment.primitives.contains ``Quot = false)
    (p2 : Environment.primitives.contains ``Quot.mk = false)
    (p3 : Environment.primitives.contains ``Quot.lift = false)
    (p4 : Environment.primitives.contains ``Quot.ind = false) : venv'.HasPrimitives := by
  obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := VEnv.addQuot_cases h
  exact (((H.addConst p1 h1).addConst p2 h2).addConst p3 h3 |>.addConst p4 h4).addDefEq

/-- The safety-independent invariants of `VEnvs.WF` that only concern the
constant map, together with the safety-indexed metadata coherence over a fixed
family of abstract environments. -/
structure QuotEnvInv (env : Environment) (V : DefinitionSafety → VEnv) : Prop where
  mapWF : env.constants.WF
  safePrimitives : ∀ {n ci}, env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  blocks : ∀ safety, InstalledBlocks safety env (V safety) .complete

theorem QuotEnvInv.add {env : Environment} {V V'} (H : QuotEnvInv env V) (ci : QuotVal)
    (hn : env.find? ci.name = none)
    (hprim : Environment.primitives.contains ci.name = false)
    (hle : ∀ safety, V safety ≤ V' safety)
    (hproj : ∀ safety {S info}, (V' safety).projections S info → (V safety).projections S info) :
    QuotEnvInv (env.add (.quotInfo ci)) V' where
  mapWF := H.mapWF.insert _ _ (by rwa [← H.mapWF.find?'_eq_find?])
  safePrimitives := safePrimitives_add' H.mapWF H.safePrimitives (.quotInfo ci) hn
    (fun h => by
      rw [show (ConstantInfo.quotInfo ci).name = ci.name from rfl, hprim] at h
      cases h)
  blocks s := (H.blocks s).addFresh H.mapWF (ci := .quotInfo ci) hn nofun nofun nofun (hle s)
    (hproj s)

/-- `markQuotInit` only sets the quotient flag; constant lookup is unchanged.
Transport the lookup-based invariants across it. -/
theorem QuotEnvInv.markQuotInit {env : Environment} {V} (H : QuotEnvInv env V) :
    QuotEnvInv (markQuotInit env) V where
  mapWF := H.mapWF
  safePrimitives := H.safePrimitives
  blocks s := (H.blocks s).mapEnvironmentEq (fun _ => rfl) (fun _ => rfl)

theorem QuotEnvInv.find?_add {env : Environment} {V} (H : QuotEnvInv env V) {ci : ConstantInfo}
    (hn : env.find? ci.name = none) {n : Name} (hne : ci.name ≠ n) :
    (env.add ci).find? n = env.find? n := by
  have hn' : env.constants.find? ci.name = none := by rwa [← H.mapWF.find?'_eq_find?]
  change SMap.find?' (env.constants.insert ci.name ci) n = SMap.find?' env.constants n
  rw [(H.mapWF.insert _ _ hn').find?'_eq_find?, H.mapWF.find?_insert, if_neg (by simpa using hne),
    H.mapWF.find?'_eq_find?]

/-- Extending every safety level of a well-formed model by the quotient
constants, as installed by the executable, preserves well-formedness. -/
theorem VEnvs.WF.addQuot {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hq : ∀ safety, (ves.venv safety).QuotReady) (hinit : env.quotInit = false)
    (n1 : env.find? ``Quot = none) (n2 : env.find? ``Quot.mk = none)
    (n3 : env.find? ``Quot.lift = none) (n4 : env.find? ``Quot.ind = none)
    (p1 : Environment.primitives.contains ``Quot = false)
    (p2 : Environment.primitives.contains ``Quot.mk = false)
    (p3 : Environment.primitives.contains ``Quot.lift = false)
    (p4 : Environment.primitives.contains ``Quot.ind = false) :
    ∃ ves' : VEnvs,
      ves'.WF (markQuotInit ((((env.add ciQuot).add ciMk).add ciLift).add ciInd)) ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) := by
  have hC : env.constants.WF := (wf.tr (safety := .safe)).map_wf
  have hc {n} (h : env.find? n = none) : env.constants.find? n = none := by
    rwa [← hC.find?'_eq_find?]
  have hv {n} (s) (h : env.find? n = none) : (ves.venv s).constants n = none :=
    (wf.tr (safety := s)).constants_eq_none h
  have hadd s : ∃ venv', AddQuot env.constants ((((env.add ciQuot).add ciMk).add ciLift).add
      ciInd).constants (ves.venv s) venv' :=
    AddQuot.exists hC (wf.tr (safety := s)).wf.ordered (hq s) (hv s n1) (hv s n2) (hv s n3)
      (hv s n4) (hc n1) (hc n2) (hc n3) (hc n4)
  obtain ⟨ves', hves'⟩ := VEnvs.ofPointwiseExists hadd
  have hsome s : (ves.venv s).addQuot = some (ves'.venv s) := (hves' s).to_addQuot
  have hle s : ves.venv s ≤ ves'.venv s := (hves' s).le
  -- the constant-map invariants through the four insertions
  have I0 : QuotEnvInv env ves.venv :=
    { mapWF := hC
      safePrimitives := wf.safePrimitives
      blocks := fun _ => wf.blocks }
  have I1 : QuotEnvInv (env.add ciQuot) ves'.venv :=
    I0.add { name := ``Quot, kind := .type, levelParams := [`u], type := tQuotC } n1 p1 hle
      fun s _ _ hp => by rwa [VEnv.addQuot_projections (hsome s)] at hp
  have m2 : (env.add ciQuot).find? ``Quot.mk = none := by
    rw [I0.find?_add (ci := ciQuot) n1 (by decide)]; exact n2
  have I2 : QuotEnvInv ((env.add ciQuot).add ciMk) ves'.venv :=
    I1.add { name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := tMkC }
      m2 p2 (fun _ => VEnv.LE.rfl) fun _ _ _ => id
  have m3 : ((env.add ciQuot).add ciMk).find? ``Quot.lift = none := by
    rw [I1.find?_add (ci := ciMk) m2 (by decide), I0.find?_add (ci := ciQuot) n1 (by decide)]
    exact n3
  have I3 : QuotEnvInv (((env.add ciQuot).add ciMk).add ciLift) ves'.venv :=
    I2.add { name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := tLiftC }
      m3 p3 (fun _ => VEnv.LE.rfl) fun _ _ _ => id
  have m4 : (((env.add ciQuot).add ciMk).add ciLift).find? ``Quot.ind = none := by
    rw [I2.find?_add (ci := ciLift) m3 (by decide), I1.find?_add (ci := ciMk) m2 (by decide),
      I0.find?_add (ci := ciQuot) n1 (by decide)]
    exact n4
  have I4 : QuotEnvInv ((((env.add ciQuot).add ciMk).add ciLift).add ciInd) ves'.venv :=
    I3.add { name := ``Quot.ind, kind := .ind, levelParams := [`u], type := tIndC }
      m4 p4 (fun _ => VEnv.LE.rfl) fun _ _ _ => id
  have I5 := I4.markQuotInit
  refine ⟨ves', ?_, hle⟩
  exact {
    tr {safety} := by
      change TrEnv' safety ((((env.add ciQuot).add ciMk).add ciLift).add ciInd).constants true _
      have := wf.tr (safety := safety)
      unfold TrEnv at this
      rw [hinit] at this
      exact .quot (hq safety) (hves' safety) this
    hasPrimitives {safety} := wf.hasPrimitives.addQuot (hsome safety) p1 p2 p3 p4
    safePrimitives := I5.safePrimitives
    blocks {safety} := I5.blocks safety
    mono {safety safety'} h := VEnv.addQuot_mono (wf.mono h) (hsome safety') (hsome safety) }

/-- Quotient initialization preserves well-formedness and extends every
safety-indexed abstract environment.  `VEnv.QuotReady` is required at every
safety level: the abstract rule `VDecl.WF.quot` types `Quot.lift` against `Eq`
in each of them, while the executable's `checkEqType` only inspects the shape
of `Eq`, not its safety. -/
theorem addQuot.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hq : ∀ safety, (ves.venv safety).QuotReady) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) := by
  cases hinit : env.quotInit with
  | true =>
    unfold Environment.addQuot
    simp only [hinit, ↓reduceIte]
    exact .pure ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  | false =>
    rw [Environment.addQuot_eq env hinit]
    have hC := (wf.tr (safety := .safe)).map_wf
    have prim {n : Name} (h : Environment.primitives.contains n → false) :
        Environment.primitives.contains n = false := by
      cases h' : Environment.primitives.contains n
      · rfl
      · simp [h'] at h
    refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
    refine (checkName.WF hC ``Quot false).bind fun _ ⟨n1, p1⟩ => ?_
    refine (checkName.WF hC ``Quot.mk false).bind fun _ ⟨n2, p2⟩ => ?_
    refine (checkName.WF hC ``Quot.lift false).bind fun _ ⟨n3, p3⟩ => ?_
    refine (checkName.WF hC ``Quot.ind false).bind fun _ ⟨n4, p4⟩ => ?_
    exact .pure (wf.addQuot hq hinit n1 n2 n3 n4 (prim p1) (prim p2) (prim p3) (prim p4))

end Lean4Lean
