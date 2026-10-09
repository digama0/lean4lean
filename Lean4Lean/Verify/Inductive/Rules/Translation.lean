import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Recursor.Signature.RecursiveShapeTranslations
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorFields
import Lean4Lean.Verify.Inductive.Rules.EquationWF
import Lean4Lean.Verify.Inductive.Rules.LhsTranslation

/-! Translation of the generated iota rules to the generator's equations.

The right-hand side of every installed recursor rule is a literal instantiation of a
rule template (`RecursorCheck.rulesLiteral`).  Its
translation target is determined syntactically: every constructor of
`TrExprS` fixes its output from the source syntax and the context, and only
the typing side conditions of `app`, `lam`, `forallE` and `letE` carry
semantic content.  `TrSyn` (`Verify/Typing/Syntactic/Basic.lean`) is the typing-free shadow of `TrExprS`.  This
file builds, constructively from the shape translations of the generated
instance, a `TrSyn` derivation of each rule's right-hand side whose
target is the generator's `Instance.equation` right-hand side; the typed
translation then follows from any typed translation of the same rule
(`RecursorCheck.ruleRhsTranslations`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open VerifyInductive

theorem TrExprS.toSyn {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') : TrSyn Us Δ e e' := H.toTrSyn

/-- A typed translation of a source expression whose syntactic translation is
known has exactly that target. -/
theorem TrExprS.of_syn {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e₁ e₂ : VExpr}
    (H : TrExprS env Us Δ e e₁) (S : TrSyn Us Δ e e₂) : TrExprS env Us Δ e e₂ :=
  H.toTrSyn.unique S ▸ H

theorem TrSyn.transportAbstract {Us : List Name} {doms doms' : List VExpr} {e : Lean.Expr}
    {e' : VExpr} (hlen : doms.length = doms'.length)
    (H : TrSyn Us (abstractForallContext doms []) e e') :
    TrSyn Us (abstractForallContext doms' []) e e' :=
  H.transport (abstractForallContext.isUniqueCtx hlen)

theorem TrSyn.mkAppList {Us : List Name} {Δ : VLCtx} {f : Lean.Expr} {f' : VExpr}
    {args : List Lean.Expr} {args' : List VExpr}
    (Hf : TrSyn Us Δ f f') (Hargs : List.Forall₂ (TrSyn Us Δ) args args') :
    TrSyn Us Δ (Expr.mkAppList f args) (VExpr.mkApps f' args') := by
  induction Hargs generalizing f f' with
  | nil => simpa [VExpr.mkApps] using Hf
  | cons ha _ ih =>
    simpa [VExpr.mkApps] using ih (Hf.app ha)

theorem TrSyn.bvar_abstract {Us : List Name} (domains : List VExpr) (Δ : VLCtx) (i : Nat)
    (hi : i < domains.length) :
    TrSyn Us (abstractForallContext domains Δ) (.bvar i) (.bvar i) := by
  rcases abstractForallContext.find?_bvar domains Δ i hi with ⟨type, hfind⟩
  exact .bvar hfind

/-- Lambda telescope over the literal binder prefix of a forall telescope:
the `i`-th lambda domain is the `i`-th literal forall domain. -/
theorem TrSyn.lambdaTelescope {Us : List Name} {n : Nat} {Fa L res : Lean.Expr}
    {doms : List VExpr} {Δ : VLCtx} {tgt : VExpr}
    (Hsame : Expr.SameForallLambdaPrefix n Fa L)
    (HL : Expr.LambdaTelescope L n res) (hlen : doms.length = n)
    (Hdoms : ∀ i (hi : i < doms.length),
      TrSyn Us (abstractForallContext (doms.take i) Δ)
        (Expr.forallDomainList n Fa)[i]! (doms[i]'hi))
    (Hres : TrSyn Us (abstractForallContext doms Δ) res tgt) :
    TrSyn Us Δ L (VExpr.wrapLams doms tgt) := by
  induction Hsame generalizing doms Δ res with
  | nil =>
    cases HL
    have : doms = [] := List.eq_nil_of_length_eq_zero hlen
    subst this
    simpa [abstractForallContext, VExpr.wrapLams] using Hres
  | @cons n fb lb name dom bi Hsame ih =>
    cases HL with
    | cons HL =>
      cases doms with
      | nil => simp at hlen
      | cons d ds =>
        have h0 := Hdoms 0 (by simp)
        simp only [List.take_zero, Expr.forallDomainList, List.getElem!_cons_zero,
          List.getElem_cons_zero] at h0
        have h0' : TrSyn Us Δ dom d := by simpa [abstractForallContext] using h0
        simp only [VExpr.wrapLams, List.foldr_cons]
        refine .lam h0' ?_
        have := ih (doms := ds) (Δ := (none, .vlam d) :: Δ) HL (by simpa using hlen) ?_ ?_
        · simpa [VExpr.wrapLams] using this
        · intro i hi
          have h := Hdoms (i + 1) (by simpa using hi)
          simpa [Expr.forallDomainList, abstractForallContext, List.take_succ_cons,
            List.map_append, List.append_assoc] using h
        · simpa [abstractForallContext, List.map_append, List.append_assoc] using Hres

theorem Expr.abstractN_mkAppList (fn : Lean.Expr) (args : List Lean.Expr) (xs : List FVarId)
    (k : Nat) :
    (Lean.Expr.mkAppList fn args).abstractN xs k =
      Lean.Expr.mkAppList (fn.abstractN xs k) (args.map fun a => a.abstractN xs k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a l ih => simp only [Lean.Expr.mkAppList, ih, List.map_cons]; rfl

theorem Expr.instantiate1'_mkAppList (fn : Lean.Expr) (args : List Lean.Expr) (v : Lean.Expr)
    (k : Nat) :
    (Lean.Expr.mkAppList fn args).instantiate1' v k =
      Lean.Expr.mkAppList (fn.instantiate1' v k) (args.map fun a => a.instantiate1' v k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a l ih => simp only [Lean.Expr.mkAppList, ih, List.map_cons]; rfl

theorem Expr.closed_mkAppList {fn : Lean.Expr} {args : List Lean.Expr} {k : Nat}
    (hfn : Closed fn k) (hargs : ∀ a ∈ args, Closed a k) :
    Closed (Lean.Expr.mkAppList fn args) k := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons a l ih =>
    exact ih ⟨hfn, hargs a (by simp)⟩ (fun b hb => hargs b (by simp [hb]))

/-- Abstracting a duplicate-free list of variables in its own order yields the
canonical descending bound-variable spine. -/
theorem Expr.abstractN_fvars_spine {xs : List FVarId} (hnd : xs.Nodup) (k : Nat) :
    (xs.map Lean.Expr.fvar).map (fun a => a.abstractN xs k) =
      (List.range xs.length).reverse.map fun i => Lean.Expr.bvar (k + i) := by
  apply List.ext_getElem
  · simp
  · intro l h1 h2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    simp only [List.length_map] at h1
    rw [Expr.abstractN_fvar_getElem hnd l h1]

theorem TrSyn.bvarSpine {Us : List Name} (domains : List VExpr) (Δ : VLCtx) (count below : Nat)
    (h : count + below ≤ domains.length) :
    List.Forall₂ (TrSyn Us (abstractForallContext domains Δ))
      ((List.range count).reverse.map fun i => Lean.Expr.bvar (below + i))
      (InductiveSignature.vars count below) := by
  unfold InductiveSignature.vars
  apply List.forall₂_of_getElem (by simp)
  intro l h1 h2
  simp only [List.getElem_map]
  apply TrSyn.bvar_abstract
  simp only [List.length_map, List.length_reverse, List.length_range] at h1
  simp only [List.getElem_reverse, List.getElem_range, List.length_range]
  omega

theorem VerifyInductive.Expr.SameForallLambdaPrefix.instantiate1'
    (H : Expr.SameForallLambdaPrefix n forallBody lambdaBody) (v : Lean.Expr) (k : Nat) :
    Expr.SameForallLambdaPrefix n
      (forallBody.instantiate1' v k) (lambdaBody.instantiate1' v k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Lean.Expr.instantiate1']
    exact .cons (ih (k + 1))

theorem VerifyInductive.Expr.ForallTelescope.forallDomainList_abstractN
    (H : Expr.ForallTelescope source n residual) (fvs : List FVarId) (k : Nat)
    {i : Nat} (hi : i < n) :
    (Expr.forallDomainList n (source.abstractN fvs k))[i]! =
      (Expr.forallDomainList n source)[i]!.abstractN fvs (k + i) := by
  induction H generalizing k i with
  | nil => omega
  | cons _ ih =>
    simp only [Lean.Expr.abstractN]
    cases i with
    | zero => simp [Expr.forallDomainList]
    | succ i =>
      simp only [Expr.forallDomainList, List.getElem!_cons_succ]
      rw [ih (k + 1) (by omega)]
      congr 1
      omega

/-- A forall telescope with closed residual whose `i`-th domain is closed at
depth `k + i` is closed at depth `k`. -/
theorem VerifyInductive.Expr.ForallTelescope.closed_of_domains
    (H : Expr.ForallTelescope source n residual) (k : Nat)
    (hdom : ∀ i < n, Closed (Expr.forallDomainList n source)[i]! (k + i))
    (hres : Closed residual (k + n)) : Closed source k := by
  induction H generalizing k with
  | nil => simpa using hres
  | @cons body arity result name dom bi Htel ih =>
    refine ⟨?_, ih (k + 1) ?_ ?_⟩
    · simpa [Expr.forallDomainList] using hdom 0 (by omega)
    · intro i hi
      have := hdom (i + 1) (by omega)
      simpa [Expr.forallDomainList, Nat.add_assoc, Nat.add_comm 1] using this
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hres

/-- Syntactic translation of one generated recursive call, closed over the
fields and the outer binders: a lambda telescope over the call's argument
domains whose body applies the recursor to the outer binders, the translated
target indices, and the recursive field applied to the arguments. -/
theorem TrSyn.recursiveCall {Us : List Name}
    {lctxC : LocalContext} {args : Array Lean.Expr} {A : List FVarId}
    (hargs : args = (A.map Lean.Expr.fvar).toArray)
    (hdecl : ∀ fv ∈ A, ∃ index name type bi kind,
      lctxC.find? fv = some (.cdecl index fv name type bi kind))
    (hA : A.Nodup)
    {I : Array Lean.Expr} {F PMN : List FVarId} {pos : Nat} (hpos : pos < F.length)
    (hF : F.Nodup) (hPMN : PMN.Nodup) (hdisj : ∀ x ∈ PMN, x ∉ F)
    (hmajA : F[pos] ∉ A)
    {name : Name} {lvls : List Level} {us' : List VLevel}
    (hlvls : lvls.mapM (VLevel.ofLevel Us) = some us')
    {Γdoms domsR idxG : List VExpr} (hΓ : Γdoms.length = PMN.length + F.length)
    (hdomsLen : domsR.length = args.size)
    (hFa : Closed (lctxC.mkForall args (.sort .zero)))
    (Hdoms : ∀ i (hi : i < domsR.length),
      TrSyn Us (abstractForallContext (Γdoms ++ domsR.take i) [])
        (((Expr.forallDomainList args.size (lctxC.mkForall args (.sort .zero)))[i]!.abstractN
          F i).abstractN PMN (F.length + i))
        (domsR[i]'hi))
    (hIclosed : ∀ e ∈ I.toList, Closed (e.abstractN A) args.size)
    (Hidx : List.Forall₂ (TrSyn Us (abstractForallContext (Γdoms ++ domsR) []))
      (I.toList.map fun e =>
        ((e.abstractN A).abstractN F args.size).abstractN PMN (F.length + args.size)) idxG) :
    TrSyn Us (abstractForallContext Γdoms [])
      ((((lctxC.mkLambda args ((mkAppN (.bvar args.size) I).app
          (mkAppN (.fvar F[pos]) args))).instantiate1
          (Lean.Expr.mkAppList (.const name lvls) (PMN.map .fvar))).abstractN F).abstractN
          PMN F.length)
      (VExpr.wrapLams domsR (VExpr.mkApps (.const name us')
        (InductiveSignature.vars PMN.length (F.length + args.size) ++ idxG ++
          [VExpr.mkApps (.bvar (F.length - 1 - pos + args.size))
            (InductiveSignature.vars args.size 0)]))) := by
  subst hargs
  have hn : (A.map Lean.Expr.fvar).toArray.size = A.length := by simp
  rw [hn] at hdomsLen Hdoms hIclosed Hidx ⊢
  let recApp := Lean.Expr.mkAppList (.const name lvls) (PMN.map .fvar)
  let T : Lean.Expr := (mkAppN (.bvar A.length) I).app
    (mkAppN (.fvar F[pos]) (A.map Lean.Expr.fvar).toArray)
  let Hsel : CDeclArray lctxC (A.map Lean.Expr.fvar).toArray := ⟨A, rfl, hdecl⟩
  have Hsame := Hsel.sameForallLambdaPrefix (show A.Nodup from hA) (.sort .zero) T
  rw [hn] at Hsame
  have HL := LocalContext.mkLambda_fvars_lambdaTelescopeN (body := T) hdecl
  have HFtel := LocalContext.mkForall_fvars_forallTelescope (body := .sort .zero) hdecl
  have hFa0 : (lctxC.mkForall (A.map Lean.Expr.fvar).toArray (.sort .zero)).instantiate1' recApp 0 =
      lctxC.mkForall (A.map Lean.Expr.fvar).toArray (.sort .zero) :=
    Lean.Expr.instantiate1'_eq_self (by simpa using hFa.looseBVarRange_le)
  have Hsame1 := Hsame.instantiate1' recApp 0
  rw [hFa0] at Hsame1
  have HL1 := HL.instantiate1 recApp
  have Hsame2 := (Hsame1.abstractN F 0).abstractN PMN F.length
  have HL2 := (HL1.abstractN F 0).abstractN PMN F.length
  have HFtel1 := HFtel.abstractN F 0
  rw [Lean.Expr.instantiate1_eq] at HL2 ⊢
  refine TrSyn.lambdaTelescope Hsame2 HL2 hdomsLen ?_ ?_
  · intro i hi
    rw [Expr.ForallTelescope.forallDomainList_abstractN HFtel1 PMN F.length (by omega),
      Expr.ForallTelescope.forallDomainList_abstractN HFtel F 0 (by omega),
      abstractForallContext_append, Nat.zero_add]
    exact Hdoms i hi
  · rw [abstractForallContext_append, Nat.zero_add]
    have hrecClosed : recApp.looseBVarRange' = 0 := by
      have : Closed recApp := Expr.closed_mkAppList trivial (by
        intro a ha; simp only [List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; trivial)
      exact this.looseBVarRange_zero
    have hrecF : recApp.abstractN F A.length = recApp := by
      simp only [recApp, Expr.abstractN_mkAppList]
      congr 1
      rw [List.map_map]
      conv => rhs; rw [← List.map_id (List.map Lean.Expr.fvar PMN)]
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      exact Expr.abstractN_fvar_of_not_mem (hdisj x hx)
    have hargsA := Expr.abstractN_fvars_spine hA 0
    have hsrc : (((T.abstractN A).instantiate1' recApp A.length).abstractN F A.length).abstractN
        PMN (F.length + A.length) =
        .app (Lean.Expr.mkAppList (Lean.Expr.mkAppList (.const name lvls)
            ((List.range PMN.length).reverse.map fun i => .bvar (F.length + A.length + i)))
            (I.toList.map fun e =>
              ((e.abstractN A).abstractN F A.length).abstractN PMN (F.length + A.length)))
          (Lean.Expr.mkAppList (.bvar (A.length + (F.length - 1 - pos)))
            ((List.range A.length).reverse.map fun i => .bvar (0 + i))) := by
      simp only [T, Lean.Expr.mkAppN_eq_mkAppList, Expr.abstractN_app, Expr.abstractN_mkAppList,
        hargsA]
      have hb : ∀ (i : Nat) (xs : List FVarId) (k : Nat),
          (Lean.Expr.bvar i).abstractN xs k = .bvar i := fun _ _ _ => rfl
      have hspineI : ((List.range A.length).reverse.map fun i => Lean.Expr.bvar (0 + i)).map
            (fun e => e.instantiate1' recApp A.length) =
          (List.range A.length).reverse.map fun i => Lean.Expr.bvar (0 + i) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [List.mem_reverse, List.mem_range] at hi
        have hi' : 0 + i < A.length := by omega
        simp only [Function.comp_apply, Lean.Expr.instantiate1', hi', if_true]
      have hidxI : (I.toList.map fun e => e.abstractN A).map
            (fun e => e.instantiate1' recApp A.length) = I.toList.map fun e => e.abstractN A := by
        rw [List.map_map]
        apply List.map_congr_left
        intro e he
        exact Lean.Expr.instantiate1'_eq_self (hIclosed e he).looseBVarRange_le
      have hheadI : (Lean.Expr.bvar A.length).instantiate1' recApp A.length = recApp := by
        simp only [Lean.Expr.instantiate1', Nat.lt_irrefl, if_false, if_true]
        exact Lean.Expr.liftLooseBVars_eq_self (by omega)
      have hmaj : (Lean.Expr.fvar F[pos]).abstractN A = .fvar F[pos] :=
        Expr.abstractN_fvar_of_not_mem hmajA
      have hmajF : (Lean.Expr.fvar F[pos]).abstractN F A.length =
          .bvar (A.length + (F.length - 1 - pos)) := Expr.abstractN_fvar_getElem hF pos hpos
      have hrecPMN : recApp.abstractN PMN (F.length + A.length) =
          Lean.Expr.mkAppList (.const name lvls)
            ((List.range PMN.length).reverse.map fun i => .bvar (F.length + A.length + i)) := by
        simp only [recApp, Expr.abstractN_mkAppList]
        rw [Expr.abstractN_fvars_spine hPMN]
        rfl
      have happI : ∀ (f a v : Lean.Expr) (k : Nat),
          (Lean.Expr.app f a).instantiate1' v k = .app (f.instantiate1' v k) (a.instantiate1' v k) :=
        fun _ _ _ _ => rfl
      have hfvI : ∀ (x : FVarId) (v : Lean.Expr) (k : Nat),
          (Lean.Expr.fvar x).instantiate1' v k = .fvar x := fun _ _ _ => rfl
      simp only [hb, hmaj, happI, hfvI, Expr.instantiate1'_mkAppList, hspineI, hidxI,
        hheadI, Expr.abstractN_mkAppList, Expr.abstractN_app, hrecF, hmajF, hrecPMN,
        List.map_map]
      rfl
    rw [hsrc]
    have hlen : (Γdoms ++ domsR).length = PMN.length + F.length + A.length := by
      simp [hΓ, hdomsLen]
    have Hhead := TrSyn.mkAppList (TrSyn.const (Δ := abstractForallContext (Γdoms ++ domsR) [])
      (c := name) hlvls)
      (TrSyn.bvarSpine (Us := Us) (Γdoms ++ domsR) [] PMN.length (F.length + A.length)
        (by omega))
    have Hmaj := TrSyn.mkAppList (TrSyn.bvar_abstract (Us := Us) (Γdoms ++ domsR) []
      (A.length + (F.length - 1 - pos)) (by omega))
      (TrSyn.bvarSpine (Us := Us) (Γdoms ++ domsR) [] A.length 0 (by omega))
    have := TrSyn.app (TrSyn.mkAppList Hhead Hidx) Hmaj
    simp only [VExpr.mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil] at this ⊢
    rw [show F.length - 1 - pos + A.length = A.length + (F.length - 1 - pos) by omega]
    exact this

/-- Syntactic translation of a rule body `minor fields calls`, closed over the
fields and the outer binders. -/
theorem TrSyn.ruleBody {Us : List Name} {F PMN : List FVarId} {m : Nat}
    (hm : m < PMN.length) (hF : F.Nodup) (hPMN : PMN.Nodup) (hdisj : ∀ x ∈ PMN, x ∉ F)
    {Γdoms : List VExpr} (hΓ : Γdoms.length = PMN.length + F.length)
    {calls : Array Lean.Expr} {callsG : List VExpr}
    (Hcalls : List.Forall₂ (TrSyn Us (abstractForallContext Γdoms []))
      (calls.toList.map fun c => (c.abstractN F).abstractN PMN F.length) callsG) :
    TrSyn Us (abstractForallContext Γdoms [])
      (((mkAppN (mkAppN (.fvar PMN[m]) (F.map Lean.Expr.fvar).toArray) calls).abstractN F).abstractN
        PMN F.length)
      (VExpr.mkApps (.bvar (F.length + (PMN.length - 1 - m)))
        (InductiveSignature.vars F.length 0 ++ callsG)) := by
  have hx : (Lean.Expr.fvar PMN[m]).abstractN F = .fvar PMN[m] :=
    Expr.abstractN_fvar_of_not_mem (hdisj _ (List.getElem_mem hm))
  have hx' : (Lean.Expr.fvar PMN[m]).abstractN PMN F.length = .bvar (F.length + (PMN.length - 1 - m)) :=
    Expr.abstractN_fvar_getElem hPMN m hm
  have hfields : List.map ((fun a => a.abstractN PMN F.length) ∘ (fun a => a.abstractN F) ∘
      Lean.Expr.fvar) F = (List.range F.length).reverse.map fun i => Lean.Expr.bvar (0 + i) := by
    have h := Expr.abstractN_fvars_spine hF 0
    rw [List.map_map] at h
    rw [show ((fun a => a.abstractN PMN F.length) ∘ (fun a => a.abstractN F) ∘ Lean.Expr.fvar) =
      (fun a => a.abstractN PMN F.length) ∘ ((fun a => a.abstractN F) ∘ Lean.Expr.fvar) from rfl,
      ← List.map_map, h, List.map_map]
    rfl
  simp only [Lean.Expr.mkAppN_eq_mkAppList, Expr.abstractN_mkAppList, hx, hx', List.map_map]
  rw [hfields]
  have H1 := TrSyn.mkAppList (TrSyn.bvar_abstract (Us := Us) Γdoms []
      (F.length + (PMN.length - 1 - m)) (by omega))
    (TrSyn.bvarSpine (Us := Us) Γdoms [] F.length 0 (by omega))
  have H2 := TrSyn.mkAppList H1 Hcalls
  simpa [VExpr.mkApps, List.foldl_append, Function.comp_def] using H2

/-- Inserting `c` anonymous binders between the outer `a` and inner `b`
binders of an abstract context weakens a syntactic translation at the inner
cutoff. -/
theorem TrSyn.insertAbstract {Us : List Name} {doms doms' : List VExpr} {e : Lean.Expr}
    {e' : VExpr} {a b c : Nat} (hdoms : doms.length = a + b) (hdoms' : doms'.length = a + c + b)
    (H : TrSyn Us (abstractForallContext doms []) e e') :
    TrSyn Us (abstractForallContext doms' []) (e.liftLooseBVars' b c) (e'.liftN c b) := by
  have H1 := H.transportAbstract (doms' := List.replicate a (.sort .zero) ++
    List.replicate b (.sort .zero)) (by simp [hdoms])
  have W := abstractForallContext.bvInsertBeforeInner (List.replicate a (.sort .zero))
    (List.replicate c (.sort .zero)) (List.replicate b (.sort .zero))
  have H2 := H1.weakBV W
  simp only [List.length_replicate] at H2
  exact H2.transportAbstract (by simp [hdoms'])

/-- Closing a term over all fields and the outer binders, when it mentions
only the fields before `pos` and the parameters `P` of `P ++ Q`, is closing
it over those alone and weakening by the later fields and by `Q`. -/
theorem Expr.closeShapeSource (e : Lean.Expr) (F P Q : List FVarId) (pos d : Nat)
    (hpos : pos ≤ F.length) (hclosed : Closed e d) (hF : F.Nodup) (hPQ : (P ++ Q).Nodup)
    (hdisj : ∀ x ∈ P ++ Q, x ∉ F)
    (hscope : e.FVarsIn fun fv => fv ∈ F.take pos ∨ fv ∈ P) :
    (e.abstractN F d).abstractN (P ++ Q) (F.length + d) =
      (((e.abstractList (F.take pos) d).abstractList P (pos + d)).liftLooseBVars' d
        (F.length - pos)).liftLooseBVars' (F.length + d) Q.length := by
  have h1 : e.abstractN F d = e.abstractList F d :=
    Lean.Expr.abstractN_eq_abstractList hF e d hclosed.looseBVarRange_le
  have hrest : (e.abstractList (F.take pos) d).FVarsIn fun fv => fv ∉ F.drop pos := by
    have h := hscope.abstractList_not (xs := F.take pos) (k := d)
    apply h.mono
    intro fv ⟨hfv, hnot⟩ hdrop
    rcases hfv with hfv | hfv
    · exact hnot hfv
    · exact hdisj fv (List.mem_append_left _ hfv) (List.mem_of_mem_drop hdrop)
  have h2 : e.abstractList F d =
      (e.abstractList (F.take pos) d).liftLooseBVars' d (F.length - pos) := by
    conv => lhs; rw [← List.take_append_drop pos F]
    rw [Lean.Expr.abstractList_append, hrest.abstractList_eq_liftLooseBVars]
    simp
  have hc1 : Closed (e.abstractList (F.take pos) d) (d + pos) := by
    have := Closed.abstractList_at (fvars := F.take pos) (outer := 0) (e := e) (depth := d)
      (by simpa using hclosed)
    simpa [Nat.min_eq_left hpos] using this
  have hc2 : ((e.abstractList (F.take pos) d).liftLooseBVars' d (F.length - pos)).looseBVarRange'
      ≤ F.length + d := by
    have := Lean.Expr.liftLooseBVars_looseBVarRange (e := e.abstractList (F.take pos) d) (k := d)
      (n := F.length - pos)
    have := hc1.looseBVarRange_le
    omega
  rw [h1, h2, Lean.Expr.abstractN_eq_abstractList hPQ _ _ hc2,
    Lean.Expr.abstractList_append]
  rw [show F.length + d = (pos + d) + (F.length - pos) by omega,
    Expr.liftLooseBVars'_abstractList_add _ _ d (pos + d) (F.length - pos) (by omega)
      (List.nodup_append.mp hPQ).1]
  apply FVarsIn.abstractList_eq_liftLooseBVars
  apply FVarsIn.liftLooseBVars
  have h := (hscope.abstractList_not (xs := F.take pos) (k := d)).abstractList_not (xs := P)
    (k := pos + d)
  apply h.mono
  intro fv ⟨⟨hfv, hnotF⟩, hnotP⟩ _
  rcases hfv with hfv | hfv
  · exact hnotF hfv
  · exact hnotP hfv

/-- A shape translation in the small context `parameters ++ earlier fields ++
earlier binders`, at the declaration universes, moves to the equation context
`parameters ++ motives ++ minors ++ fields ++ earlier binders` at the recursor
universes: its target becomes the generator's `underFields` embedding. -/
theorem TrSyn.ofShape {env : VEnv} {Us Us' : List Name} {ls : List VLevel}
    (hlev : ∀ u u', VLevel.ofLevel Us u = some u' → VLevel.ofLevel Us' u = some (u'.inst ls))
    {sp sfT rbT Γ : List VExpr} {src : Lean.Expr} {t : VExpr} {pos nf extra : Nat}
    (hsfT : sfT.length = pos) (hpos : pos ≤ nf)
    (hΓ : Γ.length = sp.length + extra + nf + rbT.length)
    (H : TrExprS env Us (abstractForallContext (sp ++ sfT ++ rbT) []) src t) :
    TrSyn Us' (abstractForallContext Γ [])
      ((src.liftLooseBVars' rbT.length (nf - pos)).liftLooseBVars' (nf + rbT.length) extra)
      (InductiveSignature.Instance.underFields (t.instL ls) pos nf 0 extra rbT.length) := by
  have H1 := H.toSyn.instL hlev
  simp only [VLCtx.instL_abstractForallContext] at H1
  have H2 := H1.transportAbstract (doms' := List.replicate (sp.length + pos + rbT.length)
    (.sort .zero)) (by simp [hsfT]; omega)
  have H3 := TrSyn.insertAbstract (a := sp.length + pos) (b := rbT.length) (c := nf - pos)
    (doms' := List.replicate (sp.length + (nf + rbT.length)) (.sort .zero)) (by simp)
    (by simp; omega) H2
  have H4 := TrSyn.insertAbstract (a := sp.length) (b := nf + rbT.length) (c := extra)
    (doms' := Γ) (by simp) (by omega) H3
  simpa [InductiveSignature.Instance.underFields, Nat.add_assoc] using H4

/-- The source of a shape translation in the small context is closed at the
shape's local depth and mentions only the earlier fields and the parameters. -/
theorem TrExprS.shapeSourceFacts {env : VEnv} {Us : List Name}
    {sp sfT rbT : List VExpr} {e : Lean.Expr} {t : VExpr} {F P : List FVarId} {pos : Nat}
    (hpos : pos ≤ F.length) (hsp : sp.length = P.length) (hsfT : sfT.length = pos)
    (H : TrExprS env Us (abstractForallContext (sp ++ sfT ++ rbT) [])
      ((e.abstractList (F.take pos) rbT.length).abstractList P (pos + rbT.length)) t) :
    Closed e rbT.length ∧ e.FVarsIn fun fv => fv ∈ F.take pos ∨ fv ∈ P := by
  have hFpos : (F.take pos).length = pos := by simp [hpos]
  have hclosed : Closed ((e.abstractList (F.take pos) rbT.length).abstractList P
      (pos + rbT.length)) (pos + rbT.length + P.length) := by
    have := H.closed
    simp only [abstractForallContext_bvars, List.length_append] at this
    simpa [hsp, hsfT, VLCtx.bvars, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hc1 := Expr.closed_of_abstractList hclosed
  refine ⟨Expr.closed_of_abstractList (by rw [hFpos, Nat.add_comm]; exact hc1), ?_⟩
  have h := H.fvarsIn
  simp only [abstractForallContext_fvars] at h
  have h1 := VerifyInductive.FVarsIn.of_abstractList h
  exact VerifyInductive.FVarsIn.of_abstractList (h1.mono fun fv hfv => by
    rcases hfv with hfv | hfv
    · exact hfv
    · simp [VLCtx.fvars] at hfv)

/-- A shape source translated in the small context, closed over the earlier
fields `F.take pos` and the parameters, translates in the equation context once
closed over all fields and all outer binders. -/
theorem TrSyn.shapeToEquation {env : VEnv} {Us Us' : List Name} {ls : List VLevel}
    (hlev : ∀ u u', VLevel.ofLevel Us u = some u' → VLevel.ofLevel Us' u = some (u'.inst ls))
    {sp sfT rbT Γ : List VExpr} {e : Lean.Expr} {t : VExpr} {F P Q : List FVarId} {pos : Nat}
    (hpos : pos ≤ F.length) (hsp : sp.length = P.length) (hsfT : sfT.length = pos)
    (hF : F.Nodup) (hPQ : (P ++ Q).Nodup) (hdisj : ∀ x ∈ P ++ Q, x ∉ F)
    (hΓ : Γ.length = (P ++ Q).length + F.length + rbT.length)
    (H : TrExprS env Us (abstractForallContext (sp ++ sfT ++ rbT) [])
      ((e.abstractList (F.take pos) rbT.length).abstractList P (pos + rbT.length)) t) :
    TrSyn Us' (abstractForallContext Γ [])
      ((e.abstractN F rbT.length).abstractN (P ++ Q) (F.length + rbT.length))
      (InductiveSignature.Instance.underFields (t.instL ls) pos F.length 0 Q.length
        rbT.length) := by
  obtain ⟨hc2, hscope⟩ := TrExprS.shapeSourceFacts hpos hsp hsfT H
  rw [Expr.closeShapeSource e F P Q pos rbT.length hpos hc2 hF hPQ hdisj hscope]
  exact TrSyn.ofShape hlev hsfT hpos (by simp at hΓ ⊢; omega) H

namespace VerifyInductive
open Kernel

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

theorem recursorLevelLift {lparams : List Name} {elim : Level}
    (ha : AddInductive.AdmissibleElimLevel lparams elim)
    (u : Level) (u' : VLevel) (hu : VLevel.ofLevel lparams u = some u') :
    VLevel.ofLevel (AddInductive.getRecLevelParams elim lparams) u =
      some (u'.inst (recursorDeclarationAbstractLevels lparams ha)) := by
  cases elim with
  | zero =>
    simp only [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels]
    rw [VLevel.inst_id (VLevel.WF.of_ofLevel hu)]
    exact hu
  | param fresh =>
    have hfresh : fresh ∉ lparams := by simpa [AddInductive.AdmissibleElimLevel] using ha
    simp only [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels]
    rw [VLevel.inst_map_id VLevel.prependShift_length]
    exact VLevel.ofLevel_fresh_cons hfresh hu
  | succ | max | imax | mvar => simp [AddInductive.AdmissibleElimLevel] at ha

theorem recLevelsTranslationOf {lparams : List Name} {elim : Level} {levels : List Level}
    (ha : AddInductive.AdmissibleElimLevel lparams elim)
    (htail : levels.mapM (VLevel.ofLevel (AddInductive.getRecLevelParams elim lparams)) =
      some (recursorDeclarationAbstractLevels lparams ha)) :
    (AddInductive.getRecLevels elim levels).mapM
      (VLevel.ofLevel (AddInductive.getRecLevelParams elim lparams)) =
      some (VLevel.params (AddInductive.getRecLevelParams elim lparams).length) := by
  cases elim with
  | zero =>
    simpa [AddInductive.getRecLevels, AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels, Level.isParam] using htail
  | param fresh =>
    have hhead : VLevel.ofLevel (fresh :: lparams) (.param fresh) = some (.param 0) := by
      simp [VLevel.ofLevel]
    simp [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels] at htail
    simp only [AddInductive.getRecLevels, Level.isParam, ↓reduceIte, List.mapM_cons]
    simp only [AddInductive.getRecLevelParams]
    rw [hhead, htail]
    simp [VLevel.params, VLevel.prependShift]
    rw [List.range_succ_eq_map]
    simp [Function.comp_def, VLevel.inst]
    intro a ha
    simp [ha]
  | succ | max | imax | mvar => simp [AddInductive.AdmissibleElimLevel] at ha

/-- The minor premise of local rule `i` of owner `o` is the flat minor binder
at the canonical offset. -/
theorem RecursorConstruction.flatMinorFVar (H : RecursorConstruction R)
    (o : Nat) (ho : o < H.recInfos.size) (i : Nat) (hlocal : i < H.origins.minorTypes[o]!.size) :
    ∃ hk : recursorMinorOffset indTypes o + i < H.bindings.flatMinors.fvars.length,
      H.recInfos[o]!.minors[i]! =
        .fvar (H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i]'hk) := by
  have hrow : i < H.recInfos[o].minors.size := by
    have := (H.origins.minors o ho).size_eq
    simp only [getElem!_pos H.recInfos o ho] at this
    omega
  have hlist : (H.recInfos.flatMap (·.minors)).toList =
      H.bindings.flatMinors.fvars.map Lean.Expr.fvar := by
    have := congrArg Array.toList H.bindings.flatMinors.expressions
    simpa using this
  have hL : H.recInfos.toList.flatMap (fun info => info.minors.toList) =
      H.bindings.flatMinors.fvars.map Lean.Expr.fvar := by
    rw [← hlist, Array.toList_flatMap]
  have hprefix := H.minorPrefixLength_eq o (Nat.le_of_lt ho)
  have hk : recursorMinorOffset indTypes o + i < H.bindings.flatMinors.fvars.length := by
    have h1 := H.sourceMinorOffsetBound o ho i hlocal
    have h2 := H.flatMinors_size_eq
    have h3 := H.bindings.flatMinors.length_fvars
    omega
  have hlen : ((H.recInfos.toList.take o).flatMap (fun info => info.minors.toList)).length + i <
      (H.recInfos.toList.flatMap (fun info => info.minors.toList)).length := by
    rw [hprefix, hL, List.length_map]; exact hk
  have hget := List.flatMap_getElem_prefix H.recInfos.toList (fun info => info.minors.toList) o i
    (by simpa using ho) (by simpa using hrow) hlen
  refine ⟨hk, ?_⟩
  have hget' : (H.bindings.flatMinors.fvars.map Lean.Expr.fvar)[recursorMinorOffset indTypes o + i]'
      (by simpa using hk) = H.recInfos[o].minors[i] := by
    simp only [hprefix, hL] at hget
    simpa using hget
  rw [getElem!_pos H.recInfos o ho, getElem!_pos _ i hrow, ← hget']
  simp

theorem RecursorConstruction.recAppEq (H : RecursorConstruction R)
    (fn : Lean.Expr) :
    mkAppN (mkAppN (mkAppN fn stats.params) (H.recInfos.map (·.motive)))
        (H.recInfos.flatMap (·.minors)) =
      Lean.Expr.mkAppList fn ((H.params.fvars ++ (H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars)).map .fvar) := by
  have h1 := congrArg Array.toList H.params.expressions
  have h2 := congrArg Array.toList H.bindings.motives.expressions
  have h3 := congrArg Array.toList H.bindings.flatMinors.expressions
  simp only at h1 h2 h3
  rw [Lean.Expr.mkAppN_eq_mkAppList, Lean.Expr.mkAppN_eq_mkAppList, Lean.Expr.mkAppN_eq_mkAppList, h1, h2, h3]
  simp

theorem RecursorConstruction.ruleCounts (H : RecursorConstruction R)
    (o : Nat) (ho : o < H.recInfos.size) (i : Nat) (hlocal : i < H.origins.minorTypes[o]!.size)
    (hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size) :
    H.generator.signature.constructors[recursorMinorOffset indTypes o + i].fields.length =
        (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length ∧
      H.generator.signature.params.length = H.params.fvars.length ∧
      H.generator.signature.families.size = H.bindings.motives.fvars.length ∧
      H.generator.signature.constructors.size = H.bindings.flatMinors.fvars.length := by
  obtain ⟨_, hft, _, _⟩ := H.generatedBy_shapeTranslations o ho i hlocal
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← InductiveSignature.fieldTypes_length, hft, H.sourceFields_length,
      (H.origins.minorShapes o ho i hlocal).fields_bound.length_fvars]
  · rw [H.generator.params, List.length_reverse, H.sourceParameterCount,
      H.params.length_fvars]
  · rw [H.generator.familyCount, H.bindings.motives.length_fvars, Array.size_map,
      H.sourceFamilyCount]
  · rw [H.generator.constructorCount, H.bindings.flatMinors.length_fvars,
      H.flatMinors_size_eq]

/-- Every generated recursive call of a rule, closed over the fields and the
outer binders, translates syntactically to the generator's recursive call. -/
theorem RecursorConstruction.ruleCallSyn (H : RecursorConstruction R)
    (o : Nat) (ho : o < H.recInfos.size) (i : Nat) (hlocal : i < H.origins.minorTypes[o]!.size)
    (hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size)
    (Γdoms : List VExpr)
    (hΓ : Γdoms.length = (H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars)).length +
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length)
    (j : Nat) (hj : j < (InductiveSignature.Instance.recursiveFields
      (s := H.generator.signature)
      H.generator.signature.constructors[recursorMinorOffset indTypes o + i]).length) :
    TrSyn (AddInductive.getRecLevelParams H.elimLevel c.lparams) (abstractForallContext Γdoms [])
      ((((H.recInfos[o]!.ruleTemplates[i]!).recursiveCalls[j]!).instantiate indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)).abstractN
          (H.origins.minorShapes o ho i hlocal).fields_bound.fvars |>.abstractN
          (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars))
          (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length)
      (H.generator.generation.recursiveCall
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i]
        (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
          H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
        (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
          H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2
        .recursor) := by
  obtain ⟨_, hft, hrfLen, Hshape⟩ := H.generatedBy_shapeTranslations o ho i hlocal
  obtain ⟨hjB, hpos, hfield, htarget, hbinders, hmajor, htemplate, Hdom, Hidx⟩ := Hshape j hj
  have hjS : j < (H.origins.minorShapes o ho i hlocal).hypotheses.size := hrfLen ▸ hj
  obtain ⟨_, _, _, _, traversal, origins, _, horig, _, _, Hcalls⟩ := H.templates.entry o ho i hlocal
  obtain ⟨originRoot, sourceType, O, D, _, _, hcall⟩ := Hcalls.entry j hjS
  simp only [AddInductive.RecCallTemplate.instantiate]
  rw [htemplate, hmajor, hfield, H.recAppEq]
  have hargs : (H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls[j]!).args = O.args := by
    rw [hcall]
  have hlctx : (H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls[j]!).lctx = O.current.lctx := by
    rw [hcall]
  rw [hargs] at Hdom Hidx hbinders ⊢
  rw [hlctx] at Hdom ⊢
  obtain ⟨hnf, hnp, hnfam, hnctor⟩ := H.ruleCounts o ho i hlocal hk
  unfold InductiveSignature.Instance.recursiveCall
  simp only [InductiveSignature.Instance.recursorHead, H.generator.levels, hnf, hnfam,
    hnctor, hnp]
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hPMN : (H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars)).Nodup := by
    simpa [List.append_assoc] using houter
  have hdisj : ∀ x ∈ H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars),
      x ∉ (H.origins.minorShapes o ho i hlocal).fields_bound.fvars := by
    intro x hx hxF
    have := H.templates.fields_outer_fresh o ho i hlocal x hxF
    rw [H.params.exprArrayFVarIds, H.bindings.motives.exprArrayFVarIds,
      H.bindings.flatMinors.exprArrayFVarIds] at this
    exact this (by simpa [List.append_assoc] using hx)
  have hmajA : (H.origins.minorShapes o ho i hlocal).fields_bound.fvars[(InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1]'hpos ∉
      O.arguments_bound.fvars := by
    obtain ⟨fv, hfv, hmem⟩ := O.field_fvar
    rw [hfield] at hfv
    cases hfv
    intro h
    exact O.arguments_bound.fresh _ h hmem
  have hdecl : ∀ fv ∈ O.arguments_bound.fvars, ∃ index name type bi kind,
      O.current.lctx.find? fv = some (.cdecl index fv name type bi kind) :=
    fun fv h => O.current_wf.findCDecl fv (O.arguments_bound.members fv h)
  have hname : H.generator.generation.recursorName
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.target =
      mkRecName indTypes[(H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls[j]!).targetTypeIdx]!.name := by
    rw [H.generator.names]
    simp only [Fin.getElem_fin]
    rw [H.generator.familyName _ (Fin.isLt _), ← htarget]
    rfl
  rw [hname, H.generator.uvars]
  have hsp : R.parameterScope.toCtx.reverse.length = H.params.fvars.length := by
    rw [List.length_reverse, H.sourceParameterCount, H.params.length_fvars]
  have hsfT : ((H.generator.signature.fieldTypes
      H.generator.signature.constructors[recursorMinorOffset indTypes o + i]).take
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1).length =
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1 := by
    rw [List.length_take, InductiveSignature.fieldTypes_length, hnf]
    omega
  have hdomsLen : (List.map (fun x => InductiveSignature.Instance.underFields
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) x.fst)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
      (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) x.snd)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o +
          i])[j].2.binders.zipIdx).length = O.args.size := by
    simp [hbinders]
  have hA : ExprArrayFVarIds O.args = O.arguments_bound.fvars :=
    O.arguments_bound.toFVarArrayIn.exprArrayFVarIds
  rw [hA] at Hidx
  have hbl : (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
      H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.binders.length =
      O.args.size := hbinders
  have hlev := recursorLevelLift H.elimLevelAdmissible
  have Hdoms' : ∀ i' (hi' : i' < (List.map (fun x => InductiveSignature.Instance.underFields
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) x.fst)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
      (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) x.snd)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o +
          i])[j].2.binders.zipIdx).length),
      TrSyn (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext (Γdoms ++ (List.map (fun x => InductiveSignature.Instance.underFields
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) x.fst)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
      (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) x.snd)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o +
          i])[j].2.binders.zipIdx).take i') [])
        (((Expr.forallDomainList O.args.size (O.current.lctx.mkForall O.args (.sort .zero)))[i']!.abstractN
          (H.origins.minorShapes o ho i hlocal).fields_bound.fvars i').abstractN
          (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars))
          ((H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length + i'))
        (List.map (fun x => InductiveSignature.Instance.underFields
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) x.fst)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
      (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) x.snd)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o +
          i])[j].2.binders.zipIdx)[i'] := by
    intro i' hi'
    have hib : i' < (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.binders.length := by
      simpa using hi'
    have Hd := Hdom i' hib
    have hlen' : ((InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.binders.take
          i').length = i' := by simp; omega
    have X := TrSyn.shapeToEquation hlev (Nat.le_of_lt hpos) hsp hsfT
      (H.origins.minorShapes o ho i hlocal).fields_nodup hPMN hdisj
      (Γ := Γdoms ++ (List.map (fun x => InductiveSignature.Instance.underFields
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) x.fst)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
      (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) x.snd)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o +
          i])[j].2.binders.zipIdx).take i') (rbT := (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.binders.take i')
      (by simp [hΓ]) (by rw [hlen']; exact Hd)
    rw [hlen'] at X
    simpa using X
  have hFa : Closed (O.current.lctx.mkForall O.args (.sort .zero)) := by
    have HFtel := O.arguments_bound.toFVarArrayIn.mkForall_forallTelescope O.current_wf
      (.sort .zero)
    apply VerifyInductive.Expr.ForallTelescope.closed_of_domains HFtel 0
    · intro i' hi'
      have hib : i' < (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
          H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.binders.length := by
        omega
      have hlen' : ((InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
          H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.binders.take
            i').length = i' := by simp; omega
      have := (TrExprS.shapeSourceFacts (Nat.le_of_lt hpos) hsp hsfT
        (by rw [hlen']; exact Hdom i' hib)).1
      rw [hlen'] at this
      simpa using this
    · trivial
  have hIclosed : ∀ e ∈ (H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls[j]!).targetIndices.toList,
      Closed (e.abstractN O.arguments_bound.fvars) O.args.size := by
    intro e he
    obtain ⟨y, _, hy⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hidx _ (List.mem_map_of_mem he)
    have := (TrExprS.shapeSourceFacts (Nat.le_of_lt hpos) hsp hsfT
      (by rw [hbl]; exact hy)).1
    rwa [hbl] at this
  have Hidx' := Hidx
  rw [List.forall₂_map_left_iff] at Hidx'
  have Hidx'' : List.Forall₂ (TrSyn (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (Γdoms ++ (List.map (fun x => InductiveSignature.Instance.underFields
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) x.fst)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
      (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) x.snd)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o +
          i])[j].2.binders.zipIdx)) []))
      ((H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls[j]!).targetIndices.toList.map fun e =>
        ((e.abstractN O.arguments_bound.fvars).abstractN
          (H.origins.minorShapes o ho i hlocal).fields_bound.fvars O.args.size).abstractN
          (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars))
          ((H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length + O.args.size))
      ((InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.indices.map
        fun e => InductiveSignature.Instance.underFields
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) e)
          (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
            H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
          (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
          (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) O.args.size) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine Lean4Lean.List.Forall₂.imp (fun e t he => ?_) Hidx'
    have X := TrSyn.shapeToEquation hlev (Nat.le_of_lt hpos) hsp hsfT
      (H.origins.minorShapes o ho i hlocal).fields_nodup hPMN hdisj
      (Γ := Γdoms ++ (List.map (fun x => InductiveSignature.Instance.underFields
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) x.fst)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
      (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) x.snd)
      (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o +
          i])[j].2.binders.zipIdx)) (rbT := (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.binders)
      (by simp [hΓ, hbl]) (by rw [hbl]; exact he)
    rw [hbl] at X
    simpa using X
  have key := TrSyn.recursiveCall (Us := AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (lctxC := O.current.lctx) (args := O.args) (A := O.arguments_bound.fvars)
    O.arguments_bound.expressions hdecl O.arguments_bound.nodup
    (I := (H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls[j]!).targetIndices)
    hpos (H.origins.minorShapes o ho i hlocal).fields_nodup hPMN hdisj hmajA
    (name := mkRecName indTypes[(H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls[j]!).targetTypeIdx]!.name)
    (recLevelsTranslationOf H.elimLevelAdmissible H.statsLevelsTranslation) (Γdoms := Γdoms) hΓ hdomsLen
    (idxG := (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
        H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].2.indices.map
        fun e => InductiveSignature.Instance.underFields
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) e)
          (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
            H.generator.signature.constructors[recursorMinorOffset indTypes o + i])[j].1
          (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length 0
          (H.bindings.motives.fvars.length + H.bindings.flatMinors.fvars.length) O.args.size)
    hFa Hdoms' hIclosed Hidx''
  rw [hdomsLen]
  simpa [List.append_assoc, Nat.add_assoc] using key

/-- A typed translation of the residual of the rule's right-hand side, in the
generator's equation telescope, closes to a typed translation of the whole
right-hand side: the binder domains are typed by the checked minor-premise
telescope (`minorTranslation`) and the field template (`minorFieldsTemplate`). -/
theorem RecursorConstruction.ruleRhsTypedOfResidual (H : RecursorConstruction R)
    (o : Nat) (ho : o < H.recInfos.size) (i : Nat) (hlocal : i < H.origins.minorTypes[o]!.size)
    (hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size)
    {env : VEnv} (hle : R.context.venv ≤ env) {res : Lean.Expr} {e₂ : VExpr}
    (Htel : Expr.LambdaTelescope
      ((H.recInfos[o]!.ruleTemplates[i]!).instantiate indTypes stats
          (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels H.elimLevel stats.levels) H.localContext.lctx).rhs
      (H.generator.generation.equationDomains
        ⟨recursorMinorOffset indTypes o + i, hk⟩).length res)
    (Hres : TrExprS env (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (H.generator.generation.equationDomains
        ⟨recursorMinorOffset indTypes o + i, hk⟩) []) res e₂) :
    ∃ X, TrExprS env (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      ((H.recInfos[o]!.ruleTemplates[i]!).instantiate indTypes stats
          (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels H.elimLevel stats.levels) H.localContext.lctx).rhs X := by
  obtain ⟨_, hft, hrfLen, Hshape⟩ := H.generatedBy_shapeTranslations o ho i hlocal
  obtain ⟨hnf, hnp, hnfam, hnctor⟩ := H.ruleCounts o ho i hlocal hk
  obtain ⟨_, hfieldsB, hlctxB, hminorB, traversal, origins, _, horig, _, _, Hcalls⟩ :=
    H.templates.entry o ho i hlocal
  obtain ⟨hkN, hminorN⟩ := H.flatMinorFVar o ho i hlocal
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hPMN : (H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars)).Nodup := by
    simpa [List.append_assoc] using houter
  have hdisj : ∀ x ∈ H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars),
      x ∉ (H.origins.minorShapes o ho i hlocal).fields_bound.fvars := by
    intro x hx hxF
    have := H.templates.fields_outer_fresh o ho i hlocal x hxF
    rw [H.params.exprArrayFVarIds, H.bindings.motives.exprArrayFVarIds,
      H.bindings.flatMinors.exprArrayFVarIds] at this
    exact this (by simpa [List.append_assoc] using hx)
  have hdeclPMN : ∀ fv ∈ H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars),
      ∃ index name type bi kind,
        H.localContext.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    apply H.localWF.findCDecl
    simp only [List.mem_append] at hfv
    rcases hfv with h | h | h
    · exact H.params.members fv h
    · exact H.bindings.motives.members fv h
    · exact H.bindings.flatMinors.members fv h
  have hdeclPMN' : ∀ fv ∈ H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars), ∃ d, H.localContext.lctx.find? fv = some d := by
    intro fv hfv
    obtain ⟨_, _, _, _, _, h⟩ := hdeclPMN fv hfv
    exact ⟨_, h⟩
  have hnest : ∀ (fl : Bool) (b : Lean.Expr),
      LocalContext.mkBinding fl H.localContext.lctx stats.params
        (LocalContext.mkBinding fl H.localContext.lctx (H.recInfos.map (·.motive))
          (LocalContext.mkBinding fl H.localContext.lctx (H.recInfos.flatMap (·.minors)) b)) =
      LocalContext.mkBinding fl H.localContext.lctx
        ((H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).map
          Lean.Expr.fvar).toArray b := by
    intro fl b
    conv => lhs; rw [H.params.expressions, H.bindings.motives.expressions,
      H.bindings.flatMinors.expressions]
    simp only [LocalContext.mkBinding_eqN]
    rw [← LocalContext.mkBindingListN_append (fun fv hfv => hdeclPMN' fv (by simp_all))
        (List.nodup_append.mp hPMN).2.1,
      ← LocalContext.mkBindingListN_append hdeclPMN' hPMN]
  simp only [AddInductive.RecRuleTemplate.instantiate] at Htel ⊢
  rw [hfieldsB, hlctxB, hminorB, hminorN] at Htel ⊢
  have hFexpr := (H.origins.minorShapes o ho i hlocal).fields_bound.expressions
  simp only [hFexpr, LocalContext.mkLambda] at Htel ⊢
  rw [hnest true] at Htel ⊢
  have hlenD : (H.generator.generation.params ++ H.generator.generation.motives ++
      H.generator.generation.minors).length =
      (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).length := by
    simp [InductiveSignature.Instance.params, InductiveSignature.Instance.motives,
      InductiveSignature.Instance.length_minors, hnp, hnfam, hnctor]
  have Hforall := (H.generator.minorTranslation).mono hle
  simp only [LocalContext.mkForall] at Hforall
  rw [hnest false] at Hforall
  have HFtel := LocalContext.mkForall_fvars_forallTelescope (lctx := H.localContext.lctx)
    (body := .sort .zero) hdeclPMN
  simp only [LocalContext.mkForall] at HFtel
  let Sel : CDeclArray H.localContext.lctx
      ((H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).map
        Lean.Expr.fvar).toArray := ⟨_, rfl, hdeclPMN⟩
  have Hsame := Sel.sameForallLambdaPrefix (show (H.params.fvars ++ (H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars)).Nodup from hPMN) (.sort .zero)
    (LocalContext.mkBinding true (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx
        (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray
        (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls)))
  have HL := LocalContext.mkLambda_fvars_lambdaTelescopeN (lctx := H.localContext.lctx)
    (body := LocalContext.mkBinding true (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx
        (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray
        (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls))) hdeclPMN
  simp only [LocalContext.mkForall, LocalContext.mkLambda, List.size_toArray, List.length_map]
    at Hsame HL
  have hsourceOwner : o < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsourceLE⟩ :=
    H.minorSources.rows o ho hsourceOwner i hlocal
  have hdeclF : ∀ fv ∈ (H.origins.minorShapes o ho i hlocal).fields_bound.fvars,
      ∃ index name type bi kind,
        (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx.find? fv =
          some (.cdecl index fv name type bi kind) :=
    fun fv h => (H.origins.minorShapes o ho i hlocal).sourceFullWF.findCDecl fv
      ((H.origins.minorShapes o ho i hlocal).fields_bound.members fv h)
  let SelF : CDeclArray (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx
      ((H.origins.minorShapes o ho i hlocal).fields_bound.fvars.map Lean.Expr.fvar).toArray :=
    ⟨_, rfl, hdeclF⟩
  have HsameF := (SelF.sameForallLambdaPrefix
    (show (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.Nodup from
      (H.origins.minorShapes o ho i hlocal).fields_nodup) (.sort .zero)
    (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls))).abstractN
    (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) 0
  have HLF := (LocalContext.mkLambda_fvars_lambdaTelescopeN hdeclF (body :=
    (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls)))).abstractN
    (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) 0
  have HFtelF := (LocalContext.mkForall_fvars_forallTelescope hdeclF (body := .sort .zero)).abstractN
    (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) 0
  simp only [LocalContext.mkForall, LocalContext.mkLambda, List.size_toArray, List.length_map]
    at HsameF HLF HFtelF
  have hlenF : (InductiveSignature.insertBinders
        (List.map (fun x => VExpr.instL H.generator.generation.levels x)
          (H.generator.signature.fieldTypes
            H.generator.signature.constructors[recursorMinorOffset indTypes o + i]))
        (H.generator.signature.families.size +
          H.generator.signature.constructors.size)).length =
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length := by
    simp [InductiveSignature.insertBinders, InductiveSignature.fieldTypes_length, hnf]
  have hins : (H.generator.generation.motives ++
      H.generator.generation.minors).length =
      (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars).length := by
    simp [InductiveSignature.Instance.motives, InductiveSignature.Instance.length_minors,
      hnfam, hnctor]
  have Htemp := H.minorFieldsTemplate o ho i hlocal
    (H.generator.generation.motives ++ H.generator.generation.minors)
    (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars) hins.symm
  simp only at Htemp
  have hclosed : Closed (H.localContext.lctx.mkForall (H.origins.minorShapes o ho i hlocal).fields
      (.sort .zero)) := by
    have := Htemp.closed
    simp only [abstractForallContext_bvars] at this
    apply Expr.closed_of_abstractList (fvars := H.params.fvars ++
      (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) (depth := 0)
    simpa [VLCtx.bvars, H.parameterDomains, hnp, hins, Nat.add_assoc,
      List.length_reverse, H.sourceParameterCount, H.params.length_fvars] using this
  rw [← Lean.Expr.abstractN_eq_abstractList_of_closed hPMN hclosed,
    (H.origins.minorShapes o ho i hlocal).fields_bound.mkForall_mono hsourceLE (.sort .zero)]
    at Htemp
  rw [hFexpr] at Htemp
  simp only [LocalContext.mkForall] at Htemp
  rw [hins, ← hft, ← H.generator.levels] at Htemp
  have hins' : (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars).length =
      H.generator.signature.families.size +
        H.generator.signature.constructors.size := by
    simp [hnfam, hnctor]
  rw [hins'] at Htemp
  have hEqLen : (H.generator.generation.equationDomains
      ⟨recursorMinorOffset indTypes o + i, hk⟩).length =
      (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).length +
        (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length := by
    rw [← hlenD, ← hlenF]
    simp only [InductiveSignature.Instance.equationDomains, Fin.getElem_fin, List.length_append]
  rw [hEqLen] at Htel
  have hres := Htel.result_eq (HL.trans HLF)
  rw [hres, Nat.zero_add] at Hres
  have Hres' := Hres
  simp only [InductiveSignature.Instance.equationDomains, Fin.getElem_fin] at Hres'
  rw [← abstractForallContext_append] at Hres'
  have hpd : H.parameterSuffix.parameterDecls.toCtx.reverse = H.generator.generation.params := by
    rw [H.parameterDomains, InductiveSignature.Instance.params, H.generator.params,
      H.generator.levels]
  rw [hpd, H.recursorEnv, ← List.append_assoc] at Htemp
  rw [Nat.zero_add] at HLF
  have H2 := HsameF.translateLambda HFtelF HLF hlenF (Htemp.mono hle) Hres'
  exact ⟨_, Hsame.translateLambda HFtel HL hlenD Hforall H2⟩

/-- The literal right-hand side built from the rule template of local rule
`i` of owner `o` translates syntactically to the right-hand side of the
generator's equation for the constructor at the canonical minor
offset. -/
theorem RecursorConstruction.ruleRhsSyn (H : RecursorConstruction R)
    (o : Nat) (ho : o < H.recInfos.size) (i : Nat) (hlocal : i < H.origins.minorTypes[o]!.size) :
    ∃ hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size,
      TrSyn (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        ((H.recInfos[o]!.ruleTemplates[i]!).instantiate indTypes stats
          (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels H.elimLevel stats.levels) H.localContext.lctx).rhs
        (H.generator.generation.equation
          ⟨recursorMinorOffset indTypes o + i, hk⟩).rhs := by
  obtain ⟨hk, hft, hrfLen, Hshape⟩ := H.generatedBy_shapeTranslations o ho i hlocal
  refine ⟨hk, ?_⟩
  obtain ⟨hnf, hnp, hnfam, hnctor⟩ := H.ruleCounts o ho i hlocal hk
  obtain ⟨_, hfieldsB, hlctxB, hminorB, traversal, origins, _, horig, _, _, Hcalls⟩ :=
    H.templates.entry o ho i hlocal
  obtain ⟨hkN, hminorN⟩ := H.flatMinorFVar o ho i hlocal
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hPMN : (H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars)).Nodup := by
    simpa [List.append_assoc] using houter
  have hdisj : ∀ x ∈ H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars),
      x ∉ (H.origins.minorShapes o ho i hlocal).fields_bound.fvars := by
    intro x hx hxF
    have := H.templates.fields_outer_fresh o ho i hlocal x hxF
    rw [H.params.exprArrayFVarIds, H.bindings.motives.exprArrayFVarIds,
      H.bindings.flatMinors.exprArrayFVarIds] at this
    exact this (by simpa [List.append_assoc] using hx)
  have hdeclPMN : ∀ fv ∈ H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars),
      ∃ index name type bi kind,
        H.localContext.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    apply H.localWF.findCDecl
    simp only [List.mem_append] at hfv
    rcases hfv with h | h | h
    · exact H.params.members fv h
    · exact H.bindings.motives.members fv h
    · exact H.bindings.flatMinors.members fv h
  have hdeclPMN' : ∀ fv ∈ H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars), ∃ d, H.localContext.lctx.find? fv = some d := by
    intro fv hfv
    obtain ⟨_, _, _, _, _, h⟩ := hdeclPMN fv hfv
    exact ⟨_, h⟩
  have hnest : ∀ (fl : Bool) (b : Lean.Expr),
      LocalContext.mkBinding fl H.localContext.lctx stats.params
        (LocalContext.mkBinding fl H.localContext.lctx (H.recInfos.map (·.motive))
          (LocalContext.mkBinding fl H.localContext.lctx (H.recInfos.flatMap (·.minors)) b)) =
      LocalContext.mkBinding fl H.localContext.lctx
        ((H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).map
          Lean.Expr.fvar).toArray b := by
    intro fl b
    conv => lhs; rw [H.params.expressions, H.bindings.motives.expressions,
      H.bindings.flatMinors.expressions]
    simp only [LocalContext.mkBinding_eqN]
    rw [← LocalContext.mkBindingListN_append (fun fv hfv => hdeclPMN' fv (by simp_all))
        (List.nodup_append.mp hPMN).2.1,
      ← LocalContext.mkBindingListN_append hdeclPMN' hPMN]
  simp only [AddInductive.RecRuleTemplate.instantiate]
  rw [hfieldsB, hlctxB, hminorB, hminorN]
  have hFexpr := (H.origins.minorShapes o ho i hlocal).fields_bound.expressions
  conv => lhs; rw [hFexpr]
  simp only [LocalContext.mkLambda]
  rw [hnest true]
  simp only [InductiveSignature.Instance.equation, Fin.getElem_fin]
  rw [VExpr.wrapLams_append (H.generator.generation.params ++
    H.generator.generation.motives ++ H.generator.generation.minors)]
  have hlenD : (H.generator.generation.params ++ H.generator.generation.motives ++
      H.generator.generation.minors).length =
      (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).length := by
    simp [InductiveSignature.Instance.params, InductiveSignature.Instance.motives,
      InductiveSignature.Instance.length_minors, hnp, hnfam, hnctor]
  have Hforall := H.generator.minorTranslation
  simp only [LocalContext.mkForall] at Hforall
  rw [hnest false] at Hforall
  have HFtel := LocalContext.mkForall_fvars_forallTelescope (lctx := H.localContext.lctx)
    (body := .sort .zero) hdeclPMN
  simp only [LocalContext.mkForall] at HFtel
  have Hdoms := fun i hi => (TrExprS.forallTelescope_domains HFtel Hforall hlenD i hi).toSyn
  let Sel : CDeclArray H.localContext.lctx
      ((H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).map
        Lean.Expr.fvar).toArray := ⟨_, rfl, hdeclPMN⟩
  have Hsame := Sel.sameForallLambdaPrefix (show (H.params.fvars ++ (H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars)).Nodup from hPMN) (.sort .zero)
    (LocalContext.mkBinding true (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx
        (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray
        (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls)))
  have HL := LocalContext.mkLambda_fvars_lambdaTelescopeN (lctx := H.localContext.lctx)
    (body := LocalContext.mkBinding true (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx
        (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray
        (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls))) hdeclPMN
  simp only [LocalContext.mkForall, LocalContext.mkLambda, List.size_toArray, List.length_map]
    at Hsame HL
  refine TrSyn.lambdaTelescope Hsame HL hlenD Hdoms ?_
  -- the field telescope
  have hsourceOwner : o < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsourceLE⟩ :=
    H.minorSources.rows o ho hsourceOwner i hlocal
  have hdeclF : ∀ fv ∈ (H.origins.minorShapes o ho i hlocal).fields_bound.fvars,
      ∃ index name type bi kind,
        (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx.find? fv =
          some (.cdecl index fv name type bi kind) :=
    fun fv h => (H.origins.minorShapes o ho i hlocal).sourceFullWF.findCDecl fv
      ((H.origins.minorShapes o ho i hlocal).fields_bound.members fv h)
  let SelF : CDeclArray (H.origins.minorShapes o ho i hlocal).sourceFullContext.lctx
      ((H.origins.minorShapes o ho i hlocal).fields_bound.fvars.map Lean.Expr.fvar).toArray :=
    ⟨_, rfl, hdeclF⟩
  have HsameF := (SelF.sameForallLambdaPrefix
    (show (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.Nodup from
      (H.origins.minorShapes o ho i hlocal).fields_nodup) (.sort .zero)
    (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls))).abstractN
    (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) 0
  have HLF := (LocalContext.mkLambda_fvars_lambdaTelescopeN hdeclF (body :=
    (mkAppN
          (mkAppN (Expr.fvar H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i])
            (List.map Expr.fvar (H.origins.minorShapes o ho i hlocal).fields_bound.fvars).toArray)
          (Array.map
            (fun call =>
              call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
                (Array.flatMap (fun x => x.minors) H.recInfos) (AddInductive.getRecLevels H.elimLevel stats.levels))
            H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls)))).abstractN
    (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) 0
  have HFtelF := (LocalContext.mkForall_fvars_forallTelescope hdeclF (body := .sort .zero)).abstractN
    (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) 0
  simp only [LocalContext.mkForall, LocalContext.mkLambda, List.size_toArray, List.length_map]
    at HsameF HLF HFtelF
  have hlenF : (InductiveSignature.insertBinders
        (List.map (fun x => VExpr.instL H.generator.generation.levels x)
          (H.generator.signature.fieldTypes
            H.generator.signature.constructors[recursorMinorOffset indTypes o + i]))
        (H.generator.signature.families.size +
          H.generator.signature.constructors.size)).length =
      (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length := by
    simp [InductiveSignature.insertBinders, InductiveSignature.fieldTypes_length, hnf]
  refine TrSyn.lambdaTelescope HsameF HLF hlenF ?_ ?_
  · have hins : (H.generator.generation.motives ++
        H.generator.generation.minors).length =
        (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars).length := by
      simp [InductiveSignature.Instance.motives, InductiveSignature.Instance.length_minors,
        hnfam, hnctor]
    have Htemp := H.minorFieldsTemplate o ho i hlocal
      (H.generator.generation.motives ++ H.generator.generation.minors)
      (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars) hins.symm
    simp only at Htemp
    have hclosed : Closed (H.localContext.lctx.mkForall (H.origins.minorShapes o ho i hlocal).fields
        (.sort .zero)) := by
      have := Htemp.closed
      simp only [abstractForallContext_bvars] at this
      apply Expr.closed_of_abstractList (fvars := H.params.fvars ++
        (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)) (depth := 0)
      simpa [VLCtx.bvars, H.parameterDomains, hnp, hins, Nat.add_assoc,
        List.length_reverse, H.sourceParameterCount, H.params.length_fvars] using this
    rw [← Lean.Expr.abstractN_eq_abstractList_of_closed hPMN hclosed,
      (H.origins.minorShapes o ho i hlocal).fields_bound.mkForall_mono hsourceLE (.sort .zero)]
      at Htemp
    rw [hFexpr] at Htemp
    simp only [LocalContext.mkForall] at Htemp
    rw [hins, ← hft, ← H.generator.levels] at Htemp
    have hins' : (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars).length =
        H.generator.signature.families.size +
          H.generator.signature.constructors.size := by
      simp [hnfam, hnctor]
    rw [hins'] at Htemp
    intro i' hi'
    have Hd := (TrExprS.forallTelescope_domains HFtelF Htemp hlenF i' hi').toSyn
    rw [abstractForallContext_append] at Hd ⊢
    refine Hd.transportAbstract ?_
    simp [H.parameterDomains, InductiveSignature.Instance.params, H.generator.params]
  · rw [abstractForallContext_append, Nat.zero_add]
    have hm : H.params.fvars.length + H.bindings.motives.fvars.length +
        (recursorMinorOffset indTypes o + i) <
        (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).length := by
      simp only [List.length_append]; omega
    have hPMNk : (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars))[
        H.params.fvars.length + H.bindings.motives.fvars.length +
          (recursorMinorOffset indTypes o + i)]'hm =
        H.bindings.flatMinors.fvars[recursorMinorOffset indTypes o + i] := by
      rw [List.getElem_append_right (by omega)]
      rw [List.getElem_append_right (by omega)]
      congr 1
      omega
    rw [← hPMNk]
    have hΓ : (H.generator.generation.params ++ H.generator.generation.motives ++
        H.generator.generation.minors ++ InductiveSignature.insertBinders
        (List.map (fun x => VExpr.instL H.generator.generation.levels x)
          (H.generator.signature.fieldTypes
            H.generator.signature.constructors[recursorMinorOffset indTypes o + i]))
        (H.generator.signature.families.size +
          H.generator.signature.constructors.size)).length =
        (H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).length +
          (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length := by
      rw [List.length_append, hlenD, hlenF]
    have hcallsLen : H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls.size =
        (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
          H.generator.signature.constructors[recursorMinorOffset indTypes o + i]).length := by
      rw [Hcalls.size_eq, hrfLen]
    have Hcalls' := TrSyn.ruleBody (Us := AddInductive.getRecLevelParams H.elimLevel c.lparams)
      hm (H.origins.minorShapes o ho i hlocal).fields_nodup hPMN hdisj hΓ
      (calls := H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls.map fun call =>
        call.instantiate indTypes stats (Array.map (fun x => x.motive) H.recInfos)
          (Array.flatMap (fun x => x.minors) H.recInfos)
          (AddInductive.getRecLevels H.elimLevel stats.levels))
      (callsG := (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
          H.generator.signature.constructors[recursorMinorOffset indTypes o + i]).map
        fun x => H.generator.generation.recursiveCall
          H.generator.signature.constructors[recursorMinorOffset indTypes o + i] x.1 x.2 .recursor)
      (by
        apply List.forall₂_of_getElem (by simp [hcallsLen])
        intro j h1 h2
        have hj : j < (InductiveSignature.Instance.recursiveFields (s := H.generator.signature)
            H.generator.signature.constructors[recursorMinorOffset indTypes o + i]).length := by
          simpa using h2
        have hjB : j < H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls.size := by omega
        simp only [List.getElem_map, Array.getElem_toList, Array.getElem_map]
        rw [← getElem!_pos H.recInfos[o]!.ruleTemplates[i]!.recursiveCalls j hjB]
        exact H.ruleCallSyn o ho i hlocal hk _ hΓ j hj)
    simp only [hnf]
    have hidx : (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length +
        H.generator.signature.constructors.size - 1 - (recursorMinorOffset indTypes o + i) =
        (H.origins.minorShapes o ho i hlocal).fields_bound.fvars.length +
          ((H.params.fvars ++ (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)).length - 1 -
            (H.params.fvars.length + H.bindings.motives.fvars.length +
              (recursorMinorOffset indTypes o + i))) := by
      simp only [List.length_append]; omega
    rw [hidx]
    exact Hcalls'

/-- The right-hand side of every installed recursor rule translates
syntactically (`TrSyn`, the typing-free shadow of `TrExprS`) to the
right-hand side of the generator's equation for the constructor at
the canonical minor offset. -/
theorem RecursorCheck.ruleRhsSyn {outEnv : Environment}
    (H : RecursorCheck R outEnv)
    (o : Nat) (ho : o < H.entries.length)
    (i : Nat) (hi : i < (H.generated.entry o ho).info.rules.length) :
    ∃ hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size,
      TrSyn (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        ((H.generated.entry o ho).info.rules[i]).rhs
        (H.generator.generation.equation ⟨recursorMinorOffset indTypes o + i, hk⟩).rhs := by
  have howner : o < H.recInfos.size := by simpa [H.generated.length] using ho
  have hlocal : i < H.origins.minorTypes[o]!.size := by
    rw [← H.templates.rows_size o howner, ← H.generated_rules_length o ho]
    exact hi
  rw [H.rulesLiteral o ho i hi]
  exact H.toRecursorConstruction.ruleRhsSyn o howner i hlocal

/-- The right-hand side of every installed recursor rule has a typed
translation in the recursor environment.  The residual is typed by the
equation frame (`equationFrame`), transported to the
generator's equation telescope along `domains_defeq`; the binder domains are
typed by `ruleRhsTypedOfResidual`. -/
theorem RecursorCheck.ruleRhsTyped {outEnv : Environment}
    (H : RecursorCheck R outEnv)
    (o : Nat) (ho : o < H.entries.length)
    (i : Nat) (hi : i < (H.generated.entry o ho).info.rules.length) :
    ∃ X, TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      ((H.generated.entry o ho).info.rules[i]).rhs X := by
  have howner : o < H.recInfos.size := by simpa [H.generated.length] using ho
  have hlocal : i < H.origins.minorTypes[o]!.size := by
    rw [← H.templates.rows_size o howner, ← H.generated_rules_length o ho]
    exact hi
  have hctor : i < indTypes[o]!.ctors.length := by
    rw [← H.minorTypes_size o howner]; exact hlocal
  rcases H.ruleAlignment o ho i hctor with ⟨A⟩
  rcases A.equationFrame with ⟨F⟩
  obtain ⟨hk, -, hnf⟩ := A.generatedConstructor
  have D := F.domains_defeq hk hnf
  obtain ⟨e₂, He₂⟩ := TrExprS.defeqDFC H.outVEnvWF (abstractForallContext.isDefEq D)
    F.rhs_translation
  have Htel := A.rule.rhsLambdaTelescope
  have heq : A.rule.sourceRhsBody.abstractN A.rule.binders =
      A.rule.sourceRhsBody.abstractList A.rule.binders :=
    Lean.Expr.abstractN_eq_abstractList_of_closed A.rule.binders_nodup A.sourceRhsBody_closed
  rw [heq, ← A.equationDomains_length hk] at Htel
  generalize A.rule.sourceRhsBody.abstractList A.rule.binders = res at Htel He₂
  rw [H.rulesLiteral o ho i hi] at Htel
  rw [H.rulesLiteral o ho i hi]
  exact H.toRecursorConstruction.ruleRhsTypedOfResidual o howner i hlocal hk
    H.installed.le Htel He₂

/-- Whenever the right-hand side of an
installed rule has some typed translation in the recursor environment, its
translation is the generator's equation right-hand side.  The target is fixed
constructively by `ruleRhsSyn`; the hypothesis supplies only the typing side
conditions of `TrExprS`. -/
theorem RecursorCheck.ruleRhsTranslation {outEnv : Environment}
    (H : RecursorCheck R outEnv)
    (o : Nat) (ho : o < H.entries.length)
    (i : Nat) (hi : i < (H.generated.entry o ho).info.rules.length)
    (htyped : ∃ X, TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      ((H.generated.entry o ho).info.rules[i]).rhs X) :
    ∃ hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size,
      TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        ((H.generated.entry o ho).info.rules[i]).rhs
        (H.generator.generation.equation ⟨recursorMinorOffset indTypes o + i, hk⟩).rhs := by
  obtain ⟨hk, Hsyn⟩ := H.ruleRhsSyn o ho i hi
  obtain ⟨X, HX⟩ := htyped
  exact ⟨hk, HX.of_syn Hsyn⟩

/-- The right-hand-side translations, with no hypothesis: the right-hand
side of every installed rule translates to the generator's equation (the form
of `RecursorCheck.RuleRhsTranslations`). -/
theorem RecursorCheck.ruleRhsTranslations {outEnv : Environment}
    (H : RecursorCheck R outEnv) :
    ∀ owner (howner : owner < H.entries.length) (i : Nat)
      (hi : i < (H.generated.entry owner howner).info.rules.length)
      (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size),
      TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        ((H.generated.entry owner howner).info.rules[i]).rhs
        (H.canonicalGeneration.equation ⟨recursorMinorOffset indTypes owner + i, hk⟩).rhs := by
  intro owner howner i hi hk
  obtain ⟨_, Htr⟩ := H.ruleRhsTranslation owner howner i hi (H.ruleRhsTyped owner howner i hi)
  exact Htr

end VerifyInductive
end Lean4Lean
