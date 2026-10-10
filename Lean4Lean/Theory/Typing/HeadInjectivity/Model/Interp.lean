import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Obs
import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.Typing

/-! # The observation interpretation

`Obs env U Δ σ S t o`: under the valuation `(σ, S)` the term `t` (in a source context `Γ`)
has the observation `o` (section 4.1 of the design notes). The valuation
consists of an *anchor* substitution `σ` from `Γ` into the target context `Δ`, from which
all classes are computed (`TyCls Δ (A.subst σ)`, `ElCls Δ D (a.subst σ)`), and observation
sets `S i` for the variables (the semantic part).

Valuations are pairs of an anchor substitution and observation sets, not lists of
(class, observation set); a key `(c, K)` extends the anchor by a representative `x` of `c`. With anchors the
substitution lemma (`Obs.subst_iff`) is purely syntactic, needing no typing; the price is
that a key's representative is chosen, so representative invariance becomes part of
soundness (its motive relates two definitionally equal anchors).

Clauses (every occurrence of `Obs` strictly positive, key typing inlined):
* `bvar i`: the observations `S i`;
* `sort l`: `.sort l.eval`;
* `forallE A B`: `piDom` of the domain class, `piDomOb o` for observations of `A`,
  `piCod c C` and `piCodOb c K o` for typed keys `(c, K)` at `A` (`c` a typed class at the
  domain class, every `k ∈ K` typed at observations of `A`), `B` read at the anchor extended
  by a representative `x` of `c` and the observation set `K`;
* `lam A t`: `app D c K o` for typed keys, `D` the domain class;
* `app f a`: `o` whenever `f` has `app D c K o` with `c` the class of `a` at `D` and `K`
  covered by observations of `a`;
* `const n ls`, `n` rigid (`env.Rigid n`: no rule headed by `n`): rigid spine observations
  `wrap keys r` (`r` the head observation `rigid n (ls.map eval) keys.length` or an argument
  observation `rigidArg i cᵢ`), **filtered**: kept only when typed at observations of
  `ci.type.instL ls`, read at the fixed valuation `(id, ∅)` (the type is closed;
  `Obs.closed_iff` shows the valuation is irrelevant there);
* `const n ls`, `n` defined: the observations of the value `df.rhs.instL ls` of its delta
  rule `df`, with the same filter;
* constructors: constructor spine observations (`ctorHead`, `ctorArg`, `ctorArgOb`), or, for
  the constructor of a projection-registered family, only field observations (`projCtor`);
  applications of a projection-registered family also have the type observations `fieldTy`
  and `fieldDom` (`famTy`, `famDom`);
* `rule` and `pat`: a spine headed by the head of a λ-wrapped definitional axiom with a
  constructor major (the quotient rule) or by the recursor of a registered ι pattern
  (`env.pats`) has the observations of the rule's right-hand side at the binding of its
  variables read from the keys (`RuleBind`), filtered by typing at the head's type;
* `proj fam j e`: the inner observations of the field observations of `e` at field `j`.

Classes are saturated by level variants (`LvEq`), so `Obs.lvEq` shows that the
observations of a term are those of its level variants. Structural lemmas: inversion (`*_iff`), weakening (`Obs.lift'_iff`), substitution
(`Obs.subst_iff`), monotonicity in the observation sets (`Obs.mono`, `Obs.mono_le`),
compactness (`Obs.compact`), and invariance for closed terms (`Obs.closed_iff`). Typed
valuations (`TV`) are defined at the end. -/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- Observation sets of the variables of a valuation. -/
abbrev ObSets := Nat → Ob → Prop

namespace ObSets

def cons (S : ObSets) (X : Ob → Prop) : ObSets
  | 0 => X
  | i+1 => S i

def lift_l (ρ : Lift) (S : ObSets) : ObSets := fun i => S (ρ.liftVar i)

protected def empty : ObSets := fun _ _ => False

def update (S : ObSets) (n : Nat) (X : Ob → Prop) : ObSets := fun i => if i = n then X else S i

theorem lift_l_cons {S : ObSets} : (S.cons X).lift_l ρ.cons = (S.lift_l ρ).cons X := by
  funext i; cases i <;> rfl

theorem update_cons {S : ObSets} : (S.cons X).update (n+1) Y = (S.update n Y).cons X := by
  funext i; cases i <;> simp [update, cons]

end ObSets

theorem _root_.Lean4Lean.VExpr.Subst.lift_l_cons {σ : VExpr.Subst} :
    (σ.cons x).lift_l ρ.cons = (σ.lift_l ρ).cons x := by
  funext i; cases i <;> rfl

theorem _root_.Lean4Lean.VExpr.Subst.lift_comp_cons {τ σ : VExpr.Subst} :
    τ.lift.comp (σ.cons x) = (τ.comp σ).cons x := by
  funext i; cases i with
  | zero => rfl
  | succ i => simp [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.cons]

/-- The finite set of a list of observations. -/
def listSet (K : List Ob) : Ob → Prop := fun k => k ∈ K

/-! ## Constructors and rules -/

/-- `c` is an installed constructor: the major premise of a stored rule is headed by `c`. -/
def IsInstalledCtor (env : VEnv) (c : Name) : Prop := ∃ df, env.defeqs df ∧ df.HasConstructorMajor c

/-- `c` is a constructor: of a stored rule (the quotient rule) or of a registered ι pattern
(`VEnv.IsPatCtor`). -/
def IsCtor (env : VEnv) (c : Name) : Prop := IsInstalledCtor env c ∨ IsPatCtor env c

/-- The innermost observations of a constructor spine after the keys `keys`: the head, an
argument class, or an argument observation (with the keys of the earlier arguments). -/
def CtorEnd (n : Name) (ℓs : List (List Nat → Nat)) (keys : List Key) (r : Ob) : Prop :=
  r = .ctorHead n ℓs keys.length ∨
  (∃ i, ∃ h : i < keys.length, r = .ctorArg i (keys[i]).2.1) ∨
  (∃ i, ∃ h : i < keys.length, ∃ k ∈ (keys[i]).2.2, r = .ctorArgOb i (keys.take i) k)

/-- `n` is the constructor of a projection-registered family. -/
def IsProjCtor (env : VEnv) (n : Name) : Prop :=
  ∃ fam info, env.projections fam info ∧ info.ctorName = n

/-- Every key list of a spine is backed. -/
def KeysBacked (keys : List Key) : Prop := ∀ k ∈ keys, Backed (fun o => o ∈ k.2.2)

/-- The innermost observations of a constructor spine of the projection-registered family
`fam`: a field observation of field `j` with the observation lists of the
earlier field keys as context. -/
def PCtorEnd (fam : Name) (info : VProjectionInfo) (keys : List Key) (r : Ob) : Prop :=
  ∃ j L k, r = .fieldOb fam j L k ∧ j < info.numFields ∧ L.length = j ∧
    (∀ i Li, L[i]? = some Li → ∃ ki, keys[info.nparams + i]? = some ki ∧ ∀ y ∈ Li, y ∈ ki.2.2) ∧
    ∃ kj, keys[info.nparams + j]? = some kj ∧ k ∈ kj.2.2

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- Anchors `as` of a prefix of the telescope `D` (outermost first) in the classes of the keys
`K`, each class typed at the type class of its domain at the earlier anchors. -/
def ChainOK (D as : List VExpr) (K : List Key) : Prop :=
  as.length = K.length ∧ ∀ i a k, as[i]? = some a → K[i]? = some k →
    TypedElCls env U Δ
      (TyCls env U Δ ((D.getD i (.sort .zero)).subst (VExpr.argSubst (as.take i)))) k.2.1 ∧ k.2.1 a

end

/-- The observation sets (de Bruijn indexed, innermost binder first) of the key lists of `K`
(outermost first). -/
def keySets (K : List Key) : ObSets :=
  fun m => if h : m < K.length then listSet (K[K.length - 1 - m]).2.2 else fun _ => False

/-- The observation of a Pi telescope recording the codomain observation `x` at the keys. -/
def piCodChain (keys : List Key) (x : Ob) : Ob := keys.foldr (fun k x => .piCodOb k.2.1 k.2.2 x) x

@[simp] theorem piCodChain_nil : piCodChain [] x = x := rfl
@[simp] theorem piCodChain_cons :
    piCodChain (k :: ks) x = .piCodOb k.2.1 k.2.2 (piCodChain ks x) := rfl

theorem piCodChain_append : piCodChain (ks ++ ks') x = piCodChain ks (piCodChain ks' x) := by
  simp [piCodChain, List.foldr_append]

/-- The type of the binder `x` (de Bruijn index in the body) of a rule whose binder
domains are `doms` (outermost first), at the levels `ls`. -/
def binderTy (doms : List VExpr) (ls : List VLevel) (x : Nat) : VExpr :=
  ((doms.reverse.getD x default).liftN (x+1)).instL ls

/-- The leading arguments of the generic redex of an ι rule whose reduct binds `k`
parameters, motives and minors and then `nf` fields (`SimplePattern.iotaRHS'`): the `k`
bound variables `bvar (k + nf - 1), …, bvar nf` followed by `nind` ignored index
positions, written as the non-variable dummy `sort 0` so that `RuleBind` binds nothing at
them (the index holes of a pattern are not variables of the reduct). -/
def iotaLead (k nind nf : Nat) : List VExpr :=
  ((List.range k).reverse.map fun i => VExpr.bvar (i + nf)) ++ List.replicate nind (.sort .zero)

/-- The field variables of the generic redex of an ι rule with `nf` fields: the trailing
constructor arguments `bvar (nf - 1), …, bvar 0`. -/
def iotaFs (nf : Nat) : List Nat := (List.range nf).reverse

@[simp] theorem iotaLead_length : (iotaLead k nind nf).length = k + nind := by
  simp [iotaLead]

@[simp] theorem iotaFs_length : (iotaFs nf).length = nf := by simp [iotaFs]

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- The binding of a rule's variables from the keys of a head chain: a variable occurring
bare among the leading arguments takes the key at its first
occurrence; otherwise it is the `j`-th field of the major and is
* (AB) read, in mode AB, from the constructor observations `Km` of the major key;
* (proof) in any mode, any term of its type, which is a proposition, with no observations;
* (eta) in mode AB, when the major's constructor `ctor` is the constructor of the
  projection-registered family `I` and the entry is never zero at the constructor's levels
  `lsC` (instantiated at `ls`), a member of the class of the projections of the major key's
  class `cm` onto the field, with the observations of the field recorded in the field
  observations of `Km`.
The anchor `τ` takes a member of each class; classes are required to be typed at the
variable's type. -/
def RuleBind (doms : List VExpr) (ls : List VLevel) (lead : List VExpr) (msLen : Nat)
    (fs : List Nat) (mC : Bool) (I ctor : Name) (lsC : List VLevel) (keys : List Key)
    (cm : VExpr → Prop) (Km : List Ob) (τ : VExpr.Subst) (S' : Nat → Ob → Prop) : Prop :=
  (∀ x, Backed (S' x)) ∧ ∀ x < doms.length,
    (∃ i : Nat, ∃ k : Key, lead[i]? = some (VExpr.bvar x) ∧ (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) ∧
      keys[i]? = some k ∧
      TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst τ)) k.2.1 ∧ k.2.1 (τ x) ∧
      S' x = listSet k.2.2) ∨
    ((∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ ∃ j : Nat, fs[j]? = some x ∧
      ((mC = false ∧ ∃ c, .ctorArg (msLen + j) c ∈ Km ∧
          TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst τ)) c ∧ c (τ x) ∧
          S' x = fun k => ∃ pre, .ctorArgOb (msLen + j) pre k ∈ Km) ∨
       ((∃ X, TyCls env U Δ ((binderTy doms ls x).subst τ) X ∧ env.HasType U Δ (τ x) X) ∧
          (∃ P, TyCls env U Δ ((binderTy doms ls x).subst τ) P ∧
            env.HasType U Δ P (.sort .zero)) ∧
          S' x = fun _ => False) ∨
       (mC = false ∧ ∃ info : VProjectionInfo, env.projections I info ∧ info.ctorName = ctor ∧
          info.nparams ≤ msLen + j ∧
          (info.resultLevel.inst (lsC.map (·.inst ls))).IsNeverZero ∧
          TypedElCls env U Δ (TyCls env U Δ ((binderTy doms ls x).subst τ))
            (projCls env U Δ I (msLen + j - info.nparams) cm
              (TyCls env U Δ ((binderTy doms ls x).subst τ))) ∧
          projCls env U Δ I (msLen + j - info.nparams) cm
            (TyCls env U Δ ((binderTy doms ls x).subst τ)) (τ x) ∧
          S' x = fun k => ∃ L, .fieldOb I (msLen + j - info.nparams) L k ∈ Km)))

/-- The head type identifies the major family `I` of a rule as a projection-registered family
whose constructor is `ctor`: the head type is a telescope of `k+1` domains whose
last is an application of `I`. This replaces the `ctorHead` observation of the major, which
constructor spines of projection-registered families never have. -/
def EtaHead (I ctor : Name) (headType : VExpr) (k : Nat) : Prop :=
  ∃ (info : VProjectionInfo) (dsH : List VExpr) (RH : VExpr) (lsI : List VLevel)
    (iargs : List VExpr), env.projections I info ∧ info.ctorName = ctor ∧
    headType = .wrapForalls dsH RH ∧ dsH.length = k + 1 ∧
    dsH[k]? = some (.mkApps (.const I lsI) iargs)

end

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- The observation interpretation. See the module docstring for the clauses. -/
inductive Obs : VExpr.Subst → ObSets → VExpr → Ob → Prop
  | bvar : S i o → Obs σ S (.bvar i) o
  | sort : Obs σ S (.sort l) (.sort l.eval)
  | piDom : Obs σ S (.forallE A B) (.piDom (TyCls env U Δ (A.subst σ)))
  | piDomOb : Obs σ S A o → Obs σ S (.forallE A B) (.piDomOb o)
  | piCod : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c → c x →
    Obs σ S (.forallE A B) (.piCod c (TyCls env U Δ (B.subst (σ.cons x))))
  | piCodOb : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c →
    (∀ τ ∈ τs, Obs σ S A τ) → (∀ k ∈ K, TypedOb env U Δ c k τs) → Backed (listSet K) → c x →
    Obs (σ.cons x) (S.cons (listSet K)) B o → Obs σ S (.forallE A B) (.piCodOb c K o)
  | lam : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c →
    (∀ τ ∈ τs, Obs σ S A τ) → (∀ k ∈ K, TypedOb env U Δ c k τs) → Backed (listSet K) → c x →
    Obs (σ.cons x) (S.cons (listSet K)) t o →
    Obs σ S (.lam A t) (.app (TyCls env U Δ (A.subst σ)) c K o)
  | app : Obs σ S f (.app D c K o) → c = ElCls env U Δ D (a.subst σ) →
    (∀ k ∈ K', Obs σ S a k) → Covers K' K → Obs σ S (.app f a) o
  | const : env.Rigid n → env.constants n = some ci →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs → RigidEnd n (ls.map (·.eval)) keys r →
    Obs σ S (.const n ls) (wrap keys r)
  /-- A defined constant has the observations of its value (the right side of its delta
  rule, at the same levels), filtered by typing at its type. -/
  | delta : env.defeqs df → df.lhs = .const n (VLevel.params df.uvars) →
    env.constants n = some ci → (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) o τs → Obs .id .empty (df.rhs.instL ls) o → Obs σ S (.const n ls) o
  /-- A constructor has its constructor spine observations, filtered by typing. -/
  | ctor : IsCtor env n → ¬ IsProjCtor env n → env.constants n = some ci →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs → CtorEnd n (ls.map (·.eval)) keys r →
    KeysBacked keys → Obs σ S (.const n ls) (wrap keys r)
  /-- The constructor of a projection-registered family has only field observations
  filtered by typing. -/
  | projCtor : env.projections fam info → info.ctorName = n → env.constants n = some ci →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs →
    keys.length = info.nparams + info.numFields → PCtorEnd fam info keys r → KeysBacked keys →
    Obs σ S (.const n ls) (wrap keys r)
  /-- A projection-registered family applied to all its arguments has the field-domain type
  observations, read from the constructor type at the parameter keys. -/
  | famTy : env.Rigid n → env.constants n = some ci → env.projections n info →
    (info.resultLevel.inst ls).IsNeverZero →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys (.fieldTy n j FL x)) τs →
    keys.length = info.nparams + info.nindices → j < info.numFields → FL.length = j →
    info.ctorType.instL ls = .wrapForalls Dc R0 → info.nparams + j < Dc.length →
    ChainOK env U Δ Dc as (keys.take info.nparams ++ FL) →
    KeysBacked (keys.take info.nparams ++ FL) → ∀ {τk : Nat → List Ob},
    (∀ i (k : Key) τ, (keys.take info.nparams ++ FL)[i]? = some k → τ ∈ τk i →
      Obs (VExpr.argSubst (as.take i)) (keySets ((keys.take info.nparams ++ FL).take i))
        (Dc.getD i (.sort .zero)) τ) →
    (∀ i (k : Key) y, (keys.take info.nparams ++ FL)[i]? = some k → y ∈ k.2.2 →
      TypedOb env U Δ k.2.1 y (τk i)) →
    Obs (VExpr.argSubst as) (keySets (keys.take info.nparams ++ FL))
      (Dc.getD (info.nparams + j) (.sort .zero)) x →
    Obs σ S (.const n ls) (wrap keys (.fieldTy n j FL x))
  | famDom : env.Rigid n → env.constants n = some ci → env.projections n info →
    (info.resultLevel.inst ls).IsNeverZero →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys (.fieldDom n j FL D)) τs →
    keys.length = info.nparams + info.nindices → j < info.numFields → FL.length = j →
    info.ctorType.instL ls = .wrapForalls Dc R0 → info.nparams + j < Dc.length →
    ChainOK env U Δ Dc as (keys.take info.nparams ++ FL) →
    D = TyCls env U Δ ((Dc.getD (info.nparams + j) (.sort .zero)).subst (VExpr.argSubst as)) →
    Obs σ S (.const n ls) (wrap keys (.fieldDom n j FL D))
  /-- The rule clause: a head chain whose keys bind the rule's
  variables has the observations of the rule's right-hand side body at that binding,
  filtered by typing at the head's type. -/
  | rule : env.defeqs df →
    df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])) →
    df.rhs = .wrapLams doms body →
    env.constants n = some ci → (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap (lkeys ++ [(Dm, cm, Km)]) o) τs → lkeys.length = lead.length →
    (mC = true → ∀ df' ls', env.defeqs df' → df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' →
        df' = df) →
    (mC = true → Obs .id .empty (ci.type.instL ls)
        (piCodChain lkeys (.piDomOb (.rigid I ℓsI mI fun _ => 0)))) →
    (mC = false → (∃ ℓs, .ctorHead ctor ℓs (ms.length + fs.length) ∈ Km) ∨
      EtaHead env I ctor ci.type lkeys.length) →
    RuleBind env U Δ doms ls lead ms.length fs mC I ctor lsC lkeys cm Km τ S' →
    KeysBacked (lkeys ++ [(Dm, cm, Km)]) → Obs τ S' (body.instL ls) o →
    Obs σ S (.const n ls) (wrap (lkeys ++ [(Dm, cm, Km)]) o)
  /-- The ι rule clause: a head chain over the recursor `n` of a registered ι pattern
  (`env.pats`, `SimplePattern.iota n (k + nind) ctor (cnp + nf)` with the reduct template
  `rhs = wrapLams doms body`) whose keys bind the rule's variables has the observations of
  `body` at that binding, filtered by typing at the recursor's type. The recursor's type is a
  telescope whose major domain is an application of the family `I` at the levels `lsI`
  (`VExpr.RecShape`); the eta binding reads `I`'s projection entry at those levels. In mode C
  the rule is the only registered pattern headed by `n`. -/
  | pat {k nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed} :
    env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true) →
    rhs = .wrapLams doms body →
    doms.length = k + nf ∧ ci.type = .wrapForalls dsH RH ∧ dsH.length = k + nind + 1 ∧
      dsH[k + nind]? = some (.mkApps (.const I lsI) iargs) →
    env.constants n = some ci → (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap (lkeys ++ [(Dm, cm, Km)]) o) τs → lkeys.length = k + nind →
    (mC = true → ∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' → p'.headConst = n →
        ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
          h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true)) →
    (mC = true → Obs .id .empty (ci.type.instL ls)
        (piCodChain lkeys (.piDomOb (.rigid I ℓsI mI fun _ => 0)))) →
    (mC = false → (∃ ℓs, .ctorHead ctor ℓs (cnp + nf) ∈ Km) ∨
      EtaHead env I ctor ci.type lkeys.length) →
    RuleBind env U Δ doms ls (iotaLead k nind nf) cnp (iotaFs nf) mC I ctor lsI lkeys cm Km τ S' →
    KeysBacked (lkeys ++ [(Dm, cm, Km)]) → Obs τ S' (body.instL ls) o →
    Obs σ S (.const n ls) (wrap (lkeys ++ [(Dm, cm, Km)]) o)
  /-- A projection observes the field observations of its major. -/
  | proj : Obs σ S e (.fieldOb fam j L o) → Obs σ S (.proj fam j e) o

/-- `o`, an observation of a value of class `cv`, is typed at a list of observations of `T`. -/
def TypedAt (cv : VExpr → Prop) (σ : VExpr.Subst) (S : ObSets) (T : VExpr) (o : Ob) : Prop :=
  ∃ τs, (∀ τ ∈ τs, Obs env U Δ σ S T τ) ∧ TypedOb env U Δ cv o τs

/-- The value class of `t : T` at the anchor `σ`. -/
def vcls (σ : VExpr.Subst) (t T : VExpr) : VExpr → Prop :=
  ElCls env U Δ (TyCls env U Δ (T.subst σ)) (t.subst σ)

/-- A typed valuation for `Γ`: every observation set of a variable is backed, and every
observation of a variable is typed at observations of its type. (The anchor's typing, `Ctx.SubstEq env U Δ σ σ Γ`, is a separate hypothesis.) -/
def TV (Γ : List VExpr) (σ : VExpr.Subst) (S : ObSets) : Prop :=
  (∀ i, Backed (S i)) ∧
    ∀ i A, Lookup Γ i A → ∀ o, S i o → TypedAt env U Δ (vcls env U Δ σ (.bvar i) A) σ S A o

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-! ## Inversion -/

namespace Obs

theorem bvar_iff : Obs' σ S (.bvar i) o ↔ S i o :=
  ⟨fun | .bvar h => h, .bvar⟩

theorem sort_iff : Obs' σ S (.sort l) o ↔ o = .sort l.eval :=
  ⟨fun | .sort => rfl, fun h => h ▸ .sort⟩

theorem forallE_iff : Obs' σ S (.forallE A B) o ↔
    o = .piDom (TyCls env U Δ (A.subst σ)) ∨
    (∃ p, o = .piDomOb p ∧ Obs' σ S A p) ∨
    (∃ c x, o = .piCod c (TyCls env U Δ (B.subst (σ.cons x))) ∧
      TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧ c x) ∨
    (∃ c K x τs p, o = .piCodOb c K p ∧ TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∀ τ ∈ τs, Obs' σ S A τ) ∧ (∀ k ∈ K, TypedOb env U Δ c k τs) ∧ Backed (listSet K) ∧ c x ∧
      Obs' (σ.cons x) (S.cons (listSet K)) B p) := by
  constructor
  · intro h; cases h with
    | piDom => exact .inl rfl
    | piDomOb h => exact .inr (.inl ⟨_, rfl, h⟩)
    | piCod h1 h2 => exact .inr (.inr (.inl ⟨_, _, rfl, h1, h2⟩))
    | piCodOb h1 h2 h3 hb h4 h5 =>
      exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩))
  · rintro (rfl | ⟨_, rfl, h⟩ | ⟨_, _, rfl, h1, h2⟩ | ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩)
    · exact .piDom
    · exact .piDomOb h
    · exact .piCod h1 h2
    · exact .piCodOb h1 h2 h3 hb h4 h5

theorem lam_iff : Obs' σ S (.lam A t) o ↔
    ∃ c K x τs p, o = .app (TyCls env U Δ (A.subst σ)) c K p ∧
      TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∀ τ ∈ τs, Obs' σ S A τ) ∧ (∀ k ∈ K, TypedOb env U Δ c k τs) ∧ Backed (listSet K) ∧
      c x ∧ Obs' (σ.cons x) (S.cons (listSet K)) t p := by
  constructor
  · intro h; cases h with
    | lam h1 h2 h3 hb h4 h5 => exact ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩
  · rintro ⟨_, _, _, _, _, rfl, h1, h2, h3, hb, h4, h5⟩; exact .lam h1 h2 h3 hb h4 h5

theorem app_iff : Obs' σ S (.app f a) o ↔
    ∃ D c K K', Obs' σ S f (.app D c K o) ∧ c = ElCls env U Δ D (a.subst σ) ∧
      (∀ k ∈ K', Obs' σ S a k) ∧ Covers K' K := by
  constructor
  · intro h; cases h with
    | app h1 h2 h3 h4 => exact ⟨_, _, _, _, h1, h2, h3, h4⟩
  · rintro ⟨_, _, _, _, h1, h2, h3, h4⟩; exact .app h1 h2 h3 h4

theorem const_iff : Obs' σ S (.const n ls) o ↔
    (∃ ci τs keys r, o = wrap keys r ∧ env.Rigid n ∧ env.constants n = some ci ∧
      (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs ∧ RigidEnd n (ls.map (·.eval)) keys r) ∨
    (∃ df ci τs, env.defeqs df ∧ df.lhs = .const n (VLevel.params df.uvars) ∧
      env.constants n = some ci ∧ (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) o τs ∧ Obs' .id .empty (df.rhs.instL ls) o) ∨
    (∃ ci τs keys r, o = wrap keys r ∧ IsCtor env n ∧ ¬ IsProjCtor env n ∧
      env.constants n = some ci ∧ (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs ∧ CtorEnd n (ls.map (·.eval)) keys r ∧
      KeysBacked keys) ∨
    (∃ df doms lsP lead ctor lsC ms fs body ci τs lkeys Dm cm Km p mC τ S' I ℓsI mI,
      o = wrap (lkeys ++ [(Dm, cm, Km)]) p ∧ env.defeqs df ∧
      df.lhs = .wrapLams doms (.mkApps (.const n lsP)
        (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])) ∧
      df.rhs = .wrapLams doms body ∧
      env.constants n = some ci ∧ (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap (lkeys ++ [(Dm, cm, Km)]) p) τs ∧
      lkeys.length = lead.length ∧
      (mC = true → ∀ df' ls', env.defeqs df' →
          df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' = df) ∧
      (mC = true → Obs' .id .empty (ci.type.instL ls)
          (piCodChain lkeys (.piDomOb (.rigid I ℓsI mI fun _ => 0)))) ∧
      (mC = false → (∃ ℓs, .ctorHead ctor ℓs (ms.length + fs.length) ∈ Km) ∨
        EtaHead env I ctor ci.type lkeys.length) ∧
      RuleBind env U Δ doms ls lead ms.length fs mC I ctor lsC lkeys cm Km τ S' ∧
      KeysBacked (lkeys ++ [(Dm, cm, Km)]) ∧ Obs' τ S' (body.instL ls) p) ∨
    (∃ k nind ctor cnp nf rhs, ∃ hc : rhs.Closed, ∃ doms body ci τs lkeys Dm cm Km p mC τ S' I ℓsI
        mI dsH RH lsI iargs,
      o = wrap (lkeys ++ [(Dm, cm, Km)]) p ∧
      env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
        (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true) ∧
      rhs = .wrapLams doms body ∧
      (doms.length = k + nf ∧ ci.type = .wrapForalls dsH RH ∧ dsH.length = k + nind + 1 ∧
        dsH[k + nind]? = some (.mkApps (.const I lsI) iargs)) ∧
      env.constants n = some ci ∧ (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap (lkeys ++ [(Dm, cm, Km)]) p) τs ∧
      lkeys.length = k + nind ∧
      (mC = true → ∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' → p'.headConst = n →
        ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
          h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true)) ∧
      (mC = true → Obs' .id .empty (ci.type.instL ls)
          (piCodChain lkeys (.piDomOb (.rigid I ℓsI mI fun _ => 0)))) ∧
      (mC = false → (∃ ℓs, .ctorHead ctor ℓs (cnp + nf) ∈ Km) ∨
        EtaHead env I ctor ci.type lkeys.length) ∧
      RuleBind env U Δ doms ls (iotaLead k nind nf) cnp (iotaFs nf) mC I ctor lsI lkeys cm Km τ S' ∧
      KeysBacked (lkeys ++ [(Dm, cm, Km)]) ∧ Obs' τ S' (body.instL ls) p) ∨
    (∃ fam info ci τs keys r, o = wrap keys r ∧ env.projections fam info ∧
      info.ctorName = n ∧ env.constants n = some ci ∧
      (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys r) τs ∧
      keys.length = info.nparams + info.numFields ∧ PCtorEnd fam info keys r ∧ KeysBacked keys) ∨
    (∃ ci info τs keys j FL x Dc R0 as, ∃ τk : Nat → List Ob, o = wrap keys (.fieldTy n j FL x) ∧ env.Rigid n ∧
      env.constants n = some ci ∧ env.projections n info ∧ (info.resultLevel.inst ls).IsNeverZero ∧
      (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys (.fieldTy n j FL x)) τs ∧
      keys.length = info.nparams + info.nindices ∧ j < info.numFields ∧ FL.length = j ∧
      info.ctorType.instL ls = .wrapForalls Dc R0 ∧ info.nparams + j < Dc.length ∧
      ChainOK env U Δ Dc as (keys.take info.nparams ++ FL) ∧
      KeysBacked (keys.take info.nparams ++ FL) ∧
      (∀ i k τ, (keys.take info.nparams ++ FL)[i]? = some k → τ ∈ τk i →
        Obs' (VExpr.argSubst (as.take i)) (keySets ((keys.take info.nparams ++ FL).take i))
          (Dc.getD i (.sort .zero)) τ) ∧
      (∀ i k y, (keys.take info.nparams ++ FL)[i]? = some k → y ∈ k.2.2 →
        TypedOb env U Δ k.2.1 y (τk i)) ∧
      Obs' (VExpr.argSubst as) (keySets (keys.take info.nparams ++ FL))
        (Dc.getD (info.nparams + j) (.sort .zero)) x) ∨
    (∃ ci info τs keys j FL D Dc R0 as, o = wrap keys (.fieldDom n j FL D) ∧ env.Rigid n ∧
      env.constants n = some ci ∧ env.projections n info ∧ (info.resultLevel.inst ls).IsNeverZero ∧
      (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) (wrap keys (.fieldDom n j FL D)) τs ∧
      keys.length = info.nparams + info.nindices ∧ j < info.numFields ∧ FL.length = j ∧
      info.ctorType.instL ls = .wrapForalls Dc R0 ∧ info.nparams + j < Dc.length ∧
      ChainOK env U Δ Dc as (keys.take info.nparams ++ FL) ∧
      D = TyCls env U Δ ((Dc.getD (info.nparams + j) (.sort .zero)).subst (VExpr.argSubst as))) := by
  constructor
  · intro h; cases h with
    | const h0 h1 h2 h3 h4 => exact .inl ⟨_, _, _, _, rfl, h0, h1, h2, h3, h4⟩
    | delta h1 h2 h3 h4 h5 h6 => exact .inr (.inl ⟨_, _, _, h1, h2, h3, h4, h5, h6⟩)
    | ctor h0 hp h1 h2 h3 h4 hb =>
      exact .inr (.inr (.inl ⟨_, _, _, _, rfl, h0, hp, h1, h2, h3, h4, hb⟩))
    | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
      exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb, h12⟩)))
    | pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
      exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb, h12⟩))))
    | projCtor h1 h2 h3 h4 h5 h6 h7 h8 =>
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩)))))
    | famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩))))))
    | famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr
        ⟨_, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩))))))
  · rintro (⟨_, _, _, _, rfl, h0, h1, h2, h3, h4⟩ | ⟨_, _, _, h1, h2, h3, h4, h5, h6⟩ |
      ⟨_, _, _, _, rfl, h0, hp, h1, h2, h3, h4, hb⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb, h12⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb, h12⟩ |
      ⟨_, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩)
    · exact .const h0 h1 h2 h3 h4
    · exact .delta h1 h2 h3 h4 h5 h6
    · exact .ctor h0 hp h1 h2 h3 h4 hb
    · exact .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12
    · exact .pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12
    · exact .projCtor h1 h2 h3 h4 h5 h6 h7 h8
    · exact .famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    · exact .famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

/-- The observations of a constant do not depend on the valuation. -/
theorem const_indep : Obs' σ S (.const n ls) o ↔ Obs' σ' S' (.const n ls) o := by
  rw [const_iff, const_iff]

theorem proj_iff : Obs' σ S (.proj n i e) o ↔ ∃ L, Obs' σ S e (.fieldOb n i L o) :=
  ⟨fun | .proj h => ⟨_, h⟩, fun ⟨_, h⟩ => .proj h⟩

/-- The `piDom` observation of a Pi type records its domain class. -/
theorem piDom_mem (h : Obs' σ S (.forallE A B) (.piDom D)) : D = TyCls env U Δ (A.subst σ) := by
  cases h; rfl

theorem piDomOb_mem (h : Obs' σ S (.forallE A B) (.piDomOb p)) : Obs' σ S A p := by
  cases h; assumption

theorem piCod_mem (h : Obs' σ S (.forallE A B) (.piCod c C)) :
    TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      ∃ x, c x ∧ C = TyCls env U Δ (B.subst (σ.cons x)) := by
  cases h with | piCod h1 h2 => exact ⟨h1, _, h2, rfl⟩

theorem piCodOb_mem (h : Obs' σ S (.forallE A B) (.piCodOb c K p)) :
    TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∃ τs, (∀ τ ∈ τs, Obs' σ S A τ) ∧ ∀ k ∈ K, TypedOb env U Δ c k τs) ∧
      ∃ x, c x ∧ Obs' (σ.cons x) (S.cons (listSet K)) B p := by
  cases h with | piCodOb h1 h2 h3 _ h4 h5 => exact ⟨h1, ⟨_, h2, h3⟩, _, h4, h5⟩

theorem piCodOb_backed (h : Obs' σ S (.forallE A B) (.piCodOb c K p)) : Backed (listSet K) := by
  cases h with | piCodOb _ _ _ hb => exact hb

theorem sort_mem (h : Obs' σ S (.sort l) o) : o = .sort l.eval := sort_iff.1 h

/-! ## Weakening -/

theorem lift'_iff {t : VExpr} {ρ : Lift} {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.lift' ρ) o ↔ Obs' (σ.lift_l ρ) (S.lift_l ρ) t o := by
  induction t generalizing ρ σ S o with
  | bvar i => simp only [VExpr.lift', bvar_iff]; rfl
  | sort => simp only [VExpr.lift', sort_iff]
  | const => exact const_indep
  | proj _ _ _ ih => simp only [VExpr.lift', proj_iff, ih]
  | app f a ihf iha =>
    simp only [VExpr.lift', app_iff, ihf, iha, VExpr.subst_lift']
  | lam A t ihA iht =>
    simp only [VExpr.lift', lam_iff, ihA, iht, VExpr.subst_lift', ObSets.lift_l_cons,
      VExpr.Subst.lift_l_cons]
  | forallE A B ihA ihB =>
    simp only [VExpr.lift', forallE_iff, ihA, ihB, VExpr.subst_lift', ObSets.lift_l_cons,
      VExpr.Subst.lift_l_cons]

theorem lift_cons_iff {t : VExpr} :
    Obs' (σ.cons x) (S.cons X) t.lift o ↔ Obs' σ S t o := by
  rw [VExpr.lift_eq_lift', lift'_iff]; rfl

/-! ## Substitution -/

theorem lift_cons_set {σ : VExpr.Subst} {S : ObSets} (τ : VExpr.Subst) :
    (fun i => Obs' (σ.cons x) (S.cons (listSet K)) (τ.lift i)) =
      ObSets.cons (fun i => Obs' σ S (τ i)) (listSet K) := by
  funext i o; cases i with
  | zero => exact propext bvar_iff
  | succ i => exact propext lift_cons_iff

theorem subst_iff {t : VExpr} {τ σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.subst τ) o ↔ Obs' (τ.comp σ) (fun i => Obs' σ S (τ i)) t o := by
  induction t generalizing τ σ S o with
  | bvar i => simp only [VExpr.subst, bvar_iff]
  | sort => simp only [VExpr.subst, sort_iff]
  | const => exact const_indep
  | proj _ _ _ ih => simp only [VExpr.subst, proj_iff, ih]
  | app f a ihf iha =>
    simp only [VExpr.subst, app_iff, ihf, iha, VExpr.subst_subst]
  | lam A t ihA iht =>
    simp only [VExpr.subst, lam_iff, ihA, iht, VExpr.subst_subst, VExpr.Subst.lift_comp_cons,
      lift_cons_set]
  | forallE A B ihA ihB =>
    simp only [VExpr.subst, forallE_iff, ihA, ihB, VExpr.subst_subst,
      VExpr.Subst.lift_comp_cons, lift_cons_set]

/-- Instantiation: the observations of `t.inst a` are those of `t` with the bound variable
read as `a` (anchor `a.subst σ`, observation set the observations of `a`). -/
theorem inst_iff {t a : VExpr} {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.inst a) o ↔ Obs' (σ.cons (a.subst σ)) (S.cons (Obs' σ S a)) t o := by
  rw [VExpr.inst_eq, subst_iff]
  have h1 : (VExpr.Subst.one a).comp σ = σ.cons (a.subst σ) := by
    funext i; cases i <;> rfl
  have h2 : (fun i => Obs' σ S (VExpr.Subst.one a i)) = S.cons (Obs' σ S a) := by
    funext i o; cases i with
    | zero => rfl
    | succ i => exact propext bvar_iff
  rw [h1, h2]

/-! ## Monotonicity and compactness -/

/-- Monotonicity under inclusion of the observation sets. -/
theorem mono (h : Obs' σ S t o) (hS : ∀ i o, S i o → S' i o) : Obs' σ S' t o := by
  induction h generalizing S' with
  | bvar h => exact .bvar (hS _ _ h)
  | sort => exact .sort
  | piDom => exact .piDom
  | piDomOb _ ih => exact .piDomOb (ih hS)
  | piCod h1 h2 => exact .piCod h1 h2
  | piCodOb h1 _ h3 hb h4 _ ih2 ih5 =>
    refine .piCodOb h1 (fun τ hτ => ih2 τ hτ hS) h3 hb h4 (ih5 fun i o h => ?_)
    cases i with
    | zero => exact h
    | succ i => exact hS i o h
  | lam h1 _ h3 hb h4 _ ih2 ih5 =>
    refine .lam h1 (fun τ hτ => ih2 τ hτ hS) h3 hb h4 (ih5 fun i o h => ?_)
    cases i with
    | zero => exact h
    | succ i => exact hS i o h
  | app _ h2 _ h4 ih1 ih3 => exact .app (ih1 hS) h2 (fun k hk => ih3 k hk hS) h4
  | const h0 h1 h2 h3 h4 => exact .const h0 h1 h2 h3 h4
  | delta h1 h2 h3 h4 h5 h6 => exact .delta h1 h2 h3 h4 h5 h6
  | ctor h0 hp h1 h2 h3 h4 hb => exact .ctor h0 hp h1 h2 h3 h4 hb
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12
  | pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact .pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12
  | projCtor h1 h2 h3 h4 h5 h6 h7 h8 => exact .projCtor h1 h2 h3 h4 h5 h6 h7 h8
  | famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
    exact .famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  | famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
    exact .famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  | proj _ ih => exact .proj (ih hS)

/-- Monotonicity up to subsumption: if every observation of `S` is subsumed by one of
`S'`, every observation under `S` is subsumed by one under `S'`. -/
theorem mono_le (h : Obs' σ S t o) (hS : ∀ i o, S i o → ∃ o', S' i o' ∧ o' ≼ o) :
    ∃ o', Obs' σ S' t o' ∧ o' ≼ o := by
  induction h generalizing S' with
  | bvar h => let ⟨o', h1, h2⟩ := hS _ _ h; exact ⟨o', .bvar h1, h2⟩
  | sort => exact ⟨_, .sort, .refl⟩
  | piDom => exact ⟨_, .piDom, .refl⟩
  | piDomOb _ ih => let ⟨o', h1, h2⟩ := ih hS; exact ⟨_, .piDomOb h1, .piDomOb h2⟩
  | piCod h1 h2 => exact ⟨_, .piCod h1 h2, .refl⟩
  | @piCodOb _ τs _ _ _ K _ _ _ h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨τs', hτ1, hτ2⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
      fun τ hτ => ih2 τ hτ hS
    have ⟨o', ho1, ho2⟩ := ih5 (S' := S'.cons (listSet K)) fun i o h => by
      cases i with
      | zero => exact ⟨o, h, .refl⟩
      | succ i => exact hS i o h
    exact ⟨_, .piCodOb h1 hτ1 (fun k hk => (h3 k hk).strengthen hτ2) hb h4 ho1,
      .piCodOb_of_covers .refl ho2⟩
  | @lam _ τs _ _ _ K _ _ _ h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨τs', hτ1, hτ2⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
      fun τ hτ => ih2 τ hτ hS
    have ⟨o', ho1, ho2⟩ := ih5 (S' := S'.cons (listSet K)) fun i o h => by
      cases i with
      | zero => exact ⟨o, h, .refl⟩
      | succ i => exact hS i o h
    exact ⟨_, .lam h1 hτ1 (fun k hk => (h3 k hk).strengthen hτ2) hb h4 ho1, .app' .refl ho2⟩
  | @app _ _ _ _ _ _ _ K' _ _ h2 _ h4 ih1 ih3 =>
    have ⟨o₁, h1', l₁⟩ := ih1 hS
    have ⟨K₀, y, e, hK₀, ly⟩ := l₁.app_inv; subst e
    have ⟨K'', hK1, hK2⟩ := exists_list_cover (L := K') (R := fun y x => y ≼ x)
      fun k hk => ih3 k hk hS
    exact ⟨y, .app h1' h2 hK1 (Covers.trans hK2 (h4.trans hK₀)), ly⟩
  | const h0 h1 h2 h3 h4 => exact ⟨_, .const h0 h1 h2 h3 h4, .refl⟩
  | delta h1 h2 h3 h4 h5 h6 => exact ⟨_, .delta h1 h2 h3 h4 h5 h6, .refl⟩
  | ctor h0 hp h1 h2 h3 h4 hb => exact ⟨_, .ctor h0 hp h1 h2 h3 h4 hb, .refl⟩
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact ⟨_, .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12, .refl⟩
  | pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact ⟨_, .pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12, .refl⟩
  | projCtor h1 h2 h3 h4 h5 h6 h7 h8 => exact ⟨_, .projCtor h1 h2 h3 h4 h5 h6 h7 h8, .refl⟩
  | famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
    exact ⟨_, .famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16, .refl⟩
  | famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
    exact ⟨_, .famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13, .refl⟩
  | proj _ ih =>
    obtain ⟨o', h1, l⟩ := ih hS
    obtain ⟨_, y, rfl, ly⟩ := l.fieldOb_inv
    exact ⟨y, .proj h1, ly⟩

/-- Merge finitely many finite witnesses into one. -/
theorem collect {α : Type} {Q : Ob → Prop} {P : List Ob → α → Prop}
    (hP : ∀ K K' x, (∀ k ∈ K, k ∈ K') → P K x → P K' x) :
    ∀ {L : List α}, (∀ x ∈ L, ∃ K, (∀ k ∈ K, Q k) ∧ P K x) →
      ∃ K, (∀ k ∈ K, Q k) ∧ ∀ x ∈ L, P K x
  | [], _ => ⟨[], nofun, nofun⟩
  | x :: L, h => by
    obtain ⟨K₁, hQ₁, hP₁⟩ := h x (.head _)
    obtain ⟨K₂, hQ₂, hP₂⟩ := collect hP fun y hy => h y (.tail _ hy)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, fun y hy => ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hQ₁ k hk
      · exact hQ₂ k hk
    · cases hy with
      | head => exact hP _ _ _ (fun k hk => List.mem_append_left _ hk) hP₁
      | tail _ hy => exact hP _ _ _ (fun k hk => List.mem_append_right _ hk) (hP₂ y hy)

theorem update_mono {S : ObSets} (h : ∀ k ∈ K, k ∈ K') :
    ∀ i o, S.update n (listSet K) i o → S.update n (listSet K') i o := by
  intro i o h'; unfold ObSets.update at h' ⊢; split <;> simp_all [listSet]

theorem compact_bvar {S : ObSets} (h : S i o) (n : Nat) :
    ∃ K : List Ob, (∀ k ∈ K, S n k) ∧ Obs' σ (S.update n (listSet K)) (.bvar i) o := by
  by_cases e : i = n
  · subst e; exact ⟨[o], by simpa using h, .bvar (by simp [ObSets.update, listSet])⟩
  · exact ⟨[], nofun, .bvar (by simpa [ObSets.update, e] using h)⟩

/-- **Compactness**: a derivation uses finitely many observations of each variable. -/
theorem compact (h : Obs' σ S t o) (n : Nat) :
    ∃ K : List Ob, (∀ k ∈ K, S n k) ∧ Obs' σ (S.update n (listSet K)) t o := by
  induction h generalizing n with
  | bvar h => exact compact_bvar h n
  | sort => exact ⟨[], nofun, .sort⟩
  | piDom => exact ⟨[], nofun, .piDom⟩
  | piDomOb _ ih => let ⟨K, h1, h2⟩ := ih n; exact ⟨K, h1, .piDomOb h2⟩
  | piCod h1 h2 => exact ⟨[], nofun, .piCod h1 h2⟩
  | piCodOb h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨K₁, hK₁, hA⟩ := collect (P := fun K τ => Obs' _ (ObSets.update _ n (listSet K)) _ τ)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun τ hτ => ih2 τ hτ n
    have ⟨K₂, hK₂, hB⟩ := ih5 (n+1)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, .piCodOb h1
      (fun τ hτ => (hA τ hτ).mono (update_mono fun k hk => List.mem_append_left _ hk))
      h3 hb h4 ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hK₁ k hk
      · exact hK₂ k hk
    · rw [ObSets.update_cons] at hB
      refine hB.mono fun i o h => ?_
      cases i with
      | zero => exact h
      | succ i => exact update_mono (fun k hk => List.mem_append_right _ hk) i o h
  | lam h1 _ h3 hb h4 _ ih2 ih5 =>
    have ⟨K₁, hK₁, hA⟩ := collect (P := fun K τ => Obs' _ (ObSets.update _ n (listSet K)) _ τ)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun τ hτ => ih2 τ hτ n
    have ⟨K₂, hK₂, hB⟩ := ih5 (n+1)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, .lam h1
      (fun τ hτ => (hA τ hτ).mono (update_mono fun k hk => List.mem_append_left _ hk))
      h3 hb h4 ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hK₁ k hk
      · exact hK₂ k hk
    · rw [ObSets.update_cons] at hB
      refine hB.mono fun i o h => ?_
      cases i with
      | zero => exact h
      | succ i => exact update_mono (fun k hk => List.mem_append_right _ hk) i o h
  | app _ h2 _ h4 ih1 ih3 =>
    have ⟨K₁, hK₁, hf⟩ := ih1 n
    have ⟨K₂, hK₂, ha⟩ := collect (P := fun K k => Obs' _ (ObSets.update _ n (listSet K)) _ k)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun k hk => ih3 k hk n
    refine ⟨K₁ ++ K₂, fun k hk => ?_,
      .app (hf.mono (update_mono fun k hk => List.mem_append_left _ hk)) h2
        (fun k hk => (ha k hk).mono (update_mono fun k hk => List.mem_append_right _ hk)) h4⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact hK₁ k hk
    · exact hK₂ k hk
  | const h0 h1 h2 h3 h4 => exact ⟨[], nofun, .const h0 h1 h2 h3 h4⟩
  | delta h1 h2 h3 h4 h5 h6 => exact ⟨[], nofun, .delta h1 h2 h3 h4 h5 h6⟩
  | ctor h0 hp h1 h2 h3 h4 hb => exact ⟨[], nofun, .ctor h0 hp h1 h2 h3 h4 hb⟩
  | projCtor h1 h2 h3 h4 h5 h6 h7 h8 => exact ⟨[], nofun, .projCtor h1 h2 h3 h4 h5 h6 h7 h8⟩
  | famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
    exact ⟨[], nofun, .famTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16⟩
  | famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
    exact ⟨[], nofun, .famDom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13⟩
  | proj _ ih => let ⟨K, h1, h2⟩ := ih n; exact ⟨K, h1, .proj h2⟩
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact ⟨[], nofun, .rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12⟩
  | pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 =>
    exact ⟨[], nofun, .pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12⟩

/-- Compactness at the bound variable of an instantiation. -/
theorem compact0 {S : ObSets} {X : Ob → Prop} (h : Obs' σ (S.cons X) t o) :
    ∃ K : List Ob, (∀ k ∈ K, X k) ∧ Obs' σ (S.cons (listSet K)) t o := by
  have ⟨K, h1, h2⟩ := h.compact 0
  refine ⟨K, h1, h2.mono fun i o h => ?_⟩
  cases i <;> simpa [ObSets.update, ObSets.cons] using h

/-- Compactness at the bound variable `0` with a backed key list, for a backed set `X`. -/
theorem compact0B {S : ObSets} {X : Ob → Prop} (h : Obs' σ (S.cons X) t o) (hX : Backed X) :
    ∃ K : List Ob, (∀ k ∈ K, X k) ∧ Backed (listSet K) ∧ Obs' σ (S.cons (listSet K)) t o := by
  have ⟨K₀, h1, h2⟩ := h.compact0
  have ⟨K, h3, h4, h5⟩ := Backed.close hX h1
  refine ⟨K, h4, h5, h2.mono fun i o h => ?_⟩
  cases i with
  | zero => exact h3 o h
  | succ i => exact h

/-! ## Closed terms -/

theorem _root_.Lean4Lean.VExpr.ClosedN.subst_congr {e : VExpr} {σ σ' : VExpr.Subst}
    (h : e.ClosedN k) (hσ : ∀ i < k, σ i = σ' i) : e.subst σ = e.subst σ' := by
  induction e generalizing k σ σ' with
  | bvar i => exact hσ i h
  | sort | const => rfl
  | app _ _ ih1 ih2 => simp only [VExpr.subst, ih1 h.1 hσ, ih2 h.2 hσ]
  | proj _ _ _ ih => simp only [VExpr.subst, ih h hσ]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    simp only [VExpr.subst, ih1 h.1 hσ]
    rw [ih2 h.2 fun i hi => ?_]
    cases i with
    | zero => rfl
    | succ i => simp [VExpr.Subst.lift, hσ i (by omega)]

/-- The observations of a term depend only on the valuation of its free variables. -/
theorem closed_iff {t : VExpr} (ht : t.ClosedN k) (hσ : ∀ i < k, σ i = σ' i)
    (hS : ∀ i < k, S i = S' i) : Obs' σ S t o ↔ Obs' σ' S' t o := by
  induction t generalizing k σ σ' S S' o with
  | bvar i => simp only [bvar_iff, hS i ht]
  | sort => simp only [sort_iff]
  | const => exact const_indep
  | proj _ _ _ ih => simp only [proj_iff, ih ht hσ hS]
  | app f a ihf iha =>
    simp only [app_iff, ihf ht.1 hσ hS, iha ht.2 hσ hS, ht.2.subst_congr hσ]
  | lam A t ihA iht =>
    have hσ' : ∀ x, ∀ i < k+1, (σ.cons x) i = (σ'.cons x) i := fun x i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hσ i (by omega)
    have hS' : ∀ X, ∀ i < k+1, (S.cons X) i = (S'.cons X) i := fun X i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hS i (by omega)
    simp only [lam_iff, ihA ht.1 hσ hS, ht.1.subst_congr hσ,
      fun x X o => iht (o := o) ht.2 (hσ' x) (hS' X)]
  | forallE A B ihA ihB =>
    have hσ' : ∀ x, ∀ i < k+1, (σ.cons x) i = (σ'.cons x) i := fun x i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hσ i (by omega)
    have hS' : ∀ X, ∀ i < k+1, (S.cons X) i = (S'.cons X) i := fun X i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hS i (by omega)
    simp only [forallE_iff, ihA ht.1 hσ hS, ht.1.subst_congr hσ,
      fun x => ht.2.subst_congr (hσ' x), fun x X o => ihB (o := o) ht.2 (hσ' x) (hS' X)]

theorem closed_iff_id {t : VExpr} (ht : t.ClosedN) : Obs' σ S t o ↔ Obs' .id .empty t o :=
  closed_iff ht (fun _ h => nomatch h) (fun _ h => nomatch h)

/-! ## Level variants -/

theorem _root_.Lean4Lean.VEnv.Model.map_eval_eq {ls ls' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) ls ls') : ls.map (·.eval) = ls'.map (·.eval) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h

theorem forall₂_inst_congr {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    ∀ (l : List VLevel), List.Forall₂ (· ≈ ·) (l.map (·.inst ls)) (l.map (·.inst ls'))
  | [] => .nil
  | _ :: l => .cons (VLevel.inst_congr rfl h) (forall₂_inst_congr h l)

theorem _root_.Lean4Lean.VEnv.Model.RuleBind.lvEq
    (h : RuleBind env U Δ doms ls lead msLen fs mC I cN lsC keys cm Km τ S')
    (w1 : ∀ l ∈ ls, l.WF U) (w2 : ∀ l ∈ ls', l.WF U) (hls : List.Forall₂ (· ≈ ·) ls ls') :
    RuleBind env U Δ doms ls' lead msLen fs mC I cN lsC keys cm Km τ S' := by
  refine ⟨h.1, fun x hx => ?_⟩
  have e : TyCls env U Δ ((binderTy doms ls x).subst τ) =
      TyCls env U Δ ((binderTy doms ls' x).subst τ) :=
    TyCls.eq_of_lvEq ((LvEq.instL _ w1 w2 hls).subst τ)
  have hnz : ∀ l : VLevel, (l.inst (lsC.map (·.inst ls))).IsNeverZero →
      (l.inst (lsC.map (·.inst ls'))).IsNeverZero := fun l h =>
    VLevel.IsNeverZero.of_equiv h
      (VLevel.inst_congr (VLevel.equiv_def.2 fun _ => rfl) (forall₂_inst_congr hls lsC))
  have := h.2 x hx
  rw [e] at this
  rcases this with h1 | ⟨h1, j, hj, h2 | h2 | ⟨h3, info, h4, h5, h6, h7, h8⟩⟩
  · exact .inl h1
  · exact .inr ⟨h1, j, hj, .inl h2⟩
  · exact .inr ⟨h1, j, hj, .inr (.inl h2)⟩
  · exact .inr ⟨h1, j, hj, .inr (.inr ⟨h3, info, h4, h5, h6, hnz _ h7, h8⟩)⟩

/-- The value class of a constant transfers to equivalent levels. -/
theorem _root_.Lean4Lean.VEnv.Model.constCls_lvEq {T : VExpr} {ls ls' : List VLevel}
    (w1 : ∀ l ∈ ls, l.WF U) (w2 : ∀ l ∈ ls', l.WF U) (hls : List.Forall₂ (· ≈ ·) ls ls') :
    ElCls env U Δ (TyCls env U Δ (T.instL ls)) (.const n ls) =
      ElCls env U Δ (TyCls env U Δ (T.instL ls')) (.const n ls') := by
  rw [TyCls.eq_of_lvEq (LvEq.instL T w1 w2 hls), ElCls.eq_of_lvEq (LvEq.const w1 w2 hls)]

theorem _root_.Lean4Lean.VEnv.Model.LvEq.wrapForalls_inv : ∀ {D : List VExpr} {R X : VExpr},
    LvEq U (.wrapForalls D R) X → ∃ D' R', X = .wrapForalls D' R' ∧ D'.length = D.length ∧
      ∀ i, LvEq U (D.getD i (.sort .zero)) (D'.getD i (.sort .zero))
  | [], R, X, _ => ⟨[], X, rfl, rfl, fun _ => .refl⟩
  | A :: D, R, X, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons] at h
    cases h with
    | refl => exact ⟨A :: D, R, rfl, rfl, fun _ => .refl⟩
    | forallE hA hB =>
      obtain ⟨D', R', rfl, hl, hD⟩ := LvEq.wrapForalls_inv hB
      refine ⟨_ :: D', R', rfl, by simp [hl], fun i => ?_⟩
      cases i with
      | zero => exact hA
      | succ i => exact hD i

theorem _root_.Lean4Lean.VEnv.Model.wrapForalls_instL_lvEq {T : VExpr} {D : List VExpr}
    (h : T.instL ls = .wrapForalls D R0) (w1 : ∀ l ∈ ls, l.WF U) (w2 : ∀ l ∈ ls', l.WF U)
    (w3 : List.Forall₂ (· ≈ ·) ls ls') : ∃ D' R', T.instL ls' = .wrapForalls D' R' ∧
      D'.length = D.length ∧ ∀ i, LvEq U (D.getD i (.sort .zero)) (D'.getD i (.sort .zero)) := by
  have := LvEq.instL T w1 w2 w3; rw [h] at this; exact LvEq.wrapForalls_inv this

theorem _root_.Lean4Lean.VEnv.Model.ChainOK.lvEq {D D' as : List VExpr} {K : List Key}
    (h : ChainOK env U Δ D as K)
    (hD : ∀ i, LvEq U (D.getD i (.sort .zero)) (D'.getD i (.sort .zero))) :
    ChainOK env U Δ D' as K := by
  refine ⟨h.1, fun i a k ha hk => ?_⟩
  rw [← TyCls.eq_of_lvEq ((hD i).subst _)]
  exact h.2 i a k ha hk

/-- **Level invariance**: the observations of a term are those of its level variants
(classes are saturated by `LvEq`, levels are observed through `VLevel.eval`). -/
theorem lvEq (h : Obs' σ S t o) (ht : LvEq U t t') : Obs' σ S t' o := by
  induction h generalizing t' with
  | bvar h => cases ht; exact .bvar h
  | @sort _ _ l =>
    cases ht with
    | refl => exact .sort
    | sort _ _ h3 => have : l.eval = _ := h3; rw [this]; exact .sort
  | @piDom _ _ A B =>
    cases ht with
    | refl => exact .piDom
    | forallE h1 _ => rw [TyCls.eq_of_lvEq (h1.subst _)]; exact .piDom
  | piDomOb _ ih =>
    cases ht with
    | refl => exact .piDomOb (ih .refl)
    | forallE h1 _ => exact .piDomOb (ih h1)
  | piCod h1 h2 =>
    cases ht with
    | refl => exact .piCod h1 h2
    | forallE l1 l2 =>
      rw [TyCls.eq_of_lvEq (l1.subst _)] at h1
      rw [TyCls.eq_of_lvEq (l2.subst _)]; exact .piCod h1 h2
  | piCodOb h1 _ h3 hb h4 _ ih2 ih5 =>
    cases ht with
    | refl => exact .piCodOb h1 (fun τ hτ => ih2 τ hτ .refl) h3 hb h4 (ih5 .refl)
    | forallE l1 l2 =>
      rw [TyCls.eq_of_lvEq (l1.subst _)] at h1
      exact .piCodOb h1 (fun τ hτ => ih2 τ hτ l1) h3 hb h4 (ih5 l2)
  | lam h1 _ h3 hb h4 _ ih2 ih5 =>
    cases ht with
    | refl => exact .lam h1 (fun τ hτ => ih2 τ hτ .refl) h3 hb h4 (ih5 .refl)
    | lam l1 l2 =>
      rw [TyCls.eq_of_lvEq (l1.subst _)] at h1 ⊢
      exact .lam h1 (fun τ hτ => ih2 τ hτ l1) h3 hb h4 (ih5 l2)
  | app _ h2 _ h4 ih1 ih3 =>
    cases ht with
    | refl => exact .app (ih1 .refl) h2 (fun k hk => ih3 k hk .refl) h4
    | app l1 l2 =>
      exact .app (ih1 l1) (h2.trans (ElCls.eq_of_lvEq (l2.subst _)))
        (fun k hk => ih3 k hk l2) h4
  | const h0 h1 _ h3 h4 ih2 =>
    cases ht with
    | refl => exact .const h0 h1 (fun τ hτ => ih2 τ hτ .refl) h3 h4
    | const w1 w2 w3 =>
      exact .const h0 h1 (fun τ hτ => ih2 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h3) (map_eval_eq w3 ▸ h4)
  | ctor h0 hp h1 _ h3 h4 hb ih2 =>
    cases ht with
    | refl => exact .ctor h0 hp h1 (fun τ hτ => ih2 τ hτ .refl) h3 h4 hb
    | const w1 w2 w3 =>
      exact .ctor h0 hp h1 (fun τ hτ => ih2 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h3) (map_eval_eq w3 ▸ h4) hb
  | projCtor h1 h2 h3 _ h5 h6 h7 h8 ih4 =>
    cases ht with
    | refl => exact .projCtor h1 h2 h3 (fun τ hτ => ih4 τ hτ .refl) h5 h6 h7 h8
    | const w1 w2 w3 =>
      exact .projCtor h1 h2 h3 (fun τ hτ => ih4 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h5) h6 h7 h8
  | famTy h1 h2 h3 h4 _ h6 h7 h8 h9 h10 h11 h12 h13 _ h15 _ ih5 ih14 ih16 =>
    cases ht with
    | refl =>
      exact .famTy h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ .refl) h6 h7 h8 h9 h10 h11 h12 h13
        (fun i k τ hk hτ => ih14 i k τ hk hτ .refl) h15 (ih16 .refl)
    | const w1 w2 w3 =>
      obtain ⟨D', R', e', hlD, hD⟩ := wrapForalls_instL_lvEq h10 w1 w2 w3
      exact .famTy h1 h2 h3 (VLevel.IsNeverZero.of_equiv h4 (VLevel.inst_congr (VLevel.equiv_def.2 fun _ => rfl) w3))
        (fun τ hτ => ih5 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h6) h7 h8 h9 e' (hlD ▸ h11) (h12.lvEq hD) h13
        (fun i k τ hk hτ => ih14 i k τ hk hτ (hD i)) h15 (ih16 (hD _))
  | famDom h1 h2 h3 h4 _ h6 h7 h8 h9 h10 h11 h12 h13 ih5 =>
    cases ht with
    | refl => exact .famDom h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ .refl) h6 h7 h8 h9 h10 h11 h12 h13
    | const w1 w2 w3 =>
      obtain ⟨D', R', e', hlD, hD⟩ := wrapForalls_instL_lvEq h10 w1 w2 w3
      exact .famDom h1 h2 h3 (VLevel.IsNeverZero.of_equiv h4 (VLevel.inst_congr (VLevel.equiv_def.2 fun _ => rfl) w3))
        (fun τ hτ => ih5 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h6) h7 h8 h9 e' (hlD ▸ h11) (h12.lvEq hD)
        (h13.trans (TyCls.eq_of_lvEq ((hD _).subst _)))
  | proj _ ih =>
    cases ht with
    | refl => exact .proj (ih .refl)
    | proj l => exact .proj (ih l)
  | rule h1 h2 h3 h4 _ h6 h7 h8 _ h10 h11 hb _ ih5 ih9 ih12 =>
    cases ht with
    | refl =>
      exact .rule h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ .refl) h6 h7 h8 (fun e => ih9 e .refl) h10
        h11 hb (ih12 .refl)
    | const w1 w2 w3 =>
      exact .rule h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h6) h7 h8
        (fun e => ih9 e (.instL _ w1 w2 w3)) h10 (h11.lvEq w1 w2 w3) hb (ih12 (.instL _ w1 w2 w3))
  | pat h1 h2 h3 h4 _ h6 h7 h8 _ h10 h11 hb _ ih5 ih9 ih12 =>
    cases ht with
    | refl =>
      exact .pat h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ .refl) h6 h7 h8 (fun e => ih9 e .refl) h10
        h11 hb (ih12 .refl)
    | const w1 w2 w3 =>
      exact .pat h1 h2 h3 h4 (fun τ hτ => ih5 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h6) h7 h8
        (fun e => ih9 e (.instL _ w1 w2 w3)) h10 (h11.lvEq w1 w2 w3) hb (ih12 (.instL _ w1 w2 w3))
  | delta h1 h2 h3 _ h5 _ ih4 ih6 =>
    cases ht with
    | refl => exact .delta h1 h2 h3 (fun τ hτ => ih4 τ hτ .refl) h5 (ih6 .refl)
    | const w1 w2 w3 =>
      exact .delta h1 h2 h3 (fun τ hτ => ih4 τ hτ (.instL _ w1 w2 w3))
        (constCls_lvEq w1 w2 w3 ▸ h5) (ih6 (.instL _ w1 w2 w3))

theorem _root_.Lean4Lean.VEnv.Model.wit_wrap :
    ∀ {keys : List Key} {o : Ob}, (wrap keys o).wit = o.wit.map (wrap keys)
  | [], o => by simp only [wrap_nil]; exact (List.map_id' _).symm
  | k :: keys, o => by
    simp only [wrap_cons, Ob.wit, wit_wrap, List.map_map]; rfl

theorem _root_.Lean4Lean.VEnv.Model.mem_wit_wrap {keys : List Key} :
    w ∈ (wrap keys o).wit ↔ ∃ w', w' ∈ o.wit ∧ w = wrap keys w' := by
  rw [wit_wrap, List.mem_map]; exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm⟩, fun ⟨a, b, c⟩ => ⟨a, b, c.symm⟩⟩

theorem _root_.Lean4Lean.VEnv.Model.take_map_take {keys : List Key} {np i j : Nat} (h : i ≤ j) :
    (((keys.drop np).take j).map (·.2.2)).take i = ((keys.drop np).take i).map (·.2.2) := by
  rw [← List.map_take, List.take_take, Nat.min_eq_left h]

/-- **Backing is structural**: observation sets at backed valuations are backed. -/
theorem backed (h : Obs' σ S t o) (hS : ∀ i, Backed (S i)) : ∀ w ∈ o.wit, Obs' σ S t w := by
  induction h with
  | bvar h => exact fun w hw => .bvar (hS _ _ h w hw)
  | sort | piDom | piCod | piDomOb | piCodOb | famTy | famDom =>
    intro w hw; simp [Ob.wit, wit_wrap] at hw
  | @lam _ _ _ c x τs K t' o h1 h2 h3 hb h4 _ _ ih5 =>
    intro w hw
    simp only [Ob.wit, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    refine .lam h1 h2 h3 hb h4 (ih5 (fun i => ?_) w' hw')
    cases i with
    | zero => exact hb
    | succ i => exact hS i
  | app _ h2 h3 h4 ih1 _ =>
    intro w hw
    exact .app (ih1 hS _ (by simp only [Ob.wit]; exact List.mem_map_of_mem hw)) h2 h3 h4
  | const h0 h1 h2 h3 h4 =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    rcases h4 with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [Ob.wit] at hw'
  | delta h1 h2 h3 h4 h5 _ _ ih6 =>
    intro w hw
    exact .delta h1 h2 h3 h4 (h5.wit w hw) (ih6 (fun _ _ h => nomatch h) w hw)
  | ctor h0 hp h1 h2 h3 h4 hb =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    rcases h4 with rfl | ⟨_, _, rfl⟩ | ⟨i, hi, k, hk, rfl⟩
    · simp [Ob.wit] at hw'
    · simp [Ob.wit] at hw'
    · simp only [Ob.wit, List.mem_map] at hw'
      obtain ⟨w'', hw'', rfl⟩ := hw'
      have hty := h3.wit _ (mem_wit_wrap.2 ⟨_, by simp only [Ob.wit]; exact List.mem_map_of_mem hw'', rfl⟩)
      exact .ctor h0 hp h1 h2 hty (.inr (.inr ⟨i, hi, w'', hb _ (List.getElem_mem hi) k hk w'' hw'', rfl⟩)) hb
  | @projCtor fam info n ci τs ls keys r σ S h1 h2 h3 h4 h5 h6 h7 h8 =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    have hty := h5.wit _ (mem_wit_wrap.2 ⟨_, hw', rfl⟩)
    obtain ⟨j, L, k, rfl, hj, hLj, hLk, kj, hkj, hk⟩ := h7
    rcases Ob.mem_wit_fieldOb.1 hw' with ⟨i, Li, y, hLi, hy, rfl⟩ | ⟨w'', hw'', rfl⟩
    · have hil : i < j := by
        have := (List.getElem?_eq_some_iff.1 hLi).1; omega
      obtain ⟨ki, hki, hyi⟩ := hLk i Li hLi
      refine .projCtor h1 h2 h3 h4 hty h6 ⟨i, _, y, rfl, by omega, by simp; omega,
        fun i' Li' hi' => ?_, ki, hki, hyi y hy⟩ h8
      rw [List.getElem?_take] at hi'
      split at hi'
      · exact hLk i' Li' hi'
      · cases hi'
    · exact .projCtor h1 h2 h3 h4 hty h6
        ⟨j, _, w'', rfl, hj, hLj, hLk, kj, hkj, h8 kj (List.mem_of_getElem? hkj) _ hk w'' hw''⟩ h8
  | rule h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 _ _ ih12 =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    have hty := h6.wit _ (mem_wit_wrap.2 ⟨_, hw', rfl⟩)
    exact .rule h1 h2 h3 h4 h5 hty h7 h8 h9 h10 h11 hb (ih12 h11.1 w' hw')
  | pat h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hb h12 _ _ ih12 =>
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_wit_wrap.1 hw
    have hty := h6.wit _ (mem_wit_wrap.2 ⟨_, hw', rfl⟩)
    exact .pat h1 h2 h3 h4 h5 hty h7 h8 h9 h10 h11 hb (ih12 h11.1 w' hw')
  | proj _ ih =>
    intro w hw
    exact .proj (ih hS _ (Ob.mem_wit_fieldOb.2 (.inr ⟨w, hw, rfl⟩)))

end Obs

/-! ## Typed observations at a type, typed valuations -/

theorem TypedAt.mono_le (h : TypedAt env U Δ cv σ S T o)
    (hT : Ob.Sub (Obs' σ S T) (Obs' σ' S' T')) : TypedAt env U Δ cv σ' S' T' o := by
  obtain ⟨τs, h1, h2⟩ := h
  have ⟨τs', h3, h4⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
    fun τ hτ => hT τ (h1 τ hτ)
  exact ⟨τs', h3, h2.strengthen h4⟩

theorem TypedAt.congr_cls (h : TypedAt env U Δ cv σ S T o) (e : cv = cv') :
    TypedAt env U Δ cv' σ S T o := e ▸ h

/-- Finitely many typed observations are typed at one common list. -/
theorem TypedAt.merge {K : List Ob} (h : ∀ k ∈ K, TypedAt env U Δ cv σ S T k) :
    ∃ τs, (∀ τ ∈ τs, Obs' σ S T τ) ∧ ∀ k ∈ K, TypedOb env U Δ cv k τs := by
  have ⟨τs, h1, h2⟩ := Obs.collect (Q := fun τ => Obs' σ S T τ)
    (P := fun τs k => TypedOb env U Δ cv k τs) (fun _ _ _ hK h => h.mono hK) fun k hk =>
      let ⟨τs, h1, h2⟩ := h k hk; ⟨τs, h1, h2⟩
  exact ⟨τs, h1, h2⟩

theorem TypedAt.lift_cons {T : VExpr} (h : TypedAt env U Δ cv σ S T o) :
    TypedAt env U Δ cv (σ.cons x) (S.cons X) T.lift o :=
  let ⟨τs, h1, h2⟩ := h; ⟨τs, fun τ hτ => Obs.lift_cons_iff.2 (h1 τ hτ), h2⟩

theorem vcls_bvar_zero {A : VExpr} :
    vcls env U Δ (σ.cons x) (.bvar 0) A.lift = ElCls env U Δ (TyCls env U Δ (A.subst σ)) x := by
  simp only [vcls, VExpr.lift_subst_cons]; rfl

theorem vcls_bvar_succ {A : VExpr} :
    vcls env U Δ (σ.cons x) (.bvar (i+1)) A.lift = vcls env U Δ σ (.bvar i) A := by
  simp only [vcls, VExpr.lift_subst_cons]; rfl

theorem TV.empty : TV env U Δ Γ σ .empty :=
  And.intro (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)

theorem TV.cons (h : TV env U Δ Γ σ S) (hb : Backed (listSet K))
    (hK : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) x) σ S A k) :
    TV env U Δ (A :: Γ) (σ.cons x) (S.cons (listSet K)) := by
  refine ⟨fun i => ?_, fun i B hL o ho => ?_⟩
  · cases i with
    | zero => exact hb
    | succ i => exact h.1 i
  · cases hL with
    | zero => rw [vcls_bvar_zero]; exact (hK o ho).lift_cons
    | succ hL => rw [vcls_bvar_succ]; exact (h.2 _ _ hL o ho).lift_cons

/-! ## Constants -/

/-- Every observation of a constant passes its typing filter. -/
theorem Obs.const_typed (h : Obs' σ S (.const n ls) o) (hci : env.constants n = some ci) :
    TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls))
      .id .empty (ci.type.instL ls) o := by
  rcases Obs.const_iff.1 h with ⟨ci', τs, _, _, rfl, _, hci', hτ, hty, _⟩ |
    ⟨_, ci', τs, _, _, hci', hτ, hty, _⟩ | ⟨ci', τs, _, _, rfl, _, _, hci', hτ, hty, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, ci', τs, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _, _, hci', hτ,
      hty, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, ci', τs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _, _,
      hci', hτ, hty, _⟩ | ⟨_, _, ci', τs, _, _, rfl, _, _, hci', hτ, hty, _⟩ |
    ⟨ci', _, τs, _, _, _, _, _, _, _, _, rfl, _, hci', _, _, hτ, hty, _⟩ |
    ⟨ci', _, τs, _, _, _, _, _, _, _, rfl, _, hci', _, _, hτ, hty, _⟩ <;>
    cases hci.symm.trans hci' <;> exact ⟨τs, hτ, hty⟩

/-- Observations of a constant transfer to equivalent levels, given that the observations
of its type transfer. -/
theorem Obs.const_levels (h : Obs' σ S (.const n ls) o)
    (hT : ∀ ci, env.constants n = some ci →
      Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (ci.type.instL ls')))
    (w1 : ∀ l ∈ ls, l.WF U) (w2 : ∀ l ∈ ls', l.WF U) (hls : List.Forall₂ (· ≈ ·) ls ls') :
    Obs' σ' S' (.const n ls') o := by
  have tr : ∀ ci τs o, env.constants n = some ci →
      (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) →
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls)) (.const n ls)) o τs →
      ∃ τs', (∀ τ ∈ τs', Obs' .id .empty (ci.type.instL ls') τ) ∧
        TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL ls')) (.const n ls')) o τs' :=
    fun ci τs o hci hτ hty => (constCls_lvEq w1 w2 hls) ▸
      TypedAt.mono_le ⟨τs, hτ, hty⟩ (hT ci hci)
  rcases Obs.const_iff.1 h with ⟨ci, τs, _, _, rfl, h0, hci, hτ, hty, hr⟩ |
    ⟨_, ci, τs, h1, h2, hci, hτ, hty, hv⟩ | ⟨ci, τs, _, _, rfl, h0, hp, hci, hτ, hty, hr, hb⟩ |
    ⟨_, _, _, _, _, _, _, _, _, ci, τs, _, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, hci,
      hτ, hty, h7, h8, h9, h10, h11, hb, h12⟩ |
    ⟨_, _, _, _, _, _, _, _, _, ci, τs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3,
      hci, hτ, hty, h7, h8, h9, h10, h11, hb, h12⟩ |
    ⟨_, _, ci, τs, _, _, rfl, h1, h2, hci, hτ, hty, h6, h7, h8⟩ |
    ⟨ci, _, τs, _, _, _, _, _, _, _, _, rfl, h0, hci, h3, h4, hτ, hty, h6, h7, h8, h9, h9', h10, h11,
      h12, h13, h14⟩ |
    ⟨ci, _, τs, _, _, _, _, _, _, _, rfl, h0, hci, h3, h4, hτ, hty, h6, h7, h8, h9, h9', h10, h11⟩ <;>
    obtain ⟨τs', h1', h2'⟩ := tr ci τs _ hci hτ hty
  · exact .const h0 hci h1' h2' (map_eval_eq hls ▸ hr)
  · exact .delta h1 h2 hci h1' h2' (hv.lvEq (.instL _ w1 w2 hls))
  · exact .ctor h0 hp hci h1' h2' (map_eval_eq hls ▸ hr) hb
  · exact .rule h1 h2 h3 hci h1' h2' h7 h8 (fun e => (h9 e).lvEq (.instL _ w1 w2 hls)) h10
      (h11.lvEq w1 w2 hls) hb (h12.lvEq (.instL _ w1 w2 hls))
  · exact .pat h1 h2 h3 hci h1' h2' h7 h8 (fun e => (h9 e).lvEq (.instL _ w1 w2 hls)) h10
      (h11.lvEq w1 w2 hls) hb (h12.lvEq (.instL _ w1 w2 hls))
  · exact .projCtor h1 h2 hci h1' h2' h6 h7 h8
  · obtain ⟨D', R', e', hlD, hD⟩ := wrapForalls_instL_lvEq h9 w1 w2 hls
    exact .famTy h0 hci h3 (VLevel.IsNeverZero.of_equiv h4 (VLevel.inst_congr (VLevel.equiv_def.2 fun _ => rfl) hls))
      h1' h2' h6 h7 h8 e' (hlD ▸ h9') (h10.lvEq hD) h11
      (fun i k τ hk hτ => (h12 i k τ hk hτ).lvEq (hD i)) h13 (h14.lvEq (hD _))
  · obtain ⟨D', R', e', hlD, hD⟩ := wrapForalls_instL_lvEq h9 w1 w2 hls
    exact .famDom h0 hci h3 (VLevel.IsNeverZero.of_equiv h4 (VLevel.inst_congr (VLevel.equiv_def.2 fun _ => rfl) hls))
      h1' h2' h6 h7 h8 e' (hlD ▸ h9') (h10.lvEq hD) (h11.trans (TyCls.eq_of_lvEq ((hD _).subst _)))

end Model
end VEnv
end Lean4Lean
