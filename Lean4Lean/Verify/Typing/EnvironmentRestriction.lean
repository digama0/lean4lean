import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean

open Lean

namespace VEnv

/-- The constants on which a particular typing/definitional-equality
derivation depends.  This is proof-relevant on purpose: merely knowing that
the endpoints avoid a name cannot exclude a transitivity detour through that
constant. -/
inductive IsDefEq.Avoids {env : VEnv} {uvars : Nat}
    (changed : Name → Prop) :
    ∀ {ctx lhs rhs type}, env.IsDefEq uvars ctx lhs rhs type → Prop where
  | pat {p : Pattern} {r : p.RHS × p.Check} {m1 m2 chk}
      (Hp : env.pats p r) (Hm : p.Matches e m1 m2)
      (He : env.IsDefEq uvars ctx e e A) (Hr : r.2.Realizes m1 m2 chk)
      (Hchk : ∀ t ∈ chk, env.IsDefEq uvars ctx t.1 t.2.1 t.2.2) :
      Avoids changed He → (∀ t ht, Avoids changed (Hchk t ht)) →
      Avoids changed (.pat Hp Hm He Hr Hchk)
  | bvar (H : Lookup ctx i type) : Avoids changed (.bvar H)
  | symm : Avoids changed H → Avoids changed (.symm H)
  | trans : Avoids changed H₁ → Avoids changed H₂ →
      Avoids changed (.trans H₁ H₂)
  | sortDF (Hleft : left.WF uvars) (Hright : right.WF uvars)
      (Heq : left ≈ right) : Avoids changed (.sortDF Hleft Hright Heq)
  | constDF
      (name : Name) (ci : VConstant)
      (levels levels' : List VLevel)
      (Hlookup : env.constants name = some ci)
      (Hleft : ∀ (level : VLevel), level ∈ levels → level.WF uvars)
      (Hright : ∀ (level : VLevel), level ∈ levels' → level.WF uvars)
      (Hlength : levels.length = ci.uvars)
      (Heq : List.Forall₂ (· ≈ ·) levels levels')
      (Hname : ¬ changed name) :
      Avoids changed (.constDF Hlookup Hleft Hright Hlength Heq)
  | appDF : Avoids changed Hfn → Avoids changed Harg →
      Avoids changed (.appDF Hfn Harg)
  | projDF
      (typeName : Name) (info : VProjectionInfo)
      (levels : List VLevel) (params indexArgs : List VExpr)
      (index : Nat) (sourceMajor fieldType : VExpr)
      (Gamma : List VExpr) (fieldLevel : VLevel)
      (major major' : VExpr)
      (Hinfo : env.projections typeName info)
      (Hlevels : ∀ level ∈ levels, level.WF uvars)
      (Huvars : levels.length = info.uvars)
      (Hparams : params.length = info.nparams)
      (Hindices : indexArgs.length = info.nindices)
      (HfieldType : info.fieldType typeName levels params index sourceMajor =
        some fieldType)
      (Hfield : env.IsDefEq uvars Gamma fieldType fieldType (.sort fieldLevel))
      (Hmajor : env.IsDefEq uvars Gamma sourceMajor major
        (VExpr.mkApps (.const typeName levels) (params ++ indexArgs)))
      (Hmajor' : env.IsDefEq uvars Gamma sourceMajor major'
        (VExpr.mkApps (.const typeName levels) (params ++ indexArgs)))
      (Hclosed : info.ctorType.Closed)
      (Hguard : (info.resultLevel.inst levels).IsNeverZero ∨
        fieldLevel ≈ .zero) :
      Avoids changed Hfield → Avoids changed Hmajor →
      Avoids changed Hmajor' →
      Avoids changed (.projDF Hinfo Hlevels Huvars Hparams Hindices
        HfieldType Hfield Hmajor Hmajor' Hclosed Hguard)
  | lamDF : Avoids changed Htype → Avoids changed Hbody →
      Avoids changed (.lamDF Htype Hbody)
  | forallEDF : Avoids changed Htype → Avoids changed Hbody →
      Avoids changed (.forallEDF Htype Hbody)
  | defeqDF : Avoids changed Htype → Avoids changed Hterm →
      Avoids changed (.defeqDF Htype Hterm)
  | beta : Avoids changed Hbody → Avoids changed Harg →
      Avoids changed (.beta Hbody Harg)
  | eta : Avoids changed H → Avoids changed (.eta H)
  | proofIrrel : Avoids changed Hprop → Avoids changed Hleft →
      Avoids changed Hright →
      Avoids changed (.proofIrrel Hprop Hleft Hright)
  | extra
      (df : VDefEq) (levels : List VLevel)
      (Hdf : env.defeqs df)
      (Hlevels : ∀ (level : VLevel), level ∈ levels → level.WF uvars)
      (Hlength : levels.length = df.uvars) :
      Avoids changed (.extra Hdf Hlevels Hlength)
  | projIota
      (Hinfo : env.projections typeName info)
      (Hproj : env.IsDefEq uvars Gamma
        (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args))
        (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args))
        fieldType)
      (Hindex : args[info.nparams + index]? = some field)
      (Hfield : env.IsDefEq uvars Gamma field field fieldType) :
      Avoids changed Hproj → Avoids changed Hfield →
      Avoids changed (.projIota Hinfo Hproj Hindex Hfield)
  | structEta
      (Hinfo : env.projections typeName info)
      (Hparams : params.length = info.nparams)
      (Hindices : info.nindices = 0)
      (He : env.IsDefEq uvars Gamma e e (VExpr.mkApps (.const typeName levels) params))
      (Hctor : env.IsDefEq uvars Gamma
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj typeName index e))
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj typeName index e))
        (VExpr.mkApps (.const typeName levels) params)) :
      Avoids changed He → Avoids changed Hctor →
      Avoids changed (.structEta Hinfo Hparams Hindices He Hctor)
  | unitLike
      (Hinfo : env.projections typeName info)
      (Hparams : params.length = info.nparams)
      (Hindices : info.nindices = 0)
      (HnumFields : info.numFields = 0)
      (He : env.IsDefEq uvars Gamma e e (VExpr.mkApps (.const typeName levels) params))
      (He' : env.IsDefEq uvars Gamma e' e' (VExpr.mkApps (.const typeName levels) params)) :
      Avoids changed He → Avoids changed He' →
      Avoids changed (.unitLike Hinfo Hparams Hindices HnumFields He He')

/-- If every installed constant is outside `changed`, every derivation in
the environment avoids `changed`. -/
theorem IsDefEq.avoids_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : env.IsDefEq uvars ctx lhs rhs type)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.Avoids changed := by
  induction H with
  | pat hp hm he hr hchk ihe ihchk => exact .pat hp hm he hr hchk ihe ihchk
  | bvar Hlookup => exact .bvar Hlookup
  | symm H IH => exact .symm IH
  | trans H₁ H₂ IH₁ IH₂ => exact .trans IH₁ IH₂
  | sortDF Hleft Hright Heq => exact .sortDF Hleft Hright Heq
  | constDF Hlookup Hleft Hright Hlength Heq =>
    exact .constDF _ _ _ _ Hlookup Hleft Hright Hlength Heq
      (Hconstants Hlookup)
  | appDF Hfn Harg IHfn IHarg => exact .appDF IHfn IHarg
  | @projDF typeName info levels params index sourceMajor fieldType Gamma
      fieldLevel major indexArgs major'
      Hinfo Hlevels Huvars Hparams Hindices HfieldType
      Hfield Hmajor Hmajor' Hclosed Hguard IHfield IHmajor IHmajor' =>
    exact .projDF typeName info levels params indexArgs index sourceMajor fieldType
      Gamma fieldLevel major major'
      Hinfo Hlevels Huvars Hparams Hindices HfieldType
      Hfield Hmajor Hmajor' Hclosed Hguard IHfield IHmajor IHmajor'
  | lamDF Htype Hbody IHtype IHbody => exact .lamDF IHtype IHbody
  | forallEDF Htype Hbody IHtype IHbody => exact .forallEDF IHtype IHbody
  | defeqDF Htype Hterm IHtype IHterm => exact .defeqDF IHtype IHterm
  | beta Hbody Harg IHbody IHarg => exact .beta IHbody IHarg
  | eta H IH => exact .eta IH
  | proofIrrel Hprop Hleft Hright IHprop IHleft IHright =>
    exact .proofIrrel IHprop IHleft IHright
  | extra Hdf Hlevels Hlength => exact .extra _ _ Hdf Hlevels Hlength
  | projIota Hinfo Hproj Hindex Hfield IHproj IHfield =>
    exact .projIota Hinfo Hproj Hindex Hfield IHproj IHfield
  | structEta Hinfo Hparams Hindices He Hctor IHe IHctor =>
    exact .structEta Hinfo Hparams Hindices He Hctor IHe IHctor
  | unitLike Hinfo Hparams Hindices HnumFields He He' IHe IHe' =>
    exact .unitLike Hinfo Hparams Hindices HnumFields He He' IHe IHe'

/-- Environment monotonicity preserves the exact constant-dependency
certificate carried by a typing derivation.  This is stronger than
reconstructing `Avoids` in the larger environment: the latter may already
contain newly installed constants which the original derivation never
consulted. -/
theorem IsDefEq.Avoids.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : env.IsDefEq uvars ctx lhs rhs type}
    (HU : H.Avoids changed) :
    (H.mono henv).Avoids changed := by
  induction HU with
  | pat hp hm he hr hchk _ _ ihe ihchk =>
    exact .pat (henv.pats hp) hm (he.mono henv) hr (fun t ht => (hchk t ht).mono henv)
      ihe ihchk
  | bvar Hlookup => exact .bvar Hlookup
  | symm _ IH => exact .symm IH
  | trans _ _ IH₁ IH₂ => exact .trans IH₁ IH₂
  | sortDF Hleft Hright Heq => exact .sortDF Hleft Hright Heq
  | constDF name ci levels levels' Hlookup Hleft Hright Hlength Heq Hname =>
    exact .constDF name ci levels levels' (henv.constants Hlookup)
      Hleft Hright Hlength Heq Hname
  | projDF typeName info levels params indexArgs index sourceMajor fieldType
      Gamma fieldLevel major major'
      Hinfo Hlevels Huvars Hparams Hindices HfieldType
      Hfield Hmajor Hmajor' Hclosed Hguard _ _ _ IHfield IHmajor IHmajor' =>
    exact .projDF typeName info levels params indexArgs index sourceMajor fieldType
      Gamma fieldLevel major major'
      (henv.projections Hinfo) Hlevels Huvars Hparams Hindices HfieldType
      (Hfield.mono henv) (Hmajor.mono henv) (Hmajor'.mono henv)
      Hclosed Hguard IHfield IHmajor IHmajor'
  | appDF _ _ IHfn IHarg => exact .appDF IHfn IHarg
  | lamDF _ _ IHtype IHbody => exact .lamDF IHtype IHbody
  | forallEDF _ _ IHtype IHbody => exact .forallEDF IHtype IHbody
  | defeqDF _ _ IHtype IHterm => exact .defeqDF IHtype IHterm
  | beta _ _ IHbody IHarg => exact .beta IHbody IHarg
  | eta _ IH => exact .eta IH
  | proofIrrel _ _ _ IHprop IHleft IHright =>
    exact .proofIrrel IHprop IHleft IHright
  | extra df levels Hdf Hlevels Hlength =>
    exact .extra df levels (henv.defeqs Hdf) Hlevels Hlength
  | projIota Hinfo Hproj Hindex Hfield _ _ IHproj IHfield =>
    exact .projIota (henv.projections Hinfo) (Hproj.mono henv) Hindex (Hfield.mono henv)
      IHproj IHfield
  | structEta Hinfo Hparams Hindices He Hctor _ _ IHe IHctor =>
    exact .structEta (henv.projections Hinfo) Hparams Hindices (He.mono henv) (Hctor.mono henv)
      IHe IHctor
  | unitLike Hinfo Hparams Hindices HnumFields He He' _ _ IHe IHe' =>
    exact .unitLike (henv.projections Hinfo) Hparams Hindices HnumFields (He.mono henv)
      (He'.mono henv) IHe IHe'

/-- A typehood derivation avoids `changed` when some typing derivation of the type at a sort
does. -/
def IsType.Avoids {env : VEnv} {uvars : Nat} {ctx : List VExpr}
    {type : VExpr} (changed : Name → Prop)
    (_H : env.IsType uvars ctx type) : Prop :=
  ∃ level, ∃ Htype : env.HasType uvars ctx type (.sort level),
    Htype.Avoids changed

theorem IsType.avoids_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : env.IsType uvars ctx type)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.Avoids changed := by
  rcases H with ⟨level, Htype⟩
  exact ⟨level, Htype, Htype.avoids_of_constants Hconstants⟩

/-- `IsType.Avoids` is preserved by environment extension, with the same
dependency set. -/
theorem IsType.Avoids.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : env.IsType uvars ctx type}
    (HU : H.Avoids changed) :
    (H.mono henv).Avoids changed := by
  rcases HU with ⟨level, Htype, Huses⟩
  exact ⟨level, Htype.mono henv, Huses.mono henv⟩

/-- Static environment dependencies of the side condition used by literal
translation. -/
def ContainsLits.Avoids (changed : Name → Prop) : Literal → Prop
  | .natVal _ => ¬ changed ``Nat
  | .strVal _ => ¬ changed ``Char.ofNat ∧ ¬ changed ``String.ofList

theorem ContainsLits.avoids_of_constants
    {env : VEnv} {changed : Name → Prop} {literal : Literal}
    (H : env.ContainsLits literal)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    ContainsLits.Avoids changed literal := by
  cases literal with
  | natVal value =>
    rcases H with ⟨ci, Hlookup⟩
    exact Hconstants Hlookup
  | strVal value =>
    rcases H with ⟨⟨charCi, Hchar⟩, stringCi, Hstring⟩
    exact ⟨Hconstants Hchar, Hconstants Hstring⟩

end VEnv

/-- A finite environment anchor for one verified projection.  Restriction
replay does not need every constant of the ambient source environment: it only
needs an earlier environment in which the same primitive projection was
already well formed and whose constants all avoid `changed`.

The explicit anchor keeps the restriction fact stable when the translation is
subsequently weakened to a larger environment. -/
structure TrExprS.ProjRestrictionSupport
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    {structName : Name} {index : Nat} {major : VExpr}
    (changed : Name → Prop)
    (_H : VExpr.WF env U Gamma (.proj structName index major)) where
  anchor : VEnv
  anchor_le : anchor ≤ env
  projection : VExpr.WF anchor U Gamma (.proj structName index major)
  constants : ∀ {name ci}, anchor.constants name = some ci →
    ¬ changed name

def TrExprS.ProjRestrictionSupport.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : VExpr.WF env U Gamma (.proj structName index major)}
    (S : TrExprS.ProjRestrictionSupport changed H) :
    TrExprS.ProjRestrictionSupport changed (H.mono henv) where
  anchor := S.anchor
  anchor_le := S.anchor_le.trans henv
  projection := S.projection
  constants := S.constants

/-- The semantic premises and constant translations used by one concrete
expression translation derivation. -/
inductive TrExprS.Avoids {env : VEnv} {levelParams : List Name}
    (changed : Name → Prop) :
    ∀ {ctx source target}, TrExprS env levelParams ctx source target → Prop where
  | bvar (ctx : VLCtx) (index : Nat) (target type : VExpr)
      (Hlookup : ctx.find? (.inl index) = some (target, type)) :
      Avoids changed (.bvar Hlookup)
  | fvar (ctx : VLCtx) (fvar : FVarId) (target type : VExpr)
      (Hlookup : ctx.find? (.inr fvar) = some (target, type)) :
      Avoids changed (.fvar Hlookup)
  | sort (level : Level) (targetLevel : VLevel)
      (Hlevel : VLevel.ofLevel levelParams level = some targetLevel) :
      Avoids changed (.sort Hlevel)
  | const
      (name : Name) (ci : VConstant) (levels : List Level)
      (targets : List VLevel)
      (Hlookup : env.constants name = some ci)
      (Hlevels : levels.mapM (VLevel.ofLevel levelParams) = some targets)
      (Hlength : levels.length = ci.uvars)
      (Hname : ¬ changed name) :
      Avoids changed (.const Hlookup Hlevels Hlength)
  | app
      (HfnTypeUses : HfnType.Avoids changed)
      (HargTypeUses : HargType.Avoids changed)
      (HfnUses : Avoids changed Hfn)
      (HargUses : Avoids changed Harg) :
      Avoids changed (.app HfnType HargType Hfn Harg)
  | lam
      (HtypeUses : Htype.Avoids changed)
      (HdomainUses : Avoids changed Hdomain)
      (HbodyUses : Avoids changed Hbody) :
      Avoids changed (.lam Htype Hdomain Hbody)
  | forallE
      (HdomainTypeUses : HdomainType.Avoids changed)
      (HbodyTypeUses : HbodyType.Avoids changed)
      (HdomainUses : Avoids changed Hdomain)
      (HbodyUses : Avoids changed Hbody) :
      Avoids changed (.forallE HdomainType HbodyType Hdomain Hbody)
  | letE
      (HvalueTypeUses : HvalueType.Avoids changed)
      (HtypeUses : Avoids changed Htype)
      (HvalueUses : Avoids changed Hvalue)
      (HbodyUses : Avoids changed Hbody) :
      Avoids changed (.letE HvalueType Htype Hvalue Hbody)
  | lit
      (Hcontains : env.ContainsLits literal)
      (Hliteral : VEnv.ContainsLits.Avoids changed literal)
      (HconstructorUses : Avoids changed Hconstructor) :
      Avoids changed (.lit Hcontains Hconstructor)
  | mdata (Huses : Avoids changed H) :
      Avoids changed (.mdata H)
  | proj (ctx : VLCtx) (source : Expr) (target : VExpr)
      (structName : Name) (index : Nat)
      (H : TrExprS env levelParams ctx source target)
      (Hproj : VExpr.WF env levelParams.length ctx.toCtx (.proj structName index target))
      (Huses : Avoids changed H)
      (HprojUses : TrExprS.ProjRestrictionSupport changed Hproj) :
      Avoids changed (.proj H Hproj)

theorem TrExprS.avoids_of_constants
    {env : VEnv} {changed : Name → Prop}
    (H : TrExprS env levelParams ctx source target)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    H.Avoids changed := by
  induction H with
  | bvar Hlookup => exact .bvar _ _ _ _ Hlookup
  | fvar Hlookup => exact .fvar _ _ _ _ Hlookup
  | sort Hlevel => exact .sort _ _ Hlevel
  | const Hlookup Hlevels Hlength =>
    exact .const _ _ _ _ Hlookup Hlevels Hlength (Hconstants Hlookup)
  | app HfnType HargType Hfn Harg IHfn IHarg =>
    exact .app
      (HfnType.avoids_of_constants Hconstants)
      (HargType.avoids_of_constants Hconstants) IHfn IHarg
  | lam Htype Hdomain Hbody IHdomain IHbody =>
    exact .lam (Htype.avoids_of_constants Hconstants) IHdomain IHbody
  | forallE HdomainType HbodyType Hdomain Hbody IHdomain IHbody =>
    exact .forallE
      (HdomainType.avoids_of_constants Hconstants)
      (HbodyType.avoids_of_constants Hconstants) IHdomain IHbody
  | letE HvalueType Htype Hvalue Hbody IHtype IHvalue IHbody =>
    exact .letE (HvalueType.avoids_of_constants Hconstants)
      IHtype IHvalue IHbody
  | lit Hcontains Hconstructor IH =>
    exact .lit Hcontains (Hcontains.avoids_of_constants Hconstants) IH
  | mdata H IH => exact .mdata IH
  | proj H Hproj IH =>
    exact .proj _ _ _ _ _ H Hproj IH {
      anchor := env
      anchor_le := VEnv.LE.rfl
      projection := Hproj
      constants := Hconstants }

/-- A translated expression retains its proof-relevant dependency
certificate when its derivation is weakened to a larger environment. -/
theorem TrExprS.Avoids.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : TrExprS env levelParams ctx source target}
    (HU : H.Avoids changed) :
    (H.mono henv).Avoids changed := by
  induction HU with
  | bvar ctx index target type Hlookup =>
    exact .bvar ctx index target type Hlookup
  | fvar ctx fvar target type Hlookup =>
    exact .fvar ctx fvar target type Hlookup
  | sort level targetLevel Hlevel => exact .sort level targetLevel Hlevel
  | const name ci levels targets Hlookup Hlevels Hlength Hname =>
    exact .const name ci levels targets (henv.constants Hlookup)
      Hlevels Hlength Hname
  | app HfnTypeUses HargTypeUses HfnUses HargUses IHfn IHarg =>
    exact .app (HfnTypeUses.mono henv) (HargTypeUses.mono henv)
      IHfn IHarg
  | lam HtypeUses HdomainUses HbodyUses IHdomain IHbody =>
    exact .lam (HtypeUses.mono henv) IHdomain IHbody
  | forallE HdomainTypeUses HbodyTypeUses HdomainUses HbodyUses
      IHdomain IHbody =>
    exact .forallE (HdomainTypeUses.mono henv)
      (HbodyTypeUses.mono henv) IHdomain IHbody
  | letE HvalueTypeUses HtypeUses HvalueUses HbodyUses
      IHtype IHvalue IHbody =>
    exact .letE (HvalueTypeUses.mono henv) IHtype IHvalue IHbody
  | lit Hcontains Hliteral HconstructorUses IH =>
    exact .lit (Hcontains.mono henv) Hliteral IH
  | mdata Huses IH => exact .mdata IH
  | proj ctx source target structName index H Hproj Huses
      HprojUses IH =>
    exact .proj ctx source target structName index
      (H.mono henv) (Hproj.mono henv) IH (HprojUses.mono henv)

end Lean4Lean
