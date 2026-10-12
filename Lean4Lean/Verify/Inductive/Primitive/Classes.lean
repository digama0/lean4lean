import Lean4Lean.Verify.Inductive.Primitive.PositivityConstant
import Lean4Lean.Verify.Axioms


namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The classification of a primitive constructor's fields: `Nat.succ`'s single field is
recursive, every other primitive constructor has no field. -/
def primitiveFieldClass (ctor : Constructor) : List Bool :=
  match ctor.type with
  | .forallE .. => [true]
  | _ => []

/-- The classifications of the constructors of a primitive declaration, family by family. -/
def primitiveFieldClasses (indTypes : Array InductiveType) : List (List (List Bool)) :=
  indTypes.toList.map (·.ctors.map primitiveFieldClass)

/-- A constant whose environment entry is an inductive type has no definition to unfold. -/
theorem isDelta_inductInfo {env : Environment} {n : Name} {us : List Level} {v : InductiveVal}
    (h : env.find? n = some (.inductInfo v)) :
    TypeChecker.Inner.isDelta env (.const n us) = none := by
  simp [TypeChecker.Inner.isDelta, Expr.getAppFn, h, ConstantInfo.deltaValue?]

theorem loopCtor_nonForall_nil {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {ctor : Name} {targetIdx : Nat} {t : Expr} {i fuel : Nat} {c : AddInductive.Context}
    {out : List Bool}
    (hforall : ¬ ∃ name dom body bi, t = .forallE name dom body bi)
    (h : AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx t i fuel c =
      .ok out) : out = [] := by
  cases fuel with
  | zero => simp [AddInductive.checkConstructors.loopCtor] at h
  | succ fuel =>
    cases t <;> simp_all [AddInductive.checkConstructors.loopCtor] <;>
      (split at h <;> simp_all [pure, ReaderT.pure, Except.pure])

/-- The single field of `Nat.succ`, literally `Nat`, is classified recursive. -/
theorem loopCtor_validConstField {stats : AddInductive.InductiveStats}
    {ctor : Name} {targetIdx : Nat} {nm : Name} {bi : BinderInfo} {n : Name} {us : List Level}
    {i fuel : Nat} {c : AddInductive.Context} {out : List Bool} {k : Nat}
    (hparamAt : stats.params[i]? = none)
    (hdelta : TypeChecker.Inner.isDelta c.env (.const n us) = none)
    (hocc : AddInductive.hasIndOcc stats.indConsts (.const n us) = true)
    (hvalid : AddInductive.isValidIndApp? stats (.const n us) = some k)
    (h : AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE nm (.const n us) (.const n us) bi) i fuel c = .ok out) : out = [true] := by
  cases fuel with
  | zero => simp [AddInductive.checkConstructors.loopCtor] at h
  | succ fuel =>
  rw [AddInductive.checkConstructors.loopCtor, hparamAt] at h
  simp only [bind, ReaderT.bind, Except.bind] at h
  split at h
  · cases h
  rename_i sort _
  split at h
  · rename_i hcond
    simp only [Bool.not_false, ↓reduceIte, ReaderT.bind] at h
    cases hb : AddInductive.checkPositivity stats (Expr.const n us) ctor i c with
    | error e => rw [hb] at h; cases h
    | ok b =>
    rw [hb] at h
    change AddInductive.withUnannotatedCheckedLocalDecl nm bi (Expr.const n us)
          (fun arg =>
            ReaderT.bind
              (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
                ((Expr.const n us).instantiate1 arg) (i + 1) fuel)
              fun __do_lift => pure (b :: __do_lift)) c = Except.ok out at h
    have hbt := checkPositivity_const_valid hdelta hocc hvalid hb
    subst hbt
    unfold AddInductive.withUnannotatedCheckedLocalDecl AddInductive.withCheckedLocalDecl at h
    simp only [withFreshId, MonadLocalNameGenerator.withFreshId, withReader, MonadWithReader.withReader,
      MonadWithReaderOf.withReader, withTheReader, ReaderT.bind] at h
    revert h
    generalize (AddInductive.Context.mk _ _ _ _ _ _ _ _ _ : AddInductive.Context) = c'
    intro h
    cases hrest : AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
        ((Expr.const n us).instantiate1 (Expr.fvar { name := c.ngen.curr })) (i + 1) fuel c' with
    | error e => rw [hrest] at h; cases h
    | ok rest =>
    rw [hrest] at h
    have hnil := loopCtor_nonForall_nil (by simp [Expr.instantiate1']) hrest
    subst hnil
    change Except.ok (true :: []) = Except.ok out at h
    cases h
    rfl
  · simp [ReaderT.bind, throw, throwThe, MonadExceptOf.throw, Except.bind, liftM, bind] at h

/-- The constructor loop of one family returns the classifications its constructor checks
return. -/
theorem loopCtors_classes {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {targetIdx : Nat} {ctors : List Constructor} {c : AddInductive.Context}
    (f : Constructor → List Bool)
    (hctor : ∀ j (hj : j < ctors.length) out,
      AddInductive.checkConstructors.loopCtor stats isUnsafe ctors[j].name targetIdx
        ctors[j].type 0 c.fuel.inductiveFuel c = .ok out → out = f ctors[j]) :
    ∀ ctorIdx foundCtors out,
      AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx ctors ctorIdx
        foundCtors c = .ok out → out = (ctors.drop ctorIdx).map f := by
  intro ctorIdx foundCtors out h
  by_cases hidx : ctorIdx < ctors.length
  · rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx] at h
    by_cases hdup : foundCtors.contains ctors[ctorIdx].name = true
    · simp [hdup, bind, ReaderT.bind, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte] at h
      simp only [bind, ReaderT.bind, Except.bind] at h
      split at h
      · cases h
      change ((AddInductive.checkConstructors.loopCtor stats isUnsafe ctors[ctorIdx].name
          targetIdx ctors[ctorIdx].type 0 c.fuel.inductiveFuel >>= fun fields => do
            return fields :: (← AddInductive.checkConstructors.loopCtors stats isUnsafe
              targetIdx ctors (ctorIdx + 1) (foundCtors.insert ctors[ctorIdx].name))) :
            AddInductive.M _) c = .ok out at h
      simp only [bind, ReaderT.bind, Except.bind] at h
      cases hfields : AddInductive.checkConstructors.loopCtor stats isUnsafe
          ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0 c.fuel.inductiveFuel c with
      | error e => rw [hfields] at h; cases h
      | ok fields =>
      rw [hfields] at h
      cases hrest : AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx ctors
          (ctorIdx + 1) (foundCtors.insert ctors[ctorIdx].name) c with
      | error e => simp [hrest] at h
      | ok rest =>
      simp [hrest, pure, ReaderT.pure, Except.pure] at h
      subst h
      rw [hctor ctorIdx hidx fields hfields,
        loopCtors_classes f hctor (ctorIdx + 1) _ rest hrest,
        List.drop_eq_getElem_cons hidx]
      rfl
  · rw [AddInductive.checkConstructors.loopCtors, dif_neg hidx] at h
    cases h
    simp [List.drop_of_length_le (Nat.le_of_not_gt hidx)]
termination_by ctorIdx => ctors.length - ctorIdx

/-- The family loop returns, family by family, the classifications its constructor checks
return. -/
theorem loopTypes_classes {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {indTypes : Array InductiveType} {c : AddInductive.Context}
    (f : Constructor → List Bool)
    (hctor : ∀ t (ht : t < indTypes.size) j (hj : j < indTypes[t].ctors.length) out,
      AddInductive.checkConstructors.loopCtor stats isUnsafe indTypes[t].ctors[j].name t
        indTypes[t].ctors[j].type 0 c.fuel.inductiveFuel c = .ok out →
      out = f indTypes[t].ctors[j]) :
    ∀ targetIdx out,
      AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe targetIdx c = .ok out →
      out = (indTypes.toList.drop targetIdx).map (·.ctors.map f) := by
  intro targetIdx out h
  by_cases hidx : targetIdx < indTypes.size
  · rw [AddInductive.checkConstructors.loopTypes, dif_pos hidx] at h
    simp only [bind, ReaderT.bind, Except.bind] at h
    cases hfields : AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        indTypes[targetIdx].ctors 0 {} c with
    | error e => rw [hfields] at h; cases h
    | ok fields =>
    rw [hfields] at h
    cases hrest : AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
        (targetIdx + 1) c with
    | error e => simp [hrest] at h
    | ok rest =>
    simp [hrest, pure, ReaderT.pure, Except.pure] at h
    subst h
    rw [loopCtors_classes f (hctor targetIdx hidx) 0 {} fields hfields,
      loopTypes_classes f hctor (targetIdx + 1) rest hrest]
    have hidx' : targetIdx < indTypes.toList.length := by simpa using hidx
    rw [List.drop_eq_getElem_cons hidx']
    simp
  · rw [AddInductive.checkConstructors.loopTypes, dif_neg hidx] at h
    cases h
    simp; omega
termination_by targetIdx => indTypes.size - targetIdx

/-- `checkConstructors` returns, family by family, the classifications its constructor checks
return. -/
theorem checkConstructors_classes {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {indTypes : Array InductiveType} {c : AddInductive.Context} {out : List (List (List Bool))}
    (f : Constructor → List Bool)
    (hctor : ∀ c' : AddInductive.Context, c'.env = c.env →
      ∀ t (ht : t < indTypes.size) j (hj : j < indTypes[t].ctors.length) out,
      AddInductive.checkConstructors.loopCtor stats isUnsafe indTypes[t].ctors[j].name t
        indTypes[t].ctors[j].type 0 c'.fuel.inductiveFuel c' = .ok out →
      out = f indTypes[t].ctors[j])
    (h : AddInductive.checkConstructors indTypes stats isUnsafe c = .ok out) :
    out = indTypes.toList.map (·.ctors.map f) := by
  unfold AddInductive.checkConstructors at h
  simp only [bind, ReaderT.bind, Except.bind, AddInductive.withCheckLCtx, withReader,
    MonadWithReader.withReader,
    AddInductive.paramCheckLCtx, pure, ReaderT.pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i v _
      simp only [withTheReader, MonadWithReaderOf.withReader] at h
      simpa using loopTypes_classes (c := { c with checkLCtx := v }) f
        (hctor _ rfl) 0 out h

end Lean4Lean.VerifyInductive
