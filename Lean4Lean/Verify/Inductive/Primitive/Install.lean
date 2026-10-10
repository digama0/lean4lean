import Lean4Lean.Verify.Inductive.Primitive.ConstructorCheck

/-! # The constructor installation of a primitive declaration

The canonical abstract constructors of the primitive `Bool`/`Nat` declarations
(`primitiveCtorVal`), the header translation of the declaration with them, and the checked
constructors (`ConstructorsChecked`) in the header data, from which the shared constructor
installation (`CtorInstall`) builds the recursor phase's input. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem forall₂_refl_of_mem {α : Type _} {R : α → α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, R a a) → List.Forall₂ R l l
  | [], _ => .nil
  | a :: as, h => .cons (h a (.head _)) (forall₂_refl_of_mem fun b hb => h b (.tail _ hb))

/-- The canonical translation of a primitive constructor type: a family constant, or a single
field of the family. -/
def primitiveCtorType : Expr → VExpr
  | .const n _ => .const n []
  | .forallE _ (.const n _) (.const m _) _ => .forallE (.const n []) (.const m [])
  | _ => .sort .zero

/-- The canonical abstract constant of a primitive constructor. -/
def primitiveCtorVal (ctor : Constructor) : VConstVal :=
  { name := ctor.name, uvars := 0, type := primitiveCtorType ctor.type }

/-- The canonical constructor rows of a primitive declaration. -/
def primitiveRows (types : List InductiveType) : List (List VConstVal) :=
  types.map (·.ctors.map primitiveCtorVal)

theorem primitiveRows_names (types : List InductiveType) :
    List.Forall₂ (fun (s : InductiveType) (row : List VConstVal) =>
      s.ctors.map (·.name) = row.map (·.name)) types (primitiveRows types) := by
  induction types with
  | nil => exact .nil
  | cons t ts ih => exact .cons (by simp [primitiveCtorVal]) ih

/-- The header data of a primitive declaration with canonical constructors carries the header
translation of the declaration. -/
theorem HeaderData.primitiveTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : HeaderData c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList isUnsafe)
    (hrows : decl.types.map (·.ctors) = primitiveRows indTypes.toList) :
    TrInductDeclHeaders sourceEnv c.lparams nparams indTypes.toList isUnsafe decl
      H.context.venv := by
  refine ⟨H.uvars, H.nparams, H.isUnsafe, H.typesAdded, ?_⟩
  have hlparams : c.lparams = [] := Hshape.1
  rcases Hshape with ⟨-, -, -, htypes | ⟨binderName, binderInfo, htypes⟩⟩ <;>
  · have Hsrc := H.trSources
    rw [htypes] at Hsrc ⊢
    rcases List.Forall₂.leftSingleton Hsrc with ⟨target, hdeclTypes, Htarget⟩
    rw [hdeclTypes]
    rw [hdeclTypes, htypes] at hrows
    simp only [List.map_cons, List.map_nil, primitiveRows, List.cons.injEq, and_true] at hrows
    have htargetType : target.type = .sort (.succ .zero) :=
      TrExprS.unique Htarget.1.type (TrExprS.sort (by rw [hlparams]; rfl))
    have htargetUvars : target.uvars = 0 := by simpa [hlparams] using Htarget.1.uvars
    have hdeclUvars : decl.uvars = 0 := by rw [H.uvars, hlparams]; rfl
    have htargetLookup : H.context.venv.constants target.name = some target.toVConstant := by
      apply VEnv.addConstVals_get H.typesAdded
      simp [VInductDecl.typeConstants, hdeclTypes]
    have hconst : ∀ (n : Name), n = target.name → ∀ Δ : VLCtx,
        TrExprS H.context.venv c.lparams Δ (.const n []) (.const n []) := by
      intro n hn Δ
      subst hn
      exact .const htargetLookup (by simp) (by simp [htargetUvars])
    refine .cons ⟨Htarget.1, ?_⟩ .nil
    rw [hrows]
    have hname := Htarget.1.name
    refine List.forall₂_map_right_iff.2 (forall₂_refl_of_mem fun ctor hctor => ?_)
    refine ⟨by simp [primitiveCtorVal, hlparams], rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hctor
    rcases hctor with rfl | rfl
    · exact hconst _ hname.symm []
    · first
      | exact hconst _ hname.symm []
      | (have hT := primitiveTargetHasType (decl := decl) hdeclUvars htargetUvars htargetLookup
            htargetType
         refine .forallE ⟨.succ .zero, ?_⟩ ⟨.succ .zero, ?_⟩ (hconst _ hname.symm [])
           (hconst _ hname.symm _)
         · simpa [hname, H.uvars, VLCtx.toCtx] using hT []
         · simpa [hname, H.uvars, VLCtx.toCtx] using hT [.const target.name []])

/-- The canonical data of a primitive declaration with its header data: one family, of type
`Sort 1`, no parameters or indices, whose constructors are the canonical ones. -/
theorem PrimitiveHeaderEnvironment.canonical
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes
      headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList isUnsafe)
    (hrows : decl.types.map (·.ctors) = primitiveRows indTypes.toList) :
    ∃ source target, indTypes.toList = [source] ∧ decl.types = [target] ∧
      target.name = source.name ∧ target.type = .sort (.succ .zero) ∧ target.uvars = 0 ∧
      target.numIndices = 0 ∧ target.resultLevel ≈ .succ .zero ∧
      decl.uvars = 0 ∧ decl.nparams = 0 ∧
      H.context.venv.constants target.name = some target.toVConstant ∧
      target.ctors = source.ctors.map primitiveCtorVal ∧
      ∀ ctor ∈ source.ctors, ctor.type = .const source.name [] ∨
        (source.name = ``Nat ∧ ∃ n bi, ctor.type = .forallE n (.const ``Nat []) (.const ``Nat []) bi) := by
  have hheaderParams := H.headerParams_eq_nil Hshape
  have Hshape' := Hshape
  rcases Hshape with ⟨hlparams, hnparams, -, htypes⟩
  have hdeclUvars : decl.uvars = 0 := by rw [H.uvars, hlparams]; rfl
  have hdeclParams : decl.nparams = 0 := H.nparams.trans hnparams
  have hex : ∃ source, indTypes.toList = [source] ∧ source.type = .sort (.succ .zero) ∧
      ∀ ctor ∈ source.ctors, ctor.type = .const source.name [] ∨
        (source.name = ``Nat ∧ ∃ n bi, ctor.type = .forallE n (.const ``Nat []) (.const ``Nat []) bi) := by
    rcases htypes with h | ⟨n, bi, h⟩
    · refine ⟨_, h, rfl, ?_⟩
      intro ctor hctor
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hctor
      rcases hctor with rfl | rfl <;> exact .inl rfl
    · refine ⟨_, h, rfl, ?_⟩
      intro ctor hctor
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hctor
      rcases hctor with rfl | rfl
      · exact .inl rfl
      · exact .inr ⟨rfl, n, bi, rfl⟩
  obtain ⟨source, hsrc, hsrcType, hctors⟩ := hex
  have Hsrc := H.trSources
  rw [hsrc] at Hsrc
  rcases List.Forall₂.leftSingleton Hsrc with ⟨target, hdeclTypes, Htarget⟩
  rw [hdeclTypes, hsrc] at hrows
  simp only [List.map_cons, List.map_nil, primitiveRows, List.cons.injEq, and_true] at hrows
  have htargetType : target.type = .sort (.succ .zero) :=
    TrExprS.unique Htarget.1.type (by rw [hsrcType]; exact TrExprS.sort (by rw [hlparams]; rfl))
  have htargetUvars : target.uvars = 0 := by simpa [hlparams] using Htarget.1.uvars
  have hsourceWF : sourceEnv.WF := by
    rw [← H.sourceContextVEnv]; exact H.sourceContext.wf
  obtain ⟨hnindices, hresult⟩ := primitiveTarget_metadata hsourceWF hdeclParams htargetType
    (by simpa [hheaderParams] using H.headers.typeShapes target (by simp [hdeclTypes]))
  refine ⟨source, target, hsrc, hdeclTypes, Htarget.1.name, htargetType, htargetUvars, hnindices,
    hresult, hdeclUvars, hdeclParams, ?_, hrows, hctors⟩
  apply VEnv.addConstVals_get H.typesAdded
  simp [VInductDecl.typeConstants, hdeclTypes]

/-- The facts of one canonical primitive constructor in the header environment: its source
translation, formation shape, typing, checked tail and raw shape. -/
theorem primitiveCtorFacts {env : VEnv} {decl : VInductDecl} {target : VInductiveType}
    {source : InductiveType} {ctor : Constructor} {Us : List Name} (hUs : Us = [])
    (hdeclTypes : decl.types = [target]) (hname : target.name = source.name)
    (htargetType : target.type = .sort (.succ .zero)) (htargetUvars : target.uvars = 0)
    (hnindices : target.numIndices = 0) (hresult : target.resultLevel ≈ .succ .zero)
    (hdeclUvars : decl.uvars = 0) (hdeclParams : decl.nparams = 0)
    (hlookup : env.constants target.name = some target.toVConstant)
    (hctor : ctor.type = .const source.name [] ∨
      (source.name = ``Nat ∧ ∃ n bi, ctor.type = .forallE n (.const ``Nat []) (.const ``Nat []) bi)) :
    TrSourceConst env Us ctor.name ctor.type (primitiveCtorVal ctor) ∧
    decl.CtorShape env [] target (primitiveCtorVal ctor) ∧
    env.IsType decl.uvars [] (primitiveCtorVal ctor).type ∧
    ConstructorTailCertificate env decl target [] 0 (primitiveCtorVal ctor).type
      (primitiveFieldClass ctor) ∧
    decl.RawCtorShape target (primitiveCtorVal ctor) := by
  subst hUs
  have hT := primitiveTargetHasType (decl := decl) hdeclUvars htargetUvars hlookup htargetType
  have hconst : ∀ Δ : VLCtx, TrExprS env [] Δ (.const target.name []) (.const target.name []) :=
    fun Δ => .const hlookup (by simp) (by simp [htargetUvars])
  rcases hctor with hty | ⟨hnat, n, bi, hty⟩
  · have hcv : (primitiveCtorVal ctor).type = .const target.name [] := by
      simp [primitiveCtorVal, hty, primitiveCtorType, hname]
    have hclass : primitiveFieldClass ctor = [] := by simp [primitiveFieldClass, hty]
    have hty' : ctor.type = .const target.name [] := by rw [hty, hname]
    refine ⟨⟨by simp [primitiveCtorVal], rfl, ?_, ?_⟩, primitiveResultCtorShape hdeclTypes
      hdeclUvars hdeclParams htargetUvars hnindices hcv hlookup htargetType, ?_, ?_, ?_⟩
    · rw [hcv, hty']; exact hconst []
    · show env.IsType 0 [] _
      rw [hcv]; exact ⟨_, by simpa [hdeclUvars] using hT []⟩
    · rw [hcv]; exact ⟨_, hT []⟩
    · rw [hcv, hclass]
      exact primitiveResultTailCertificate hdeclTypes hdeclUvars hdeclParams htargetUvars
        hnindices hlookup htargetType
    · refine ⟨[], .const target.name [], by rw [hcv]; rfl, by simp [hdeclParams], ?_, ?_⟩
      · exact (primitiveValidIndApp hdeclTypes hdeclUvars hdeclParams hnindices _).raw
      · simp [hdeclUvars, VLevel.params]
  · have htn : target.name = ``Nat := hname.trans hnat
    have hcv : (primitiveCtorVal ctor).type = .forallE .nat .nat := by
      simp [primitiveCtorVal, hty, primitiveCtorType, VExpr.nat]
    have hclass : primitiveFieldClass ctor = [true] := by simp [primitiveFieldClass, hty]
    have hdom : env.HasType decl.uvars [] .nat (.sort (.succ .zero)) := by
      simpa [VExpr.nat, htn] using hT []
    have hbody : env.HasType decl.uvars [.nat] .nat (.sort (.succ .zero)) := by
      simpa [VExpr.nat, htn] using hT [.nat]
    have hforall : env.HasType decl.uvars [] (.forallE .nat .nat)
        (.sort (.imax (.succ .zero) (.succ .zero))) := VEnv.IsDefEq.forallEDF hdom hbody
    refine ⟨⟨by simp [primitiveCtorVal], rfl, ?_, ?_⟩, primitiveNatSuccCtorShape hdeclTypes htn
      hdeclUvars hdeclParams htargetUvars hnindices hresult hcv hlookup htargetType, ?_, ?_, ?_⟩
    · rw [hcv, hty]
      refine .forallE ⟨.succ .zero, ?_⟩ ⟨.succ .zero, ?_⟩ ?_ ?_
      · simpa [hdeclUvars, VLCtx.toCtx] using hdom
      · simpa [hdeclUvars, VLCtx.toCtx] using hbody
      · simpa [VExpr.nat, htn] using hconst []
      · simpa [VExpr.nat, htn] using hconst _
    · show env.IsType 0 [] _
      rw [hcv]; exact ⟨_, by simpa [hdeclUvars] using hforall⟩
    · rw [hcv]; exact ⟨_, hforall⟩
    · rw [hcv, hclass]
      exact primitiveNatSuccTailCertificate hdeclTypes htn hdeclUvars hdeclParams htargetUvars
        hnindices hresult hlookup htargetType
    · refine ⟨[.nat], .nat, by rw [hcv]; rfl, by simp [hdeclParams], ?_, ?_⟩
      · simpa [VExpr.nat, htn, hdeclParams] using
          (primitiveValidIndApp hdeclTypes hdeclUvars hdeclParams hnindices 1).raw
      · simp [hdeclUvars, VLevel.params, VExpr.nat, htn]

/-- The checked constructors of a primitive declaration with canonical constructors, in its
header data: proved directly from the canonical syntax, without running the checker in the
header-only environment. -/
theorem PrimitiveHeaderEnvironment.constructorsChecked
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes
      headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList isUnsafe)
    (hrows : decl.types.map (·.ctors) = primitiveRows indTypes.toList) :
    ConstructorsChecked H.toHeaderData (primitiveFieldClasses indTypes) := by
  have hheaderParams := H.headerParams_eq_nil Hshape
  have hlparams : c.lparams = [] := Hshape.1
  obtain ⟨source, target, hsrc, hdeclTypes, hname, htargetType, htargetUvars, hnindices, hresult,
    hdeclUvars, hdeclParams, hlookup, htctors, hctors⟩ := H.canonical Hshape hrows
  have F : ∀ ctor ∈ source.ctors, _ := fun ctor hctor =>
    primitiveCtorFacts (env := H.context.venv) hlparams hdeclTypes hname htargetType htargetUvars
      hnindices hresult hdeclUvars hdeclParams hlookup (hctors ctor hctor)
  have hmemT : ∀ ctor' ∈ target.ctors, ∃ ctor ∈ source.ctors, ctor' = primitiveCtorVal ctor := by
    intro ctor' h; rw [htctors] at h
    obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.1 h; exact ⟨ctor, hctor, rfl⟩
  have hclasses : primitiveFieldClasses indTypes = [source.ctors.map primitiveFieldClass] := by
    simp [primitiveFieldClasses, hsrc]
  have hsize : indTypes.size = 1 := by
    have := congrArg List.length hsrc; simpa using this
  refine {
    ctorTr := ?_
    parameterShapes := ⟨?_⟩
    shapes := ⟨?_⟩
    rawShapes := ?_
    types := ?_
    classes_length := by rw [hclasses, hsize]; rfl
    tails := ?_
    parameterPrefixes := H.parameterPrefixes Hshape
    constructorTails := H.constructorTails Hshape
    ownerNormalForms := H.ownerNormalForms Hshape }
  · rw [hsrc, hdeclTypes]
    refine .cons ?_ .nil
    rw [htctors]
    exact List.forall₂_map_right_iff.2 (forall₂_refl_of_mem fun ctor hctor => (F ctor hctor).1)
  · intro type htype ctor' hctor'
    rw [hdeclTypes, List.mem_singleton] at htype; subst htype
    refine ⟨[], ctor'.type, by simp [hdeclParams, VExpr.takeForalls], ?_⟩
    show VEnv.IsDefEqCtx _ _ [] _ _
    rw [hheaderParams]; exact .zero
  · intro owned howned
    obtain ⟨type, htype, howned⟩ := List.mem_flatMap.1 howned
    rw [hdeclTypes, List.mem_singleton] at htype; subst htype
    obtain ⟨ctor', hctor', rfl⟩ := List.mem_map.1 howned
    obtain ⟨ctor, hctor, rfl⟩ := hmemT _ hctor'
    rw [hheaderParams]; exact (F ctor hctor).2.1
  · intro type htype ctor' hctor'
    rw [hdeclTypes, List.mem_singleton] at htype; subst htype
    obtain ⟨ctor, hctor, rfl⟩ := hmemT _ hctor'
    exact (F ctor hctor).2.2.2.2
  · intro ctor' hctor'
    obtain ⟨type, htype, hctor'⟩ := List.mem_flatMap.1 hctor'
    rw [hdeclTypes, List.mem_singleton] at htype; subst htype
    obtain ⟨ctor, hctor, rfl⟩ := hmemT _ hctor'
    exact (F ctor hctor).2.2.1
  · intro i hi j hj
    have hi0 : i = 0 := by rw [hdeclTypes] at hi; simpa using hi
    subst hi0
    have hj' : j < source.ctors.length := by
      simp only [hdeclTypes, List.getElem_cons_zero, htctors, List.length_map] at hj; exact hj
    have hctor := List.getElem_mem hj'
    have hget : decl.types[0].ctors[j] = primitiveCtorVal source.ctors[j] := by
      simp [hdeclTypes, htctors]
    have hcls : (primitiveFieldClasses indTypes)[0]![j]! = primitiveFieldClass source.ctors[j] := by
      simp [hclasses, hj']
    have htgt : decl.types[0] = target := by simp [hdeclTypes]
    rw [hget, hcls, htgt]
    obtain ⟨-, -, ⟨u, hu⟩, hcert, -⟩ := F _ hctor
    refine ⟨[], (primitiveCtorVal source.ctors[j]).type, ?_, ⟨_, hu⟩, hcert⟩
    rw [hheaderParams]; exact .zero

/-- The constants of a primitive declaration with canonical constructors are the canonical
`Bool` or `Nat` batch. -/
theorem PrimitiveHeaderEnvironment.primitiveConstants
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes
      headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList isUnsafe)
    (hrows : decl.types.map (·.ctors) = primitiveRows indTypes.toList) :
    decl.typeConstants ++ decl.constructorConstants = primitiveBoolConstants ∨
      decl.typeConstants ++ decl.constructorConstants = primitiveNatConstants := by
  obtain ⟨source, target, hsrc, hdeclTypes, hname, htargetType, htargetUvars, -, -, -, -, -,
    htctors, -⟩ := H.canonical Hshape hrows
  have htarget : target.toVConstVal =
      ({ name := source.name, uvars := 0, type := .sort (.succ .zero) } : VConstVal) := by
    rw [← hname, ← htargetUvars, ← htargetType]
  have hdecl : decl.typeConstants ++ decl.constructorConstants =
      target.toVConstVal :: source.ctors.map primitiveCtorVal := by
    simp [VInductDecl.typeConstants, VInductDecl.constructorConstants, hdeclTypes, htctors]
  rw [hdecl, htarget]
  rcases Hshape with ⟨-, -, -, htypes | ⟨n, bi, htypes⟩⟩ <;> rw [hsrc] at htypes <;>
    cases htypes
  · left; rfl
  · right; rfl

/-- The primitive invariant of the constructor model of a primitive declaration: the batch of
the family and its constructors is complete. -/
theorem PrimitiveHeaderEnvironment.hasPrimitives
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes
      headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList isUnsafe)
    (hrows : decl.types.map (·.ctors) = primitiveRows indTypes.toList) :
    ∀ venv', H.context.venv.addConstVals decl.constructorConstants = some venv' →
      venv'.HasPrimitives := by
  intro venv' h
  have hall := VEnv.addConstVals_append H.typesAdded h
  have hsrc : sourceEnv.HasPrimitives := by
    rw [← H.sourceContextVEnv]; exact H.sourceContext.checking.hasPrimitives
  rcases H.primitiveConstants Hshape hrows with he | he <;> rw [he] at hall
  · exact VEnv.HasPrimitives.addBoolConstants hsrc hall
  · exact VEnv.HasPrimitives.addNatConstants hsrc hall

/-- Literal expansion never mentions the `Bool` family header. -/
theorem primitiveBoolLiteralDisjoint :
    checkPositivityStep.LiteralDisjoint #[.const ``Bool []] := by
  exact (checkPositivityStep.IndConstArray.ofExact (names := [``Bool])
    rfl).literalDisjoint (by
      simp [checkPositivityStep.LiteralConstructorNamesDisjoint,
        checkPositivityStep.literalConstructorNames])

/-- Literal expansion uses `Nat.zero` and `Nat.succ`, not the `Nat` family header. -/
theorem primitiveNatLiteralDisjoint :
    checkPositivityStep.LiteralDisjoint #[.const ``Nat []] := by
  exact (checkPositivityStep.IndConstArray.ofExact (names := [``Nat])
    rfl).literalDisjoint (by
      simp [checkPositivityStep.LiteralConstructorNamesDisjoint,
        checkPositivityStep.literalConstructorNames])

/-- The inductive-constant array of a primitive declaration is literal-disjoint. -/
theorem HeaderData.primitiveLiteralDisjoint
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : HeaderData c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList isUnsafe) :
    checkPositivityStep.LiteralDisjoint stats.indConsts := by
  have hnames : decl.types.map (·.name) = indTypes.toList.map (·.name) := by
    have go : ∀ {sources : List InductiveType} {targets : List VInductiveType},
        List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
          TrSourceConst sourceEnv c.lparams source.name source.type t.toVConstVal ∧
          source.ctors.map (·.name) = t.ctors.map (·.name)) sources targets →
        targets.map (·.name) = sources.map (·.name) := by
      intro s t h
      induction h with
      | nil => rfl
      | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h.1.name
    exact go H.trSources
  have hconsts : (decl.types.map fun type => Expr.const type.name stats.levels).toArray =
      (indTypes.toList.map fun type => Expr.const type.name stats.levels).toArray := by
    simpa [List.map_map, Function.comp_def] using congrArg
      (fun names => (names.map fun name => Expr.const name stats.levels).toArray) hnames
  rcases Hshape with ⟨hlp, -, -, htypes | ⟨_, _, htypes⟩⟩ <;>
  · rw [H.statsWF.consts, hconsts, H.statsWF.levelParams, htypes, hlp]
    first | exact primitiveBoolLiteralDisjoint | exact primitiveNatLiteralDisjoint

end VerifyInductive
end Lean4Lean
