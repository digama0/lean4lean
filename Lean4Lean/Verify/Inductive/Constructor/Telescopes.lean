import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.TypeChecker.GhostTelescope

/-!
# Telescope certificates of checked constructor types

Every constructor type is checked by `AddInductive.checkClosedType`, a `checkType` run in the
empty local context with a fresh state. The ghost telescope theorem (`checkType.WF_telTr`) reads a
telescope certificate off that run; this file carries it through the constructor loops of
`checkConstructors`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A successful closed check of a type certifies its telescope in the empty context. The
environment must be ghost-free: no constant mentions a free variable. -/
theorem checkClosedType.telTrWF (Hc : ContextWF c)
    (henv : TypeChecker.EnvGhostFree (fun _ => True) c.env) :
    (AddInductive.checkClosedType name type c).WF fun _ =>
      ∃ T, TelTrN Hc.venv c.lparams (AddInductive.constructorArity type) [] type T := by
  change (c.env.checkNoMVarNoFVar name type >>= fun _ =>
    (monadLift (TypeChecker.checkType type) : AddInductive.M Expr)
      { c with checkLCtx := {} }).WF _
  have hno : (c.env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := c.env) (name := name) h
  exact hno.bind fun _ hclosed =>
    liftTypeChecker.WF (Hc.withCheckLCtx {} Hc.baseNil)
      (TypeChecker.checkType.WF_telTr henv (by intro k r h; simp at h)
        (hclosed.mono fun _ h => False.elim h) (by simp))

/-- Every constructor checked by one constructor loop has a certified type. -/
theorem checkConstructors.loopCtors.telTrWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {targetIdx : Nat} {ctors : List Constructor}
    (Hc : ContextWF c) (henv : TypeChecker.EnvGhostFree (fun _ => True) c.env) :
    ∀ (ctorIdx : Nat) (foundCtors : NameSet),
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF fun _ =>
        ∀ i, ctorIdx ≤ i → ∀ (h : i < ctors.length),
          ∃ T, TelTrN Hc.venv c.lparams (AddInductive.constructorArity ctors[i].type) [] ctors[i].type T := by
  intro ctorIdx foundCtors
  by_cases hidx : ctorIdx < ctors.length
  · rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
    cases hfresh : foundCtors.contains ctors[ctorIdx].name with
    | true =>
        simp only [↓reduceIte]
        exact Except.WF.throw
    | false =>
        rw [if_neg (by simp)]
        change (AddInductive.checkClosedType ctors[ctorIdx].name
          ctors[ctorIdx].type c >>= fun _ => ((do
            let _ ← readThe AddInductive.Context
            let fields ← AddInductive.checkConstructors.loopCtor stats isUnsafe
              ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
              c.fuel.inductiveFuel
            return fields :: (← AddInductive.checkConstructors.loopCtors stats isUnsafe
              targetIdx ctors (ctorIdx + 1)
              (foundCtors.insert ctors[ctorIdx].name))) :
            AddInductive.M (List (List Bool))) c).WF _
        refine (checkClosedType.telTrWF Hc henv).bind fun _ hT => ?_
        change ((read : AddInductive.M AddInductive.Context) c >>= fun c' =>
          ((AddInductive.checkConstructors.loopCtor stats isUnsafe
              ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
              c'.fuel.inductiveFuel >>= fun fields => do
            return fields :: (← AddInductive.checkConstructors.loopCtors stats isUnsafe
              targetIdx ctors (ctorIdx + 1)
              (foundCtors.insert ctors[ctorIdx].name))) :
            AddInductive.M (List (List Bool))) c).WF _
        have hread : ((read : AddInductive.M AddInductive.Context) c).WF
            (fun c' => c' = c) := by
          intro c' h
          cases h
          rfl
        refine hread.bind fun c' hc' => ?_
        subst c'
        have hloop : (AddInductive.checkConstructors.loopCtor stats isUnsafe
            ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
            c.fuel.inductiveFuel c).WF fun _ => True := fun _ _ => trivial
        refine hloop.bind fun _ _ => ?_
        refine (checkConstructors.loopCtors.telTrWF Hc henv (ctorIdx + 1)
          (foundCtors.insert ctors[ctorIdx].name)).bind fun _ H => ?_
        refine Except.WF.pure fun i hi h => ?_
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · exact hT
        · exact H i hlt h
  · rw [AddInductive.checkConstructors.loopCtors, dif_neg hidx]
    exact Except.WF.pure fun i hi h => absurd (Nat.lt_of_le_of_lt hi h) hidx
termination_by ctorIdx => ctors.length - ctorIdx

/-- Every constructor of the families checked by `checkConstructors.loopTypes` has a certified
type. -/
theorem checkConstructors.loopTypes.telTrWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {indTypes : Array InductiveType}
    (Hc : ContextWF c) (henv : TypeChecker.EnvGhostFree (fun _ => True) c.env) :
    ∀ (targetIdx : Nat),
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe targetIdx c).WF
      fun _ => ∀ i, targetIdx ≤ i → ∀ (h : i < indTypes.size), ∀ ctor ∈ indTypes[i].ctors,
        ∃ T, TelTrN Hc.venv c.lparams (AddInductive.constructorArity ctor.type) [] ctor.type T := by
  intro targetIdx
  by_cases hidx : targetIdx < indTypes.size
  · rw [AddInductive.checkConstructors.loopTypes, dif_pos hidx]
    refine (checkConstructors.loopCtors.telTrWF (ctors := indTypes[targetIdx].ctors)
      (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx) Hc henv 0 {}).bind
      fun _ hhead => ?_
    refine (checkConstructors.loopTypes.telTrWF Hc henv (targetIdx + 1)).bind
      fun _ H => Except.WF.pure fun i hi h ctor hctor => ?_
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hctor
      exact hhead j (Nat.zero_le _) hj
    · exact H i hlt h ctor hctor
  · rw [AddInductive.checkConstructors.loopTypes, dif_neg hidx]
    exact Except.WF.pure fun i hi h => absurd (Nat.lt_of_le_of_lt hi h) hidx
termination_by targetIdx => indTypes.size - targetIdx

/-- A translation in the empty context mentions no free variable at all. -/
theorem _root_.Lean4Lean.TrExprS.envGhostFree {e : Expr} (H : TrExprS venv Us [] e e') :
    TypeChecker.GhostFree (fun _ => True) e :=
  H.fvarsIn.mono fun _ h => absurd h (by simp)

/-- No constant of a well-formed environment mentions a free variable: the unsafe observer
translates every constant type, delta value and recursor rule in the empty context. -/
theorem _root_.Lean4Lean.VEnvs.WF.envGhostFree {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    TypeChecker.EnvGhostFree (fun _ => True) env := by
  intro n ci hfind
  have htr := wf.tr (safety := .unsafe)
  have hvis : DefinitionSafety.unsafe ≤ ci.safety := by cases h : ci.safety <;> decide
  obtain ⟨ci', hci'⟩ := htr.toChecking.find?_iff.1 ⟨ci, hfind, hvis⟩
  obtain ⟨-, -, -, hty⟩ := htr.toChecking.find?_uniq hfind hci'
  refine ⟨hty.envGhostFree, fun v hv => ?_, fun rv hrv r hr => ?_⟩
  · exact (htr.of_value hfind hvis hv).fvarsIn.mono fun _ h => absurd h (by simp)
  · subst hrv
    have hrec := (htr.recursorEnvCoherent.rules (name := n)
      (by rwa [← htr.map_wf.find?'_eq_find?]) hvis).1
    obtain ⟨_, _, _, _, -, hrules⟩ := hrec
    obtain ⟨df, hdf⟩ := hrules r hr
    exact hdf.rhs.envGhostFree

end VerifyInductive
end Lean4Lean
