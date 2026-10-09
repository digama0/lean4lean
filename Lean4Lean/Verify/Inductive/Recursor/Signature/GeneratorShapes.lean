import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
/-! Shapes of the generated recursors and iota equations.

The shape records used by the reduction proofs (`VRecursorShape`, `VIotaRuleShape`) follow
from the generator's syntax. The index arity of each constructor is a separate hypothesis,
supplied by formation.
-/

namespace Lean4Lean
namespace InductiveSignature

/-- A generated iota equation is headed by the recursor of its constructor's family. -/
theorem Instance.equation_head {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) :
    (g.equation index).lhs.stripLams.getAppFnArgs.1 =
      .const (g.recursorName s.constructors[index].owner) (VLevel.params g.uvars) := by
  apply Restoration.wrapLams_head_const (r := {})
    (fun _ h => by cases h) ?_ (Restoration.expr_empty (g.equation index).lhs)
  exact VExpr.getAppFnArgs_mkApps_head _ _

/-- A generated recursor installed with its generated type has the shape expected by recursor
reduction (`VRecursorShape`): its last domain is the family applied to the parameters and the
indices, and constructors take the recursor's parameters. -/
theorem Instance.recursor_shape {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) {env : VEnv}
    (hlookup : env.constants (g.recursorName owner) = some (g.recursor owner).toVConstant) :
    Nonempty (VRecursorShape env (g.recursorName owner) g.uvars s.params.length
      s.params.length s.families.size s.constructors.size s.families[owner].indices.length
      s.families[owner].name g.levels) := by
  let extra := s.families.size + s.constructors.size
  let indices := insertBinders (s.families[owner].indices.map (·.instL g.levels)) extra
  let major := g.familyApp owner
    (vars s.params.length (extra + indices.length)) (vars indices.length 0)
  let pre := g.params ++ g.motives ++ g.minors ++ indices
  have hindices : indices.length = s.families[owner].indices.length := by
    simp [indices, insertBinders]
  have hpre : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    simp [pre, Instance.params, Instance.motives, Instance.minors, hindices, Nat.add_assoc]
  refine ⟨{
    ctorParams_length := by simp
    ctorParams_closed := ?_
    type := g.recursorType owner
    const := hlookup
    doms := pre ++ [major]
    result := VExpr.mkApps
      (.bvar (indices.length + 1 + s.constructors.size + (s.families.size - 1 - owner.val)))
      (vars indices.length 1 ++ [.bvar 0])
    type_eq := rfl
    doms_length := by simp [hpre]
    major_eq := ?_ }⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
    simp only [List.mem_range] at hi
    change s.params.length - 1 - i < s.params.length
    omega
  · rw [← hpre]
    simp only [List.getElem?_concat_length]
    congr 1
    simp only [major, Instance.familyApp, InductiveSignature.familyApp,
      vars_eq_bvarRange, Nat.add_zero]
    rw [VExpr.bvarRange_map_liftN _ _ _ (Nat.le_refl _)]
    congr 2 <;> simp [extra, hindices, Nat.add_assoc]

/-- A field domain agreement in the constructor's own telescope, moved into a telescope that
inserts `e` binders between the parameters and the fields. -/
theorem insertBinders_defeq {env : VEnv} (henv : VEnv.WF env) {U n i e : Nat}
    {Ps F Cd X : List VExpr} (hX : X.length = e) (hi : i < F.length)
    (hCd : n + i < Cd.length)
    (hD : env.IsDefEqU U ((F.take i).reverse ++ Ps.reverse) F[i] Cd[n + i])
    (hclosed : (Cd[n + i]).ClosedN (n + i)) :
    env.IsDefEqU U (((insertBinders F e).take i).reverse ++ X ++ Ps.reverse)
      ((insertBinders F e)[i]'(by rw [insertBinders_length]; exact hi))
      ((Cd[n + i]).instOuter
        (((VExpr.bvarRange n n).map fun p => p.liftN (e + i)) ++ VExpr.bvarRange i i)) := by
  have hW := hD.weakN henv.ordered (insertBinders_liftN F X Ps.reverse e hX i (by omega))
  rw [insertBinders_getElem, VExpr.instOuter_insert_bvars _ _ _ _ hclosed]
  exact hW

/-- A generated iota equation has the iota-rule shape (`VIotaRuleShape`), given that the
equation is stored, the recursor is installed with its generated type, the constructor has its
family's number of indices, and the installed constructor type is definitionally the
signature's. -/
theorem Instance.iota_shape {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) {env₀ env : VEnv}
    (henv : VEnv.WF env₀) (hle : env₀ ≤ env) (hconst : ∀ n, env.constants n = env₀.constants n)
    (hdef : env.defeqs (g.equation index))
    (hindices : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length)
    (hlevelsWF : ∀ l ∈ g.levels, l.WF g.uvars)
    (hrec : env₀.constants (g.recursorName s.constructors[index].owner) =
      some (g.recursor s.constructors[index].owner).toVConstant)
    (hctorTy : ∀ ctorUvars ctorDoms ctorBody,
      env₀.constants s.constructors[index].name =
        some ⟨ctorUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ →
      env₀.IsDefEqU s.uvars [] (s.constructorType s.constructors[index])
        (VExpr.wrapForalls ctorDoms ctorBody)) :
    Nonempty (VIotaRuleShape env (g.recursorName s.constructors[index].owner) g.uvars
      s.params.length s.params.length s.families.size s.constructors.size
      s.families[s.constructors[index].owner].indices.length s.constructors[index].name
      g.levels s.constructors[index].fields.length (g.equation index)) := by
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  have hdomains : domains.length = s.params.length + s.families.size + s.constructors.size + nf := by
    simp [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes, nf, Nat.add_assoc]
  refine ⟨{
    defeq := hdef
    uvars := rfl
    doms := domains
    lhsBody := VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
      (vars (s.params.length + extra) nf ++ indices ++ [major])
    rhsBody := VExpr.mkApps (.bvar (nf + s.constructors.size - 1 - index.val))
      (vars nf 0 ++ (recursiveFields ctor).map fun (field, r) => g.recursiveCall ctor field r)
    typeBody := VExpr.mkApps (.bvar (nf + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
      (indices ++ [major])
    lhs_eq := rfl
    rhs_eq := rfl
    type_eq := rfl
    doms_length := hdomains
    indexArgs := indices
    indexArgs_length := by simpa [indices, ctor] using hindices
    lhs_pattern := ?_
    rec_doms := ?_
    ctor_doms := ?_ }⟩
  · simp only [hdomains, vars_eq_bvarRange, major, Instance.constructorApp, Nat.add_zero]
    rw [VExpr.bvarRange_map_liftN _ _ _ (Nat.le_refl _)]
    simp [extra, nf, ctor, Nat.add_assoc]
  · -- the recursor-argument binders are the recursor's own binders
    intro recDoms recBody hc hlen j hj
    rw [hconst, hrec] at hc
    have htype := congrArg VConstant.type (Option.some.inj hc)
    simp only [Instance.recursor, Instance.recursorType] at htype
    obtain ⟨rfl, -⟩ := VExpr.wrapForalls_inj_of_length (by
      rw [hlen]
      simp [Instance.params, Instance.motives, Instance.minors, insertBinders,
        Nat.add_assoc]) htype
    have hj' : j < (g.params ++ g.motives ++ g.minors).length := by
      simp [Instance.params, Instance.motives, Instance.minors]; omega
    rw [List.getElem?_append_left (l₁ := g.params ++ g.motives ++ g.minors) hj',
      List.getElem?_append_left (l₁ := g.params ++ g.motives ++ g.minors ++ _)
        (by simp only [List.length_append] at hj' ⊢; omega),
      List.getElem?_append_left (l₁ := g.params ++ g.motives ++ g.minors) hj']
  · -- the field binders agree with the constructor's field domains
    intro ctorUvars ctorDoms ctorBody hc hlen i hi hd hcd
    rw [hconst] at hc
    refine VEnv.IsDefEqU.mono hle ?_
    have hplen : g.params.length = s.params.length := by simp [Instance.params]
    have hmolen : g.motives.length = s.families.size := by simp [Instance.motives]
    have hmilen : g.minors.length = s.constructors.size := by simp [Instance.minors]
    have hFlen : ((s.fieldTypes ctor).map (·.instL g.levels)).length =
        s.constructors[index].fields.length := by
      simp [fieldTypes, ctor]
    have hFlen' : (s.fieldTypes ctor).length = s.constructors[index].fields.length := by
      simp [fieldTypes, ctor]
    -- the constructor's type, at the generated levels
    have hT := (hctorTy ctorUvars ctorDoms ctorBody hc).instL hlevelsWF
    simp only [List.map_nil, InductiveSignature.constructorType, VExpr.instL_wrapForalls,
      List.map_append] at hT
    have hD := VEnv.IsDefEqU.wrapForalls_doms henv (Γ := []) trivial
      (by simp [fieldTypes, hlen]) hT (s.params.length + i)
      (by simp [fieldTypes]; omega) (by simp; omega)
    have hctx : ((s.params.map (·.instL g.levels) ++ (s.fieldTypes ctor).map (·.instL g.levels)).take
          (s.params.length + i)).reverse ++ [] =
        (((s.fieldTypes ctor).map (·.instL g.levels)).take i).reverse ++
          (s.params.map (·.instL g.levels)).reverse := by
      rw [List.append_nil, List.take_append, List.take_of_length_le (by simp),
        List.length_map, Nat.add_sub_cancel_left, List.reverse_append]
    have hdom : (s.params.map (·.instL g.levels) ++ (s.fieldTypes ctor).map (·.instL g.levels))[
          s.params.length + i]'(by simp; omega) =
        ((s.fieldTypes ctor).map (·.instL g.levels))[i]'(by omega) := by
      rw [List.getElem_append_right (by simp)]
      simp
    rw [hctx, hdom] at hD
    have hclosed := (VEnv.VEnv.constant_doms_closed henv hc hlevelsWF).1 (s.params.length + i)
      (by simp; omega)
    have H := insertBinders_defeq henv (Ps := s.params.map (·.instL g.levels))
      (X := g.minors.reverse ++ g.motives.reverse) (e := extra) (n := s.params.length)
      (by simp [hmolen, hmilen, extra, Nat.add_comm]) (by omega) (by simp; omega) hD hclosed
    have hctxR : (domains.take (s.params.length + s.families.size + s.constructors.size + i)).reverse =
        ((insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra).take i).reverse ++
          (g.minors.reverse ++ g.motives.reverse) ++ (s.params.map (·.instL g.levels)).reverse := by
      have hsub : s.params.length + s.families.size + s.constructors.size + i -
          (g.params ++ g.motives ++ g.minors).length = i := by
        simp only [List.length_append, hplen, hmolen, hmilen]; omega
      simp only [domains]
      rw [List.take_append, List.take_of_length_le (by simp [hplen, hmolen, hmilen]; omega), hsub]
      simp [List.reverse_append, List.append_assoc, Instance.params]
    have hdomR : domains[s.params.length + s.families.size + s.constructors.size + i]'hd =
        (insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra)[i]'(by
          rw [insertBinders_length]; omega) := by
      simp only [domains]
      rw [List.getElem_append_right (by simp [hplen, hmolen, hmilen]; omega)]
      congr 1
      simp only [List.length_append, hplen, hmolen, hmilen]; omega
    rw [hctxR, hdomR]
    simpa [List.getElem_map, extra] using H
