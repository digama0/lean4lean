import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Environment.Blocks
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.RecursiveShapeCorrespondence
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! # The recursor shapes of an ordinary block

The recursor and constructor telescopes (`RecursorShapes`, wave 1A) of the recursors installed
by a recursor check: the recursor type is the generator's `Instance.recursorType`, literally a
recursor telescope over its major family; each rule fires on a source constructor of the major
family, whose raw shape (`RawCtorShape`) is the constructor telescope. Recorded in the installed
block's descriptor (`InstalledBlock.WF.shapes`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace InductiveSignature

theorem bvarRange_liftN (n k : Nat) :
    (VExpr.bvarRange n n).map (VExpr.liftN k) = VExpr.bvarRange n (n + k) := by
  unfold VExpr.bvarRange
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp at h1
  simp [VExpr.liftN, liftVar]
  omega

theorem bvarRange_closedN (n : Nat) : ∀ p ∈ VExpr.bvarRange n n, p.ClosedN n := by
  intro p hp
  simp only [VExpr.bvarRange, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  simp [VExpr.ClosedN]; omega

theorem insertBinders_length (l : List VExpr) (k : Nat) : (insertBinders l k).length = l.length := by
  simp [insertBinders]

/-- The generated recursor type is a recursor telescope over its major family. -/
theorem Instance.recursorType_shape {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    ∃ doms result, g.recursorType owner = VExpr.wrapForalls doms result ∧
      doms.length = s.params.length + s.families.size + s.constructors.size +
        s.families[owner].indices.length + 1 ∧
      doms[s.params.length + s.families.size + s.constructors.size +
        s.families[owner].indices.length]? =
        some (VExpr.mkApps (.const s.families[owner].name g.levels)
          (((VExpr.bvarRange s.params.length s.params.length).map fun p =>
              p.liftN (s.families.size + s.constructors.size +
                s.families[owner].indices.length)) ++
            VExpr.bvarRange s.families[owner].indices.length s.families[owner].indices.length)) := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp [Instance.params, Instance.motives, Instance.minors, insertBinders_length]
    omega
  · have hp : g.params.length = s.params.length := by simp [Instance.params]
    have hm : g.motives.length = s.families.size := by simp [Instance.motives]
    have hn : g.minors.length = s.constructors.size := by simp [Instance.minors]
    have hi : (insertBinders (s.families[owner].indices.map (·.instL g.levels))
        (s.families.size + s.constructors.size)).length = s.families[owner].indices.length := by
      simp [insertBinders_length]
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp only [hp, hm, hn, hi]
    rw [show s.params.length + s.families.size + s.constructors.size +
        s.families[owner].indices.length - s.params.length - s.families.size -
        s.constructors.size - s.families[owner].indices.length = 0 by omega]
    simp only [List.getElem?_cons_zero, Option.some.injEq]
    simp only [Instance.familyApp, InductiveSignature.familyApp, vars_eq_bvarRange,
      bvarRange_liftN]
    rw [Nat.zero_add]
    congr 3; omega

end InductiveSignature

/-- A raw constructor shape is a constructor telescope: parameters and fields ending in the
family at the universe parameters, applied to the parameter variables and the indices. -/
theorem VInductDecl.RawCtorShape.toShape {decl : VInductDecl} {type : VInductiveType}
    {ctor : VConstVal} (H : decl.RawCtorShape type ctor) (htype : type ∈ decl.types)
    (hnodup : (decl.types.map (·.name)).Nodup) :
    ∃ doms indices, ctor.type = VExpr.wrapForalls doms
        (VExpr.mkApps (.const type.name (VLevel.params decl.uvars))
          (VExpr.bvarRange decl.nparams (decl.nparams + (doms.length - decl.nparams)) ++
            indices)) ∧
      decl.nparams ≤ doms.length ∧ indices.length = type.numIndices := by
  obtain ⟨doms, result, hty, hle, hraw, hhead⟩ := H
  have hres := VExpr.mkApps_getAppFnArgs result
  rcases hgf : result.getAppFnArgs with ⟨fn, args⟩
  rw [hgf] at hres hhead
  simp only [VInductDecl.RawIndAppAt, hgf] at hraw
  obtain ⟨type', htype', htgt, levels, hfn, -, hlen, htake⟩ := hraw
  have hname : type'.name = type.name := by
    rcases htgt with h | h
    · cases h
    · exact (Option.some.inj h).symm
  have heq : type' = type := List.eq_of_mem_of_nodup_map hnodup htype' htype hname
  subst heq
  refine ⟨doms, args.drop decl.nparams, ?_, hle, by simp [hlen]⟩
  rw [hty, ← hres, show fn = .const type'.name (VLevel.params decl.uvars) from hhead]
  congr 2
  conv => lhs; rw [← List.take_append_drop decl.nparams args]
  rw [htake, VInductDecl.paramVars, show ((List.range decl.nparams).reverse.map fun i =>
      VExpr.bvar (doms.length - decl.nparams + i)) =
      InductiveSignature.vars decl.nparams (doms.length - decl.nparams) from rfl,
    InductiveSignature.vars_eq_bvarRange, Nat.add_comm]

namespace VerifyInductive

theorem VExpr.piArity_mkApps_const (n : Name) (ls : List VLevel) :
    ∀ (args : List VExpr) (f : VExpr), (f = .const n ls ∨ ∃ a b, f = .app a b) →
      (VExpr.mkApps f args).piArity = 0
  | [], f, h => by
    rcases h with rfl | ⟨a, b, rfl⟩ <;> rfl
  | a :: as, f, _ => VExpr.piArity_mkApps_const n ls as (.app f a) (.inr ⟨_, _, rfl⟩)

theorem VExpr.piArity_wrapForalls_mkApps_const (doms args : List VExpr) (n : Name)
    (ls : List VLevel) :
    (VExpr.wrapForalls doms (VExpr.mkApps (.const n ls) args)).piArity = doms.length := by
  induction doms with
  | nil => exact VExpr.piArity_mkApps_const n ls args _ (.inl rfl)
  | cons d ds ih => simp [VExpr.wrapForalls, VExpr.piArity] at ih ⊢; exact ih

/-- The recursor shapes of the generated recursors, from the facts a recursor check records:
the generator (`g`, modelling the declaration), the recursor constants in the recursor-stage
model `envR`, the kernel recursors' translations (`TrRecursor`, read for the names and the rule
data) and metadata, the rule coverage, the rules' constructor shapes, the source constructors'
raw shapes, and the parameter count of the constructor infos the rules fire on. -/
theorem recursorShapesOf {decl : VInductDecl} {s : InductiveSignature} (g : InductiveSignature.Instance s)
    {safety : DefinitionSafety} {sourceEnv envT envC envA envR : VEnv} {C : ConstMap}
    {rvals : List RecursorVal} {recs : List VRecursor}
    (models : s.Models sourceEnv decl) (hlevels : g.levels.length = s.uvars)
    (typesAdded : sourceEnv.addConstVals decl.typeConstants = some envT)
    (ctorsAdded : envT.addConstVals decl.constructorConstants = some envC)
    (hnames : decl.sourceNames.Nodup)
    (rawShapes : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor)
    (hleC : envC ≤ envR)
    (recsFind : ∀ r ∈ recs, envR.constants r.name = some r.toVConstVal.toVConstant)
    (recursors_eq : recs.map (·.toVConstVal) = g.recursors)
    (trRecs : List.Forall₂ (TrRecursor safety envA envR C) rvals recs)
    (metadata : List.Forall₂ (fun (owner : Fin s.families.size) rval =>
      InductiveSignature.RecursorMetadata g envR owner rval) (List.finRange s.families.size) rvals)
    (coverage : List.Forall₂ (fun (owner : Fin s.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule g envR rval.levelParams)
        (s.ownedConstructors owner) rval.rules) (List.finRange s.families.size) rvals)
    (rules_ctor : ∀ r ∈ recs, ∀ ru ∈ r.rules,
      ∃ ci, envC.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields))
    (hnp : ∀ {n cval}, C.find? n = some (.ctorInfo cval) →
      (∃ src ∈ decl.constructorConstants, src.name = n) → cval.numParams = decl.nparams) :
    ∀ rval ∈ rvals, RecursorShapesAt C envR rval := by
  intro rval hrval
  obtain ⟨i, hiR, rfl⟩ := List.getElem_of_mem hrval
  have hlenR : rvals.length = recs.length := List.Forall₂.length_eq trRecs
  have hlenF : (List.finRange s.families.size).length = rvals.length :=
    List.Forall₂.length_eq metadata
  have hi : i < recs.length := hlenR ▸ hiR
  have hiF : i < (List.finRange s.families.size).length := hlenF ▸ hiR
  have htr := Lean4Lean.List.Forall₂.getElem_of trRecs i hiR hi
  have hmeta := Lean4Lean.List.Forall₂.getElem_of metadata i hiF hiR
  have hrules := Lean4Lean.List.Forall₂.getElem_of coverage i hiF hiR
  generalize howner : (List.finRange s.families.size)[i] = owner at hmeta hrules
  have hrec : recs[i].toVConstVal = g.recursor owner := by
    have h := congrArg (fun l => l[i]?) recursors_eq
    simp only [InductiveSignature.Instance.recursors, List.getElem?_map,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiF, Option.map_some,
      Option.some.injEq, howner] at h
    exact h
  -- the recursor constant
  have hconst : envR.constants rvals[i].name =
      some ⟨rvals[i].levelParams.length, g.recursorType owner⟩ := by
    have h := recsFind recs[i] (List.getElem_mem hi)
    have hname : (ConstantInfo.recInfo rvals[i]).name = recs[i].toVConstVal.name :=
      htr.tr.2
    rw [hrec] at hname h
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    rw [hname]
    rw [h]
    simp [InductiveSignature.Instance.recursor, VConstVal.toVConstant, hmeta.uvars]
  obtain ⟨doms, result, htype, hdomslen, hmajor⟩ := g.recursorType_shape owner
  refine ⟨⟨s.params.length, g.levels,
    VExpr.bvarRange s.params.length s.params.length, ⟨{
      ctorParams_length := by simp
      ctorParams_closed := by rw [hmeta.numParams]; exact InductiveSignature.bvarRange_closedN _
      type := g.recursorType owner
      const := hconst
      doms := doms
      result := result
      type_eq := htype
      doms_length := by
        rw [hmeta.numParams, hmeta.numMotives, hmeta.numMinors, hmeta.numIndices]; exact hdomslen
      major_eq := by
        rw [hmeta.numParams, hmeta.numMotives, hmeta.numMinors, hmeta.numIndices, hmeta.major]
        exact hmajor }⟩, ?_⟩, ?_⟩
  · intro rule hrule
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrule
    have hj' : j < recs[i].rules.length := List.Forall₂.length_eq htr.rules ▸ hj
    have hjO : j < (s.ownedConstructors owner).length :=
      (List.Forall₂.length_eq hrules).symm ▸ hj
    have hrr := Lean4Lean.List.Forall₂.getElem_of hrules j hjO hj
    have hru := Lean4Lean.List.Forall₂.getElem_of htr.rules j hj hj'
    generalize hindex : (s.ownedConstructors owner)[j] = index at hrr
    have howner' : s.constructors[index].owner = owner := by
      have hmem := List.getElem_mem (l := s.ownedConstructors owner) hjO
      rw [hindex] at hmem
      simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
      exact hmem.2
    obtain ⟨source, hsource, hfname, -, hfidx, -, hfctors⟩ := models.family owner
    have htypesNodup : (decl.types.map (·.name)).Nodup := by
      have := (List.nodup_append.mp hnames).1
      simpa [VInductDecl.typeConstants, List.map_map, Function.comp_def] using this
    obtain ⟨src, hsrc, hsname, hsuv, -⟩ := models.constructorInFamily hnames index
      typesAdded hsource (by rw [howner']; exact hfctors)
    obtain ⟨cdoms, indices, hctype, hle, hidx⟩ :=
      (rawShapes source hsource src hsrc).toShape hsource htypesNodup
    have stC : decl.addCtors envT = some envC := by
      rw [VInductDecl.addCtors_eq_addConstVals]; exact ctorsAdded
    have hsrcC : envC.constants src.name = some src.toVConstant :=
      VEnv.addCtors_find stC source hsource src hsrc
    have hrulector : rvals[i].rules[j].ctor = src.name := hrr.ctor.trans hsname
    have hsrcMem : ∃ s' ∈ decl.constructorConstants, s'.name = rvals[i].rules[j].ctor :=
      ⟨src, List.mem_flatMap.2 ⟨source, hsource, hsrc⟩, hrulector.symm⟩
    obtain ⟨hctor, hnfields, ⟨cval, hcval, hcparams⟩, -⟩ := hru
    have hcvalNp := hnp hcval hsrcMem
    obtain ⟨ci, hci, hshape⟩ := rules_ctor _ (List.getElem_mem hi) _ (List.getElem_mem hj')
    rw [hctor, hrulector, hsrcC] at hci
    cases hci
    have harity := hshape.1
    rw [hctype, VExpr.piArity_wrapForalls_mkApps_const, hcparams, hcvalNp, hnfields] at harity
    have hnp' : decl.nparams = s.params.length := models.nparams.symm
    have huv : g.levels.length = decl.uvars :=
      hlevels.trans models.uvars
    refine ⟨g.levels.length, rfl, ⟨{
      type := src.type
      const := by
        rw [hrulector, hleC.constants hsrcC, huv, ← hsuv.symm.trans models.uvars]
      doms := cdoms
      indices := indices
      type_eq := by
        rw [hctype, huv, hmeta.major, hfname, ← hnp']
        congr 4
        omega
      doms_length := by rw [← hnp']; omega
      indices_length := by rw [hidx, hmeta.numIndices, hfidx] }⟩, ?_⟩
    intro cval' hcval'
    rw [hnp hcval' hsrcMem, hnp']
  · intro rule hrule
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrule
    have hj' : j < recs[i].rules.length := List.Forall₂.length_eq htr.rules ▸ hj
    obtain ⟨-, -, ⟨cval, hcval, -⟩, -⟩ := Lean4Lean.List.Forall₂.getElem_of htr.rules j hj hj'
    exact ⟨cval, hcval⟩


end VerifyInductive

end Lean4Lean
