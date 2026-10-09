import Lean4Lean.Theory.Inductive.Compilation

/-! Syntactic consequences of finite compilation (`CompilationData`, `CompiledInductive`): no
generated equation has a bare sort on its left, and every equation is headed by a recursor of
the same compilation.

These results use the generated equation syntax, independently of typing
inversion or the consistency of the ambient environment.
-/

namespace Lean4Lean
namespace VExpr

theorem getAppFnArgs_mkApps_head (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    change (mkApps (.app fn arg) args).getAppFnArgs.1 = _
    rw [ih, getAppFnArgs_app]

theorem stripLams_of_head_const {e : VExpr}
    (h : e.getAppFnArgs.1 = .const name levels) : e.stripLams = e := by
  cases e <;> first | rfl | cases h

end VExpr
namespace InductiveSignature

/-- Every generated equation binds at least its own constructor's minor. -/
theorem Instance.equation_lhs_lam {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) :
    ∃ domain body, (g.equation index).lhs = .lam domain body := by
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
      (s.families.size + s.constructors.size)
  have hlength : g.minors.length = s.constructors.size := by simp [Instance.minors]
  have hnonempty : domains ≠ [] := by
    intro hempty
    have hzero := congrArg List.length hempty
    simp only [domains, List.length_append, List.length_nil] at hzero
    have := index.isLt
    omega
  unfold Instance.equation
  change ∃ domain body, VExpr.wrapLams domains _ = .lam domain body
  cases hd : domains with
  | nil => exact (hnonempty hd).elim
  | cons domain domains => exact ⟨domain, _, rfl⟩

/-- Successful restoration preserves an outer lambda. -/
theorem Restoration.expr_lam {r : Restoration} {domain body restored : VExpr}
    (H : r.expr (.lam domain body) = some restored) :
    ∃ domain' body', restored = .lam domain' body' := by
  cases hdomain : Restoration.expr.go r domain [] with
  | none => simp [Restoration.expr, Restoration.expr.go, hdomain] at H
  | some domain' =>
    cases hbody : Restoration.expr.go r body [] with
    | none => simp [Restoration.expr, Restoration.expr.go, hdomain, hbody] at H
    | some body' =>
      simp [Restoration.expr, Restoration.expr.go, hdomain, hbody, VExpr.mkApps] at H
      exact ⟨domain', body', H.symm⟩

/-- A restored generated equation cannot have a bare sort on its left. -/
theorem Instance.restored_equation_lhs_ne_sort {s : InductiveSignature}
    (g : Instance s) (index : Fin s.constructors.size) (r : Restoration)
    {equation : VDefEq} (H : r.equation (g.equation index) = some equation)
    (u : VLevel) : equation.lhs ≠ .sort u := by
  rcases g.equation_lhs_lam index with ⟨domain, body, hlhs⟩
  cases hleft : r.expr (g.equation index).lhs with
  | none => simp [Restoration.equation, hleft] at H
  | some lhs =>
    cases hright : r.expr (g.equation index).rhs with
    | none => simp [Restoration.equation, hleft, hright] at H
    | some rhs =>
      cases htype : r.expr (g.equation index).type with
      | none => simp [Restoration.equation, hleft, hright, htype] at H
      | some type =>
        simp [Restoration.equation, hleft, hright, htype] at H
        cases H
        rw [hlhs] at hleft
        rcases Restoration.expr_lam hleft with ⟨domain', body', rfl⟩
        intro hsort
        cases hsort

/-- Every equation admitted by the finite data retains the generator's
non-sort left-hand side, regardless of the specialization table. -/
theorem CompilationData.equation_lhs_ne_sort
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (H : CompilationData env source expanded s g auxiliaries block) :
    ∀ equation ∈ block.rules, ∀ u, equation.lhs ≠ .sort u := by
  have hrelation := Lean4Lean.List.Forall₂.and_mem (List.mapM_eq_some.mp H.equations)
  suffices h : ∀ {left right},
      List.Forall₂ (fun generated restored =>
        (compilationRestoration source auxiliaries).equation generated = some restored ∧
        generated ∈ g.equations) left right →
      ∀ equation ∈ right, ∀ u, equation.lhs ≠ .sort u from
    h (Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1⟩) hrelation)
  intro left right h
  induction h with
  | nil => simp
  | @cons generated restored left right hhead htail ih =>
    intro equation hmem u
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rcases List.mem_map.mp hhead.2 with ⟨index, _, rfl⟩
      exact g.restored_equation_lhs_ne_sort index _ hhead.1 u
    · exact ih equation hmem u


theorem Restoration.go_head_const {r : Restoration} {e output : VExpr}
    {args : List VExpr} {name : Name} {levels : List VLevel}
    (hname : ∀ head ∈ r.heads, head.auxiliary ≠ name)
    (hhead : e.getAppFnArgs.1 = .const name levels)
    (hgo : Restoration.expr.go r e args = some output) :
    output.getAppFnArgs.1 = .const (r.recursorName name) levels := by
  induction e generalizing args with
  | app fn arg ihfn iharg =>
    have hf : fn.getAppFnArgs.1 = .const name levels := by simpa using hhead
    cases ha : Restoration.expr.go r arg [] with
    | none => simp [Restoration.expr.go, ha] at hgo
    | some arg' =>
      simp [Restoration.expr.go, ha] at hgo
      exact ihfn hf hgo
  | const n ls =>
    have heq : n = name ∧ ls = levels := by simpa using hhead
    rcases heq with ⟨hn, hls⟩
    subst n
    subst ls
    have hn : r.heads.find? (fun h => h.auxiliary == name) = none := by
      apply List.find?_eq_none.mpr
      intro head hmem
      simpa using hname head hmem
    simp [Restoration.expr.go, hn] at hgo
    cases hgo
    exact VExpr.getAppFnArgs_mkApps_head _ _
  | bvar | sort | elim | lam | forallE | proj => cases hhead

theorem Restoration.wrapLams_head_const {r : Restoration} {e output : VExpr}
    {domains : List VExpr} {name : Name} {levels : List VLevel}
    (hname : ∀ head ∈ r.heads, head.auxiliary ≠ name)
    (hhead : e.getAppFnArgs.1 = .const name levels)
    (hgo : r.expr (VExpr.wrapLams domains e) = some output) :
    output.stripLams.getAppFnArgs.1 = .const (r.recursorName name) levels := by
  induction domains generalizing output with
  | nil =>
    have h := Restoration.go_head_const hname hhead hgo
    rw [VExpr.stripLams_of_head_const h]
    exact h
  | cons dom domains ih =>
    change (do
      let domain' ← Restoration.expr.go r dom []
      let body' ← Restoration.expr.go r (VExpr.wrapLams domains e) []
      pure (.lam domain' body')) = some output at hgo
    cases hd : Restoration.expr.go r dom [] with
    | none => simp [hd] at hgo
    | some dom' =>
      cases hb : Restoration.expr.go r (VExpr.wrapLams domains e) [] with
      | none => simp [hd, hb] at hgo
      | some body =>
        have hout : output = .lam dom' body := by simpa [hd, hb] using hgo.symm
        rw [hout]
        simpa only [VExpr.stripLams] using ih (output := body) hb

def familyNames (types : List VInductiveType) : List Name :=
  types.flatMap fun type => type.name :: type.ctors.map (·.name)

theorem familyNames_eq_of_forall₂ {left right : List VInductiveType}
    (H : List.Forall₂ (fun left right => left.name = right.name ∧
      left.ctors.map (·.name) = right.ctors.map (·.name)) left right) :
    familyNames left = familyNames right := by
  induction H with
  | nil => rfl
  | @cons a b left right h _ ih =>
    change (a.name :: a.ctors.map (·.name)) ++ familyNames left =
      (b.name :: b.ctors.map (·.name)) ++ familyNames right
    rw [h.1, h.2, ih]

theorem ctorNames_eq_of_forall₂ {left right : List VConstVal}
    {R : VConstVal → VConstVal → Prop}
    (H : List.Forall₂ R left right)
    (hname : ∀ left right, R left right → left.name = right.name) :
    left.map (·.name) = right.map (·.name) := by
  induction H with
  | nil => rfl
  | cons h _ ih => simp [hname _ _ h, ih]

theorem ContainerSpecialization.directFamily_heads
    {a : ContainerSpecialization} {uvars : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.specializedFamily uvars params = some direct) :
    (a.heads uvars params.length).map (·.auxiliary) =
      direct.name :: direct.ctors.map (·.name) := by
  unfold ContainerSpecialization.specializedFamily at H
  cases htype : specializeType (a.source.type.instL a.levels) a.arguments with
  | none => simp [htype] at H
  | some type =>
    simp [htype] at H
    rcases H with ⟨ctors, hctors, H⟩
    cases H
    have hnames : ctors.map (·.name) = a.source.ctors.map (a.constructorName) := by
      have hrelation := List.mapM_eq_some.mp hctors
      have hrelation' := Lean4Lean.List.Forall₂.imp
        (S := fun original restored : VConstVal =>
          a.constructorName original = restored.name) (fun original restored h => ?_) hrelation
      · have hmap : (a.source.ctors.map fun original => a.constructorName original) =
            ctors.map (·.name) := by
          clear hctors hrelation
          generalize a.source.ctors = originals at hrelation' ⊢
          induction hrelation' with
          | nil => rfl
          | cons h _ ih => simp [h, ih]
        exact hmap.symm
      · cases hspec : specializeType (original.type.instL a.levels) a.arguments with
        | none => simp [hspec] at h
        | some type =>
          simp [hspec] at h
          cases h
          rfl
    simp [ContainerSpecialization.heads, hnames]
theorem CompilationData.heads_not_recursors
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (H : CompilationData env source expanded s g auxiliaries block)
    (owner : Fin s.families.size) :
    ∀ head ∈ (compilationRestoration source auxiliaries).heads,
      head.auxiliary ≠ g.recursorName owner := by
  rcases H.correspondence with ⟨envTypes, direct, htypes, hdirect, hargs, hfamilies⟩
  have hparams : s.params.length = source.nparams := H.model.nparams.trans H.nparams
  have hsourceNames : familyNames s.declaration.types = familyNames (source.types ++ direct) :=
    familyNames_eq_of_forall₂ (Lean4Lean.List.Forall₂.imp (fun left right h =>
      ⟨h.name, ctorNames_eq_of_forall₂ h.constructors (fun _ _ h => h.1)⟩) hfamilies)
  have hexpandedNames : familyNames s.declaration.types = familyNames expanded.types :=
    familyNames_eq_of_forall₂ (Lean4Lean.List.Forall₂.imp (fun left right h =>
      ⟨h.1, h.2.2.2.2⟩) H.model.families)
  have hheadNames :
      ((compilationRestoration source auxiliaries).heads.map (·.auxiliary)) =
        familyNames direct := by
    have hrelation := List.mapM_eq_some.mp hdirect
    change (auxiliaries.flatMap (fun a => a.heads source.uvars source.nparams)).map
      (·.auxiliary) = familyNames direct
    clear hfamilies hsourceNames hexpandedNames hargs hdirect H
    induction hrelation with
    | nil => rfl
    | @cons a direct auxiliaries rest ha htail ih =>
      simp only [List.flatMap_cons, List.map_append]
      change (a.heads source.uvars source.nparams).map (·.auxiliary) ++ _ =
        (direct.name :: direct.ctors.map (·.name)) ++ familyNames rest
      have hhead := a.directFamily_heads ha
      rw [hparams] at hhead
      rw [hhead, ih]
  have hrec : g.recursorName owner ∈ g.recursors.map (·.name) := by
    exact List.mem_map.mpr ⟨g.recursor owner,
      List.mem_map.mpr ⟨owner, List.mem_finRange owner, rfl⟩, rfl⟩
  have hnd : ((expanded.typeConstants ++ expanded.constructorConstants).map (·.name) ++
      g.recursors.map (·.name)).Nodup := by
    simpa only [List.map_append] using H.generatedNames
  intro head hmem
  have hn : head.auxiliary ∈ familyNames expanded.types := by
    rw [← hexpandedNames, hsourceNames]
    have hd : head.auxiliary ∈ familyNames direct := by
      rw [← hheadNames]
      exact List.mem_map.mpr ⟨head, hmem, rfl⟩
    simpa only [familyNames, List.flatMap_append, List.mem_append] using Or.inr hd
  have hn' : head.auxiliary ∈
      (expanded.typeConstants ++ expanded.constructorConstants).map (·.name) := by
    rcases List.mem_flatMap.mp hn with ⟨type, htype, hname⟩
    rcases List.mem_cons.mp hname with hname | hctor
    · apply List.mem_map.mpr
      exact ⟨type.toVConstVal, List.mem_append_left _
        (List.mem_map.mpr ⟨type, htype, rfl⟩), hname.symm⟩
    · rcases List.mem_map.mp hctor with ⟨ctor, hctor, hname⟩
      apply List.mem_map.mpr
      exact ⟨ctor, List.mem_append_right _
        (List.mem_flatMap.mpr ⟨type, htype, hctor⟩), hname⟩
  exact (List.nodup_append.mp hnd).2.2 _ hn' _ hrec

private theorem forall₂_exists_left {R : α → β → Prop} {left : List α} {right : List β}
    (H : List.Forall₂ R left right) {b : β} (hb : b ∈ right) :
    ∃ a ∈ left, R a b := by
  induction H with
  | nil => cases hb
  | @cons a b' left right h _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, by simp, h⟩
    · rcases ih hb with ⟨a', ha', h'⟩
      exact ⟨a', by simp [ha'], h'⟩

private theorem forall₂_exists_right {R : α → β → Prop} {left : List α} {right : List β}
    (H : List.Forall₂ R left right) {a : α} (ha : a ∈ left) :
    ∃ b ∈ right, R a b := by
  induction H with
  | nil => cases ha
  | @cons a' b left right h _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, by simp, h⟩
    · rcases ih ha with ⟨b', hb', h'⟩
      exact ⟨b', by simp [hb'], h'⟩

/-- The shared instance determines each equation head and its
corresponding restored recursor declaration. -/
theorem CompilationData.equation_head_owned
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (H : CompilationData env source expanded s g auxiliaries block)
    {df : VDefEq} (hdf : df ∈ block.rules) :
    ∃ recursor ∈ block.recursors, ∃ levels,
      df.lhs.stripLams.getAppFnArgs.1 = .const recursor.name levels := by
  let r := compilationRestoration source auxiliaries
  rcases forall₂_exists_left (List.mapM_eq_some.mp H.equations) hdf with
    ⟨generated, hgenerated, hrestored⟩
  rcases List.mem_map.mp hgenerated with ⟨index, _, rfl⟩
  have hrecMem : g.recursor s.constructors[index].owner ∈ g.recursors :=
    List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
  rcases forall₂_exists_right (List.mapM_eq_some.mp H.recursors) hrecMem with
    ⟨recursor, hrecursor, hrecRestore⟩
  have hrecName : recursor.name = r.recursorName (g.recursorName s.constructors[index].owner) := by
    simp [Restoration.recursor] at hrecRestore
    rcases hrecRestore with ⟨type, _, h⟩
    cases h
    rfl
  refine ⟨recursor, hrecursor, VLevel.params g.uvars, ?_⟩
  rw [hrecName]
  have hleft : r.expr (g.equation index).lhs = some df.lhs := by
    simp [Restoration.equation] at hrestored
    rcases hrestored with ⟨lhs, hleft, rhs, _, type, _, h⟩
    cases h
    exact hleft
  apply Restoration.wrapLams_head_const
    (H.heads_not_recursors s.constructors[index].owner) ?_ hleft
  exact VExpr.getAppFnArgs_mkApps_head _ _

end InductiveSignature

/-- All finite ordinary/nested derivations, including environment replay,
reject equations whose entire left-hand side is a sort. -/
theorem CompiledInductive.equation_lhs_ne_sort
    {env : VEnv} {source : VInductDecl} {block : VInductBlock}
    (H : CompiledInductive env source block) :
    ∀ equation ∈ block.rules, ∀ u, equation.lhs ≠ .sort u := by
  exact CompiledInductive.rec
    (motive_1 := fun _ _ block _ =>
      ∀ equation ∈ block.rules, ∀ u, equation.lhs ≠ .sort u)
    (motive_2 := fun _ _ _ => True)
    (fun data _ _ => data.equation_lhs_ne_sort)
    (fun _ _ _ ih => ih)
    trivial
    (fun _ _ _ _ _ _ _ => trivial)
    H

/-- An equality with a bare sort as its left-hand side cannot be inserted by choosing some other
normalized signature, lowering table, or compilation derivation. -/
theorem CompiledInductive.reject_sort_lhs
    {env : VEnv} {source : VInductDecl} {block : VInductBlock}
    {equation : VDefEq} {u : VLevel}
    (hmem : equation ∈ block.rules) (hlhs : equation.lhs = .sort u) :
    ¬ CompiledInductive env source block := by
  intro H
  exact H.equation_lhs_ne_sort equation hmem u hlhs

/-- Every generated/restored equation is headed by a recursor installed by
the same finite compilation; replay preserves this ownership. -/
theorem CompiledInductive.equation_head_owned
    {env : VEnv} {source : VInductDecl} {block : VInductBlock}
    (H : CompiledInductive env source block) :
    ∀ df ∈ block.rules, ∃ recursor ∈ block.recursors, ∃ levels,
      df.lhs.stripLams.getAppFnArgs.1 = .const recursor.name levels := by
  exact CompiledInductive.rec
    (motive_1 := fun _ _ block _ =>
      ∀ df ∈ block.rules, ∃ recursor ∈ block.recursors, ∃ levels,
        df.lhs.stripLams.getAppFnArgs.1 = .const recursor.name levels)
    (motive_2 := fun _ _ _ => True)
    (fun data _ _ df hdf => data.equation_head_owned hdf)
    (fun _ _ _ ih => ih)
    trivial
    (fun _ _ _ _ _ _ _ => trivial)
    H

end Lean4Lean
