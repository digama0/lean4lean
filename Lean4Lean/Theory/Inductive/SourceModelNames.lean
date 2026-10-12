import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.CompilationNames

/-! Ordered constructor ownership when assembling a normalized source model. -/

namespace Lean4Lean.InductiveSignature

private theorem forall2_filterMap {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → Option γ} {g : β → Option δ}
    (H : List.Forall₂ R left right)
    (h : ∀ a b, R a b →
      (f a = none ∧ g b = none) ∨ ∃ x y, f a = some x ∧ g b = some y ∧ S x y) :
    List.Forall₂ S (left.filterMap f) (right.filterMap g) := by
  induction H with
  | nil => exact .nil
  | cons hr _ ih =>
    rcases h _ _ hr with ⟨hf, hg⟩ | ⟨x, y, hf, hg, hs⟩
    · simpa only [List.filterMap_cons, hf, hg] using ih
    · simpa only [List.filterMap_cons, hf, hg] using List.Forall₂.cons hs ih

private theorem owned_select (types : List VInductiveType)
    (hn : (types.map (·.name)).Nodup) (hmem : family ∈ types) :
    (types.flatMap fun t => t.ctors.map (t, ·)).filterMap
      (fun pair => if pair.1.name = family.name then some pair.2 else none) = family.ctors := by
  induction types with
  | nil => cases hmem
  | cons first rest ih =>
    obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hmem with rfl | hm
    · simp only [List.flatMap_cons, List.filterMap_append, List.filterMap_map]
      have hnil : (rest.flatMap fun t => t.ctors.map (t, ·)).filterMap
          (fun pair => if pair.1.name = family.name then some pair.2 else none) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro pair hp
        obtain ⟨t, ht, hp⟩ := List.mem_flatMap.mp hp
        obtain ⟨ctor, _, rfl⟩ := List.mem_map.mp hp
        have hne : t.name ≠ family.name := fun he => hfresh (List.mem_map.mpr ⟨t, ht, he⟩)
        simp [hne]
      simp [hnil, Function.comp_def]
    · have hne : first.name ≠ family.name := fun he =>
        hfresh (List.mem_map.mpr ⟨family, hm, he.symm⟩)
      have hempty : first.ctors.filterMap (fun _ => (none : Option VConstVal)) = [] := by simp
      simpa [List.filterMap_map, hne, Function.comp_def, hempty] using ih hrest hm

/-- Filtering the normalized constructor table by an owner yields exactly the
source family's constructors, in source order. Ownership is established by
family names and their uniqueness, rather than a caller-provided coverage list. -/
theorem constructor_model_in_family
    {s : InductiveSignature} {decl : VInductDecl}
    {R : Constructor s.families.size → VConstVal → Prop}
    (hfamilies : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hnames : (decl.types.map (·.name)).Nodup)
    (H : List.Forall₂ (fun ctor pair =>
      s.families[ctor.owner].name = pair.1.name ∧ R ctor pair.2)
      s.constructors.toList decl.ownedConstructors)
    (owner : Fin s.families.size) (hfamily : family ∈ decl.types)
    (hname : s.families[owner].name = family.name) :
    List.Forall₂ (fun normalized source =>
      ∃ ctor : Constructor s.families.size, normalized = ({ name := ctor.name, uvars := s.uvars, type := s.constructorType ctor } : VConstVal) ∧ R ctor source)
      (s.declarationFamily owner).ctors family.ctors := by
  have hnd : (s.families.toList.map (·.name)).Nodup := hfamilies ▸ hnames
  have howner {ctor : Constructor s.families.size} {pair : VInductiveType × VConstVal}
      (hn : s.families[ctor.owner].name = pair.1.name) :
      ctor.owner.val = owner.val ↔ pair.1.name = family.name := by
    constructor
    · intro he
      have he' : ctor.owner = owner := Fin.ext he
      exact hn.symm.trans ((congrArg (fun i : Fin s.families.size => s.families[i].name) he').trans hname)
    · intro he
      apply (List.getElem_inj (h₀ := by simp)
        (h₁ := by simp) hnd).mp
      simpa only [List.getElem_map, Array.getElem_toList, Fin.getElem_fin] using
        hn.trans (he.trans hname.symm)
  have hfiltered := forall2_filterMap (f := fun ctor : Constructor s.families.size =>
      if ctor.owner.val = owner.val then some
        ({ name := ctor.name, uvars := s.uvars, type := s.constructorType ctor } : VConstVal) else none)
    (g := fun pair : VInductiveType × VConstVal =>
      if pair.1.name = family.name then some pair.2 else none)
    (S := fun normalized source => ∃ ctor : Constructor s.families.size, normalized =
      ({ name := ctor.name, uvars := s.uvars, type := s.constructorType ctor } : VConstVal) ∧ R ctor source)
    H (by
      intro ctor pair hr
      by_cases ho : ctor.owner.val = owner.val
      · exact Or.inr ⟨_, _, if_pos ho, if_pos ((howner hr.1).mp ho), ctor, rfl, hr.2⟩
      · exact Or.inl ⟨if_neg ho, if_neg (fun he => ho ((howner hr.1).mpr he))⟩)
  rw [show decl.ownedConstructors = decl.types.flatMap
    (fun t => t.ctors.map (t, ·)) from rfl, owned_select _ hnames hfamily] at hfiltered
  exact hfiltered

end Lean4Lean.InductiveSignature
