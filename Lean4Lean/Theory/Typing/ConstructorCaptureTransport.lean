import Lean4Lean.Theory.Typing.Strong

/-!
Explicit type conversions (`TypeConversion`: chains of definitional equalities, each at its
own sort, along which a term can be cast without uniqueness of sorts), and dependent
constructor captures under related substitutions into the same target context
(`ConstructorCaptureReplay`). A data capture comes from an actual source variable, with an
explicit conversion from its domain to the constructor-field domain; a proof capture can be
retained literally.

`ConstructorCaptureReplay.transport` follows the constructor telescope itself. In particular it
does not assume that a domain instantiated with reconstructed index terms is well typed before
substitution, which fails for dependent singleton indices. It does not construct the initial
conversions.
-/

namespace Lean4Lean.VEnv
open VExpr

/-- Explicit successive type conversions. Different edges may inhabit
different sorts; no sort uniqueness is needed to cast along the path. -/
inductive TypeConversion (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → VExpr → Prop where
  | refl : TypeConversion env U Γ A A
  | tail : TypeConversion env U Γ A B →
      IsDefEq env U Γ B C (.sort u) → TypeConversion env U Γ A C

namespace TypeConversion

theorem single (h : IsDefEq env U Γ A B (.sort u)) :
    TypeConversion env U Γ A B := .tail .refl h

theorem trans (h : TypeConversion env U Γ A B) (h' : TypeConversion env U Γ B C) :
    TypeConversion env U Γ A C := by
  induction h' with
  | refl => exact h
  | tail _ edge ih => exact .tail ih edge

theorem cast (h : TypeConversion env U Γ A B) (he : IsDefEq env U Γ e e' A) :
    IsDefEq env U Γ e e' B := by
  induction h with
  | refl => exact he
  | tail _ edge ih => exact .defeqDF edge ih

end TypeConversion

/-- A finite constructor-field replay. `source` is the actual argument
context; `declared` is the constructor telescope accumulated so far.
The index case records the conversion from the source variable's natural
domain to its constructor-field domain after the given substitution.
The proof case can use any already typed proof in the common target context.
No endpoint equality or computation callback is supplied. -/
inductive ConstructorCaptureReplay (env : VEnv) (U : Nat) (Γ source : List VExpr)
    (arguments : Subst) : List VExpr → Subst → Prop where
  | nil : ConstructorCaptureReplay env U Γ source arguments [] captures
  | index : ConstructorCaptureReplay env U Γ source arguments declared captures.tail →
      HasType env U declared domain (.sort level) →
      Lookup source position naturalDomain →
      captures.head = arguments position →
      TypeConversion env U Γ (naturalDomain.subst arguments) (domain.subst captures.tail) →
      ConstructorCaptureReplay env U Γ source arguments (domain :: declared) captures
  | proof : ConstructorCaptureReplay env U Γ source arguments declared captures.tail →
      HasType env U declared domain (.sort .zero) →
      HasType env U Γ captures.head (domain.subst captures.tail) →
      ConstructorCaptureReplay env U Γ source arguments (domain :: declared) captures

/-- Transport all captures by induction on their declared telescope.
Previously related captures transport the next declared domain. An index
uses its existing alignment path; a proof is reused and cast at the new
domain. This works when alignment is available only after substitution.

Only strong substitution and explicit conversion are used. In particular,
the freshly obtained typing/guard proofs are never induction arguments. -/
theorem ConstructorCaptureReplay.transport
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (W : Ctx.SubstEq env U Γ arguments arguments' source)
    (H : ConstructorCaptureReplay env U Γ source arguments declared captures) :
    ∃ captures', ConstructorCaptureReplay env U Γ source arguments' declared captures' ∧
      Ctx.SubstEq env U Γ captures captures' declared := by
  induction H with
  | @nil emptyCaptures => exact ⟨emptyCaptures, .nil, .nil⟩
  | @index declared domain level position naturalDomain captures previous hd hi he hp ih =>
    obtain ⟨tail', htail', Wtail⟩ := ih
    have hdomain := hd.substDF henv Wtail.wf hΓ Wtail
    have hindex := W.lookup hi
    obtain ⟨naturalLevel, hnatural⟩ := (show HasType env U source (.bvar position) naturalDomain from
      .bvar hi).isType henv W.wf
    have hnatural' := hnatural.substDF henv W.wf hΓ W
    have newPath : TypeConversion env U Γ (naturalDomain.subst arguments')
        (domain.subst tail') :=
      ((TypeConversion.single hnatural'.symm).trans hp).tail hdomain
    refine ⟨tail'.cons (arguments' position), ?_, ?_⟩
    · exact .index htail' hd hi rfl newPath
    · apply Ctx.SubstEq.cons Wtail hd
      simpa only [Subst.cons_head, he] using hp.cast hindex
  | @proof declared domain captures previous hd hq ih =>
    obtain ⟨tail', htail', Wtail⟩ := ih
    have hdomain := hd.substDF henv Wtail.wf hΓ Wtail
    refine ⟨tail'.cons captures.head, ?_, ?_⟩
    · exact .proof htail' hd (.defeqDF hdomain hq)
    · exact .cons Wtail hd hq

end Lean4Lean.VEnv
