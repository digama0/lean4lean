import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker.CheckingContext
import Lean4Lean.Verify.TypeChecker.MLCtxLemmas

/-! # Shared semantics of inductive-checker frames

The active universe parameters index the main metacontext and its embedded checking
context. Operations here preserve this parameter list. The public ordinary and recursor
frames in `Context.lean` separately certify the executable universe selection and, for
recursors, how it arose from the declaration parameters. The data constructors are
abbreviations so unfolding a public frame operation still exposes its record projections. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Shared semantics at the active universe parameters. The ordinary and recursor
frames separately retain their `none`/`some` contracts and recursor universe origin. -/
structure ContextSemantics (c : AddInductive.Context) (Us : List Name) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv

  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv Us
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv
  /-- The shapes of the visible recursors (wave 1A's `CheckerEnv.shapes`). -/
  shapes : RecursorShapesCoherent c.safety c.env.constants venv
  /-- The ι rules of the visible recursors are registered (wave 1A's `CheckerEnv.iota`). -/
  iota : IotaRulesRegistered c.safety c.env venv
  /-- The semantic checker context, embedded in the main one. -/
  check : CheckBase venv Us mlctx c.lctx c.checkLCtx

theorem ContextSemantics.current_not_mem (H : ContextSemantics c Us) :
    ⟨c.ngen.curr⟩ ∉ H.mlctx.vlctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.indFresh _ hmem)

theorem ContextSemantics.kernel_reserves_current (H : ContextSemantics c Us) :
    ({} : TypeChecker.State).ngen.Reserves ⟨c.ngen.curr⟩ := by
  apply NameGenerator.Reserves.num_of_prefix_ne
  simp [H.ngen_prefix]

theorem ContextSemantics.lctxWF (H : ContextSemantics c Us) : c.lctx.WF :=
  H.lctx_eq ▸ H.mlctx_wf.tr.1

abbrev ContextSemantics.chk (H : ContextSemantics c Us) : TypeChecker.MLCtx := H.check.m

theorem ContextSemantics.checkSub (H : ContextSemantics c Us) : c.checkLCtx.SubContextOf c.lctx :=
  H.check.sub

abbrev ContextSemantics.Base (H : ContextSemantics c Us) (l : LocalContext) : Type :=
  CheckBase H.venv Us H.mlctx c.lctx l

abbrev ContextSemantics.baseNil (H : ContextSemantics c Us) : H.Base {} :=
  .nil H.checking.tr.wf.orderedStrong H.mlctx_wf

abbrev ContextSemantics.baseMain (H : ContextSemantics c Us) (j : Nat) (hj : j ≤ H.mlctx.length) :
    H.Base (H.mlctx.dropN j hj).lctx :=
  .ofMain H.checking.tr.wf.orderedStrong H.mlctx_wf H.onlyLams H.lctx_eq j hj

abbrev ContextSemantics.withEnv (H : ContextSemantics c Us)
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hshapes : RecursorShapesCoherent c.safety env'.constants venv')
    (hiota : IotaRulesRegistered c.safety env' venv')
    (hle : H.venv ≤ venv') :
    ContextSemantics { c with env := env' } Us where
  venv := venv'
  checking := hchecking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf.mono hle
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  shapes := hshapes
  iota := hiota
  check := H.check.mono hle

/-- Replace the checking context by a certified sub-context of the main context. -/
abbrev ContextSemantics.withCheckLCtx (H : ContextSemantics c Us) (l : LocalContext) (B : H.Base l) :
    ContextSemantics { c with checkLCtx := l } Us where
  venv := H.venv
  checking := H.checking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  shapes := H.shapes
  iota := H.iota
  check := B

/-- View the embedded checking context as the main context of the same frame. -/
abbrev ContextSemantics.atCheckLCtx (H : ContextSemantics c Us) :
    ContextSemantics { c with lctx := c.checkLCtx } Us where
  venv := H.venv
  checking := H.checking
  mlctx := H.chk
  mlctx_wf := H.check.wf
  onlyLams := H.check.onlyLams
  lctx_eq := H.check.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := fun fv h => H.indFresh fv (H.check.embed.fvars_subset h)
  kernelFresh := fun fv h => H.kernelFresh fv (H.check.embed.fvars_subset h)
  shapes := H.shapes
  iota := H.iota
  check := { m := H.chk, wf := H.check.wf, onlyLams := H.check.onlyLams,
             lctx_eq := H.check.lctx_eq,
             embed := .refl H.checking.tr.wf.orderedStrong H.check.wf.tr.wf,
             sub := .refl _ }

/-- Open a fresh declaration in the main context, keeping the checking context. -/
abbrev ContextSemantics.withLocalDecl (H : ContextSemantics c Us)
    (htr : TrExprS H.venv Us H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType Us.length H.mlctx.vlctx.toCtx ty') :
    ContextSemantics { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } Us where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := ⟨H.mlctx_wf,
    H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩
  onlyLams := H.onlyLams.vlam
  lctx_eq := by
    change H.mlctx.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi =
      c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    rw [H.lctx_eq]
  ngen_prefix := by
    change c.ngen.namePrefix = `_ind_fresh
    exact H.ngen_prefix
  indFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact c.ngen.next_reserves_self
    · exact (H.indFresh _ hmem).mono NameGenerator.LE.next
  shapes := H.shapes
  iota := H.iota
  kernelFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact H.kernel_reserves_current
    · exact H.kernelFresh _ hmem
  check := H.check.skip H.checking.tr.wf.orderedStrong H.mlctx_wf H.lctx_eq
    (⟨H.mlctx_wf, H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩ :
      (TypeChecker.MLCtx.vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx).WF H.venv Us)

/-- Open the same source declaration in both contexts, with their respective translations. -/
abbrev ContextSemantics.withCheckedLocalDecl (H : ContextSemantics c Us)
    (htr : TrExprS H.venv Us H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType Us.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv Us H.chk.vlctx ty ty₀)
    (hty₀ : H.venv.IsType Us.length H.chk.vlctx.toCtx ty₀) :
    ContextSemantics { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } Us where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf
  onlyLams := H.onlyLams.vlam
  lctx_eq := (H.withLocalDecl (name := name) (bi := bi) htr hty).lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).indFresh
  kernelFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).kernelFresh
  shapes := H.shapes
  iota := H.iota
  check := H.check.cons H.checking.tr.wf H.lctx_eq
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf htr₀ hty₀

/-- Open a main declaration and the corresponding checking declaration above a chosen base. -/
abbrev ContextSemantics.withCheckedLocalDeclOn (H : ContextSemantics c Us) (base : LocalContext)
    (B : H.Base base)
    (htr : TrExprS H.venv Us H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType Us.length H.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS H.venv Us B.m.vlctx ty ty₀)
    (hty₀ : H.venv.IsType Us.length B.m.vlctx.toCtx ty₀) :
    ContextSemantics { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } Us where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf
  onlyLams := H.onlyLams.vlam
  lctx_eq := (H.withLocalDecl (name := name) (bi := bi) htr hty).lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).indFresh
  kernelFresh := (H.withLocalDecl (name := name) (bi := bi) htr hty).kernelFresh
  shapes := H.shapes
  iota := H.iota
  check := B.cons H.checking.tr.wf H.lctx_eq
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx_wf htr₀ hty₀

end VerifyInductive

end Lean4Lean
