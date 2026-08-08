import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
namespace VEnv

/-!
# Environment-extension lemmas for `VEnv.addInduct`

`addInduct_le` (adding an inductive only grows the environment) and `addInduct_pat`
(every recursor rule's ι-reduction rule ends up in the resulting `pats`), plus the
still-open soundness statement `addInduct_WF`.
-/

/-- Monotonicity of a monadic left fold in the `Option` monad: if each successful
step only grows the environment, then so does the whole fold. -/
theorem foldlM_le {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e x e'}, f e x = some e' → e ≤ e') :
    ∀ {l : List α} {init r}, l.foldlM f init = some r → init ≤ r
  | [], init, r, h => by simp [List.foldlM] at h; exact h ▸ .rfl
  | _ :: _, init, r, h => by
    simp only [List.foldlM] at h
    obtain ⟨_, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (hf h1).trans (foldlM_le hf h2)

/-- Registering one ι rule only grows the environment. -/
theorem addRecRule_le {env env' : VEnv} {r ru}
    (h : env.addRecRule r ru = some env') : env ≤ env' := by
  unfold addRecRule at h
  split at h
  · cases h; exact addPat_le
  · cases h

/-- Registering the ι rule of recursor rule `ru` (of recursor `r`) makes exactly
that rule present in the resulting environment's `pats`. -/
theorem addRecRule_pats {env env' : VEnv} {r ru} (hclosed : ru.rhs.Closed)
    (h : env.addRecRule r ru = some env') :
    env'.pats
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (r.numParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.nfields ru.rhs hclosed, .true) := by
  unfold addRecRule at h
  rw [dif_pos hclosed] at h
  cases h
  exact addPat_self

/-- Adding an inductive declaration only grows the environment. -/
theorem addInduct_le {env env' : VEnv} {decl} (h : env.addInduct decl = some env') :
    env ≤ env' := by
  unfold addInduct at h
  obtain ⟨env1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env3, s3, s4⟩ := Option.bind_eq_some_iff.1 h
  exact (foldlM_le (fun hh => addConst_le hh) s1).trans <|
    (foldlM_le (fun hh => foldlM_le (fun hh2 => addConst_le hh2) hh) s2).trans <|
    (foldlM_le (fun hh => addConst_le hh) s3).trans <|
    (foldlM_le (fun hh => foldlM_le (fun hh2 => addRecRule_le hh2) hh) s4)

/-- If some `x ∈ l` yields a `P` under a successful step, `P` is `≤`-monotone, and
every step only grows the environment, then the fold result satisfies `P`. Used to
carry a freshly-registered `pat` through the rest of a `foldlM`. -/
theorem foldlM_mono_of_mem {α} {f : VEnv → α → Option VEnv} {P : VEnv → Prop} {x : α}
    (hf : ∀ {e a e'}, f e a = some e' → e ≤ e')
    (hmono : ∀ {e e'}, e ≤ e' → P e → P e')
    (hstep : ∀ {e e'}, f e x = some e' → P e')
    {l : List α} (hx : x ∈ l) {init final} (hfold : l.foldlM f init = some final) : P final := by
  induction l generalizing init with
  | nil => nomatch hx
  | cons a as ih =>
    simp only [List.foldlM] at hfold
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 hfold
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact hmono (foldlM_le hf h2) (hstep h1)
    · exact ih hx' h2

/-- After `addInduct`, the ι-reduction rule for every recursor rule `ru ∈ r.rules`
(with `r ∈ decl.recs` and `ru.rhs` closed) is present in `env'.pats`. -/
theorem addInduct_pat {env env' : VEnv} {decl : VInductDecl} {r ru}
    (hr : r ∈ decl.recs) (hru : ru ∈ r.rules) (hclosed : ru.rhs.Closed)
    (h : env.addInduct decl = some env') :
    env'.pats
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (r.numParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.nfields ru.rhs hclosed, .true) := by
  unfold addInduct at h
  obtain ⟨env1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨env3, s3, s4⟩ := Option.bind_eq_some_iff.1 h
  refine foldlM_mono_of_mem (x := r)
    (f := fun e r => List.foldlM (fun e ru => e.addRecRule r ru) e r.rules)
    (fun hh => foldlM_le (fun hh2 => addRecRule_le hh2) hh)
    (fun le hp => le.pats hp)
    (fun {e e'} hh => ?_)
    hr s4
  exact foldlM_mono_of_mem (x := ru) (f := fun e u => e.addRecRule r u)
    (fun hh2 => addRecRule_le hh2)
    (fun le hp => le.pats hp)
    (fun hh2 => addRecRule_pats hclosed hh2)
    hru hh

/-- Soundness of `addInduct`: extending an `Ordered` environment with an inductive
declaration keeps it `Ordered`.

IOTA-TODO(soundness): not provable as stated. `Ordered` has no constructor for the
`addPat` stage, and `VInductDecl.WF` does not line up the per-constant `uvars`;
both need strengthening. -/
theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' :=
  sorry

end VEnv
end Lean4Lean
