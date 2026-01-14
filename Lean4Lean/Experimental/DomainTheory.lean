import Lean4Lean.Experimental.SExpr

namespace Lean4Lean

namespace SExpr
variable [Params]

inductive SExprF (V F : Type) where
  | bvar (i : Nat)
  | sort (u : SLevel)
  | const (c : Name) (ls : List SLevel)
  | papp (f a : V)
  | lam (A : V) (f : F)
  | forallE (A : V) (f : F)

def SExprF.map (v : V → V') (f : F → F') : SExprF V F → SExprF V' F'
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => .const c ls
  | .papp f a => .papp (v f) (v a)
  | .lam A e => .lam (v A) (f e)
  | .forallE A e => .forallE (v A) (f e)

def SExprF.select : (x : SExprF V F) →
    (V → (∀ {V₂ F₂} {v₂ : V₂ → V} {f₂ : F₂ → F} y, map v₂ f₂ y = x → V₂) → V') →
    (F → (∀ {V₂ F₂} {v₂ : V₂ → V} {f₂ : F₂ → F} y, map v₂ f₂ y = x → F₂) → F') →
    SExprF V' F'
  | .bvar i, _, _  => .bvar i
  | .sort u, _, _ => .sort u
  | .const c ls, _, _ => .const c ls
  | .papp g a, v, _ => .papp (v g fun (.papp g' _) _ => g') (v a fun (.papp _ a') _ => a')
  | .lam A e, v, f => .lam (v A fun (.lam A' _) _ => A') (f e fun (.lam _ e') _ => e')
  | .forallE A e, v, f =>
    .forallE (v A fun (.forallE A' _) _ => A') (f e fun (.forallE _ e') _ => e')

inductive FinFun (A B : Type) where
  | bot
  | cons (a : A) (b : B) : FinFun A B → FinFun A B

inductive FinElem where
  | bot
  | val : SExprF FinElem (FinFun FinElem FinElem) → FinElem

def DomN : Nat → Type
  | 0 => Unit
  | n+1 => Option (SExprF (DomN n) (DomN n → DomN n))

mutual
def DomN.up : ∀ {n}, DomN n → DomN (n+1)
  | 0 => fun _ => none
  | _+1 => .map (.map up (up ∘ · ∘ down))
def DomN.down : ∀ {n}, DomN (n+1) → DomN n
  | 0 => fun _ => ()
  | _+1 => .map (.map down (down ∘ · ∘ up))
end

theorem SExprF.map_comp (v₁ : V₁ → V₂) (v₂ : V₂ → V₃) (f₁ : F₁ → F₂) (f₂ : F₂ → F₃) (x) :
    map v₂ f₂ (map v₁ f₁ x) = map (v₂ ∘ v₁) (f₂ ∘ f₁) x := by
  cases x <;> simp [map]

theorem SExprF.map_id (x : SExprF V F) : map id id x = x := by
  cases x <;> simp [map]

theorem DomN.down_up : ∀ {n} (x : DomN n), down (up x) = x
  | 0, _ => rfl
  | n+1, _ => by
    simp [up, down]; refine .trans ?_ Option.map_id'; congr 1; ext
    simp [SExprF.map_comp]; refine .trans ?_ (SExprF.map_id _)
    congr 1 <;> ext <;> simp [@DomN.down_up n]

def DomN.upN (x : DomN n) : DomN (n + k) :=
  match k with
  | 0 => x
  | _+1 => x.upN.up

def DomN.downN (x : DomN (n + k)) : DomN n :=
  match k with
  | 0 => x
  | _+1 => x.down.downN

def DomN.cast (x : DomN n) : DomN m :=
  if h : n ≤ m then Nat.add_sub_cancel' h ▸ x.upN (k := m - n)
  else ((Nat.add_sub_cancel' (Nat.le_of_not_le h)).symm ▸ x).downN (k := n - m)

theorem DomN.cast_eq_upN (x : DomN n) : x.cast (m := n + k) = x.upN := by
  simp [cast]
  generalize Nat.add_sub_cancel' (Nat.le_add_right ..) = p
  generalize eq : n + k - n = k' at p
  simp at eq; subst eq; rfl

theorem DomN.cast_eq_downN (x : DomN (n + k)) : x.cast (m := n) = x.downN := by
  by_cases h : n + k ≤ n
  · cases show k = 0 by omega
    exact x.cast_eq_upN (k := 0)
  · simp [cast, h]
    change let p : n + k = n + (n + k - n) := _; (p ▸ x).downN = _
    intro p; clear_value p
    generalize eq : n + k - n = k' at p
    simp at eq; subst eq; rfl

theorem DomN.downN_cast (x : DomN (a + k)) (h : b ≤ a) : x.downN.cast = (x.cast : DomN b) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  rw [DomN.cast_eq_downN]
  induction k with
  | zero => rw [DomN.cast_eq_downN]; rfl
  | succ k ih =>
    rw [DomN.downN, ih]; clear ih
    revert x; change ∀ x : DomN (b+m+k+1), x.down.cast = x.cast
    generalize eq : b+m+k = k'; rw [Nat.add_assoc] at eq; subst eq; intro x
    rw [DomN.cast_eq_downN, ← DomN.downN, ← DomN.cast_eq_downN]

theorem DomN.upN_cast (x : DomN a) : (x.upN : DomN (a + b)).cast = (x.cast : DomN c) := by
  obtain h' | h' := Nat.le_or_le (a+b) c
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h'; clear h'
    rw [DomN.cast_eq_upN]
    induction k with
    | zero => rw [DomN.cast_eq_upN]; rfl
    | succ k ih =>
      rw [DomN.upN, ih]; clear ih
      change _ = x.cast (m := a+b+k+1)
      generalize eq : a + b + k = k'; rw [Nat.add_assoc] at eq; subst eq
      rw [DomN.cast_eq_upN, ← DomN.upN, ← DomN.cast_eq_upN]
  · induction b with
    | zero => simp [DomN.upN]
    | succ b ih =>
      simp [DomN.upN]
      by_cases h : c ≤ a + b
      · rw [← (x.upN (k := b)).up.downN_cast h, DomN.downN, DomN.down_up,
          DomN.downN_cast _ h, ih h]
      · cases show c = a + b + 1 by omega
        rw [← DomN.upN, x.cast_eq_upN (k := b+1), x.upN.cast_eq_upN (k := 0)]; rfl

theorem DomN.cast_cast (x : DomN a) (h : a ≤ b ∨ c ≤ b) :
    (x.cast : DomN b).cast = (x.cast : DomN c) := by
  by_cases h' : a ≤ b
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h'; clear h'
    rw [DomN.cast_eq_upN, DomN.upN_cast]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le h')
    rw [DomN.cast_eq_downN, DomN.downN_cast _ (h.resolve_left h')]

theorem DomN.cast_upN (x : DomN a) (h : a ≤ b) :
    (x.cast : DomN b).upN = (x.cast : DomN (b + k)) := by
  rw [← DomN.cast_eq_upN, DomN.cast_cast _ (.inl h)]

theorem DomN.cast_downN (x : DomN a) :
    (x.cast : DomN (b + k)).downN = x.cast := by
  rw [← DomN.cast_eq_downN, DomN.cast_cast _ (.inr (Nat.le_add_right ..))]

theorem DomN.cast_eq (x : DomN (a + 1)) :
    (x.cast : DomN (b + 1)) = x.map (.map cast (cast ∘ · ∘ cast)) := by
  obtain h | h := Nat.le_or_le a b
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
    induction k with
    | zero =>
      rw [cast_eq_downN (k := 0)]
      refine Option.map_id'.symm.trans ?_; congr 1; ext x
      have : cast = @id (DomN a) := by ext x; simp [DomN.cast_eq_downN (k := 0)]; rfl
      simp [this]; exact (SExprF.map_id _).symm
    | succ k ih =>
      rw [← cast_upN _ (by omega), ih, upN, upN, up, Option.map_map]; congr 1; ext x
      have (x : DomN a) : (x.cast : DomN (a+k)).up = x.cast :=
        DomN.cast_upN (k := 1) _ (Nat.le_add_right ..)
      simp [SExprF.map_comp]; congr 1 <;> ext t <;> simp [this]
      congr 2; exact DomN.downN_cast (k := 1) _ (Nat.le_add_right ..)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
    induction k with
    | zero =>
      rw [cast_eq_upN (k := 0)]
      refine Option.map_id'.symm.trans ?_; congr 1; ext x
      have : cast = @id (DomN b) := by ext x; simp [DomN.cast_eq_upN (k := 0)]; rfl
      simp [this]; exact (SExprF.map_id _).symm
    | succ k ih =>
      rw [← downN_cast _ (by omega), ih, downN, downN, down, Option.map_map]; congr 1; ext x
      have (x : DomN (b+k+1)) : (x.down.cast : DomN b) = x.cast :=
        DomN.downN_cast (k := 1) _ (Nat.le_add_right ..)
      simp [SExprF.map_comp]; congr 1 <;> ext t <;> simp [this]
      congr 2; exact DomN.cast_upN (k := 1) _ (Nat.le_add_right ..)

def Dom : Type := { f : ∀ n, DomN n // ∀ n, f n = (f (n + 1)).down }

def Dom.bot : Dom := ⟨fun | 0 => () | _+1 => none, fun | 0 | _+1 => rfl⟩

theorem Dom.downN (x : Dom) : (x.1 (n+k)).downN = x.1 n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [DomN.downN]
    conv => enter [1,1]; apply (x.2 (n+k)).symm
    exact ih

theorem Dom.cast_eq (x : Dom) (h : n ≤ m) : (x.1 m).cast = x.1 n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [DomN.cast_eq_downN, Dom.downN]

def Dom.mkN {n} (x : DomN n) : Dom :=
  ⟨fun _ => x.cast, fun _ => (DomN.cast_downN _ (k := 1)).symm⟩

theorem Dom.mkN_upN {n} (x : DomN n) : mkN (x.upN (k := k)) = mkN x := by
  apply Subtype.ext; ext i; simp [mkN, DomN.upN_cast]

theorem Dom.mkN_up {n} (x : DomN n) : mkN x.up = mkN x := mkN_upN (k := 1) x

def Dom.in (x : Option (SExprF Dom (Dom → Dom))) : Dom := by
  refine match x with | none => .bot | some x => ?_
  refine ⟨fun | 0 => () | n+1 => ?_, fun | 0 => rfl | n+1 => ?_⟩
  · exact some (x.map (·.1 n) ((·.1 n) ∘ · ∘ .mkN))
  · simp [DomN.down, SExprF.map_comp]; congr 2
    · ext x; exact x.2 _
    · ext f x; simp [Dom.mkN_up]; exact (f (mkN x)).2 _

noncomputable def Dom.out (x : Dom) : Option (SExprF Dom (Dom → Dom)) := by
  classical
  refine if H : ∃ n, (x.1 (n+1)).isSome then ?_ else none
  let ⟨n, h⟩ := Classical.indefiniteDescription _ H
  let xf := Option.get _ h
  have this k : (x.1 (n+k+1)).map (.map .cast (.cast ∘ · ∘ .cast)) = some xf := by
    rw [← DomN.cast_eq, x.cast_eq] <;> [apply Option.eq_some_of_isSome; omega]
  let y k := Option.get (x.1 (n+k+1)) <| by simp at this; let ⟨_, h, _⟩ := this k; simp [h]
  have eqy k : _ = some (y k) := Option.eq_some_of_isSome _; clear_value y
  replace hy k : (y k).map .cast (.cast ∘ · ∘ .cast) = xf :=
    Option.some_inj.1 (eqy _ ▸ this k :)
  clear this
  refine some <| xf.select
    (fun v S => ⟨fun k => have := S _ (hy k); _, _⟩)
    (fun f S => _)
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => .const c ls
  | .papp f a => .papp ⟨fun k => have := hy k; _, _⟩ _
  | .lam A e => .lam _ _
  | .forallE A e => .forallE _ _
  refine ⟨fun | 0 => () | n+1 => ?_, fun | 0 => rfl | n+1 => ?_⟩
  · exact some (x.map (·.1 n) ((·.1 n) ∘ · ∘ .mkN))
  · simp [DomN.down_succ, SExprF.map_comp]; congr 2
    · ext x; exact x.2 _
    · ext f x; simp [Dom.mkN_up]; exact (f (mkN x)).2 _


def Dom.fin : FinElem → Dom
  | .bot => .bot
  | .val => .bot
