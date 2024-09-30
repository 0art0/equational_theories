import equational_theories.Conjecture
import equational_theories.AllEquations
import equational_theories.MagmaHom

universe u
universe v

inductive FreeMagma (α : Type u)
  | Leaf : α → FreeMagma α
  | Fork : FreeMagma α → FreeMagma α → FreeMagma α
  deriving DecidableEq

instance (α : Type u) : Magma (FreeMagma α) where
  op := FreeMagma.Fork

infixl:65 " ⋆ " => FreeMagma.Fork

theorem FreeMagma_op_eq_fork (α : Type u) (a b : FreeMagma α) : a ∘ b = a ⋆ b := rfl

@[simp]
theorem fork_eq_FreeMagma_op (α : Type u) (a b : FreeMagma α) : a ⋆ b = a ∘ b := rfl

notation "Lf" => FreeMagma.Leaf

instance FreeMagma.Magma {α} : Magma (FreeMagma α) := ⟨ Fork ⟩

def fmapFreeMagma.fun {α : Type u} {β : Type v} (f : α → β) : FreeMagma α → FreeMagma β
  | Lf a => FreeMagma.Leaf (f a)
  | lchild ⋆ rchild => FreeMagma.Fork (fmapFreeMagma.fun f lchild) (fmapFreeMagma.fun f rchild)

def evalInMagma.fun {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α → G
  | Lf a => f a
  | lchild ⋆ rchild => (evalInMagma.fun f lchild) ∘ (evalInMagma.fun f rchild)

def evalInMagma {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α →∘ G := {
  toFun := evalInMagma.fun f,
  map_op' := by
    intro a b
    cases a <;> cases b <;> rfl
}

theorem evalHom {α : Type u} {G G' : Type _} [Magma G] [Magma G'] (f : α → G) (φ : G →∘ G') (t : FreeMagma α) :
  evalInMagma (φ ∘ f) t = φ (evalInMagma f t) := by
  induction t
  . rfl
  · rw [← FreeMagma_op_eq_fork]
    repeat (rw [MagmaHom.map_op])
    simp_all only

theorem ExpressionEqualsAnything_implies_Equation2 (G: Type u) [Magma G]
  : (∃ n : Nat, ∃ expr : FreeMagma (Fin n), ∀ x : G, ∀ sub : Fin n → G, x = evalInMagma sub expr) → Equation2 G := by
  intro ⟨n, expr, univ⟩ x y
  let constx : Fin n → G := fun _ ↦ x
  exact (univ x constx).trans (univ y constx).symm

theorem Equation37_implies_Equation2 (G : Type u) [Magma G]
  : (∀ x y z w : G, x = (y ∘ z) ∘ w) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    3,
    (Lf 0 ⋆ Lf 1) ⋆ Lf 2, -- The syntactic representation of (y ∘ z) ∘ w
    fun k sub ↦ univ k (sub 0) (sub 1) (sub 2)
  ⟩

theorem Equation514_implies_Equation2 (G : Type u) [Magma G]
  : (∀ x y : G, x = y ∘ (y ∘ (y ∘ y))) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    1,
    Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)), -- The syntactic representation of y ∘ (y ∘ (y ∘ y)))
    fun k sub ↦ univ k (sub 0)
  ⟩
