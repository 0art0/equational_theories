import equational_theories.Magma
import Mathlib.Data.FunLike.Basic

class MagmaHom (α : Type _) (β : Type _) [Magma α] [Magma β] where
  toFun : α → β
  map_op' : ∀ {a b : α}, toFun (a ∘ b) = toFun a ∘ toFun b

infix:25 " →∘ " => MagmaHom

instance (α : Type _) (β : Type _) [Magma α] [Magma β] : FunLike (MagmaHom α β) α β where
  coe f := f.toFun
  coe_injective' f g _ := by cases f; cases g; simp_all only

@[simp] theorem MagmaHom.map_op {α : Type _} {β : Type _} [Magma α] [Magma β] (f : α →∘ β) :
  ∀ {a a' : α}, f (a ∘ a') = f a ∘ f a' := by
    intro a a'
    show f.toFun (a ∘ a') = f.toFun a ∘ f.toFun a'
    erw [MagmaHom.map_op']
