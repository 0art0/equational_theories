import equational_theories.Completeness
import equational_theories.MagmaHom

class LiftingMagma (G : Type → Type) where
  instMagma {α} : Magma (G α)
  ι : ∀ {α}, α → G α
  lift : ∀ {α}, (α → G α) → (G α →∘ G α)
  lift_factors : ∀ {α}, ∀ f : α → G α, f = (lift f) ∘ ι

instance {G : Type → Type} [LiftingMagma G] {α : Type} : Magma (G α) := LiftingMagma.instMagma

theorem MagmaLaw.models_iff {α : Type} {G : Type → Type} (law : MagmaLaw α) [LiftingMagma G] :
    (evalInMagma (G := G α) LiftingMagma.ι law.lhs = evalInMagma (G := G α) LiftingMagma.ι law.rhs) ↔
    (∀ f : α → G α, evalInMagma f law.lhs = evalInMagma f law.rhs) := by
  constructor
  · intro h
    intro f
    have := LiftingMagma.lift_factors f
    rw [this, evalHom, h, evalHom]
  · intro h
    apply h
