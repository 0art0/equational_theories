import equational_theories.LiftingMagmaFamilies
import equational_theories.Generated.InvariantMetatheoremNonimplications
import VersoBlog

open Verso Genre Blog

#doc (Page) "Families of magma counter-examples" =>

# Lifting magma families

```leanInit liftingMagmaFamilies
```

- The metatheorems make it possible to prove non-implications by checking satisfiability in specific magmas.

- These magmas are such that checking the satisfiability of an equation in the magma is equivalent to
  checking whether the equation holds for a specific set of elements (the "generating set" of the magma).

- Magmas with this property can be abstractly characterized by an abstract definition such as

```lean liftingMagmaFamilies
namespace LiftingMagmaFamilies

class LiftingMagmaFamily (G : Type _ → Type _) where
  instMagma (α) [DecidableEq α] : Magma (G α)
  instMagmaDecidableEq {α} [DecidableEq α] : DecidableEq (G α)
  ι : ∀ {α}, α → G α
  lift : ∀ {α} [DecidableEq α], (α → G α) → (G α →◇ G α)
  lift_factors : ∀ {α} [DecidableEq α], ∀ f : α → G α, f = (lift f) ∘ ι

variable {α : Type _} [DecidableEq α] (G : Type → Type) [family : LiftingMagmaFamily G]

instance [LiftingMagmaFamily G] : Magma (G α) := LiftingMagmaFamily.instMagma α

instance [DecidableEq α] : DecidableEq (G α) :=
  LiftingMagmaFamily.instMagmaDecidableEq
```

- It can be shown that the satisfiability of a law in a lifting magma family is decidable.

```lean liftingMagmaFamilies
open Law

variable {α : Type _} [DecidableEq α] (G : Type → Type) [family : LiftingMagmaFamily G]

theorem MagmaLaw.models_iff_satisfies_ι (law : MagmaLaw α) :
    G α ⊧ law ↔ satisfiesPhi (G := G α) LiftingMagmaFamily.ι law :=
  ⟨fun h ↦ h _, fun h f ↦ by
    rw [LiftingMagmaFamily.lift_factors f, satisfiesPhi_evalHom, h]⟩

instance [DecidableEq α] (law : MagmaLaw α) :
    Decidable (@satisfiesPhi α (G α) (LiftingMagmaFamily.instMagma α) LiftingMagmaFamily.ι law) :=
  inferInstanceAs <|
    Decidable (law.lhs ⬝ LiftingMagmaFamily.ι = law.rhs ⬝ LiftingMagmaFamily.ι)

instance instDecidableSatisfiesLaw [DecidableEq α] (law : MagmaLaw α) : Decidable (G α ⊧ law) :=
  decidable_of_decidable_of_iff (MagmaLaw.models_iff_satisfies_ι G law).symm
```

# Examples of lifting magma families

## Lists

```lean liftingMagmaFamilies
instance instMagmaList {α : Type _} : Magma (List α) where
  op := List.append

instance : LiftingMagmaFamily List where
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ [a]
  lift f := {
    toFun := (List.bind · f),
    map_op' := by
      intro x y
      dsimp [Magma.op, List.bind]
      rw [← List.join_append, List.map_append]
  }
  lift_factors := by
    intro α _ f
    funext x
    exact (List.bind_singleton _ _).symm
```

## Multisets

```lean liftingMagmaFamilies

instance (priority := high) instMagmaMultiset (α : Type _) [DecidableEq α] : Magma (Multiset α) where
  op := (· + ·)

instance : LiftingMagmaFamily Multiset where
  instMagma := instMagmaMultiset
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ {a}
  lift f := {
    toFun := (Multiset.bind · f),
    map_op' := by
      intros
      dsimp [Magma.op, Multiset.bind]
      rw [Multiset.map_add, Multiset.join_add]
    }
  lift_factors := by
    intros
    funext x
    exact (Multiset.singleton_bind _ _).symm
```

## Left-projection magmas

```lean liftingMagmaFamilies
def LeftProj (α : Type _) := α

instance (priority := low) leftProj (α : Type _) : Magma (LeftProj α) where
  op := fun a _ => a

instance instLiftingMagmaFamilyLeftProj : LiftingMagmaFamily LeftProj where
  instMagma := (leftProj ·)
  instMagmaDecidableEq := inferInstance
  ι := id
  lift f := {
    toFun := f,
    map_op' := fun _ _ ↦ rfl
  }
  lift_factors := by intros; rfl
```

## Right-projection magmas

```lean liftingMagmaFamilies
def RightProj (α : Type _) := α

instance (priority := low+1) rightProj (α : Type _) : Magma (RightProj α) where
  op := fun _ a ↦ a

instance instLiftingMagmaFamilyRightProj : LiftingMagmaFamily RightProj where
  instMagma := (rightProj ·)
  instMagmaDecidableEq := inferInstance
  ι := id
  lift f := {
    toFun := f,
    map_op' := fun _ _ ↦ rfl
  }
  lift_factors := by intros; rfl
```

## Free magma with laws

```lean liftingMagmaFamilies
instance instLiftingMagmaFamilyFreeMagmaWithLaws {α} (Γ : Ctx α)
    [∀ α [DecidableEq α], DecidableEq (FreeMagmaWithLaws α Γ)] : LiftingMagmaFamily (FreeMagmaWithLaws · Γ) where
  instMagma := inferInstance
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ embed Γ (.Leaf a)
  lift {α} _ f := FreeMagmaWithLaws.evalHom (G := FreeMagmaWithLaws α Γ) f (FreeMagmaWithLaws.isModel α Γ)
  lift_factors := by intros; ext; rfl
```

# Results

- One can generate proofs of anti-implications by checking satisfiability in these magmas.

- Given a pair of laws, one which is satisfied in the magma and another that isn't, one can generate a proof
  that the first does not imply the second, using this magma as a counter-example.
