open import Relation.Binary renaming (IsStrictTotalOrder to IsSTO)

module Common.Relation.Binary.Props where

   -- Extra properties of strict total orders.
   -- StrictTotalOrder is in scope, so give it a different name (or maybe rename Relation.Binary.Props?)
   module StrictTotalOrder′ {a ℓ₁ ℓ₂} {A : Set a}
          (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) (isStrictTotalOrder : IsSTO _≈_ _<_) where

      open IsStrictTotalOrder isStrictTotalOrder
      open IsEquivalence isEquivalence

      open import Algebra.FunctionProperties _≈_
      open import Data.Product
      open import Data.Sum
      open import Relation.Binary.StrictToNonStrict _≈_ _<_

      -- Should show that this forms a trivial meet-semilattice.
      _⊓_ : Op₂ A
      x ⊓ y with compare x y
      ... | tri< _ _ _ = x
      ... | tri≈ _ _ _ = x
      ... | tri> _ _ _ = y

      -- Then this would amount to the reflexivity of ≤.
      x⊓y≤x : ∀ {x y} → (x ⊓ y) ≤ x
      x⊓y≤x {x} {y} with compare x y
      ... | tri< _ _ _ = inj₂ refl
      ... | tri≈ _ _ _ = inj₂ refl
      ... | tri> _ _ y<x = inj₁ y<x

      -- And this would follow from commutativity, but I haven't shown that yet, nor figured out how to use
      -- <-resp-≈.
      x⊓y≤y : ∀ {x y} → (x ⊓ y) ≤ y
      x⊓y≤y {x} {y} with compare x y
      ... | tri< x<y _ _ = inj₁ x<y
      ... | tri≈ _ x≈y _ = inj₂ x≈y
      ... | tri> _ _ y<x = inj₂ refl
