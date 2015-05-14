open import Algebra

module Ext.Algebra.Properties.Lattice {𝑙₁ 𝑙₂} (L : Lattice 𝑙₁ 𝑙₂) where

   open import Algebra.FunctionProperties
   open import Algebra.Structures
   open import Data.Product
   open import Function
   open Lattice L
   open import Relation.Binary

   open import Algebra.Properties.Lattice L public

   open Poset poset public hiding (Carrier; _≈_) renaming (refl to ≤-refl)
   open import Relation.Binary.EqReasoning setoid

   ∧-absorbs-∨ : _Absorbs_ _≈_ _∧_ _∨_
   ∧-absorbs-∨ = proj₂ absorptive

   ∨-absorbs-∧ : _Absorbs_ _≈_ _∨_ _∧_
   ∨-absorbs-∧ = proj₁ absorptive

   -- The partial order happens to be defined in terms of the meet, but there is an equivalent
   -- definition in terms of the join.
   ≤-to-∨ : ∀ x y → x ≤ y → y ≈ x ∨ y
   ≤-to-∨ x y x≤y =
      begin
         y
      ≈⟨ sym (∨-absorbs-∧ _ _) ⟩
         y ∨ (y ∧ x)
      ≈⟨ refl ⟨ ∨-cong ⟩ ∧-comm _ _ ⟩
         y ∨ (x ∧ y)
      ≈⟨ refl ⟨ ∨-cong ⟩ sym x≤y ⟩
         y ∨ x
      ≈⟨ ∨-comm _ _ ⟩
         x ∨ y
      ∎

   ∨-to-≤ : ∀ x y → y ≈ x ∨ y → x ≤ y
   ∨-to-≤ x y y≈x∨y =
      begin
         x
      ≈⟨ sym (∧-absorbs-∨ _ _) ⟩
         x ∧ (x ∨ y)
      ≈⟨ refl ⟨ ∧-cong ⟩ sym y≈x∨y ⟩
         x ∧ y
      ∎

   ∨ʳ : ∀ {x y} → x ≤ (x ∨ y)
   ∨ʳ {x} {y} = sym (∧-absorbs-∨ x y)

   ∨ˡ : ∀ {x y} → x ≤ (y ∨ x)
   ∨ˡ {x} {y} =
      begin
         x
      ≈⟨ ∨ʳ ⟩
         x ∧ (x ∨ y)
      ≈⟨ refl ⟨ ∧-cong ⟩ ∨-comm _ _ ⟩
         x ∧ (y ∨ x)
      ∎

   _∧-compatible_ : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x ∧ y ≤ x′ ∧ y′
   _∧-compatible_ {x} {x′} {y} {y′} x≤x′ y≤y′ =
      begin
         x ∧ y
      ≈⟨ x≤x′ ⟨ ∧-cong ⟩ y≤y′ ⟩
         (x ∧ x′) ∧ (y ∧ y′)
      ≈⟨ ∧-assoc _ _ _ ⟩
         x ∧ (x′ ∧ (y ∧ y′))
      ≈⟨ refl ⟨ ∧-cong ⟩ ∧-comm _ _ ⟩
         x ∧ ((y ∧ y′) ∧ x′)
      ≈⟨ refl ⟨ ∧-cong ⟩ ∧-assoc _ _ _ ⟩
         x ∧ (y ∧ (y′ ∧ x′))
      ≈⟨ sym (∧-assoc _ _ _) ⟩
         (x ∧ y) ∧ (y′ ∧ x′)
      ≈⟨ refl ⟨ ∧-cong ⟩ ∧-comm _ _ ⟩
         (x ∧ y) ∧ (x′ ∧ y′)
      ∎

   infixr 7 _∧-compatible_

   _∨-compatible_ : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x ∨ y ≤ x′ ∨ y′
   _∨-compatible_ {x} {x′} {y} {y′} x≤x′ y≤y′ = ∨-to-≤ _ _ (
      begin
         x′ ∨ y′
      ≈⟨ ≤-to-∨ _ _ x≤x′ ⟨ ∨-cong ⟩ ≤-to-∨ _ _ y≤y′ ⟩
         (x ∨ x′) ∨ (y ∨ y′)
      ≈⟨ ∨-assoc _ _ _ ⟩
         x ∨ (x′ ∨ (y ∨ y′))
      ≈⟨ refl ⟨ ∨-cong ⟩ ∨-comm _ _ ⟩
         x ∨ ((y ∨ y′) ∨ x′)
      ≈⟨ refl ⟨ ∨-cong ⟩ ∨-assoc _ _ _ ⟩
         x ∨ (y ∨ (y′ ∨ x′))
      ≈⟨ sym (∨-assoc _ _ _) ⟩
         (x ∨ y) ∨ (y′ ∨ x′)
      ≈⟨ refl ⟨ ∨-cong ⟩ ∨-comm _ _ ⟩
         (x ∨ y) ∨ (x′ ∨ y′)
      ∎)

   infixr 6 _∨-compatible_

   -- x ∨ y is the least upper bound of x and y.
   _∨-lub_ : ∀ {x y z} → x ≤ z → y ≤ z → x ∨ y ≤ z
   _∨-lub_ {x} {y} {z} x≤z y≤z = ∨-to-≤ _ _ ((
      begin
         z
      ≈⟨ ≤-to-∨ _ _ x≤z ⟩
         x ∨ z
      ≈⟨ refl ⟨ ∨-cong ⟩ ≤-to-∨ _ _ y≤z ⟩
         x ∨ (y ∨ z)
      ≈⟨ sym (∨-assoc _ _ _) ⟩
         (x ∨ y) ∨ z
      ∎))

   infixr 6 _∨-lub_

   -- x ∧ y is the greatest lower bound of x and y.
   _∧-glb_ : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ x ∧ y
   _∧-glb_ {x} {y} {z} z≤x z≤y =
      begin
         z
      ≈⟨ z≤y ⟩
         z ∧ y
      ≈⟨ z≤x ⟨ ∧-cong ⟩ refl ⟩
         (z ∧ x) ∧ y
      ≈⟨ ∧-assoc _ _ _ ⟩
         z ∧ (x ∧ y)
      ∎

   infixr 7 _∧-glb_
