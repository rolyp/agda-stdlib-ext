open import Algebra.Structures
open import Relation.Binary

-- Lattices are closed under products. See 0.6.9 for discussion on generalising to dependent pairs.
module Ext.Algebra.Properties.Lattice.Product
   {𝑎 𝑏 𝑙₁ 𝑙₂}
   {A : Set 𝑎} {B : Set 𝑏}
   {_≈₁_ : Rel A 𝑙₁} {_∨₁_ _∧₁_}
   {_≈₂_ : Rel B 𝑙₂} {_∨₂_ _∧₂_}
   (isLattice₁ : IsLattice _≈₁_ _∨₁_ _∧₁_)
   (isLattice₂ : IsLattice _≈₂_ _∨₂_ _∧₂_) where

   open import Algebra.FunctionProperties
   open import Data.Product hiding (_-×-_)

   open import Ext
   import Ext.Algebra.Properties.Lattice

   module IsL₁ = IsLattice isLattice₁
   module IsL₂ = IsLattice isLattice₂

   _≈_ : Rel (A × B) _
   _≈_ = _≈₁_ -×- _≈₂_

   _∧_ : Op₂ (A × B)
   (x , y) ∧ (x′ , y′) = x ∧₁ x′ , y ∧₂ y′

   _∨_ : Op₂ (A × B)
   (x , y) ∨ (x′ , y′) = x ∨₁ x′ , y ∨₂ y′

   isLattice : IsLattice _≈_ _∨_ _∧_
   isLattice = record {
         isEquivalence = ×-preserves-isEquiv IsL₁.isEquivalence IsL₂.isEquivalence;
         ∨-comm = λ _ _ → IsL₁.∨-comm _ _ , IsL₂.∨-comm _ _;
         ∨-assoc = λ _ _ _ → IsL₁.∨-assoc _ _ _ , IsL₂.∨-assoc _ _ _;
         ∨-cong = λ { (x≈₁x′ , y≈₂y′) (u≈₁u′ , v≈₂v′) → IsL₁.∨-cong x≈₁x′ u≈₁u′ , IsL₂.∨-cong y≈₂y′ v≈₂v′ };
         ∧-comm = λ _ _ → IsL₁.∧-comm _ _ , IsL₂.∧-comm _ _;
         ∧-assoc = λ _ _ _ → IsL₁.∧-assoc _ _ _ , IsL₂.∧-assoc _ _ _;
         ∧-cong = λ { (x≈₁x′ , y≈₂y′) (u≈₁u′ , v≈₂v′) → IsL₁.∧-cong x≈₁x′ u≈₁u′ , IsL₂.∧-cong y≈₂y′ v≈₂v′ };
         absorptive =
            (λ _ _ → proj₁ IsL₁.absorptive _ _ , proj₁ IsL₂.absorptive _ _) ,
             λ _ _ → proj₂ IsL₁.absorptive _ _ , proj₂ IsL₂.absorptive _ _
      }

   private
      open module LatticeProps =
         Ext.Algebra.Properties.Lattice (record { isLattice = isLattice }) public
