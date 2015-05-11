open import Relation.Binary

module Common.Relation.Binary.Props.Poset
   {𝑐 ℓ₁ ℓ₂} (P : Poset 𝑐 ℓ₁ ℓ₂) where

   open import Function
   open Relation.Binary.Poset P

   dual : Poset _ _ _
   dual = record {
         _≈_ = _≈_;
         _≤_ = flip _≤_;
         isPartialOrder = record {
               isPreorder = record {
                     isEquivalence = isEquivalence;
                     reflexive = reflexive ∘ sym;
                     trans = flip trans
                  };
               antisym = flip antisym
            }
      } where
         open IsEquivalence isEquivalence using (sym)
