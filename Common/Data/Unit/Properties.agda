module Common.Data.Unit.Properties where

   open import Data.Unit
   open import Function
   open import Relation.Binary.PropositionalEquality as P

   open import Common.Algebra.Structures

   -- ⊤ gives rise to a trivial semilattice.
   bjs-⊤ : IsBoundedJoinSemilattice _≡_ (const id) tt
   bjs-⊤ = record {
         isCommutativeMonoid = record {
               isSemigroup = record { isEquivalence = P.isEquivalence; assoc = λ _ _ _ → P.refl; ∙-cong = const id };
               identityˡ = const P.refl;
               comm = const (const P.refl)
            };
         idem = const P.refl
      }
