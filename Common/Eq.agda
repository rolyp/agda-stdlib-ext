module Common.Eq where

   open import Data.Nat using (ℕ)
   open import Relation.Binary.PropositionalEquality
   open import Relation.Nullary

   record Eq {𝑎} (A : Set 𝑎) : Set 𝑎 where
      field
         _≟_ : (x y : A) → Dec (x ≡ y)

   instance
      nat-eq : Eq ℕ
      nat-eq = record { _≟_ = Data.Nat._≟_ }
