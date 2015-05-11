module Common.Data.List.Eq where

   open import Data.List
   open import Data.Product
   open import Function
   open import Relation.Binary
   open import Relation.Binary.PropositionalEquality
   open import Relation.Nullary

   open import Common.Eq using (Eq; module Eq); open Eq ⦃...⦄ renaming (_≟_ to _≟′_)

   ∷-injective : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
   ∷-injective refl = refl , refl

   instance
      eq : {A : Set} ⦃ _ : Eq A ⦄ → Eq (List A)
      eq = record { _≟_ = _≟_ }
         where
            _≟_ : ∀ {A : Set} ⦃ _ : Eq A ⦄ → (xs ys : List A) → Dec (xs ≡ ys)
            [] ≟ [] = yes refl
            [] ≟ (_ ∷ _) = no (λ ())
            (_ ∷ _) ≟ [] = no (λ ())
            (x ∷ xs) ≟ (y ∷ ys) with x ≟′ y | xs ≟ ys
            (x ∷ xs) ≟ (.x ∷ .xs) | yes refl | yes refl = yes refl
            ... | yes _ | no xs≢ys = no (xs≢ys ∘ proj₂ ∘ ∷-injective)
            ... | no x≢y | yes _ = no (x≢y ∘ proj₁ ∘ ∷-injective)
            ... | no x≢y | no _ = no (x≢y ∘ proj₁ ∘ ∷-injective)
