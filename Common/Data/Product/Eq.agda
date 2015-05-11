module Common.Data.Product.Eq where

   open import Data.Product
   open import Function
   open import Relation.Binary.PropositionalEquality
   open import Relation.Nullary

   open import Common.Eq using (Eq; module Eq); open Eq ⦃...⦄ renaming (_≟_ to _≟′_)

   _,_-injective₁ : ∀ {𝒂 𝑏} {A : Set 𝒂} {B : A → Set 𝑏} {a a′ b b′} → _≡_ {A = Σ[ a ∈ A ] B a} (a , b) (a′ , b′) → a ≡ a′
   _,_-injective₁ refl = refl

   _,_-injective₂ : ∀ {𝒂 𝑏} {A : Set 𝒂} {B : A → Set 𝑏} {a b b′} → _≡_ {A = Σ[ a ∈ A ] B a} (a , b) (a , b′) → b ≡ b′
   _,_-injective₂ refl = refl

   instance
      eq : ∀ {𝒂 𝑏} {A : Set 𝒂} {B : A → Set 𝑏} ⦃ _ : Eq A ⦄ ⦃ _ : ∀ {a} → Eq (B a) ⦄ → Eq (Σ[ a ∈ A ] B a)
      eq = record { _≟_ = _≟_ }
         where
            _≟_ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : A → Set 𝑏} ⦃ _ : Eq A ⦄ ⦃ _ : ∀ {a} → Eq (B a) ⦄ →
                  (p p′ : Σ[ a ∈ A ] B a) → Dec (p ≡ p′)
            (a , b) ≟ (a′ , b′) with a ≟′ a′
            (a , b) ≟ (.a , b′) | yes refl with b ≟′ b′
            (a , b) ≟ (.a , .b) | yes refl | yes refl = yes refl
            ... | no b≢b′ = no (b≢b′ ∘ _,_-injective₂)
            (a , b) ≟ (a′ , b′) | no a≢a′ = no (a≢a′ ∘ _,_-injective₁)
