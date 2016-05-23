module Ext.Data.Product where

   open import Data.Product
   open import Function
   open import Level
   open import Relation.Binary.PropositionalEquality

   ,-injective₁ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : A → Set 𝑏} {ab cd : Σ[ a ∈ A ] B a} → ab ≡ cd → proj₁ ab ≡ proj₁ cd
   ,-injective₁ refl = refl

   -- Non-dependent version for now.
   ,-injective₂ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} {ab cd : A × B} → ab ≡ cd → proj₂ ab ≡ proj₂ cd
   ,-injective₂ refl = refl

   _₁ : ∀ {𝑎 𝑏 𝑐} {A : Set 𝑎} {B : A → Set 𝑏} {X : Set 𝑐} → (A → X) → Σ[ a ∈ A ] (B a) → X
   f ₁ = f ∘ proj₁

   _₂ : ∀ {𝑎 𝑏 𝑐} {A : Set 𝑎} {B : A → Set 𝑏} {X : Set 𝑐} → ({a : A} → B a → X) → Σ[ a ∈ A ] (B a) → X
   f ₂ = f ∘ proj₂

   -- Version of ∃! that allows the type of the binder to be given, as per the Σ[ x ∈ X ] syntax.
   ∃!-syntax : ∀ {𝑎 𝑏} (A : Set 𝑎) → (A → Set 𝑏) → Set _
   ∃!-syntax A = ∃! {A = A} _≡_
   syntax ∃!-syntax B (λ x → C) = ∃![ x ∈ B ] C

   -- Pair of a value and an (irrelevant) proof that it satisfies some property.
   record Σ̣ {𝑎 𝑏} (A : Set 𝑎) (B : A → Set 𝑏) : Set (𝑎 ⊔ 𝑏) where
      constructor _,_
      field
         val : A
         .prop : B val

   Σ̣-syntax : ∀ {𝑎 𝑏} (A : Set 𝑎) → (A → Set 𝑏) → Set (𝑎 ⊔ 𝑏)
   Σ̣-syntax = Σ̣

   syntax Σ̣-syntax A (λ x → B) = Σ̣[ x ∈ A ] B
