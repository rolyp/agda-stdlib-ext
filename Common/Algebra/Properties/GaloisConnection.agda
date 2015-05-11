-- Galois connections form a category.
module Common.Algebra.Properties.GaloisConnection where

   open import Function renaming (_∘_ to _∘ᶠ_; id to idᶠ)
   open import Relation.Binary
   open import Relation.Binary.PropositionalEquality
   import Relation.Binary.PreorderReasoning as PreorderReasoning

   open import Common.Algebra
   open import Common.Algebra.Structures

   infixr 9 _∘_
   _∘_ : ∀ {𝑐 ℓ₁ ℓ₂} {A B C : Poset 𝑐 ℓ₁ ℓ₂} →
        GaloisConnection B C → GaloisConnection A B → GaloisConnection A C
   _∘_ {A = A} {C = C} ⟪ f» , f« ~ 𝒇 ⟫ ⟪ g» , g« ~ 𝒈 ⟫ = ⟪ f» ∘ᶠ g» , g« ∘ᶠ f« ~ 𝒇∘𝒈 ⟫
      where
         𝒇∘𝒈 = record {
               f-mono = λ a a′ → f-mono 𝒇 (g» a) (g» a′) ∘ᶠ f-mono 𝒈 a a′;
               g-mono = λ c c′ → g-mono 𝒈 (f« c) (f« c′) ∘ᶠ g-mono 𝒇 c c′;
               g∘f≤id = λ a →
                  let open PreorderReasoning (Poset.preorder A) renaming (_∼⟨_⟩_ to _≤⟨_⟩_) in
                  begin
                     g« ((f« ∘ᶠ f») (g» a))
                  ≤⟨ g-mono 𝒈 _ _ (g∘f≤id 𝒇 _) ⟩
                     g« (g» a)
                  ≤⟨ g∘f≤id 𝒈 _ ⟩
                     a
                  ∎;
               id≤f∘g = λ c →
                  let open PreorderReasoning (Poset.preorder C) renaming (_∼⟨_⟩_ to _≤⟨_⟩_) in
                  begin
                     c
                  ≤⟨ id≤f∘g 𝒇 _ ⟩
                     f» (f« c)
                  ≤⟨ f-mono 𝒇 _ _ (id≤f∘g 𝒈 _) ⟩
                     f» ((g» ∘ᶠ g«) (f« c))
                  ∎
            } where open IsGaloisConnection

   id : ∀ {𝑐 ℓ₁ ℓ₂} {A : Poset 𝑐 ℓ₁ ℓ₂} → GaloisConnection A A
   id {A = A} = ⟪ idᶠ , idᶠ ~ 𝒊𝒅 ⟫
      where
         𝒊𝒅 = record {
               f-mono = λ _ _ → idᶠ;
               g-mono = λ _ _ → idᶠ;
               g∘f≤id = λ _ → Poset.refl A;
               id≤f∘g = λ _ → Poset.refl A
            }
