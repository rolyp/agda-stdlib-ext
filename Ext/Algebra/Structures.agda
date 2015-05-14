module Ext.Algebra.Structures where

   open import Algebra
   open import Algebra.FunctionProperties
   open import Algebra.Structures
   open import Data.Bool
   open import Function using (_∘_)
   open import Level
   open import Relation.Binary

   open import Ext.Relation.Binary.Props.Poset

   record IsMagma {a ℓ} {A : Set a}
                  (≈ : Rel A ℓ) (∙ : Op₂ A) : Set (a ⊔ ℓ) where
      field
         isEquivalence : IsEquivalence ≈
         ∙-cong : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈

      open IsEquivalence isEquivalence public

   record IsIdempotentMagma {a ℓ} {A : Set a}
                            (≈ : Rel A ℓ) (∙ : Op₂ A) : Set (a ⊔ ℓ) where
      field
         isMagma : IsMagma ≈ ∙
         idem : Algebra.FunctionProperties.Idempotent ≈ ∙

      open IsMagma isMagma public

   record IsCommutativeSemigroup {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                                 (_∙_ : Op₂ A) : Set (a ⊔ ℓ) where
     field
       isSemigroup : IsSemigroup ≈ _∙_
       comm        : Commutative ≈ _∙_

     open IsSemigroup isSemigroup public

   record IsJoinSemilattice {a ℓ} {A : Set a}
                                  (_≈_ : Rel A ℓ) (_∨_ : Op₂ A) : Set (a Level.⊔ ℓ) where
      field
         isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _∨_
         idem : Idempotent _≈_ _∨_

      open IsCommutativeSemigroup isCommutativeSemigroup public

      -- A semilattice gives rise to a poset.
      poset : Poset a ℓ ℓ
      poset = record {
            _≤_ = λ x y → y ≈ (x ∨ y);
            isPartialOrder = record {
                  isPreorder = record {
                        isEquivalence = isEquivalence;
                        reflexive = λ {i j} i≈j →
                           begin
                              j
                           ≈⟨ sym (idem _) ⟩
                              j ∨ j
                           ≈⟨ ∙-cong (sym i≈j) refl ⟩
                              i ∨ j
                           ∎;
                        trans = λ {i j k} j≈i∨j k≈j∨k →
                           begin
                              k
                              ≈⟨ k≈j∨k ⟩
                              j ∨ k
                              ≈⟨ ∙-cong j≈i∨j refl ⟩
                              (i ∨ j) ∨ k
                              ≈⟨ assoc _ _ _ ⟩
                              (i ∨ (j ∨ k))
                              ≈⟨ ∙-cong refl (sym k≈j∨k) ⟩
                              i ∨ k
                           ∎
                     };
                  antisym = λ {x y} y≈x∨y x≈y∨x →
                     begin
                        x
                        ≈⟨ x≈y∨x ⟩
                        y ∨ x
                        ≈⟨ comm _ _ ⟩
                        x ∨ y
                        ≈⟨ sym y≈x∨y ⟩
                        y
                     ∎
               }
         } where
            open import Relation.Binary.EqReasoning record { isEquivalence = isEquivalence }

      isIdempotentMagma : IsIdempotentMagma _≈_ _∨_
      isIdempotentMagma = record {
            isMagma = record { isEquivalence = isEquivalence; ∙-cong = ∙-cong }; idem = idem
         }

   record IsMeetSemilattice {a ℓ} {A : Set a}
                            (_≈_ : Rel A ℓ) (_∧_ : Op₂ A) : Set (a Level.⊔ ℓ) where
      field
         isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _∧_
         idem : Idempotent _≈_ _∧_

      open IsCommutativeSemigroup isCommutativeSemigroup public

      poset : Poset a ℓ ℓ
      poset = dual poset′
         where
            poset′ = IsJoinSemilattice.poset record {
                  isCommutativeSemigroup = isCommutativeSemigroup;
                  idem = idem
               }

      isIdempotentMagma : IsIdempotentMagma _≈_ _∧_
      isIdempotentMagma = IsJoinSemilattice.isIdempotentMagma record {
            isCommutativeSemigroup = isCommutativeSemigroup; idem = idem
         }

   -- Could make this "inherit" from IsJoinSemilattice.
   record IsBoundedJoinSemilattice {a ℓ} {A : Set a}
                                   (_≈_ : Rel A ℓ) (_∨_ : Op₂ A) (⊥ : A) : Set (a Level.⊔ ℓ) where
      field
         isCommutativeMonoid : IsCommutativeMonoid _≈_ _∨_ ⊥
         idem : Idempotent _≈_ _∨_
         -- Provide a test for ⊥ without requiring a full-blown Eq instance.
         is-⊥ : A → Bool

      open IsCommutativeMonoid isCommutativeMonoid public

      poset : Poset a ℓ ℓ
      poset = IsJoinSemilattice.poset record {
            isCommutativeSemigroup = record { isSemigroup = isSemigroup; comm = comm };
            idem = idem
         }

   -- TODO: use these field name conventions in GaloisConnection too.
   record IsGaloisConnection
      {𝑐 ℓ₁ ℓ₂}
      (A B : Poset 𝑐 ℓ₁ ℓ₂)
      (f : Poset.Carrier A → Poset.Carrier B)
      (g : Poset.Carrier B → Poset.Carrier A) : Set (𝑐 ⊔ ℓ₁ ⊔ ℓ₂) where

      open Poset A renaming (_≤_ to _≤ₗ_)
      open Poset B renaming (_≤_ to _≤ᵣ_)

      field
         f-mono : ∀ x y → x ≤ₗ y → f x ≤ᵣ f y
         g-mono : ∀ x y → x ≤ᵣ y → g x ≤ₗ g y
         g∘f≤id : ∀ x → (g ∘ f) x ≤ₗ x
         id≤f∘g : ∀ x → x ≤ᵣ (f ∘ g) x
