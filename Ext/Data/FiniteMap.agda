{-# OPTIONS --sized-types #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)

-- A list of (key, value) pairs, sorted by key in strictly descending order.
module Ext.Data.FiniteMap
   {𝒌 𝒗 ℓ}
   {Key : Set 𝒌}
   (Value : Key → Set 𝒗)
   {_<_ : Rel Key ℓ}
   (isStrictTotalOrder′ : IsStrictTotalOrder _≡_ _<_)
   where

   open import Algebra.FunctionProperties
   open import Algebra.Structures
   open import Data.Empty
   open import Data.Product
   open import Data.Unit hiding (setoid)
   open import Function
   open import Level
   open import Size

   open import Ext.Data.Extended-key isStrictTotalOrder′

   module Indexed where
      open IsStrictTotalOrder isStrictTotalOrder renaming (trans to <⁺-trans)

      -- The bounds are not tight.
      data FiniteMap (l u : Key⁺) : {ι : Size} → Set (𝒌 ⊔ 𝒗 ⊔ ℓ) where
         [] : {ι : _} → .(l <⁺ u) → FiniteMap l u {↑ ι}
         _↦_∷[_]_ : {ι : _} (k : Key) (v : Value k) →
                     .(l <⁺ [ k ]) → (m : FiniteMap [ k ] u {ι}) → FiniteMap l u {↑ ι}

      infixr 3 _↦_∷[_]_

      unionWith′ : ∀ {l u} → (∀ {k} → Op₂ (Value k)) →
                  {ι : _} → FiniteMap l u {ι} → {ι′ : _} → FiniteMap l u {ι′} → FiniteMap l u
      unionWith′ _ ([] l<u) ([] _) = [] l<u
      unionWith′ _ ([] _) m = m
      unionWith′ _ m ([] _ )= m
      unionWith′ ∙ (k ↦ v ∷[ _ ] m) (k′ ↦ v′ ∷[ _ ] m′) with compare [ k ] [ k′ ]
      ... | (tri< _ _ _) = k ↦ v ∷[ _ ] unionWith′ ∙ m (k′ ↦ v′ ∷[ _ ] m′)
      unionWith′ ∙ (k ↦ v ∷[ l<k ] m) (.k ↦ v′ ∷[ _ ] m′) | (tri≈ _ refl _) =
         k ↦ (v ⟨ ∙ ⟩ v′) ∷[ l<k ] unionWith′ ∙ m m′
      ... | (tri> _ _ _) = k′ ↦ v′ ∷[ _ ] unionWith′ ∙ (k ↦ v ∷[ _ ] m) m′

      unionWith : ∀ {l u} → (∀ {k} → Op₂ (Value k)) → Op₂ (FiniteMap l u)
      unionWith ∙ x y = unionWith′ ∙ x y

      comm′ : ∀ {l u} {∙ : ∀ {k} → Op₂ (Value k)} → (∀ {k} → Commutative _≡_ (∙ {k})) →
             {ι : _} (x : FiniteMap l u {ι}) {ι′ : _} (y : FiniteMap l u {ι′}) → unionWith′ ∙ x y ≡ unionWith′ ∙ y x
      comm′ _ ([] _) ([] _) = refl
      comm′ _ ([] _) (_ ↦ _ ∷[ _ ] _) = refl
      comm′ _ (_ ↦ _ ∷[ _ ] _) ([] _) = refl
      comm′ comm-∙ (k ↦ _ ∷[ _ ] _) (k′ ↦ _ ∷[ _ ] _) with compare [ k ] [ k′ ] | compare [ k′ ] [ k ]
      comm′ comm-∙ (k ↦ v ∷[ _ ] m) (k′ ↦ v′ ∷[ _ ] m′) | (tri< k<k′_ _ _) | (tri> _ _ _) =
         cong (λ m → k ↦ v ∷[ _ ] m) (sym (comm′ comm-∙ (k′ ↦ v′ ∷[ _ ] m′) m))
      comm′ comm-∙ (k ↦ v ∷[ l<k ] m) (.k ↦ v′ ∷[ _ ] m′) | (tri≈ _ refl _) | (tri≈ _ refl _) =
         cong₂ (λ v m → k ↦ v ∷[ l<k ] m) (comm-∙ v v′) (comm′ comm-∙ m m′)
      comm′ comm-∙ (k ↦ v ∷[ _ ] m) (k′ ↦ v′ ∷[ _ ] m′) | (tri> _ _ k′<k) | (tri< _ _ _) =
         cong (λ m → k′ ↦ v′ ∷[ _ ] m) (comm′ comm-∙ (k ↦ v ∷[ _ ] m) m′)
      comm′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) | (tri< k<k′ _ _) | (tri≈ _ _ k≮k′) = ⊥-elim (k≮k′ k<k′)
      comm′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) | (tri< k<k′ _ _) | (tri< _ _ k≮k′) = ⊥-elim (k≮k′ k<k′)
      comm′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) | (tri≈ _ k≡k′ _) | (tri> _ k′≢k _) = ⊥-elim (k′≢k (sym k≡k′))
      comm′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) | (tri≈ _ k≡k′ _) | (tri< _ k′≢k _) = ⊥-elim (k′≢k (sym k≡k′))
      comm′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) | (tri> _ _ k′<k) | (tri> k′≮k _ _) = ⊥-elim (k′≮k k′<k)
      comm′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) | (tri> _ _ k′<k) | (tri≈ k′≮k _ _) = ⊥-elim (k′≮k k′<k)

      comm : ∀ {l u} {∙ : ∀ {k} → Op₂ (Value k)} →
             (∀ {k} → Commutative _≡_ (∙ {k})) → Commutative _≡_ (unionWith {l} {u} ∙)
      comm comm-∙ x y = comm′ comm-∙ x y

      -- Trivial lemmas that are immediate from the definition of unionWith′, but that Agda requires us to have.
      -- There is a lemma for each way the comparison can go.
      unionWith′≡ : ∀ {k v v′ l u} {∙ : ∀ {k} → Op₂ (Value k)} (l<k : l <⁺ [ k ]) {ι₁ : _}
                   (m : FiniteMap [ k ] u {ι₁}) {ι₂ : _} (m′ : FiniteMap [ k ] u {ι₂}) →
                   unionWith′ {l} ∙ (k ↦ v ∷[ l<k ] m) (k ↦ v′ ∷[ l<k ] m′) ≡ (k ↦ (∙ v v′) ∷[ l<k ] unionWith′ ∙ m m′)
      unionWith′≡ {k} _ _ _ with compare [ k ] [ k ]
      unionWith′≡ _ _ _ | tri< _ k≢k _ = ⊥-elim (k≢k refl)
      unionWith′≡ _ _ _ | tri≈ _ refl _ = refl
      unionWith′≡ _ _ _ | tri> _ k≢k _ = ⊥-elim (k≢k refl)

      unionWith′< : ∀ {k k′ v v′ l u} {∙ : ∀ {k} → Op₂ (Value k)}
                    (l<k : l <⁺ [ k ]) (l<k′ : l <⁺ [ k′ ]) (k<k′ : [ k ] <⁺ [ k′ ])
                    {ι₁ : _} (m : FiniteMap [ k ] u {ι₁}) {ι₂ : _} (m′ : FiniteMap [ k′ ] u {ι₂}) →
                    unionWith′ {l} ∙ (k ↦ v ∷[ l<k ] m) (k′ ↦ v′ ∷[ l<k′ ] m′) ≡
                    (k ↦ v ∷[ l<k ] unionWith′ ∙ m (k′ ↦ v′ ∷[ k<k′ ] m′))
      unionWith′< {k} {k′} _ _ _ _ _ with compare [ k ] [ k′ ]
      unionWith′< _ _ _ _ _ | tri< _ _ _ = refl
      unionWith′< _ _ k<k′ _ _ | tri≈ k≮k′ _ _ = ⊥-elim (k≮k′ k<k′)
      unionWith′< _ _ k<k′ _ _ | tri> k≮k′ _ _ = ⊥-elim (k≮k′ k<k′)

      unionWith′> : ∀ {k k′ v v′ l u} {∙ : ∀ {k} → Op₂ (Value k)}
                    (l<k : l <⁺ [ k ]) (l<k′ : l <⁺ [ k′ ]) (k′<k : [ k′ ] <⁺ [ k ])
                    {ι₁ : _} (m : FiniteMap [ k ] u {ι₁}) {ι₂ : _} (m′ : FiniteMap [ k′ ] u {ι₂}) →
                    unionWith′ {l} ∙ (k ↦ v ∷[ l<k ] m) (k′ ↦ v′ ∷[ l<k′ ] m′) ≡
                    (k′ ↦ v′ ∷[ l<k′ ] unionWith′ ∙ (k ↦ v ∷[ k′<k ] m) m′)
      unionWith′> {k} {k′} _ _ _ _ _ with compare [ k ] [ k′ ]
      unionWith′> _ _ k′<k _ _ | tri< _ _ k′≮k = ⊥-elim (k′≮k k′<k)
      unionWith′> _ _ k′<k _ _ | tri≈ _ _ k′≮k = ⊥-elim (k′≮k k′<k)
      unionWith′> _ _ _ _ _ | tri> _ _ _ = refl

      assoc′ : ∀ {l u} {∙ : ∀ {k} → Op₂ (Value k)} → (∀ {k} → Associative _≡_ (∙ {k})) →
              {ι₁ : _} (x : FiniteMap l u {ι₁}) {ι₂ : _} (y : FiniteMap l u {ι₂}) {ι₃ : _} (z : FiniteMap l u {ι₃}) →
              unionWith′ ∙ (unionWith′ ∙ x y) z ≡ unionWith′ ∙ x (unionWith′ ∙ y z)
      assoc′ _ ([] _) ([] _) ([] _) = refl
      assoc′ _ ([] _) ([] _) (_ ↦ _ ∷[ _ ] _) = refl
      assoc′ _ ([] _) (_ ↦ _ ∷[ _ ] _) ([] _) = refl
      assoc′ _ ([] _) (k ↦ _ ∷[ _ ] _) (k′ ↦ _ ∷[ _ ] _) with compare [ k ] [ k′ ]
      assoc′ _ ([] _) (k ↦ _ ∷[ _ ] _) (.k ↦ _ ∷[ _ ] _) | tri≈ _ refl _ = refl
      ... | tri< _ _ _ = refl
      ... | tri> _ _ _ = refl
      assoc′ _ (_ ↦ _ ∷[ _ ] _) ([] _) ([] _) = refl
      assoc′ _ (k ↦ _ ∷[ _ ] _) ([] _) (k′ ↦ _ ∷[ _ ] _) with compare [ k ] [ k′ ]
      assoc′ _ (k ↦ _ ∷[ _ ] _) ([] _) (.k ↦ _ ∷[ _ ] _) | tri≈ _ refl _ = refl
      ... | tri< _ _ _ = refl
      ... | tri> _ _ _ = refl
      assoc′ _ (k ↦ _ ∷[ _ ] _) (k′ ↦ _ ∷[ _ ] _) ([] _) with compare [ k ] [ k′ ]
      assoc′ _ (k ↦ _ ∷[ _ ] _) (.k ↦ _ ∷[ _ ] _) ([] _) | tri≈ _ refl _ = refl
      ... | tri< _ _ _ = refl
      ... | tri> _ _ _ = refl
      assoc′ _ (k₁ ↦ _ ∷[ _ ] _) (k₂ ↦ _ ∷[ _ ] _) (k₃ ↦ _ ∷[ _ ] _)
            with compare [ k₁ ] [ k₂ ] | compare [ k₂ ] [ k₃ ] |
                 inspect (hide (compare [ k₁ ]) [ k₂ ]) unit | inspect (hide (compare [ k₂ ]) [ k₃ ]) unit
      assoc′ _ (k₁ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) (k₃ ↦ _ ∷[ _ ] _) |
            tri< _ _ _ | tri< _ _ _ | [ eq ] | [ _ ] rewrite eq with compare [ k₁ ] [ k₃ ]
      assoc′ {l} {u} {∙} assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃) |
            tri< k₁<k₂ _ _ | tri< k₂<k₃ _ _ | [ _ ] | [ _ ] | tri< k₁<k₃ _ _ =
         begin
             k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ (unionWith′ ∙ m₁ (k₂ ↦ v₂ ∷[ _ ] m₂)) (k₃ ↦ v₃ ∷[ _ ] m₃)
         ≡⟨ cong (λ m → k₁ ↦ v₁ ∷[ _ ] m) (assoc′ assoc-∙ m₁ (k₂ ↦ v₂ ∷[ _ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃)) ⟩
            k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ (unionWith′ ∙ (k₂ ↦ v₂ ∷[ _ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃))
         ≡⟨ cong (λ m → k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ m) (unionWith′< k₁<k₂ k₁<k₃ k₂<k₃ m₂ m₃) ⟩
            k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ (k₂ ↦ v₂ ∷[ _ ] unionWith′ ∙ m₂ (k₃ ↦ v₃ ∷[ _ ] m₃))
         ∎ where open import Relation.Binary.EqReasoning (setoid (FiniteMap l u))
      assoc′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) (._ ↦ _ ∷[ _ ] _) |
            tri< _ _ k₂≮k₁ | tri< k₂<k₁ _ _ | [ _ ] | [ _ ] | tri≈ _ refl _ = ⊥-elim (k₂≮k₁ k₂<k₁)
      assoc′ _ (k₁ ↦ _ ∷[ _ ] _) (k₂ ↦ _ ∷[ _ ] _) (k₃ ↦ _ ∷[ _ ] _) |
            tri< _ _ _ | tri< _ _ _ | [ _ ] | [ _ ] | tri> k₁≮k₃ _ _ =
         ⊥-elim (k₁≮k₃ (<⁺-trans {[ k₁ ]} {[ k₂ ]} {[ k₃ ]} _ _))
      assoc′ {l} {u} {∙} assoc-∙ (k ↦ v₁ ∷[ l<k ] m₁) (k′ ↦ v₂ ∷[ _ ] m₂) (.k′ ↦ v₃ ∷[ _ ] m₃)
            | tri< k₁<k₂ _ _ | tri≈ _ refl _ | [ eq ] | [ _ ] rewrite eq =
         begin
            k ↦ v₁ ∷[ _ ] unionWith′ ∙ (unionWith′ ∙ m₁ (k′ ↦ v₂ ∷[ _ ] m₂)) (k′ ↦ v₃ ∷[ _ ] m₃)
         ≡⟨ cong (λ m → k ↦ v₁ ∷[ l<k ] m) (assoc′ assoc-∙ m₁ (k′ ↦ v₂ ∷[ _ ] m₂) (k′ ↦ v₃ ∷[ _ ] m₃)) ⟩
            k ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ (unionWith′ ∙ (k′ ↦ v₂ ∷[ _ ] m₂) (k′ ↦ v₃ ∷[ _ ] m₃))
         ≡⟨ cong (λ m → k ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ m) (unionWith′≡ {k′} k₁<k₂ m₂ m₃) ⟩
            k ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ (k′ ↦ v₂ ⟨ ∙ ⟩ v₃ ∷[ _ ] unionWith′ ∙ m₂ m₃)
         ∎ where open import Relation.Binary.EqReasoning (setoid (FiniteMap l u))
      assoc′ _ (k₁ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) (k₃ ↦ _ ∷[ _ ] _) |
            tri< _ _ _ | tri> _ _ _ | [ _ ] | [ _ ] with compare [ k₁ ] [ k₃ ]
      assoc′ {l} {u} {∙} assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃) |
            tri< k₁<k₂ _ _ | tri> _ _ k₃<k₂ | [ eq ] | [ _ ] | tri< k₁<k₃ _ _ rewrite eq =
         begin
            k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ (unionWith′ ∙ m₁ (k₂ ↦ v₂ ∷[ _ ] m₂)) (k₃ ↦ v₃ ∷[ _ ] m₃)
         ≡⟨ cong (λ m → k₁ ↦ v₁ ∷[ _ ] m) (assoc′ assoc-∙ m₁ (k₂ ↦ v₂ ∷[ _ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃)) ⟩
            k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ (unionWith′ ∙ (k₂ ↦ v₂ ∷[ k₁<k₂ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃))
         ≡⟨ cong (λ m → k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ m) (unionWith′> k₁<k₂ k₁<k₃ k₃<k₂ m₂ m₃) ⟩
            k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ (k₃ ↦ v₃ ∷[ k₁<k₃ ] unionWith′ ∙ (k₂ ↦ v₂ ∷[ k₃<k₂ ] m₂) m₃)
         ∎ where open import Relation.Binary.EqReasoning (setoid (FiniteMap l u))
      assoc′ {∙ = ∙} assoc-∙ (k ↦ v₁ ∷[ l<k ] m₁) (k′ ↦ v₂ ∷[ _ ] m₂) (.k ↦ v₃ ∷[ _ ] m₃) |
            tri< _ _ _ | tri> _ _ _ | [ _ ] | [ _ ] | tri≈ _ refl _ =
         cong (λ xs → k ↦ v₁ ⟨ ∙ ⟩ v₃ ∷[ l<k ] xs) (assoc′ assoc-∙ m₁ (k′ ↦ v₂ ∷[ _ ] m₂) m₃)
      assoc′ {l} {u} {∙} assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃) |
            tri< k₁<k₂ _ _ | tri> _ _ k₃<k₂ | [ _ ] | [ _ ] | tri> _ _ k₃<k₁ =
         begin
            k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ (k₁ ↦ v₁ ∷[ _ ] unionWith′ ∙ m₁ (k₂ ↦ v₂ ∷[ _ ] m₂)) m₃
         ≡⟨ cong (λ m → k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ m m₃) (sym (unionWith′< k₃<k₁ k₃<k₂ k₁<k₂ m₁ m₂)) ⟩
            k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ (unionWith′ ∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂)) m₃
         ≡⟨ cong (λ m → k₃ ↦ v₃ ∷[ _ ] m) (assoc′ assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂) m₃) ⟩
            k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (unionWith′ ∙ (k₂ ↦ v₂ ∷[ _ ] m₂) m₃)
         ∎ where open import Relation.Binary.EqReasoning (setoid (FiniteMap l u))
      assoc′ {∙ = ∙} assoc-∙ (k ↦ v₁ ∷[ l<k ] m₁) (.k ↦ v₂ ∷[ _ ] m₂) (k′ ↦ v₃ ∷[ _ ] m₃) |
            tri≈ _ refl _ | tri< _ _ _ | [ eq ] | [ eq′ ] rewrite eq | eq′ =
         cong (λ m → k ↦ v₁ ⟨ ∙ ⟩ v₂ ∷[ l<k ] m) (assoc′ assoc-∙ m₁ m₂ (k′ ↦ v₃ ∷[ _ ] m₃))
      assoc′ {∙ = ∙} assoc-∙ (k ↦ v₁ ∷[ l<k ] m₁) (.k ↦ v₂ ∷[ _ ] m₂) (.k ↦ v₃ ∷[ _ ] m₃) |
            tri≈ _ refl _ | tri≈ _ refl _ | [ eq ] | [ _ ] rewrite eq =
         cong₂ (λ v m → k ↦ v ∷[ l<k ] m) (assoc-∙ v₁ v₂ v₃) (assoc′ assoc-∙ m₁ m₂ m₃)
      assoc′ _ (k ↦ _ ∷[ _ ] _) (.k ↦ _ ∷[ _ ] _) (k′ ↦ _ ∷[ _ ] _) |
            tri≈ _ refl _ | tri> _ _ _  | [ _ ] | [ _ ] with compare [ k ] [ k′ ]
      assoc′ _ (_ ↦ _ ∷[ _ ] _) (._ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) |
            tri≈ _ refl _ | tri> _ _ k₃<k₁  | [ _ ] | [ _ ] | tri< _ _ k₃≮k₁ = ⊥-elim (k₃≮k₁ k₃<k₁)
      assoc′ _ (_ ↦ _ ∷[ _ ] _) (._ ↦ _ ∷[ _ ] _) (._ ↦ _ ∷[ _ ] _) |
            tri≈ _ refl _ | tri> _ k≢k _  | [ _ ] | [ _ ] | tri≈ _ refl _ = ⊥-elim (k≢k refl)
      assoc′ {l} {u} {∙} assoc-∙ (k ↦ v₁ ∷[ _ ] m₁) (._ ↦ v₂ ∷[ _ ] m₂) (k′ ↦ v₃ ∷[ _ ] m₃) |
            tri≈ _ refl _ | tri> _ _ k′<k  | [ _ ] | [ _ ] | tri> _ _ _ =
         begin
            k′ ↦ v₃ ∷[ _ ] unionWith′ ∙ (k ↦ v₁ ⟨ ∙ ⟩ v₂ ∷[ _ ] unionWith′ ∙ m₁ m₂) m₃
         ≡⟨ cong (λ m → k′ ↦ v₃ ∷[ _ ] (unionWith′ ∙ m m₃)) (sym (unionWith′≡ {k} k′<k m₁ m₂)) ⟩
            k′ ↦ v₃ ∷[ _ ] unionWith′ ∙ (unionWith′ ∙ (k ↦ v₁ ∷[ _ ] m₁) (k ↦ v₂ ∷[ _ ] m₂)) m₃
         ≡⟨ cong (λ m → k′ ↦ v₃ ∷[ _ ] m) (assoc′ assoc-∙ (k ↦ v₁ ∷[ _ ] m₁) (k ↦ v₂ ∷[ _ ] m₂) m₃) ⟩
            k′ ↦ v₃ ∷[ _ ] unionWith′ ∙ (k ↦ v₁ ∷[ _ ] m₁) (unionWith′ ∙ (k ↦ v₂ ∷[ _ ] m₂) m₃)
         ∎ where open import Relation.Binary.EqReasoning (setoid (FiniteMap l u))
      assoc′ assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ l<k₂ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃) |
            tri> _ _ _ | tri< _ _ _ | [ eq ] | [ eq′ ] rewrite eq | eq′ =
         cong (λ m → k₂ ↦ v₂ ∷[ l<k₂ ] m) (assoc′ assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) m₂ (k₃ ↦ v₃ ∷[ _ ] m₃))
      assoc′ {∙ = ∙} assoc-∙ (k ↦ v₁ ∷[ _ ] m₁) (k′ ↦ v₂ ∷[ l<k′ ] m₂) (.k′ ↦ v₃ ∷[ _ ] m₃) |
            tri> _ _ _ | tri≈ _ refl _ | [ eq ] | [ eq′ ] rewrite eq | eq′ =
         cong (λ m → k′ ↦ v₂ ⟨ ∙ ⟩ v₃ ∷[ l<k′ ] m) (assoc′ assoc-∙ (k ↦ v₁ ∷[ _ ] m₁) m₂ m₃)
      assoc′ _ (k₁ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) (k₃ ↦ _ ∷[ _ ] _) |
            tri> _ _ _ | tri> _ _ _ | [ _ ] | [ eq ] rewrite eq with compare [ k₁ ] [ k₃ ]
      assoc′ _ (k₁ ↦ _ ∷[ _ ] _) (k₂ ↦ _ ∷[ _ ] _) (k₃ ↦ _ ∷[ _ ] _) |
            tri> _ _ _ | tri> _ _ _ | [ _ ] | [ _ ] | tri< _ _ k₃≮k₁ =
         ⊥-elim (k₃≮k₁ (<⁺-trans {[ k₃ ]} {[ k₂ ]} {[ k₁ ]} _ _))
      assoc′ _ (_ ↦ _ ∷[ _ ] _) (_ ↦ _ ∷[ _ ] _) (._ ↦ _ ∷[ _ ] _) |
            tri> k₁≮k₂ _ _ | tri> _ _ k₁<k₂ | [ _ ] | [ _ ] | tri≈ _ refl _ = ⊥-elim (k₁≮k₂ k₁<k₂)
      assoc′ {l} {u} {∙} assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂) (k₃ ↦ v₃ ∷[ _ ] m₃) |
            tri> _ _ k₂<k₁ | tri> _ _ k₃<k₂ | [ _ ] | [ _ ] | tri> _ _ k₃<k₁ =
         begin
            k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ (k₂ ↦ v₂ ∷[ _ ] unionWith′ ∙ (k₁ ↦ v₁ ∷[ _ ] m₁) m₂) m₃
         ≡⟨ cong (λ m → k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ m m₃) (sym (unionWith′> k₃<k₁ k₃<k₂ k₂<k₁ m₁ m₂)) ⟩
            k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ (unionWith′ ∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂)) m₃
         ≡⟨ cong (λ m → k₃ ↦ v₃ ∷[ _ ] m) (assoc′ assoc-∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (k₂ ↦ v₂ ∷[ _ ] m₂) m₃) ⟩
            k₃ ↦ v₃ ∷[ _ ] unionWith′ ∙ (k₁ ↦ v₁ ∷[ _ ] m₁) (unionWith′ ∙ (k₂ ↦ v₂ ∷[ _ ] m₂) m₃)
         ∎  where open import Relation.Binary.EqReasoning (setoid (FiniteMap l u))

      assoc : ∀ {l u} {∙ : ∀ {k} → Op₂ (Value k)} →
              (∀ {k} → Associative _≡_ (∙ {k})) → Associative _≡_ (unionWith {l} {u} ∙)
      assoc assoc-∙ x y z = assoc′ assoc-∙ x y z

      identityˡ : ∀ {l u} {∙ : ∀ {k} → Op₂ (Value k)} (l<u : l <⁺ u) →
                 LeftIdentity _≡_ ([] l<u) (unionWith {l} {u} ∙)
      identityˡ _ ([] _) = refl
      identityˡ _ (_ ↦ _ ∷[ _ ] _) = refl

      -- Finite maps preserve commutative monoidal structure.
      cm : ∀ {l u} {∙ : ∀ {k} → Op₂ (Value k)} {ε : ∀ {k} → Value k} → (l<u : l <⁺ u) →
           (∀ {k} → IsCommutativeMonoid _≡_ (∙ {k}) (ε {k})) →
           IsCommutativeMonoid _≡_ (unionWith {l} {u} ∙) ([] l<u)
      cm {∙ = ∙} l<u cm-∙-ε = record {
            isSemigroup = record {
                  isEquivalence = ≡-isEquivalence;
                  assoc = assoc (IsCommutativeMonoid.assoc cm-∙-ε);
                  ∙-cong = cong₂ (unionWith ∙)
               };
            identityˡ = identityˡ l<u;
            comm = comm (IsCommutativeMonoid.comm cm-∙-ε)
         }

      idem : ∀ {l u} {∙ : ∀ {k} → Op₂ (Value k)} →
             (∀ {k} → Idempotent _≡_ (∙ {k})) → Idempotent _≡_ (unionWith {l} {u} ∙)
      idem _ ([] _) = refl
      idem idem-∙ (k ↦ _ ∷[ _ ] _) with compare [ k ] [ k ]
      idem idem-∙ (k ↦ v ∷[ _ ] m) | tri≈ _ refl _ =
         cong₂ (λ v m → k ↦ v ∷[ _ ] m) (idem-∙ v) (idem idem-∙ m)
      idem _ (_ ↦ _ ∷[ _ ] _) | tri< _ k≢k _ = ⊥-elim (k≢k refl)
      idem _ (_ ↦ _ ∷[ _ ] _) | tri> _ k≢k _ = ⊥-elim (k≢k refl)

      -- Could generalise this to Any, as per Data.List.
      data _↦_∈_ (k : Key) (v : Value k) {l u} : FiniteMap l u → Set (𝒌 ⊔ 𝒗 ⊔ ℓ) where
         here : ∀ {m} → (_ : l <⁺ [ k ]) → k ↦ v ∈ (k ↦ v ∷[ _ ] m)
         there : ∀ {k′ v′ m} → (_ : l <⁺ [ k′ ]) → k ↦ v ∈ m → k ↦ v ∈ (k′ ↦ v′ ∷[ _ ] m)

      -- A tree-like way of constructing a finite map, which we could use to convert an (indexed) AVL tree to a
      -- finite map. It's not so easy to convert the other way around, at least not so as to form an isomorphism,
      -- because AVL trees don't use proof-irrelevance for the ordering constraints (which they could, I think).
      -- We would first need to switch Data.AVL to use Data.Extended-key.
      construct : ∀ {l u} → (k : Key) → (v : Value k) → FiniteMap l [ k ] → FiniteMap [ k ] u → FiniteMap l u
      construct k v ([] _) m = k ↦ v ∷[ _ ] m
      construct k v (k′ ↦ v′ ∷[ _ ] m) m′ = k′ ↦ v′ ∷[ _ ] construct k v m m′

      syntax construct k v m m′ = m ++ k ↦ v ∷ m′

   -- Finite maps with hidden bounds fixed at ⊥⁺ and ⊤⁺.
   open Indexed using ([]; _↦_∷[_]_)

   data FiniteMap : Set (𝒌 ⊔ 𝒗 ⊔ ℓ) where
      finMap : Indexed.FiniteMap ⊥⁺ ⊤⁺ → FiniteMap

   empty : FiniteMap
   empty = finMap ([] _)

   singleton : (k : Key) → Value k → FiniteMap
   singleton k v = finMap (k ↦ v ∷[ _ ] ([] _))

   unionWith : (∀ {k} → Op₂ (Value k)) → Op₂ FiniteMap
   unionWith ∙ (finMap m) (finMap m′) = finMap (Indexed.unionWith′ ∙ m m′)

   data _↦_∈_ (k : Key) (v : Value k) : FiniteMap → Set (𝒌 ⊔ 𝒗 ⊔ ℓ) where
      finMap : ∀ {m} → k Indexed.↦ v ∈ m → k ↦ v ∈ finMap m

   comm : {∙ : ∀ {k} → Op₂ (Value k)} → (∀ {k} → Commutative _≡_ (∙ {k})) → Commutative _≡_ (unionWith ∙)
   comm comm-∙ (finMap x) (finMap y) = cong finMap (Indexed.comm comm-∙ x y)

   assoc : {∙ : ∀ {k} → Op₂ (Value k)} → (∀ {k} → Associative _≡_ (∙ {k})) → Associative _≡_ (unionWith ∙)
   assoc assoc-∙ (finMap x) (finMap y) (finMap z) = cong finMap (Indexed.assoc assoc-∙ x y z)

   identityˡ : {∙ : ∀ {k} → Op₂ (Value k)} → LeftIdentity _≡_ (finMap ([] _)) (unionWith ∙)
   identityˡ (finMap x) = cong finMap (Indexed.identityˡ (lift tt) x)

   -- Finite maps preserve commutative monoidal structure. Move this to Data.FiniteMap.Properties?
   cm : {∙ : ∀ {k} → Op₂ (Value k)} {ε : ∀ {k} → Value k} →
        (∀ {k} → IsCommutativeMonoid _≡_ (∙ {k}) (ε {k})) → IsCommutativeMonoid _≡_ (unionWith ∙) (finMap ([] _))
   cm {∙} cm-∙-ε = record {
         isSemigroup = record {
               isEquivalence = ≡-isEquivalence;
               assoc = assoc (IsCommutativeMonoid.assoc cm-∙-ε);
               ∙-cong = cong₂ (unionWith ∙)
            };
         identityˡ = identityˡ;
         comm = comm (IsCommutativeMonoid.comm cm-∙-ε)
      }

   idem : {∙ : ∀ {k} → Op₂ (Value k)} → (∀ {k} → Idempotent _≡_ (∙ {k})) → Idempotent _≡_ (unionWith ∙)
   idem idem-∙ (finMap x) = cong finMap (Indexed.idem idem-∙ x)
