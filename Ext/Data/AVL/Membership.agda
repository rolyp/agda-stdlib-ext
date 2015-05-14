open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

-- Based on code by Vít Šefl at http://stackoverflow.com/questions/21081583.
module Ext.Data.AVL.Membership
   {k v ℓ}
   {Key : Set k}
   (Value : Key → Set v)
   {_<_ : Rel Key ℓ}
   (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

   open import Data.AVL Value isStrictTotalOrder; open Extended-key; open Height-invariants
   open import Data.Empty
   open import Data.Nat hiding (_⊔_; compare; _≮_; _<_)
   open import Data.Product
   open import Level

   open IsStrictTotalOrder isStrictTotalOrder

   private
      _≮_ : Rel Key ℓ
      x ≮ y = ¬ x < y

   open Indexed

   data _∈_ {l u} (k′ : Key) : ∀ {bal} → Indexed.Tree l u bal → Set (k ⊔ v ⊔ ℓ) where
      here : ∀ {hₗ hᵣ} v {tₗ : Indexed.Tree l [ k′ ] hₗ} {tᵣ : Indexed.Tree [ k′ ] u hᵣ} {bal : hₗ ∼ hᵣ} →
             k′ ∈ node (k′ , v) tₗ tᵣ bal
      left : ∀ {hₗ hᵣ k v} {tₗ : Indexed.Tree l [ k ] hₗ} {tᵣ : Indexed.Tree [ k ] u hᵣ} {bal : hₗ ∼ hᵣ} →
             k′ < k → k′ ∈ tₗ → k′ ∈ node (k , v) tₗ tᵣ bal
      right : ∀ {hₗ hᵣ k v} {tₗ : Indexed.Tree l [ k ] hₗ} {tᵣ : Indexed.Tree [ k ] u hᵣ} {bal : hₗ ∼ hᵣ} →
             k < k′ → k′ ∈ tᵣ → k′ ∈ node (k , v) tₗ tᵣ bal

   get : ∀ {l u h} {k : Key} {t : Indexed.Tree l u h} → k ∈ t → Value k
   get (here v) = v
   get (left _ k∈tₗ) = get k∈tₗ
   get (right _ k∈tᵣ) = get k∈tᵣ

   dichot : ∀ {l u hₗ hᵣ k k′ v} {tₗ : Indexed.Tree l [ k′ ] hₗ} {tᵣ : Indexed.Tree [ k′ ] u hᵣ} {bal : hₗ ∼ hᵣ} →
            k ∈ node (k′ , v) tₗ tᵣ bal → (k′ ≮ k → k ≢ k′ → k ∈ tₗ) × (k ≮ k′ → k ≢ k′ → k ∈ tᵣ)
   dichot (here v) = (λ _ k≢k′ → ⊥-elim (k≢k′ refl)) , λ _ k≢k′ → ⊥-elim (k≢k′ refl)
   dichot (left k<k′ k∈tₗ) = (λ _ _ → k∈tₗ) , λ k≮k′ _ → ⊥-elim (k≮k′ k<k′)
   dichot (right k′<k k∈tᵣ) = (λ k′≮k _ → ⊥-elim (k′≮k k′<k)) , λ _ _ → k∈tᵣ

   find : ∀ {l u bal} (k : Key) → (t : Indexed.Tree l u bal) → Dec (k ∈ t)
   find k (Indexed.leaf l<u) = no λ ()
   find k (node (k′ , _) _ _ _) with compare k k′
   find k (node (_ , _) tₗ _ bal) | tri< k<k′ k≢k′ k′≮k with find k tₗ
   ... | no k∉tₗ = no (λ k∈t → k∉tₗ (proj₁ (dichot {bal = bal} k∈t) k′≮k k≢k′))
   ... | yes k∈tₗ = yes (left {bal = bal} k<k′ k∈tₗ)
   find k (node (k′ , v) _ _ bal) | tri≈ _ k≡k′ _ rewrite P.sym k≡k′ = yes (here v {bal = bal})
   find k (node (_ , _) _ tᵣ bal) | tri> k≮k′ k≢k′ k′<k with find k tᵣ
   ... | no k∉tᵣ = no (λ k∈t → k∉tᵣ (proj₂ (dichot {bal = bal} k∈t) k≮k′ k≢k′))
   ... | yes k∈tᵣ = yes (right {bal = bal} k′<k k∈tᵣ)
