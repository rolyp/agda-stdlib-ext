{-# OPTIONS --sized-types #-}

open import Relation.Binary renaming (IsStrictTotalOrder to IsSTO)
open import Relation.Binary.PropositionalEquality

module Ext.Data.FiniteMap.Properties
   {𝒌 ℓ}
   {Key : Set 𝒌}
   {_<_ : Rel Key ℓ}
   (isStrictTotalOrder : IsSTO _≡_ _<_) where

   import Ext.Data.FiniteMap
   open module FiniteMap {𝒗} (A : Key → Set 𝒗) = Common.Data.FiniteMap A isStrictTotalOrder
   open Indexed using ([]; _↦_∷[_]_)

   _<$′>_ : ∀ {𝒗} {A B : Key → Set 𝒗} {l u} →
           ({k : Key} → A k → B k) → {ι : _} → Indexed.FiniteMap A l u {ι } → Indexed.FiniteMap B l u {ι}
   f <$′> ([] _) = [] _
   f <$′> (k ↦ v ∷[ _ ] m) = k ↦ f v ∷[ _ ] f <$′> m

   _<$>_ : ∀ {𝒗} {A B : Key → Set 𝒗} → ({k : Key} → A k → B k) → FiniteMap A → FiniteMap B
   f <$> (finMap m) = finMap (f <$′> m)
