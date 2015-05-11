open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P hiding ([_])

-- Used Vít Šefl's setoid version of this for a while. However I've dropped the convention of
-- parameterising over equality, instead preferring propositional equality. I've seen this
-- approach used in several Agda libraries.
module Common.Data.Extended-key
   {k ℓ}
   {Key : Set k}
   {_<_ : Rel Key ℓ}
   (isStrictTotalOrder′ : IsStrictTotalOrder _≡_ _<_) where

   open import Data.Empty
   open import Data.Product
   open import Data.Unit
   open import Function
   open import Level

   infix 4 _<⁺_

   -- This and the proof of transitivity taken from Data.AVL.
   data Key⁺ : Set k where
      ⊥⁺ ⊤⁺ : Key⁺
      [_] : (k : Key) → Key⁺

   _<⁺_ : Key⁺ → Key⁺ → Set ℓ
   ⊥⁺ <⁺ [ _ ] = Lift ⊤
   ⊥⁺ <⁺ ⊤⁺ = Lift ⊤
   [ x ] <⁺ [ y ] = x < y
   [ _ ] <⁺ ⊤⁺ = Lift ⊤
   _ <⁺ _ = Lift ⊥

   -- Strict total orders are closed under λ A → A + 2.
   isStrictTotalOrder : IsStrictTotalOrder _≡_ _<⁺_
   isStrictTotalOrder = record {
         isEquivalence = isEquivalence;
         trans = λ {x} {y} {z} → trans⁺ x {y} {z};
         compare = compare⁺;
         <-resp-≈ = (λ { {x} P.refl → id }) , λ { {x} refl → id }
      } where
         trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u
         trans⁺ [ l ] {m = [ m ]} {u = [ u ]} l<m m<u = IsStrictTotalOrder.trans isStrictTotalOrder′ l<m m<u --
         trans⁺ ⊥⁺ {u = [ _ ]} _ _ = _
         trans⁺ ⊥⁺ {u = ⊤⁺} _ _ = _
         trans⁺ [ _ ] {u = ⊤⁺} _ _ = _
         trans⁺ _ {m = ⊥⁺} {u = ⊥⁺} _ (lift ())
         trans⁺ _ {m = [ _ ]} {u = ⊥⁺} _ (lift ())
         trans⁺ _ {m = ⊤⁺} {u = ⊥⁺} _ (lift ())
         trans⁺ [ _ ] {m = ⊥⁺} {u = [ _ ]} (lift ()) _
         trans⁺ [ _ ] {m = ⊤⁺} {u = [ _ ]} _ (lift ())
         trans⁺ ⊤⁺ {m = ⊥⁺} (lift ()) _
         trans⁺ ⊤⁺ {m = [ _ ]} (lift ()) _
         trans⁺ ⊤⁺ {m = ⊤⁺} (lift ()) _

         -- Do I really need this? Or am I just being stupid?
         [-]-injective : ∀ {x y} → [ x ] ≡ [ y ] → x ≡ y
         [-]-injective refl = refl

         compare⁺ : Trichotomous _≡_ _<⁺_
         compare⁺ ⊥⁺ ⊥⁺ = tri≈ lower refl lower
         compare⁺ ⊥⁺ ⊤⁺ = tri< _ (λ ()) lower
         compare⁺ ⊥⁺ [ y ] = tri< _ (λ ()) lower
         compare⁺ ⊤⁺ ⊥⁺ = tri> lower (λ ()) _
         compare⁺ ⊤⁺ ⊤⁺ = tri≈ lower refl lower
         compare⁺ ⊤⁺ [ y ] = tri> lower (λ ()) _
         compare⁺ [ x ] ⊥⁺ = tri> lower (λ ()) _
         compare⁺ [ x ] ⊤⁺ = tri< _ (λ ()) lower
         compare⁺ [ x ] [ y ] with IsStrictTotalOrder.compare isStrictTotalOrder′ x y
         ... | tri< x<⁺y x≢y y≮x = tri< x<⁺y (x≢y ∘ [-]-injective) y≮x
         compare⁺ [ x ] [ .x ] | tri≈ x≮y refl y≮x = tri≈ x≮y refl y≮x
         ... | tri> x≮y x≢y y<⁺x = tri> x≮y (x≢y ∘ [-]-injective) y<⁺x
