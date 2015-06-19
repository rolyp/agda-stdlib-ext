{- TODO: Drop the ≅- prefix for consistency with the standard library. -}
module Ext.Relation.Binary.HeterogeneousEquality where

   open import Relation.Binary.HeterogeneousEquality
   open import Relation.Binary.PropositionalEquality as P

   ≅-subst₃ : ∀ {𝑎 𝑏 𝑐 𝑝} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} (P : A → B → C → Set 𝑝) →
              ∀ {x₁ x₂ y₁ y₂ z₁ z₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → z₁ ≅ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
   ≅-subst₃ P refl refl refl p = p

   ≅-cong₃ : ∀ {𝑎 𝑏 𝑐 𝑑} {A : Set 𝑎} {B : A → Set 𝑏} {C : ∀ x → B x → Set 𝑐} {D : ∀ x → (y : B x) → C x y → Set 𝑑}
             {x y u v w z}
             (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → w ≅ z → f x u w ≅ f y v z
   ≅-cong₃ f refl refl refl = refl

   -- These adapted from http://stackoverflow.com/questions/24139810. Seems that A needs to be explicit.
   ≅-subst✴ : ∀ {𝑖 𝑎 𝑝} {I : Set 𝑖} (A : I → Set 𝑎) (P : ∀ {k} → A k → Set 𝑝)
              {i j} {x₁ : A i} {x₂ : A j} → i ≡ j → x₁ ≅ x₂ → P x₁ → P x₂
   ≅-subst✴ _ _ P.refl refl p = p

   ≅-subst✴₂ : ∀ {𝑖 𝑎 𝑏 𝑝} {I : Set 𝑖} (A : I → Set 𝑎) {B : ∀ {k} → A k → Set 𝑏}
               (P : ∀ {k} (x : A k) → B x → Set 𝑝)
               {i j} {x₁ : A i} {x₂ : A j} {y₁ y₂} → i ≡ j → x₁ ≅ x₂ → y₁ ≅ y₂ → P x₁ y₁ → P x₂ y₂
   ≅-subst✴₂ _ _ P.refl refl refl p = p

   ≅-cong✴ : ∀ {𝑖 𝑎 𝑏} {I : Set 𝑖} (A : I → Set 𝑎) {B : ∀ {k} → A k → Set 𝑏}
             {i j} {x : A i} {y : A j} → i ≡ j → (f : ∀ {k} (x : A k) → B x) → x ≅ y → f x ≅ f y
   ≅-cong✴ _ P.refl _ refl = refl

   ≅-cong✴₂ : ∀ {𝑖 𝑎 𝑏 𝑐} {I : Set 𝑖} (A : I → Set 𝑎) {B : ∀ {k} → A k → Set 𝑏}
              {C : ∀ {k} (x : A k) → B x → Set 𝑐}
              {i j} {x : A i} {y : A j} {u v} → i ≡ j →
              (f : ∀ {k} (x : A k) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
   ≅-cong✴₂ _ P.refl _ refl refl = refl

   ≅-cong✴₃ : ∀ {𝑖 𝑎 𝑏 𝑐 𝑑} {I : Set 𝑖} (A : I → Set 𝑎) {B : ∀ {k} → A k → Set 𝑏}
              {C : ∀ {k} (x : A k) → B x → Set 𝑐}
              {D : ∀ {k} (x : A k) (y : B x) → C x y → Set 𝑑}
              {i j} {x : A i} {y : A j} {u v w z} → i ≡ j →
              (f : ∀ {k} (x : A k) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → w ≅ z → f x u w ≅ f y v z
   ≅-cong✴₃ _ P.refl _ refl refl refl = refl
