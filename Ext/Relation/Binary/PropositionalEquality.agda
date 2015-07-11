module Ext.Relation.Binary.PropositionalEquality where

   open import Relation.Binary.PropositionalEquality

   subst₃ : ∀ {𝑎 𝑏 𝑐 𝑝} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} (P : A → B → C → Set 𝑝)
         {x₁ x₂ y₁ y₂ z₁ z₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
   subst₃ _ refl refl refl p = p

   cong₃ : ∀ {𝑎 𝑏 𝑐 𝑑} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} {D : Set 𝑑}
           (f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a ≡ f y v b
   cong₃ _ refl refl refl = refl

   -- Dependently-typed version of cong₂ where f is proof-irrelevant in its second argument.
   cong₂̣ : ∀ {𝑎 𝑏 𝑐} {A : Set 𝑎} {B : A → Set 𝑏} {C : Set 𝑐}
            (f : (a : A) → .(B a) → C) {x y} → x ≡ y → .{u : B x} → .{v : B y} → f x u ≡ f y v
   cong₂̣ _ refl = refl
