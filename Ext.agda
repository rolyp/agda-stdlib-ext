module Ext where

   open import Algebra.FunctionProperties
   open import Algebra.Structures
   open import Data.Product hiding (_-×-_; map; zip)
   open import Data.Sum hiding (map)
   open import Data.Unit
   open import Function
   open import Level
   open import Relation.Binary
   open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to ≅-refl)
   open import Relation.Binary.PropositionalEquality as P using (_≡_; subst)
   open import Relation.Nullary

   -- Extensional equivalence for functions.
   infix 4 _≃ₑ_
   _≃ₑ_ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : A → Set 𝑏} (f g : (x : A) → B x) → Set _
   f ≃ₑ g = ∀ x → f x ≡ g x

   ≃ₑ-sym : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : A → Set 𝑏} → Symmetric (_≃ₑ_ {B = B})
   ≃ₑ-sym = _∘_ P.sym

   ≃ₑ-equiv : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : A → Set 𝑏} → IsEquivalence (_≃ₑ_ {B = B})
   ≃ₑ-equiv =
      record {
         refl = λ _ → P.refl;
         sym = ≃ₑ-sym;
         trans = λ { {i = f} {g} {h} f≃g g≃h x → P.trans (f≃g x) (g≃h x)}
      }

   subst₃ : ∀ {𝑎 𝑏 𝑐 𝑝} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} (P : A → B → C → Set 𝑝)
         {x₁ x₂ y₁ y₂ z₁ z₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
   subst₃ P P.refl P.refl P.refl p = p

   ≅-subst₃ : ∀ {𝑎 𝑏 𝑐 𝑝} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} (P : A → B → C → Set 𝑝) →
              ∀ {x₁ x₂ y₁ y₂ z₁ z₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → z₁ ≅ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
   ≅-subst₃ P ≅-refl ≅-refl ≅-refl p = p

   cong₃ : ∀ {𝑎 𝑏 𝑐 𝑑} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} {D : Set 𝑑}
           (f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a ≡ f y v b
   cong₃ f P.refl P.refl P.refl = P.refl

   ≅-cong₃ : ∀ {𝑎 𝑏 𝑐 𝑑} {A : Set 𝑎} {B : A → Set 𝑏} {C : ∀ x → B x → Set 𝑐} {D : ∀ x → (y : B x) → C x y → Set 𝑑}
             {x y u v w z}
           (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → w ≅ z → f x u w ≅ f y v z
   ≅-cong₃ f ≅-refl ≅-refl ≅-refl = ≅-refl

   -- From http://stackoverflow.com/questions/24139810.
   hcong : ∀ {𝑖 𝑎 𝑏} {I : Set 𝑖} (A : I → Set 𝑎) {B : {k : I} → A k → Set 𝑏}
           {i j : I} {x : A i} {y : A j} → i ≡ j → (f : {k : I} → (x : A k) → B x) → x ≅ y → f x ≅ f y
   hcong _ P.refl _ ≅-refl = ≅-refl

   -- Dependently-typed version of cong₂ where f is proof-irrelevant in its second argument.
   cong₂̣ : ∀ {𝑎 𝑏 𝑐} {A : Set 𝑎} {B : A → Set 𝑏} {C : Set 𝑐}
            (f : (a : A) → .(B a) → C) {x y} → x ≡ y → .{u : B x} → .{v : B y} → f x u ≡ f y v
   cong₂̣ f P.refl = P.refl

   swap⁺ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} → A ⊎ B → B ⊎ A
   swap⁺ (inj₁ a) = inj₂ a
   swap⁺ (inj₂ b) = inj₁ b

   -- Direct product of binary relations. Preserves reflexivity, transitivity, symmetry and decidability,
   -- plus irreflexivity and antisymmetry, but we only prove the first four.
   _-×-_ : ∀ {𝑎 𝑏 𝑐 𝑑 ℓ₁ ℓ₂} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} {D : Set 𝑑} →
           REL A C ℓ₁ → REL B D ℓ₂ → A × B → C × D → Set (ℓ₁ ⊔ ℓ₂)
   (R -×- S) (a , b) (c , d) = R a c × S b d

   ×-preserves-isEquiv : {𝑎 𝑏 ℓ₁ ℓ₂ : Level} {A : Set 𝑎} {B : Set 𝑏} {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} →
                         IsEquivalence ≈₁ → IsEquivalence ≈₂ → IsEquivalence (≈₁ -×- ≈₂)
   ×-preserves-isEquiv equiv-≈₁ equiv-≈₂ = record {
         refl = refl₁ , refl₂;
         sym = Data.Product.map sym₁ sym₂;
         trans = λ { (a≈c , b≈d) (c≈e , d≈f) → trans₁ a≈c c≈e , trans₂ b≈d d≈f }
      } where
         open IsEquivalence equiv-≈₁ renaming (refl to refl₁; sym to sym₁; trans to trans₁)
         open IsEquivalence equiv-≈₂ renaming (refl to refl₂; sym to sym₂; trans to trans₂)

   ×-preserves-dec : {𝑎 𝑏 ℓ₁ ℓ₂ : Level} {A : Set 𝑎} {B : Set 𝑏} {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} →
                     Decidable ≈₁ → Decidable ≈₂ → Decidable (≈₁ -×- ≈₂)
   ×-preserves-dec ≈₁? ≈₂? (a , b) (a′ , b′) with ≈₁? a a′ | ≈₂? b b′
   ... | yes a≈a′ | yes b≈b′ = yes (a≈a′ , b≈b′)
   ... | yes _ | no b≉b′ = no (b≉b′ ∘ proj₂)
   ... | no a≉a′ | yes _ = no (a≉a′ ∘ proj₁)
   ... | no a≉a′ | no _ = no (a≉a′ ∘ proj₁)

   -- Commutative monoids are closed under products.
   cm-× : ∀ {𝑎} {A : Set 𝑎} {∙₁ : Op₂ A} {ε₁ : A} → IsCommutativeMonoid _≡_ ∙₁ ε₁ →
          ∀ {𝑏} {B : Set 𝑏} {∙₂ : Op₂ B} {ε₂ : B} → IsCommutativeMonoid _≡_ ∙₂ ε₂ →
          IsCommutativeMonoid _≡_ (Data.Product.zip ∙₁ ∙₂) (ε₁ , ε₂)
   cm-× {∙₁ = ∙₁} cm₁ {∙₂ = ∙₂} cm₂ = record {
         isSemigroup = record {
               isEquivalence = P.isEquivalence;
               assoc = λ {
                  (σ₁ , σ₂) (σ₁′ , σ₂′) (σ₁″ , σ₂″) → P.cong₂ _,_ (assoc cm₁ σ₁ σ₁′ σ₁″) (assoc cm₂ σ₂ σ₂′ σ₂″)
               };
               ∙-cong = λ {
                  {x} {.x} {u} {.u} P.refl P.refl → P.cong₂ (Data.Product.zip ∙₁ ∙₂) P.refl P.refl
               }
            };
         identityˡ = λ { (σ₁ , σ₂) → P.cong₂ _,_ (identityˡ cm₁ σ₁) (identityˡ cm₂ σ₂) };
         comm = λ { (σ₁ , σ₂) (σ₁′ , σ₂′) → P.cong₂ _,_ (comm cm₁ σ₁ σ₁′) (comm cm₂ σ₂ σ₂′) }
      } where
         open IsCommutativeMonoid
