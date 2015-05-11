module Common where

   open import Algebra.FunctionProperties
   open import Algebra.Structures
   open import Data.Product hiding (_-×-_; map; zip)
   open import Data.Sum hiding (map)
   open import Data.Unit
   open import Function
   open import Level
   open import Relation.Binary
   open import Relation.Binary.PropositionalEquality as P using (_≡_; subst)
   open import Relation.Nullary

   -- Extensional equivalence over functions.
   infix 4 _≃ₑ_
   _≃ₑ_ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : A → Set 𝑏} (f g : (x : A) → B x) → Set _
   f ≃ₑ g = ∀ x → f x ≡ g x

   ≃ₑ-equiv : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : A → Set 𝑏} → IsEquivalence (_≃ₑ_ {B = B})
   ≃ₑ-equiv =
      record {
         refl = λ _ → P.refl;
         sym = _∘_ P.sym;
         trans = λ { {i = f} {g} {h} f≃g g≃h x → P.trans (f≃g x) (g≃h x)}
      }

   cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
           (f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a ≡ f y v b
   cong₃ f P.refl P.refl P.refl = P.refl

   -- Dependently-typed version of cong₂ where f is proof-irrelevant in its second argument.
   cong₂̣ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
            (f : (a : A) → .(B a) → C) {x y} → x ≡ y → .{u : B x} → .{v : B y} → f x u ≡ f y v
   cong₂̣ f P.refl = P.refl

   swap⁺ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} → A ⊎ B → B ⊎ A
   swap⁺ (inj₁ a) = inj₂ a
   swap⁺ (inj₂ b) = inj₁ b

   -- Direct product of binary relations. Preserves reflexivity, transitivity and symmetry, and also irreflexivity
   -- and antisymmetry, but we only prove the first three, plus decidability.
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
