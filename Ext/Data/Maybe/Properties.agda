module Ext.Data.Maybe.Properties where

   open import Data.Maybe
   open import Data.Product
   open import Function
   open import Algebra.FunctionProperties
   open import Algebra.Structures
   open import Relation.Binary
   open import Relation.Binary.PropositionalEquality as P

   open import Ext.Algebra.Structures

   -- Lift a magma over A to Maybe A in the obvious way.
   ∙-Maybe : ∀ {a} {A : Set a} → Op₂ A → Op₂ (Maybe A)
   ∙-Maybe _∙_ (just a) (just a′ ) = just (a ⟨ _∙_ ⟩ a′)
   ∙-Maybe _∙_ nothing (just a) = just a
   ∙-Maybe _∙_ (just a) nothing = just a
   ∙-Maybe _∙_ nothing nothing = nothing

   magma-Maybe : ∀ {𝑎} {A : Set 𝑎} {∙ : Op₂ A} → IsMagma _≡_ ∙ → IsMagma _≡_ (∙-Maybe ∙)
   magma-Maybe {∙ = ∙} m = record {
         isEquivalence = P.isEquivalence;
         ∙-cong = ∙-cong′
      } where
         open IsMagma m

         ∙-cong′ : (∙-Maybe ∙) Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
         ∙-cong′ {just x} {just .x} {just u} {just .u} P.refl P.refl = cong just (∙-cong P.refl P.refl)
         ∙-cong′ {just x} {just .x} {nothing} {nothing} P.refl _ = P.refl
         ∙-cong′ {nothing} {nothing} {just x} {just .x} _ P.refl = P.refl
         ∙-cong′ {nothing} {nothing} {nothing} {nothing} _ _ = P.refl
         ∙-cong′ {just _} {nothing} {_} {_} () _
         ∙-cong′ {nothing} {just _} {_} {_} () _
         ∙-cong′ {_} {_} {just _} {nothing} _ ()
         ∙-cong′ {_} {_} {nothing} {just _} _ ()

   -- Extend any monoid over A to Maybe A.
   m-Maybe : ∀ {𝑎} {A : Set 𝑎} {∙ : Op₂ A} {ε : A} →
             IsMonoid _≡_ ∙ ε → IsMonoid _≡_ (∙-Maybe ∙) nothing
   m-Maybe {∙ = ∙} m = record {
         isSemigroup = record {
               isEquivalence = IsMagma.isEquivalence magma;
               assoc = assoc′;
               ∙-cong = IsMagma.∙-cong magma
            };
         identity = identityˡ , identityʳ
      } where
         open IsMonoid m
         magma = magma-Maybe record { isEquivalence = P.isEquivalence; ∙-cong = ∙-cong }

         identityˡ : LeftIdentity _≡_ nothing (∙-Maybe ∙)
         identityˡ (just _) = P.refl
         identityˡ nothing = P.refl

         identityʳ : RightIdentity _≡_ nothing (∙-Maybe ∙)
         identityʳ (just _) = P.refl
         identityʳ nothing = P.refl

         assoc′ : Associative _≡_ (∙-Maybe ∙)
         assoc′ (just a₁) (just a₂) (just a₃) = cong just (assoc a₁ a₂ a₃) --
         assoc′ (just _) (just _) nothing = P.refl
         assoc′ (just _) nothing (just _) = P.refl
         assoc′ nothing (just _) (just _) = P.refl
         assoc′ (just _) nothing nothing = P.refl
         assoc′ nothing (just _) nothing = P.refl
         assoc′ nothing nothing (just _) = P.refl
         assoc′ nothing nothing nothing = P.refl

   -- Extend any commutative monoid over A to Maybe A.
   cm-Maybe : ∀ {𝑎} {A : Set 𝑎} {∙ : Op₂ A} {ε : A} →
              {{_ : IsCommutativeMonoid _≡_ ∙ ε}} → IsCommutativeMonoid _≡_ (∙-Maybe ∙) nothing
   cm-Maybe {∙ = ∙} {{cm}} = record {
         isSemigroup = IsMonoid.isSemigroup m-Maybe′;
         identityˡ = proj₁ (IsMonoid.identity m-Maybe′);
         comm = comm′
      } where
         open IsCommutativeMonoid cm
         m-Maybe′ = m-Maybe isMonoid

         comm′ : Commutative _≡_ (∙-Maybe ∙)
         comm′ (just x) (just y) = cong just (comm x y)
         comm′ (just _) nothing = P.refl
         comm′ nothing (just _) = P.refl
         comm′ nothing nothing = P.refl

   -- Extend any idempotent operation over A to Maybe A.
   idem-Maybe : ∀ {𝑎} {A : Set 𝑎} {∙ : Op₂ A} → Idempotent _≡_ ∙ → Idempotent _≡_ (∙-Maybe ∙)
   idem-Maybe idem-∙ (just x) = cong just (idem-∙ x)
   idem-Maybe idem-∙ nothing = P.refl

   -- Kleisi extension, plus a binary variant for convenience.
   _⁺ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} → (A → Maybe B) → Maybe A → Maybe B
   (f ⁺) nothing = nothing
   (f ⁺) (just x) = f x

   _⁺₂ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} → (A → A → Maybe B) → Maybe A → Maybe A → Maybe B
   _⁺₂ f nothing _ = nothing
   _⁺₂ f _ nothing = nothing
   _⁺₂ f (just x) (just y) = f x y

   -- If A has a decidable equality, there is a trivial semilattice over Maybe A.
   module Semilattice
      {A : Set}
      (_≟_ : Decidable {A = A} _≡_) where

      open import Data.Empty
      open import Relation.Nullary

      private
         _⊓′_ : A → A → Maybe A
         x ⊓′ y with x ≟ y
         ... | no _ = nothing
         ... | yes _ = just x

      _⊓_ : Op₂ (Maybe A)
      _⊓_ = _⊓′_ ⁺₂

      ⊓-idem : Idempotent _≡_ _⊓_
      ⊓-idem nothing = refl
      ⊓-idem (just x) with x ≟ x
      ... | no x≢x = ⊥-elim (x≢x refl)
      ... | yes _ = refl

      ⊓-comm : Commutative _≡_ _⊓_
      ⊓-comm nothing nothing = refl
      ⊓-comm nothing (just _) = refl
      ⊓-comm (just _) nothing = refl
      ⊓-comm (just x) (just y) with x ≟ y | y ≟ x
      ... | no _ | no _ = refl
      ... | no x≢y | yes y≡x = ⊥-elim (x≢y (sym y≡x))
      ... | yes x≡y | no y≢x = ⊥-elim (y≢x (sym x≡y))
      ⊓-comm (just x) (just .x) | yes refl | yes refl = refl

      nothing-leftZ : LeftZero _≡_ nothing _⊓_
      nothing-leftZ nothing = refl
      nothing-leftZ (just _) = refl

      nothing-rightZ : RightZero _≡_ nothing _⊓_
      nothing-rightZ nothing = refl
      nothing-rightZ (just _) = refl

      ⊓-cong : _⊓_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
      ⊓-cong {x} {.x} {u} {.u} refl refl = refl

      private
         ⊓′-assoc : (x y z : A) → (x ⊓′ y) ⊓ (just z) ≡ (just x) ⊓ (y ⊓′ z)
         ⊓′-assoc x y z with x ≟ y | y ≟ z
         ... | no _ | no _ = refl
         ... | no x≢y | yes _ with x ≟ y
         ... | no _ = refl
         ... | yes x≡y = ⊥-elim (x≢y x≡y)
         ⊓′-assoc x _ z | yes x≡y | no y≢z with x ≟ z
         ... | no _ = refl
         ... | yes x≡z = ⊥-elim (y≢z (trans (sym x≡y) x≡z))
         ⊓′-assoc x y z | yes x≡y | yes y≡z with x ≟ z | x ≟ y
         ... | no _ | no _ = refl
         ... | no x≢z | yes _ = ⊥-elim (x≢z (trans x≡y y≡z))
         ... | yes _ | no x≢y = ⊥-elim (x≢y x≡y)
         ... | yes _ | yes _ = refl

      ⊓-assoc : Associative _≡_ _⊓_
      ⊓-assoc nothing nothing nothing = refl
      ⊓-assoc nothing nothing (just _) = refl
      ⊓-assoc nothing (just _) nothing = refl
      ⊓-assoc (just _) nothing nothing = refl
      ⊓-assoc (just _)  nothing (just _) = refl
      ⊓-assoc nothing (just y) (just z) =
         begin
            (nothing ⊓ just y) ⊓ just z
         ≡⟨ sym (⊓-cong {x = nothing} {u = just z} (nothing-leftZ (just y)) refl) ⟩
            nothing ⊓ just z
         ≡⟨ nothing-leftZ (just z) ⟩
            nothing
         ≡⟨ sym (nothing-leftZ (just y ⊓ just z)) ⟩
            nothing ⊓ (just y ⊓ just z)
         ∎ where open import Relation.Binary.EqReasoning (P.setoid _)
      ⊓-assoc (just x) (just y) nothing =
         begin
            (just x ⊓ just y) ⊓ nothing
          ≡⟨ nothing-rightZ (just x ⊓ just y) ⟩
            nothing
         ≡⟨ sym (nothing-rightZ (just x)) ⟩
          just x ⊓ nothing
         ≡⟨ ⊓-cong {x = just x} {u = nothing} refl (sym (nothing-rightZ (just y))) ⟩
            just x ⊓ (just y ⊓ nothing)
         ∎ where open import Relation.Binary.EqReasoning (P.setoid _)
      ⊓-assoc (just x) (just y) (just z) rewrite ⊓′-assoc x y z = refl

      isMeetSemilattice : IsMeetSemilattice _≡_ _⊓_
      isMeetSemilattice = record {
            isCommutativeSemigroup = record {
                  isSemigroup = record { isEquivalence = isEquivalence; assoc = ⊓-assoc; ∙-cong = ⊓-cong };
                  comm = ⊓-comm
               };
            idem = ⊓-idem
         }

      leftZ : LeftZero _≡_ nothing _⊓_
      leftZ (just _) = refl
      leftZ nothing = refl

      rightZ : RightZero _≡_ nothing _⊓_
      rightZ (just _) = refl
      rightZ nothing = refl
