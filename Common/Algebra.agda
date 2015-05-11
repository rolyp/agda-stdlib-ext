module Common.Algebra where

   open import Algebra
   open import Algebra.FunctionProperties
   open import Function
   open import Level hiding (lower)
   open import Relation.Binary

   open import Common.Algebra.Structures

   record Magma c ℓ : Set (suc (c ⊔ ℓ)) where
      infixl 7 _∙_
      field
         Carrier : Set c
         _≈_ : Rel Carrier ℓ
         _∙_ : Op₂ Carrier
         isMagma : IsMagma _≈_ _∙_

      open IsMagma isMagma public

      setoid : Setoid _ _
      setoid = record { isEquivalence = isEquivalence }

   record IdempotentMagma c ℓ : Set (suc (c ⊔ ℓ)) where
      infixl 7 _∙_
      field
         Carrier : Set c
         _≈_ : Rel Carrier ℓ
         _∙_ : Op₂ Carrier
         isIdempotentMagma : IsIdempotentMagma _≈_ _∙_

      open IsIdempotentMagma isIdempotentMagma public

      magma : Magma _ _
      magma = record { isMagma = isMagma }

      open Magma magma public using (setoid)

   record CommutativeSemigroup c ℓ : Set (suc (c ⊔ ℓ)) where
     infixl 7 _∙_
     infix  4 _≈_
     field
       Carrier             : Set c
       _≈_                 : Rel Carrier ℓ
       _∙_                 : Op₂ Carrier
       isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _∙_

     open IsCommutativeSemigroup isCommutativeSemigroup public

     semigroup : Semigroup _ _
     semigroup = record { isSemigroup = isSemigroup }

     open Semigroup semigroup public using (setoid)

   record JoinSemilattice c ℓ : Set (suc (c ⊔ ℓ)) where
      infixr 6 _∨_
      infix  4 _≈_
      field
         Carrier : Set c
         _≈_ : Rel Carrier ℓ
         _∨_ : Op₂ Carrier
         isJoinSemilattice : IsJoinSemilattice _≈_ _∨_

      open IsJoinSemilattice isJoinSemilattice public

      setoid : Setoid _ _
      setoid = record { isEquivalence = isEquivalence }

      commutativeSemigroup : CommutativeSemigroup _ _
      commutativeSemigroup = record {
            Carrier = Carrier;
            _≈_ = _≈_;
            _∙_ = _∨_;
            isCommutativeSemigroup = isCommutativeSemigroup
         }

      idempotentMagma : IdempotentMagma _ _
      idempotentMagma = record {
            Carrier = Carrier;
            _≈_ = _≈_;
            _∙_ = _∨_;
            isIdempotentMagma = record {
                  isMagma = record { isEquivalence = isEquivalence; ∙-cong = ∙-cong };
                  idem = IsJoinSemilattice.idem isJoinSemilattice
               }
         }

   record BoundedJoinSemilattice c ℓ : Set (suc (c ⊔ ℓ)) where
      infixr 6 _∨_
      infix  4 _≈_
      field
         Carrier : Set c
         _≈_ : Rel Carrier ℓ
         _∨_ : Op₂ Carrier
         ⊥ : Carrier
         isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _∨_ ⊥

      open IsBoundedJoinSemilattice isBoundedJoinSemilattice public

      setoid : Setoid _ _
      setoid = record { isEquivalence = isEquivalence }

      commutativeMonoid : CommutativeMonoid _ _
      commutativeMonoid = record {
            Carrier = Carrier;
            _≈_ = _≈_;
            _∙_ = _∨_;
            ε = ⊥;
            isCommutativeMonoid = isCommutativeMonoid
         }

   record GaloisConnection
      {c} {ℓ₁} {ℓ₂} (Dom : Poset c ℓ₁ ℓ₂) (Codom : Poset c ℓ₁ ℓ₂) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
      constructor ⟪_,_~_⟫

      field
         f» : Poset.Carrier Dom → Poset.Carrier Codom
         f« : Poset.Carrier Codom → Poset.Carrier Dom
         isGaloisConnection : IsGaloisConnection Dom Codom f» f«
