module Relation.Binary.Lattice.Residuated where

open import Level
open import Algebra.FunctionProperties using (Op₂)
open import Algebra.Structures using (IsMonoid)
open import Algebra using (Monoid)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.Lattice using (Lattice; IsLattice)
open import Data.Product


LeftResidual : ∀ {c ℓ₂} {L : Set c}
                → (_≤_ : Rel L ℓ₂) -- The partial order.
                → (_∙_ : Op₂ L)    -- The monoid operation.
                → (_◁_ : Op₂ L)    -- The left residual.
                → Set (c ⊔ ℓ₂)
LeftResidual _≤_ _∙_ _◁_ = ∀ y z → (((z ◁ y) ∙ y) ≤ z) × (Maximum _≤_ (z ◁ y))

RightResidual : ∀ {c ℓ₂} {L : Set c}
                → (_≤_ : Rel L ℓ₂) -- The partial order.
                → (_∙_ : Op₂ L)    -- The monoid operation.
                → (_▷_ : Op₂ L)    -- The right residual.
                → Set (c ⊔ ℓ₂)
RightResidual _≤_ _∙_ _▷_ = ∀ x z → ((x ∙ (x ▷ z)) ≤ z) × (Maximum _≤_ (x ▷ z))


record IsResiduated {c ℓ₁ ℓ₂} {L : Set c}
                    (_≈_ : Rel L ℓ₁) -- The underlying equality.
                    (_≤_ : Rel L ℓ₂) -- The partial order.
                    (_∨_ : Op₂ L)    -- The join operation.
                    (_∧_ : Op₂ L)    -- The meet operation.
                    (_∙_ : Op₂ L)    -- The monoid operation.
                    (ε   : L)        -- The identity element.
                    (_▷_ : Op₂ L)    -- The right residual.
                    (_◁_ : Op₂ L)    -- The left residual.
                    : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
        isLattice : IsLattice _≈_ _≤_ _∨_ _∧_
        isMonoid  : IsMonoid _≈_ _∙_ ε
        isLeftResidual : LeftResidual _≤_ _∙_ _◁_
        isRightResidual : RightResidual _≤_ _∙_ _▷_
        ∙-monotonic : _∙_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_


    -- ∀ x y x
    --           y ≤ x ▷ z
    --     ⇔ x ∙ y ≤     z
    --     ⇔ x     ≤     z ◁ y

    module Pre = IsPreorder (IsPartialOrder.isPreorder (IsLattice.isPartialOrder isLattice))

    -- theorems about the residuals, requires _∙_ to be monotonic
    ∙-at-left : ∀ x y z
        → y ≤ (x ▷ z)
        → (x ∙ y) ≤ z
    ∙-at-left x y z P = Pre.trans (∙-monotonic Pre.refl P) (proj₁ (isRightResidual x z))

    ∙-at-right : ∀ x y z
        → x ≤ (z ◁ y)
        → (x ∙ y) ≤ z
    ∙-at-right x y z P = Pre.trans (∙-monotonic P Pre.refl) (proj₁ (isLeftResidual y z))

    apply-▷ : ∀ x y z
        → (x ∙ y) ≤ z
        → y ≤ (x ▷ z)
    apply-▷ x y z P = proj₂ (isRightResidual x z) y

    apply-◁ : ∀ x y z
        → (x ∙ y) ≤ z
        → x ≤ (z ◁ y)
    apply-◁ x y z P = proj₂ (isLeftResidual y z) x

    

    -- other modules

    monoid : Monoid c ℓ₁
    monoid = record { isMonoid = isMonoid }

    lattice : Lattice c ℓ₁ ℓ₂
    lattice = record { isLattice = isLattice }


record Residuated c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix  4 _≈_ _≤_
    infixr 6 _∨_
    infixr 7 _∧_
    infixr 5 _∙_
    infixr 8 _▷_ _◁_

    field
        Carrier   : Set c
        _≈_       : Rel Carrier ℓ₁  -- The underlying equality.
        _≤_       : Rel Carrier ℓ₂  -- The partial order.
        _∨_       : Op₂ Carrier     -- The join operation.
        _∧_       : Op₂ Carrier     -- The meet operation.
        _∙_       : Op₂ Carrier     -- The monoid operation.
        ε         : Carrier         -- The identity element.

        _▷_      : Op₂ Carrier      -- The right residual.
        _◁_      : Op₂ Carrier      -- The left residual.
        isResiduated : IsResiduated _≈_ _≤_ _∨_ _∧_ _∙_ ε _▷_ _◁_
