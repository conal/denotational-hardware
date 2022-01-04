{-# OPTIONS --safe --without-K #-}

open import Level

module Functions.Raw (ℓ : Level) where

import Function as F
open import Data.Product as × using (_,_; proj₁; proj₂; <_,_>)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Data.Empty.Polymorphic using (⊥-elim)
import Data.Bool as B

open import Categorical.Raw
open import Categorical.Equiv

open import Functions.Type ℓ public

module →-raw-instances where

  instance

    category : Category Function
    category = record { id = F.id ; _∘_ = F._∘′_ }

    cocartesian : Cocartesian Function
    cocartesian = record { void = ⊥-elim ; _▿_ = [_,_] ; inl = inj₁ ; inr = inj₂ }

    cartesian : Cartesian Function
    cartesian = record { _▵_ = <_,_> ; exl = proj₁ ; exr = proj₂ }

    -- indexedCartesian : ∀ {I : Set ℓ} → IndexedCartesian I Function
    -- indexedCartesian = record
    --   { △  = λ fs x i → fs i x
    --   ; ex = λ i xs → xs i
    --   }

    cartesianClosed : CartesianClosed Function
    cartesianClosed = record { curry = ×.curry ; apply = ×.uncurry id }

    open import HasAlgebra

    semigroup : ∀ {A : Set ℓ} ⦃ _ : HasRawSemigroup A ⦄ → Semigroup Function
    semigroup = record { ⟨∙⟩ = uncurry _∙_ }

    monoid : ∀ {A : Set ℓ} ⦃ _ : HasRawSemigroup A ⦄ ⦃ _ : HasRawMonoid A ⦄ →
      Monoid Function
    monoid = record { ⟨ι⟩ = λ { tt → ι } }

    logic : Logic Function
    logic = record
              { false = λ tt → 𝕗
              ; true  = λ tt → 𝕥
              ; not   = lift₁ B.not
              ; ∧     = uncurry (lift₂ B._∧_)
              ; ∨     = uncurry (lift₂ B._∨_)
              ; xor   = uncurry (lift₂ B._xor_)
              ; cond  = λ (lift c , e , t) → B.if c then t else e
              }

    open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

    -- TODO: move to Relation.Binary.PropositionalEquality.Properties as a PR
    equivalent : Equivalent ℓ Function
    equivalent = record
      { _≈_ = _≗_
      ; equiv = record
          { refl  = λ _ → ≡.refl
          ; sym   = λ f∼g x → ≡.sym (f∼g x)
          ; trans = λ f∼g g∼h x → ≡.trans (f∼g x) (g∼h x)
          }
      }
