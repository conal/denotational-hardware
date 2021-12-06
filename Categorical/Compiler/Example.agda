module Categorical.Compiler.Example where

open import Level

open import Categorical.Raw
open import Categorical.Laws
open import Categorical.Homomorphism
open import Functions 0ℓ

open import Data.Nat
open import Data.Product
import Data.Bool as Bool

-- Simplest class of examples: when H is the identity functor.
-- This gives us a pointwise to pointfree conversion
module PointFreeConversion where

  open import Categorical.IdInstances Function
  import Categorical.Compiler Function
    ⦃ hₒ = id-Hₒ ⦄ ⦃ h = id-H ⦄
    ⦃ H = id-CategoryH ⦄
    as C2C
  open import Function using (const)

  test1 : ℕ → ℕ
  test1 x = x + x
  --    == λ x → _+_ x x
  --    == apply ∘ (λ x → _+_ x) ▵ id
  --    == apply ∘ (apply ∘ (λ x → _+_ ▵ id) ▵ id)
  --    == apply ∘ (apply ∘ ((const _+_) ▵ id) ▵ id)

  test1' : ℕ → ℕ
  test1' = apply ∘ ((apply ∘ (const _+_ ▵ id)) ▵ id)

  -- Conal: I'd use uncurried addition, in which case the translation is
  -- simpler, obviating CartesianClosed (often unavailable).

  tgt1 : C2C.ResultType test1
  tgt1 = test1' , refl

  test2 : ℕ → ℕ
  test2 x = x

  tgt2 : C2C.ResultType test2
  tgt2 = (id ,  refl)

  tgt2' : C2C.ResultType test2
  tgt2' = C2C.invert Bool.false test2

-- Now, let us try to pick H : ℕ → Set, whose action on objects is Fin,
-- what would the target look like?
module ToFinite where

  open import Finite
  open import Categorical.Compiler {obj = ℕ} _⇨_

  import Data.Fin as Fin

  test1 : Fin.Fin 3 → Fin.Fin 4
  test1 Fin.zero    = Fin.zero
  test1 (Fin.suc x) = Fin.suc (Fin.suc x)

  test1' : 3 ⇨ 4
  test1' = {!!}

  tgt1 : ResultType test1
  tgt1 = test1' , {!!}
