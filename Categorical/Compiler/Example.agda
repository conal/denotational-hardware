module Categorical.Compiler.Example where

open import Level renaming (zero to lz)

import Categorical.Raw as C
import Categorical.Equiv as C
import Categorical.Laws as C renaming (Category to CategoryLaws)
import Categorical.Homomorphism as C
import Functions as F

open import Data.Nat
open import Data.Product

-- Simplest class of examples: when H is the identity functor.
-- This gives us a pointwise to pointfree conversion
module PointFreeConversion where

  open F.→-instances lz
  open F.→-raw-instances lz
  open F.→-laws-instances lz

  import Categorical.Compiler (F.Function lz)
    ⦃ hₒ = C.id-Hₒ ⦄ ⦃ h = C.id-H ⦄
    ⦃ H = C.id-CategoryH ⦄
    as C2C

  const : ∀{a b}{A : Set a}{B : Set b} → A → B → A
  const f _ = f

  test1 : ℕ → ℕ
  test1 x = x + x
  --    == λ x → _+_ x x
  --    == apply ∘ (λ x → _+_ x) ▵ id
  --    == apply ∘ (apply ∘ (λ x → _+_ ▵ id) ▵ id)
  --    == apply ∘ (apply ∘ ((const _+_) ▵ id) ▵ id)

  test1' : ℕ → ℕ
  test1' = C.apply C.∘ ((C.apply C.∘ (const _+_ C.▵ C.id)) C.▵ C.id)

  tgt1 : C2C.ResultType test1
  tgt1 = test1' , C.refl

-- Now, let us try to pick H : ℕ → Set, whose action on objects is Fin,
-- what would the target look like?
module ToFinite where

  open import Functions lz
  open →-instances
  open →-raw-instances
  open →-laws-instances

  open import Finite
  open finite-object-instances
  open subcategory-instances

  import Categorical.Compiler {obj = ℕ} _⇨_
    as C2C

  import Data.Fin as Fin

  test1 : Fin.Fin 3 → Fin.Fin 4
  test1 Fin.zero    = Fin.zero
  test1 (Fin.suc x) = Fin.suc (Fin.suc x)

  test1' : 3 ⇨ 4
  test1' = {!!}

  tgt1 : C2C.ResultType test1
  tgt1 = test1' , {!!}
