{-# OPTIONS --safe --without-K #-}

module Examples.Add.Properties where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Nat

open import Categorical.Equiv
open import Categorical.Raw
open import Functions.Type
open import Functions.Raw

open import Examples.Add

bval : Bool → ℕ
bval = bool 0 1

val : ∀ n → Vˡ Bool n → ℕ
val  zero      tt    = zero
val (suc n) (bs , b) = bval b + val n bs * 2

private
  add : ℕ × ℕ → ℕ
  add = uncurry _+_

open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)
open ≡-Reasoning

module halfAdd where

  i : Bool × Bool → ℕ × ℕ
  i = bval ⊗ bval

  o : Bool × Bool → ℕ
  o (cₒ , s) = val 2 ((tt , cₒ) , s)

  -- TODO: Define _、_ to be *left-associative* _,_
  -- I'll have to replace the current use of _、_

  _ : i (𝕗 , 𝕥) ≡ (0 , 1)
  _ = refl≡

  _ : o (𝕥 , 𝕥) ≡ 3
  _ = refl≡

  spec : o ∘ halfAdd ≈ add ∘ i
  spec {𝕗 , 𝕗} = refl≡
  spec {𝕗 , 𝕥} = refl≡
  spec {𝕥 , 𝕗} = refl≡
  spec {𝕥 , 𝕥} = refl≡

module fullAdd where

  -- fullAdd : Bool × Bool ⇨ᶜ Bool
  -- fullAdd = second ∨ ∘ inAssocˡ′ halfAdd ∘ second halfAdd
  -- 
  -- λ (c , (a , b)) → let (p , d) = halfAdd (a , b)
  --                       (q , e) = halfAdd (c , p) in (q , e ∨ d)

  i : (Bool × Bool) × Bool → (ℕ × ℕ) × ℕ
  i = (bval ⊗ bval) ⊗ bval

  o : Bool × Bool → ℕ
  o (cₒ , s) = val 2 ((tt , cₒ) , s)

  spec : o ∘ fullAdd ≈ (add ∘ first add) ∘ i

  spec {(𝕗 , 𝕗) , 𝕗} = refl≡
  spec {(𝕗 , 𝕗) , 𝕥} = refl≡
  spec {(𝕗 , 𝕥) , 𝕗} = refl≡
  spec {(𝕗 , 𝕥) , 𝕥} = refl≡
  spec {(𝕥 , 𝕗) , 𝕗} = refl≡
  spec {(𝕥 , 𝕗) , 𝕥} = refl≡
  spec {(𝕥 , 𝕥) , 𝕗} = refl≡
  spec {(𝕥 , 𝕥) , 𝕥} = refl≡

module rippleAdd where

  -- rippleAdd : ∀ n → Vˡ (Bool × Bool) n ⇨ᶜ Vˡ Bool n

  module _ (n : ℕ) where

    bvalₙ : Bool → ℕ
    bvalₙ b = (2 ^ n) * bval b

    valₙ : Vˡ Bool n → ℕ
    valₙ = val n

    i : Vˡ (Bool × Bool) n × Bool → (ℕ × ℕ) × ℕ
    i = (valₙ ⊗ valₙ) ∘ unzipⱽˡ n ⊗ bval

    o : Bool × Vˡ Bool n → ℕ
    o = add ∘ (bvalₙ ⊗ valₙ)

  -- spec : ∀ n → o n ∘ rippleAdd n ≈ (add ∘ first add) ∘ i n
  -- spec n = {!!}

-- TODO: Replace ℕ by Fin (2 ^ n) throughout this module, and leave the carry
-- bit as a bit.
