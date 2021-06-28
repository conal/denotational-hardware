{-# OPTIONS --safe --without-K #-}

-- Arithmetic on bounded unary and binary natural numbers

module Examples.FinBin where

open import Data.Product using (_,_)
open import Data.Fin hiding (_+_)
open import Data.Nat as ℕ hiding (_+_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import Categorical.Equiv
open import Categorical.Raw
open import Functions.Raw

𝟚 : Set
𝟚 = Fin 2

infix 10 𝟚^_
𝟚^_ : ℕ → Set
𝟚^_ k = Fin (2 ^ k)

infixl 6 _+_
_+_ : ∀ {m n} → Fin (suc m) → Fin n → Fin (m ℕ.+ n)
_+_ {m}      zero   j = raise m j
_+_ {suc _} (suc i) j = suc (i + j)

add𝟚 : ∀ k → 𝟚 × 𝟚^ k × 𝟚^ k → 𝟚^ suc k
add𝟚 k (cᵢ , a , b) rewrite +-identityʳ (2 ^ k) = cᵢ + a + b

cons : {m : ℕ} → Fin 2 × Fin m → Fin (2 * m)
cons {m} (b , i) rewrite +-identityʳ m = b + i + i

-- quotRem : ∀ {n} k → Fin (n * k) → Fin k × Fin n

cons⁻¹ : {m : ℕ} → Fin (2 * m) → Fin 2 × Fin m
cons⁻¹ {m} i = swap (quotRem m i)

cons∘cons⁻¹ : {m : ℕ} → cons {m} ∘ cons⁻¹ ≈ id
cons∘cons⁻¹ = {!!}

cons⁻¹∘cons : {m : ℕ} → cons⁻¹ ∘ cons {m} ≈ id
cons⁻¹∘cons b = {!!}


-- Bit vectors

open import Data.Unit

𝔹 : Set
𝔹 = Bool

infix 10 𝔹^_
𝔹^_ : ℕ → Set
𝔹^_ k = V 𝔹 k

pattern one = suc zero

bval : 𝔹 → 𝟚
bval 𝕗 = zero
bval 𝕥  = one

bval⁻¹ : 𝟚 → 𝔹
bval⁻¹ zero = 𝕗
bval⁻¹ one  = 𝕥

bval∘bval⁻¹ : bval ∘ bval⁻¹ ≈ id
bval∘bval⁻¹ i = {!!}

bval⁻¹∘bval : bval⁻¹ ∘ bval ≈ id
bval⁻¹∘bval b = {!!}

val : (k : ℕ) → 𝔹^ k → 𝟚^ k
val  zero   = λ tt → zero
val (suc k) = cons ∘ (bval ⊗ val k)

val⁻¹ : (k : ℕ) → 𝟚^ k → 𝔹^ k
val⁻¹ zero zero = tt
val⁻¹ (suc k) = (bval⁻¹ ⊗ val⁻¹ k) ∘ cons⁻¹

val∘val⁻¹ : ∀ k → val k ∘ val⁻¹ k ≈ id
val∘val⁻¹ k i = {!!}

val⁻¹∘val : ∀ k → val⁻¹ k ∘ val k ≈ id
val⁻¹∘val k b = {!!}

add𝔹₀ : ∀ k → 𝔹 × 𝔹^ k × 𝔹^ k → 𝔹^ suc k
add𝔹₀ k = val⁻¹ (suc k) ∘ add𝟚 k ∘ (bval ⊗ val k ⊗ val k)

open import Level using (0ℓ)

open import Categorical.Arrow Function 0ℓ
open import Functions.Laws

i : ∀ k → 𝔹 × 𝔹^ k × 𝔹^ k → 𝟚 × 𝟚^ k × 𝟚^ k
i k = bval ⊗ val k ⊗ val k

o : ∀ k → 𝔹^ suc k → 𝟚^ suc k
o k = val (suc k)

spec₀ : ∀ k → o k ∘ add𝔹₀ k ≈ add𝟚 k ∘ i k
spec₀ k = {!!}

-- Arrow category morphism
arr₀ : ∀ k → i k ⇉ o k
arr₀ k = mk (add𝔹₀ k) (add𝟚 k) (spec₀ k)
