-- 1D convolution from [*Type-Directed Scheduling of Streaming
-- Accelerators*](https://aetherling.org/aetherling.pdf)

module Samples.Conv where

open import Data.Product hiding (map; zip)
open import Function
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Vec hiding (splitAt)

private
  variable
    m n : ℕ
    a b s : Set

-- Note: I think the definitions would simpler 

shiftʳ : a → Vec a n → Vec a n
shiftʳ x₀ [] = []
shiftʳ x₀ (x ∷ xs) = x₀ ∷ shiftʳ x xs

avg : ℕ × ℕ × ℕ → ℕ
avg (a , b , c) = (a + b + c) div 3

ℕ² : Set
ℕ² = ℕ × ℕ

conv : ℕ² × Vec ℕ m → Vec ℕ m
conv ((a , b) , v₂) = map avg (zip v₀ (zip v₁ v₂))
 where
   v₁ = shiftʳ b v₂
   v₀ = shiftʳ a v₁

mealy : (s × a → b × s) → (∀ {n} → s × Vec a n → Vec b n)
mealy f (s , []) = []
mealy f (s , x ∷ xs) = let b , s′ = f (s , x) in b ∷ mealy f (s′ , xs)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Now write conv via mealy in various ways.


-- Figure 1a in "Type-Directed Scheduling of Streaming Accelerators"

conv₁ : ℕ² × Vec ℕ m → Vec ℕ m
conv₁ = mealy λ ((a , b) , c) → avg (a , b , c) , (b , c)

conv₁-spec : conv₁ ≗ conv {m}
conv₁-spec (_ , []) = refl
conv₁-spec ((_ , b) , c ∷ xs) rewrite conv₁-spec ((b , c) , xs) = refl


-- Figure 1b

conv₂ : ℕ² × Vec ℕ² m → Vec ℕ² m
conv₂ = mealy λ ((a , b) , (c , d)) →
          (avg (a , b , c) , avg (b , c , d)) , (c , d)

-- Note: we could drop from four adders to three by removing a redundant b + c.
-- I think one addition and one subtraction suffices for any window width.

decode₂ : Vec ℕ² m → Vec ℕ (m * 2)
decode₂ [] = []
decode₂ ((a , b) ∷ ps) = a ∷ b ∷ decode₂ ps

conv₂-spec : decode₂ ∘ conv₂ {m} ≗ conv {m * 2} ∘ map₂ decode₂
conv₂-spec {zero } (_ ,   []  ) = refl
conv₂-spec {suc _} (_ , p ∷ ps) rewrite conv₂-spec (p , ps) = refl


-- Figure 1c

decode₃ : Vec ℕ (m * 3) → Vec ℕ m
decode₃ {zero } [] = []
decode₃ {suc _} (x₀ ∷ x₁ ∷ x₂ ∷ v) = x₀ ∷ decode₃ v

open import Data.Bool
open import Data.Fin hiding (_+_)

pattern one = suc zero
pattern two = suc one

none : ℕ
none = 7  -- anything

bump : Fin 3 → Fin 3  -- TODO: Generalize
bump zero = one
bump one  = two
bump two  = zero

State₃ : Set
State₃ = Fin 3 × ℕ² × ℕ

h₃ : State₃ × ℕ → ℕ × State₃
h₃ ((i , (a , b) , c) , x) = tot div 3 , (bump i , ab′ i , c′ i)
 where
   ab′ : Fin 3 → ℕ²
   ab′ zero = x , a
   ab′ one  = a , b
   ab′ two  = a , b
   c′ : Fin 3 → ℕ
   c′ zero = 0 -- or x ?
   c′ one  = c
   c′ two  = c
   serialized : Fin 3 → ℕ
   serialized zero = x
   serialized one  = a
   serialized two  = b
   tot : ℕ
   tot = serialized i + c′ i

conv₃ : State₃ × Vec ℕ m → Vec ℕ m
conv₃ = mealy h₃

-- conv₃-spec : ∀ {ab c xs} → conv₃ ((zero , ab , c) , xs) ≡ conv {m} (ab , xs)
-- conv₃-spec = {!!}

-- *WORKING HERE*
