{-# OPTIONS --safe --without-K #-}

open import Level using (0ℓ)
open import Data.Nat

open import Categorical.Raw
open import Functions.Raw

module Examples.Add
         {o} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         {_⇨_ : obj → obj → Set} (let private infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄
 where

-- TODO: package up module parameters into one record to pass in and open.

private variable a b c : obj

-- Morphism with carry-in and carry-out
infix 0 _⇨ᶜ_
_⇨ᶜ_ : obj → obj → Set
a ⇨ᶜ b = a × Bool ⇨ Bool × b

-- Note for a ⇨ᶜ b that the carry-in denotes 0 or 1, while the carry-out denotes
-- (in these examples) 0 or 2^n. Positioning carry-in on the one side and
-- carry-out on the other helps definitions below come out more simply. Left-in
-- and right-out reflect the little-endian interpretation and use of
-- left-pointing vectors, Vˡ. Choosing Vˡ rather than the more common Vʳ
-- reflects the practice of writing least significant bit on the right and most
-- significant on the left.

-- Summands ⇨ sum , carry
-- λ (a , cᵢ) → (a ∧ b , a ⊕ b)
halfAdd : Bool ⇨ᶜ Bool
halfAdd = ∧ ▵ xor

fullAdd : Bool × Bool ⇨ᶜ Bool
fullAdd = first ∨ ∘ inAssocʳ′ halfAdd ∘ first halfAdd

-- λ ((a , b) , c) → let (d , p) = halfAdd (b , a)
--                       (e , q) = halfAdd (p , c) in (e ∨ d , q)

-- (a , b) , c
-- (d , p) , c
-- (d , e) , q
-- e ∨ d , q

ripple : (a ⇨ᶜ b) → (n : ℕ) → (Vˡ a n ⇨ᶜ Vˡ b n)
ripple f  zero   = swap
ripple f (suc n) = assocʳ ∘ first (ripple f n) ∘ inAssocʳ′ f

-- (as , a) , cᵢ
-- (as , c′) , b
-- (cₒ , bs) , b
-- cₒ , (bs , b)

rippleAdd : ∀ n → Vˡ (Bool × Bool) n ⇨ᶜ Vˡ Bool n
rippleAdd = ripple fullAdd

constˡ : (a × b ⇨ c) → (⊤ ⇨ a) → (b ⇨ c)
constˡ f a = f ∘ first a ∘ unitorⁱˡ

-- b
-- tt , b
-- a , b
-- f (a , b)

speculateˡ : (Bool × b ⇨ c) → (Bool × b ⇨ c)
speculateˡ f = cond ∘ second (constˡ f false ▵ constˡ f true)

constʳ : (a × b ⇨ c) → (⊤ ⇨ b) → (a ⇨ c)
constʳ f a = f ∘ second a ∘ unitorⁱʳ

-- (cᵢ , a)
-- (cᵢ , (f (false , a) , f (true , a)))
-- cond (cᵢ , (f (false , a) , f (true , a)))

-- b
-- tt , b
-- a , b
-- f (a , b)

speculateʳ : (a × Bool ⇨ c) → (a × Bool ⇨ c)
speculateʳ f = cond ∘ swap ∘ first (constʳ f false ▵ constʳ f true)

-- (a , cᵢ)
-- ((f (a , false) , f (a , true)) , cᵢ)
-- (cᵢ , (f (a , false) , f (a , true)))
-- cond (cᵢ , (f (a , false) , f (a , true)))

V² : obj → ℕ → ℕ → obj
V² a m n = Vˡ (Vˡ a n) m

carrySelect : ∀ m n → V² (Bool × Bool) m n ⇨ᶜ V² Bool m n
carrySelect m n = ripple (speculateʳ (ripple fullAdd n)) m
