{-# OPTIONS --safe --without-K #-}

open import Data.Nat

open import Categorical.Raw
open import Functions.Raw

module Samples.Add
         {o} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         {_⇨_ : obj → obj → Set} (let private infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄
 where

-- TODO: package up module parameters into one record to pass in and open.

private variable a b c : obj

-- With carry-in 
Cⁱ Cᵒ : obj → obj
Cⁱ b = Bool × b
Cᵒ b = b × Bool

-- Morphism with carry-in and carry-out
infix 0 _⇨ᶜ_
_⇨ᶜ_ : obj → obj → Set
a ⇨ᶜ b = Cⁱ a ⇨ Cᵒ b

-- Note for a ⇨ᶜ b that the carry-in denotes 0 or 1, while the carry-out denotes
-- (in these examples) 0 or 2^n. Positioning carry-in on the one side and
-- carry-out on the other helps definitions below come out more simply. Left-in
-- and right-out reflect the little-endian interpretation and use of
-- right-pointing vectors, though unfortunately contradicts customary practice
-- of writing least significant bit on the right and most significant on the
-- left. It might instead be worth defining and using left-pointing vectors, or
-- trying with big-endian ordering. A catch, however, is that _,_ is
-- right-associative, so right-pointing vectors are more easier to write and
-- read.

-- Summands ⇨ sum , carry
-- λ (a , b) → (a ⊕ b , a ∧ b)
halfAdd : Bool ⇨ᶜ Bool
halfAdd = xor ▵ ∧

fullAdd : Bool × Bool ⇨ᶜ Bool
fullAdd = second ∨ ∘ inAssocˡ halfAdd ∘ second halfAdd

-- λ (c , (a , b)) → let p , d = halfAdd (a , b)
--                       q , e = halfAdd (c , p) in (q , e ∨ d)

-- c , (a , b)
-- c , (p , d)
-- q , (e , d)
-- q , e ∨ d

-- TODO: semantic specifications and correctness proofs.

ripple : (a ⇨ᶜ b) → (n : ℕ) → (V a n ⇨ᶜ V b n)
ripple f  zero   = swap
ripple f (suc n) = assocˡ ∘ second (ripple f n) ∘ inAssocˡ f

-- cᵢ , (a , as)
-- b , (c′ , as)
-- b , (bs , cₒ)
-- (b , bs) , cₒ

rippleAdd : ∀ n → V (Bool × Bool) n ⇨ᶜ V Bool n
rippleAdd = ripple fullAdd

speculate : (Cⁱ a ⇨ b) → (Cⁱ a ⇨ b)
speculate f = cond ∘ second (f ∘ constˡ false ▵ f ∘ constˡ true)

-- (cᵢ , a)
-- (cᵢ , (f (false , a) , f (true , a)))
-- cond (cᵢ , (f (false , a) , f (true , a)))

V² : obj → ℕ → ℕ → obj
V² a m n = V (V a n) m

carrySelect : ∀ m n → V² (Bool × Bool) m n ⇨ᶜ V² Bool m n
carrySelect m n = ripple (speculate (ripple fullAdd n)) m
