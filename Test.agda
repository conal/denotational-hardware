-- Miscellaneous circuit examples
{-# OPTIONS --guardedness #-}

module Test where

open import Level using (0ℓ; lift)
open import Data.Product using (_,_)
open import Data.String hiding (show)
open import Data.Nat
import Data.Bool as B
open import IO

open import Show
open import Categorical.Raw
open import Functions.Laws 0ℓ
open import Ty
open import Index
open import Primitive.Raw _⇾_ renaming (_⇨_ to _⇨ₚ_)
open import Routing.Raw renaming (_⇨_ to _⇨ᵣ_)
open import Linearize.Raw _⇾_ _⇨ₚ_ _⇨ᵣ_

open import SSA
open import Dot

-- TODO: trim imports

open import Ty.Utils
open import Samples.Add

shiftR-swap : ∀ {n} → Bool × V Bool n ⇨ Bool × V Bool n
shiftR-swap = swap ∘ shiftR

-- General feedback right-shift register
fsr : ∀ n → (V Bool n ⇨ Bool) → (V Bool n ⇨ V Bool n)
fsr _ f = shiftR⇃ ∘ (f ▵ id)

linear : ∀ n → V Bool (suc n) → V Bool (suc n) ⇨ Bool
linear zero (c , tt) = unitorᵉʳ
linear (suc n) (c , cs) = bool xor exr c ∘ second (linear n cs)

lfsr : ∀ n → V Bool (suc n) → V Bool (suc n) ⇨ V Bool (suc n)
lfsr n cs = fsr (suc n) (linear n cs)

lfsr₅ : V Bool 6 ⇨ V Bool 6
lfsr₅ = lfsr 5 (𝕥 , 𝕗 , 𝕗 , 𝕥 , 𝕗 , 𝕥 , tt)


example : ∀ {i o : Ty} → String → (i ⇨ o) → IO {0ℓ} _
example name f =
  do -- save "ssa" (show s)
     save "dot" d
 where
   save : String → String → IO {0ℓ} _
   save ext str = do
     let file = "Figures/" ++ name ++ "." ++ ext
     putStrLn ("⟹ " ++ name) -- file
     writeFile file str
   s = ssa f
   d = dot s

main = run do

  example "id-Bool"   (id {a = Bool})
  example "id-Bool2"  (id {a = Bool × Bool})
  example "not"       not
  example "and"       ∧
  example "nand"      (not ∘ ∧)
  example "first-not" (first {b = V Bool 2} not)

  example "shiftR-swap-c5" (shiftR-swap {5})
  example "lfsr-c5"  lfsr₅   -- wrong

  example "half-add"     halfAdd
  example "full-add"     fullAdd
  example "ripple-add-4" (rippleAdd 4)
  example "ripple-add-8" (rippleAdd 8)

  example "carry-select-3x5" (carrySelect 3 5)
  example "carry-select-4x4" (carrySelect 4 4)
  example "carry-select-8x8" (carrySelect 8 8)
  -- example "carry-select-16x16" (carrySelect 16 16)

  -- example "curry-and" (curry ∧)
