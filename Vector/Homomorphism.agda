{-# OPTIONS --safe --without-K #-}

module Vector.Homomorphism {A : Set} where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Categorical.Raw
open import Categorical.Homomorphism hiding (refl)
open import Functions

open import Vector.Raw {A} public

module vec-laws where

  app : ∀ {m n : ℕ} → Vec A m × Vec A n → Vec A (m + n)
  app (u , v) = u ++ v

  app⁻¹ : ∀ {m n : ℕ} → Vec A (m + n) → Vec A m × Vec A n
  app⁻¹ {m} = take m ▵ drop m

  take∘app : ∀ {m n : ℕ} → take m {n} ∘ app ≈ exl
  take∘app {zero } {n} ([] , v) = refl
  take∘app {suc m} {n} (x ∷ u , v) =
    begin
      take (suc m) (x ∷ u ++ v)
    ≡⟨ unfold-take m {n} x (u ++ v) ⟩
      x ∷ take m (u ++ v)
    ≡⟨ cong (x ∷_) (take∘app (u , v)) ⟩
      x ∷ u
    ∎

  drop∘app : ∀ {m n : ℕ} → drop m {n} ∘ app ≈ exr
  drop∘app {zero } {n} ([] , v) = refl
  drop∘app {suc m} {n} (x ∷ u , v) =
    begin
      drop (suc m) (x ∷ u ++ v)
    ≡⟨ unfold-drop m {n} x (u ++ v) ⟩
      drop m (u ++ v)
    ≡⟨ drop∘app (u , v) ⟩
      v
    ∎

  app⁻¹∘app : ∀ {m n : ℕ} → app⁻¹ ∘ app {m}{n} ≈ id
  app⁻¹∘app {m} uv = cong₂ _,_ (take∘app uv) (drop∘app uv)

  app∘app⁻¹ : ∀ {m n : ℕ} → app {m}{n} ∘ app⁻¹ ≈ id
  app∘app⁻¹ {m} = take-drop-id m

module vec-homomorphism-instances where

  open vec-laws

  instance

    categoryH : CategoryH _⇨_ Function
    categoryH = record
      { F-id = λ _ → refl
      ; F-∘  = λ _ → refl 
      }

    pH : ProductsH ℕ Function
    pH = record
      { ε     = λ { tt → [] }
      ; μ     = app
      ; ε⁻¹   = λ { [] → tt }
      ; μ⁻¹   = app⁻¹
      ; ε⁻¹∘ε = λ { tt → refl }
      ; ε∘ε⁻¹ = λ { [] → refl } 
      ; μ⁻¹∘μ = app⁻¹∘app
      ; μ∘μ⁻¹ = λ {a} → app∘app⁻¹ {a}
      }

    cartesian : CartesianH _⇨_ Function
    cartesian = record
      { F-!   = λ _ → refl
      ; F-▵   = λ _ → refl
      ; F-exl = take∘app
      ; F-exr = drop∘app
      }
