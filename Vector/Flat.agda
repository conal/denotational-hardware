{-# OPTIONS --safe --without-K #-}

module Vector.Flat {A : Set} where

open import Data.Nat
open import Data.Vec
open import Data.Unit using (tt)
open import Data.Product using (_,_; ∃)
open import Relation.Binary.PropositionalEquality
       renaming (refl to refl≡)

open import Categorical.Raw
open import Categorical.Equiv
open import Functions

open import Vector.Type {A}
open import Vector.Homomorphism {A}

private
  variable
    P Q : Set

record Flat (P : Set) : Set where
  field
    size : ℕ
    flatten   : P → Vec A size
    flatten⁻¹ : Vec A size → P
    flatten⁻¹∘flatten : flatten⁻¹ ∘ flatten ≈ id
    flatten∘flatten⁻¹ : flatten ∘ flatten⁻¹ ≈ id
open Flat ⦃ … ⦄ public

instance

  flat₀ : Flat ⊤
  flat₀ = record
    { size = 0
    ; flatten = λ tt → []
    ; flatten⁻¹ = λ [] → tt
    ; flatten⁻¹∘flatten = refl
    ; flatten∘flatten⁻¹ = λ { [] → refl≡ }
    }

  flat₁ : Flat A
  flat₁ = record
    { size = 1
    ; flatten = λ x → x ∷ []
    ; flatten⁻¹ = λ { (x ∷ []) → x }
    ; flatten⁻¹∘flatten = refl
    ; flatten∘flatten⁻¹ = λ { (x ∷ []) → refl≡ }
    }

  flat× : ∀ ⦃ _ : Flat P ⦄ ⦃ _ : Flat Q ⦄ → Flat (P × Q)
  flat× {P}{Q} = record
    { size = m + n
    ; flatten = app ∘ (flatten ⊗ flatten)
    ; flatten⁻¹ = (flatten⁻¹ ⊗ flatten⁻¹) ∘ app⁻¹
    ; flatten⁻¹∘flatten = λ (p , q) →
        begin
          (flatten⁻¹ ⊗ flatten⁻¹) (app⁻¹ (app (flatten p , flatten q)))
        ≡⟨ cong (flatten⁻¹ ⊗ flatten⁻¹) (app⁻¹∘app (flatten p , flatten q)) ⟩
          (flatten⁻¹ ⊗ flatten⁻¹) (flatten p , flatten q)
        ≡⟨⟩
          flatten⁻¹ (flatten p) , flatten⁻¹ (flatten q)
        ≡⟨ cong₂ _,_ (flatten⁻¹∘flatten p) (flatten⁻¹∘flatten q) ⟩
          (p , q)
        ∎
    ; flatten∘flatten⁻¹ = λ w → let u , v = app⁻¹ {m}{n} w in
        begin
          flatten (flatten⁻¹ u) ++ flatten (flatten⁻¹ v)
        ≡⟨ cong₂ _++_ (flatten∘flatten⁻¹ u) (flatten∘flatten⁻¹ v) ⟩
          u ++ v
        ≡⟨ app∘app⁻¹ {m} w  ⟩
          w
        ∎
    }
   where m = size {P}
         n = size {Q}
         open ≡-Reasoning
         open vec-laws

