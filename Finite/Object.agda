{-# OPTIONS --safe --without-K #-}
module Finite.Object where

open import Level using (0ℓ)

open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Fin
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (uncurry) -- for μ⁻¹∘μ

open import Categorical.Homomorphism hiding (uncurry; refl)

open import Functions 0ℓ


module finite-object-instances where

  instance

    Hₒ : Homomorphismₒ ℕ Set
    Hₒ = record { Fₒ = Fin }

    coproducts : Coproducts ℕ
    coproducts = record { ⊥ = 0 ; _+_ = _+ℕ_ }

    products : Products ℕ
    products = record { ⊤ = 1 ; _×_ = _*_ }

    pH : ProductsH ℕ ⟨→⟩
    pH = record
           { ε   = λ { tt → zero }
           ; μ   = uncurry combine
           ; ε⁻¹ = λ { zero → tt }
           ; μ⁻¹ = λ {m n} → remQuot n
           }

    spH : StrongProductsH ℕ ⟨→⟩
    spH = record
            { ε⁻¹∘ε = λ { tt → refl }
            ; ε∘ε⁻¹ = λ { zero → refl }
            ; μ⁻¹∘μ = uncurry remQuot-combine
            ; μ∘μ⁻¹ = λ {m n} → combine-remQuot {m} n
            }
    -- TODO: Construct pH and spH from 1↔⊤ and *↔×

    -- TODO: Exponentials

    boolean : Boolean ℕ
    boolean = record { Bool = 2 }

    booleanH : BooleanH ℕ ⟨→⟩
    booleanH = record { β = bool 0F 1F ; β⁻¹ = two 𝕗 𝕥}
    -- As @JacquesCarette noted there are two *different* such isomorphisms.

    strongBooleanH : StrongBooleanH ℕ ⟨→⟩
    strongBooleanH = record
      { β⁻¹∘β = λ { 𝕗  → refl ; 𝕥  → refl }
      ; β∘β⁻¹ = λ { 0F → refl ; 1F → refl }
      }
