{-# OPTIONS --safe --without-K #-}

open import Level

module Functions.Type (ℓ : Level) where

import Data.Unit as U
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥′)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using () renaming (_×_ to _×′_)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F)

import Data.Bool as B

⟨→⟩ : Set ℓ → Set ℓ → Set ℓ
⟨→⟩ a b = a → b

Function : Set ℓ → Set ℓ → Set ℓ
Function = ⟨→⟩

pattern 𝕗 = lift B.false
pattern 𝕥 = lift B.true

pattern tt = lift U.tt

infix  0 if_then_else_

if_then_else_ :  ∀ {a}{A : Set a} → Lift ℓ B.Bool → A → A → A
if 𝕥 then t else f = t
if 𝕗 then t else f = f

bool : ∀ {a}{A : Set a} → A → A → Lift ℓ B.Bool → A
bool e t c = if c then t else e

two : ∀ {a}{A : Set a} → A → A → (Fin 2 → A)
two z o 0F = z
two z o 1F = o

lift₁ : ∀ {a b}{A : Set a}{B : Set b}{a′ b′}
      → (A → B) → (Lift a′ A → Lift b′ B)
lift₁ f (lift x) = lift (f x)

lift₂ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}{a′ b′ c′}
      → (A → B → C) → (Lift a′ A → Lift b′ B → Lift c′ C)
lift₂ f (lift x) (lift y) = lift (f x y)

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Functions with left inverses are injective. TODO: maybe generalize to monic morphisms.
invertible-injective : ∀ {A B : Set ℓ} (f : A → B) (f⁻¹ : B → A) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id) →
  ∀ {x y} → f x ≡ f y → x ≡ y
invertible-injective f f⁻¹ f⁻¹∘f≗id {x} {y} fx≡fy =
  begin
    x
  ≡⟨ sym (f⁻¹∘f≗id x) ⟩
    f⁻¹ (f x)
  ≡⟨ cong f⁻¹ fx≡fy ⟩
    f⁻¹ (f y)
  ≡⟨ f⁻¹∘f≗id y ⟩
    y
  ∎

module →-instances where

  open import Categorical.Object

  instance

    coproducts : Coproducts (Set ℓ)
    coproducts = record { ⊥ = ⊥′ ; _+_ = _⊎_ }

    products : Products (Set ℓ)
    products = record { ⊤ = ⊤′ ; _×_ = _×′_ }

    -- indexedProducts : ∀ {I : Set ℓ} → IndexedProducts (Set ℓ) I
    -- indexedProducts {I = I} = record { Π = λ f → ∀ i → f i }

    exponentials : Exponentials (Set ℓ)
    exponentials = record { _⇛_ = Function }

    boolean : Boolean (Set ℓ)
    boolean = record { Bool = Lift ℓ B.Bool }

    open import HasAlgebra

    monoidObj : ∀ {A : Set ℓ} ⦃ _ : HasRawSemigroup A ⦄ → MonoidObj (Set ℓ)
    monoidObj {A = A} = record { M = A }
