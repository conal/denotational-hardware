{-# OPTIONS --safe --without-K #-}

module Functions.Laws where

open import Function.Equivalence hiding (id; _∘_)

open import Categorical.Raw as R hiding (Category; Cartesian; CartesianClosed; Logic)
open import Categorical.Laws
open import Categorical.Equiv
open import Functions.Raw public
open import Axiom.Extensionality.Propositional

module →-laws-instances where

  open import Level
  open import Data.Product using (_,_)
  open import Relation.Binary.PropositionalEquality
       hiding (Extensionality)
       renaming ( refl to refl≡
                ; trans to trans≡
                ; sym to sym≡
                )
  instance

    category : Category Function
    category = record
      { identityˡ = λ _ → refl≡
      ; identityʳ = λ _ → refl≡
      ; assoc     = λ _ → refl≡
      ; ∘≈        = λ { {f = f}{k = k} h≈k f≈g x →
                      trans≡ (h≈k (f x)) (cong k (f≈g x)) }
      }

    cartesian : Cartesian Function
    cartesian = record
      { ∀⊤ = λ _ → refl≡
      ; ∀× = equivalence
          (λ k≈f▵g → (λ x → cong exl (k≈f▵g x)) , (λ x → cong exr (k≈f▵g x)))
          (λ (exl∘k≈f , exr∘k≈g) x → cong₂ _,_ (exl∘k≈f x) (exr∘k≈g x))
      ; ▵≈ = λ h≈k f≈g x → cong₂ _,_ (h≈k x) (f≈g x)
      }

    module ccc (extensionality : Extensionality _ _) where

      cartesianClosed : CartesianClosed Function
      cartesianClosed = record
        { ∀⇛ = equivalence
            (λ g≈f (x , y) → sym≡ (cong (λ h → h y) (g≈f x)))
            (λ f≈uncurry-g x → extensionality λ y → sym≡ (f≈uncurry-g (x , y)))
        ; curry≈ = λ f≈g x → extensionality λ y → f≈g (x , y)
        }

    logic : Logic Function zero
    logic = record
      { ∨-idˡ = λ x → refl≡
      ; ∨-idʳ = ∨-idʳ-aux
      ; ∧-idˡ = λ x → refl≡
      ; ∧-idʳ = ∧-idʳ-aux
      ; de-morganŝ = λ
          { (𝕗 , 𝕗) → refl≡
          ; (𝕗 , 𝕥) → refl≡
          ; (𝕥 , 𝕗) → refl≡
          ; (𝕥 , 𝕥) → refl≡
          }
      ; de-morganš = λ
          { (𝕗 , 𝕗) → refl≡
          ; (𝕗 , 𝕥) → refl≡
          ; (𝕥 , 𝕗) → refl≡
          ; (𝕥 , 𝕥) → refl≡
          }
      ; not∘not≈id = λ
          { 𝕗 → refl≡
          ; 𝕥 → refl≡
          }
      ; ∧∨-xor = λ
          { (𝕗 , 𝕗) → refl≡
          ; (𝕗 , 𝕥) → refl≡
          ; (𝕥 , 𝕗) → refl≡
          ; (𝕥 , 𝕥) → refl≡
          }
      ; condˡ = λ x → refl≡
      ; condʳ = λ x → refl≡
      } where
          ∨-idʳ-aux : ∀ { any : ⊤ → Bool } → ∨ ∘ (any ▵ true) ≈ true
          ∨-idʳ-aux {any} x with (any x)
          ... | 𝕗 = refl≡
          ... | 𝕥 = refl≡
          ∧-idʳ-aux : ∀ { any : ⊤ → Bool } → ∧ ∘ (any ▵ false) ≈ false
          ∧-idʳ-aux {any} x with (any x)
          ... | 𝕗 = refl≡
          ... | 𝕥 = refl≡
