{-# OPTIONS --safe --without-K #-}

module Functions.Laws where

open import Function.Equivalence hiding (id; _∘_)
open import Axiom.Extensionality.Propositional

open import Categorical.Raw hiding (Category; Cartesian; CartesianClosed)
open import Categorical.Laws
open import Categorical.Equiv
open import Functions.Raw public

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
