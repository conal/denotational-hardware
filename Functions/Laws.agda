{-# OPTIONS --safe --without-K #-}

open import Level

module Functions.Laws (ℓ : Level) where

open import Function.Equivalence hiding (id; _∘_)
open import Data.Product using (_,_)
open import Data.Empty.Polymorphic using (⊥-elim)

open import Categorical.Raw
      hiding (Category; Cocartesian; Cartesian; Semigroup; Monoid; CartesianClosed; Logic)
open import Categorical.Laws
open import Categorical.Equiv
open import Functions.Raw ℓ public
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality
     hiding (Extensionality)
     renaming ( refl to refl≡
              ; trans to trans≡
              ; sym to sym≡
              )

module →-laws-instances where

  instance

    category : Category Function
    category = record
      { identityˡ = λ _ → refl≡
      ; identityʳ = λ _ → refl≡
      ; assoc     = λ _ → refl≡
      ; ∘≈        = λ { {f = f}{k = k} h≈k f≈g x →
                      trans≡ (h≈k (f x)) (cong k (f≈g x)) }
      }

    cocartesian : Cocartesian Function
    cocartesian = record
      { ∀void = ⊥-elim
      ; ∀+ = equivalence
              (λ k≈f▿g → (λ x → k≈f▿g (inl x)) , λ x → k≈f▿g (inr x))
              (λ { (k∘inl≈f , k∘inr≈g) (inj₁ x) → k∘inl≈f x
                 ; (k∘inl≈f , k∘inr≈g) (inj₂ x) → k∘inr≈g x
                 })
      ; ▿≈ = λ h≈k f≈g → λ { (inj₁ x) → h≈k x
                           ; (inj₂ x) → f≈g x
                           }
      }
      where
        open import Data.Sum

    cartesian : Cartesian Function
    cartesian = record
      { ∀⊤ = λ _ → refl≡
      ; ∀× = equivalence
          (λ k≈f▵g → (λ x → cong exl (k≈f▵g x)) , (λ x → cong exr (k≈f▵g x)))
          (λ (exl∘k≈f , exr∘k≈g) x → cong₂ _,_ (exl∘k≈f x) (exr∘k≈g x))
      ; ▵≈ = λ h≈k f≈g x → cong₂ _,_ (h≈k x) (f≈g x)
      }

    -- -- I don't think this one can be proved without extensionality.
    -- indexedCartesian : ∀ {I : Set ℓ} → IndexedCartesian I Function
    -- indexedCartesian = record
    --   { ∀Π = equivalence
    --       (λ k≈△fs i x → cong (λ f → f i) (k≈△fs x))
    --       (λ eqs x → {!!})
    --   ; △≈ = λ eqs x → {!!}
    --   }

    module ccc (extensionality : Extensionality _ _) where

      cartesianClosed : CartesianClosed Function
      cartesianClosed = record
        { ∀⇛ = equivalence
            (λ g≈f (x , y) → sym≡ (cong (λ h → h y) (g≈f x)))
            (λ f≈uncurry-g x → extensionality λ y → sym≡ (f≈uncurry-g (x , y)))
        ; curry≈ = λ f≈g x → extensionality λ y → f≈g (x , y)
        }

    open import HasAlgebra

    semigroup : ∀ {A : Set ℓ} ⦃ _ : HasRawSemigroup A ⦄ ⦃ _ : HasSemigroup A ⦄ → Semigroup Function
    semigroup = record { ⟨∙⟩-assoc = λ _ → ∙-assoc }

    monoid : ∀ {A : Set ℓ} ⦃ _ : HasRawSemigroup A ⦄ ⦃ _ : HasSemigroup A ⦄
      ⦃ _ : HasRawMonoid A ⦄ ⦃ _ : HasMonoid A ⦄ → Monoid Function
    monoid = record
      { ⟨∙⟩-identityˡ = λ (tt , _) → ∙-identityˡ
      ; ⟨∙⟩-identityʳ = λ (_ , tt) → ∙-identityʳ
      }

    logic : Logic Function
    logic = record { f∘cond = λ { (𝕗 , _) → refl≡ ; (𝕥 , _) → refl≡ } }
