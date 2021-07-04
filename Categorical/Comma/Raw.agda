{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category; Cartesian)
open import Categorical.Homomorphism
open ≈-Reasoning
open import Categorical.Reasoning

module Categorical.Comma.Raw
   {o₁}{obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄
     {ℓ₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Cartesian _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
     {ℓ₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Cartesian _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} ⦃ _ : Products obj₃ ⦄
     {ℓ₃} (_⇨₃_ : obj₃ → obj₃ → Set ℓ₃) ⦃ _ : Cartesian _⇨₃_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₃_ ⦄ ⦃ _ : L.Cartesian _⇨₃_ ⦄
   ⦃ _ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₁_ _⇨₃_ ⦄
     ⦃ catH₁ : CategoryH _⇨₁_ _⇨₃_ ⦄ ⦃ _ : ProductsH obj₁ _⇨₃_ ⦄
     ⦃ cartH₁ : CartesianH _⇨₁_ _⇨₃_ ⦄
   ⦃ _ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₂_ _⇨₃_ ⦄
     ⦃ catH₂ : CategoryH _⇨₂_ _⇨₃_ ⦄ ⦃ _ : ProductsH obj₂ _⇨₃_ ⦄
     ⦃ cartH₂ : CartesianH _⇨₂_ _⇨₃_ ⦄
 where

open import Categorical.Comma.Type _⇨₁_ _⇨₂_ _⇨₃_
       ⦃ catH₁ = catH₁ ⦄ ⦃ catH₂ = catH₂ ⦄
     public

open Obj

private

  -- variable a : Obj  --  "No instance of type CategoryH _⇨₂_ _⇨₃_ was found in scope."

  -- id′ : ∀ {a} → a ⇨ a
  -- id′ {a} = mk id id
  --   (begin
  --      h a ∘ Fₘ id
  --    ≈⟨ elimʳ F-id ⟩
  --      h a
  --    ≈⟨ introˡ F-id ⟩
  --      Fₘ id ∘ h a
  --    ∎)
  -- -- 4.5s

  id′ : ∀ {a} → a ⇨ a
  id′ = mk id id (elimʳ F-id ; introˡ F-id)

  -- comp : ∀ {a b c} → (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  -- comp {a}{b}{c} (mk g₁ g₂ comm-g) (mk f₁ f₂ comm-f) =
  --   mk (g₁ ∘ f₁) (g₂ ∘ f₂)
  --     (begin
  --        h c ∘ Fₘ (g₁ ∘ f₁)
  --      ≈⟨ ∘≈ʳ F-∘ ⟩
  --        h c ∘ (Fₘ g₁ ∘ Fₘ f₁)
  --      ≈⟨ ∘-assocˡ′ comm-g ⟩
  --        (Fₘ g₂ ∘ h b) ∘ Fₘ f₁
  --      ≈⟨ ∘-assocʳ′ comm-f ⟩
  --        Fₘ g₂ ∘ (Fₘ f₂ ∘ h a)
  --      ≈⟨ ∘-assocˡ′ (sym F-∘) ⟩
  --        Fₘ (g₂ ∘ f₂) ∘ h a
  --      ∎)
  -- -- 35s

  comp : ∀ {a b c} → (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  comp (mk g₁ g₂ comm-g) (mk f₁ f₂ comm-f) =
    mk (g₁ ∘ f₁) (g₂ ∘ f₂)
       (∘≈ʳ F-∘ ; ∘-assocˡ′ comm-g ; ∘-assocʳ′ comm-f ; ∘-assocˡ′ (sym F-∘))

module comma-raw-instances-obj where

  instance

    products : Products Obj
    products = record { ⊤   = mk (ε ∘ ε⁻¹)
                      ; _×_ = λ (mk h) (mk k) → mk (μ ∘ (h ⊗ k) ∘ μ⁻¹)
                      }

private

  -- !′ : ∀ {a} → a ⇨ ⊤
  -- !′ {a} = mk ! !
  --   (begin
  --    --   h ⊤ ∘ Fₘ !
  --    -- ≡⟨⟩
  --      (ε ∘ ε⁻¹) ∘ Fₘ !
  --    ≈⟨ ∘≈ʳ F-! ; cancelInner ε⁻¹∘ε ⟩
  --      ε ∘ !
  --    ≈⟨ ∘≈ʳ (sym ∀⊤) ⟩
  --      ε ∘ (! ∘ h a)
  --    ≈⟨ ∘-assocˡ′ (sym F-!) ⟩
  --      Fₘ ! ∘ h a
  --    ∎)
  -- -- 23s

  !′ : ∀ {a} → a ⇨ ⊤
  !′ = mk ! ! (∘≈ʳ F-! ; cancelInner ε⁻¹∘ε ; ∘≈ʳ (sym ∀⊤) ; ∘-assocˡ′ (sym F-!))

  -- fork : ∀ {a c d} → (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
  -- fork {a}{c}{d} (mk f₁ f₂ comm-f) (mk g₁ g₂ comm-g) =
  --   mk (f₁ ▵ g₁) (f₂ ▵ g₂)
  --     (begin
  --        h (c × d) ∘ Fₘ (f₁ ▵ g₁)
  --      ≈⟨ ∘≈ ∘-assocˡ F-▵ ; cancelInner μ⁻¹∘μ ⟩
  --        (μ ∘ (h c ⊗ h d)) ∘ (Fₘ f₁ ▵ Fₘ g₁)
  --      ≈⟨ ∘-assocʳ′ (⊗∘▵ ; ▵≈ comm-f comm-g ; sym ▵∘) ⟩
  --        μ ∘ ((Fₘ f₂ ▵ Fₘ g₂) ∘ h a)
  --      ≈⟨ ∘-assocˡ′ (sym F-▵) ⟩
  --        Fₘ (f₂ ▵ g₂) ∘ h a
  --      ∎)
  -- -- 1m ?

  fork : ∀ {a c d} → (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
  fork (mk f₁ f₂ comm-f) (mk g₁ g₂ comm-g) =
    mk (f₁ ▵ g₁) (f₂ ▵ g₂)
       ( ∘≈ ∘-assocˡ F-▵
       ; cancelInner μ⁻¹∘μ
       ; ∘-assocʳ′ (⊗∘▵ ; ▵≈ comm-f comm-g ; sym ▵∘)
       ; ∘-assocˡ′ (sym F-▵)
       )

  -- exl′ : ∀ {a b} → a × b ⇨ a
  -- exl′ {a}{b} = mk exl exl
  --   (begin
  --      h a ∘ Fₘ exl
  --    ≈⟨ ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exl) ⟩
  --      h a ∘ (exl ∘ μ⁻¹)
  --    ≈⟨ ∘-assocˡʳ′ (sym exl∘▵) ⟩
  --      exl ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ≈⟨ sym (∘-assocˡ′ F-exl) ⟩
  --      Fₘ exl ∘ μ ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ∎)
  -- -- 45s

  exl′ : ∀ {a b} → a × b ⇨ a
  exl′ = mk exl exl
    ( ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exl)
    ; ∘-assocˡʳ′ (sym exl∘▵)
    ; sym (∘-assocˡ′ F-exl)
    )

  -- exr′ : ∀ {a b} → a × b ⇨ b
  -- exr′ {a}{b} = mk exr exr
  --   (begin
  --      h b ∘ Fₘ exr
  --    ≈⟨ ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exr) ⟩
  --      h b ∘ (exr ∘ μ⁻¹)
  --    ≈⟨ ∘-assocˡʳ′ (sym exr∘▵) ⟩
  --      exr ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ≈⟨ sym (∘-assocˡ′ F-exr) ⟩
  --      Fₘ exr ∘ μ ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ∎)
  -- -- 45s

  exr′ : ∀ {a b} → a × b ⇨ b
  exr′ = mk exr exr
    ( ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exr)
    ; ∘-assocˡʳ′ (sym exr∘▵)
    ; sym (∘-assocˡ′ F-exr)
    )


module comma-raw-instances where

  instance

    category : Category _⇨_
    category = record { id = id′ ; _∘_ = comp }
  
    cartesian : Cartesian _⇨_
    cartesian = record { ! = !′ ; _▵_ = fork ; exl = exl′ ; exr = exr′ }

    -- TODO: CartesianClosed and Logic.
