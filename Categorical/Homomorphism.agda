{-# OPTIONS --safe --without-K #-}

module Categorical.Homomorphism where

open import Level

open import Categorical.Raw public
open import Categorical.Laws as L
       hiding (Category; Cartesian; Semigroup; Monoid; CartesianClosed; Logic)
open import Categorical.Reasoning

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj₁ obj₂ : Set o
    a b c d : obj₁

open import Categorical.Equiv  public

open ≈-Reasoning

-- Category homomorphism (functor)
record CategoryH {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
                 {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
                 {q} ⦃ _ : Equivalent q _⇨₂_ ⦄
                 ⦃ _ : Category _⇨₁_ ⦄
                 ⦃ _ : Category _⇨₂_ ⦄
                 ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
                 ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  field
    F-id : Fₘ (id {_⇨_ = _⇨₁_}{a = a}) ≈ id
    F-∘  : ∀ {a b c} {g : b ⇨₁ c} {f : a ⇨₁ b} → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f
    -- TODO: make g and f explicit arguments? Wait and see.

  module _ ⦃ _ : L.Category _⇨₂_ ⦄ where

    F-∘³ : {a₀ a₁ a₂ a₃ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}
         → Fₘ (f₃ ∘ f₂ ∘ f₁) ≈ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘³ = F-∘ ; ∘≈ʳ F-∘

    F-∘⁴ : {a₀ a₁ a₂ a₃ a₄ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}{f₄ : a₃ ⇨₁ a₄}
         → Fₘ (f₄ ∘ f₃ ∘ f₂ ∘ f₁) ≈ Fₘ f₄ ∘ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘⁴ = F-∘ ; ∘≈ʳ F-∘³

    F-∘⁵ : {a₀ a₁ a₂ a₃ a₄ a₅ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}{f₄ : a₃ ⇨₁ a₄}
             {f₅ : a₄ ⇨₁ a₅}
         → Fₘ (f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁) ≈ Fₘ f₅ ∘ Fₘ f₄ ∘ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘⁵ = F-∘ ; ∘≈ʳ F-∘⁴

    F-∘⁶ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}{f₄ : a₃ ⇨₁ a₄}
             {f₅ : a₄ ⇨₁ a₅}{f₆ : a₅ ⇨₁ a₆}
         → Fₘ (f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁) ≈
           Fₘ f₆ ∘ Fₘ f₅ ∘ Fₘ f₄ ∘ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘⁶ = F-∘ ; ∘≈ʳ F-∘⁵

open CategoryH ⦃ … ⦄ public

id-CategoryH : {obj : Set o} {_⇨_ : obj → obj → Set ℓ}
               {q : Level} ⦃ _ : Equivalent q _⇨_ ⦄
               ⦃ _ : Category _⇨_ ⦄
             → CategoryH _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ H = id-H ⦄
id-CategoryH = record { F-id = refl ; F-∘ = refl }

record CoproductsH
    (obj₁ : Set o₁) ⦃ _ : Coproducts obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Coproducts obj₂ ⦄
    (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    u : Fₒ ⊥ ⇨₂ ⊥
    δ : {a b : obj₁} → Fₒ (a + b) ⇨₂ Fₒ a + Fₒ b

    u⁻¹ : ⊥ ⇨₂ Fₒ ⊥
    δ⁻¹ : {a b : obj₁} → Fₒ a + Fₒ b ⇨₂ Fₒ (a + b)

open CoproductsH ⦃ … ⦄ public

record ProductsH
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
    (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    -- https://ncatlab.org/nlab/show/monoidal+functor
    ε : ⊤ ⇨₂ Fₒ ⊤
    μ : {a b : obj₁} → Fₒ a × Fₒ b ⇨₂ Fₒ (a × b)

    ε⁻¹ : Fₒ ⊤ ⇨₂ ⊤
    μ⁻¹ : {a b : obj₁} → Fₒ (a × b) ⇨₂ Fₒ a × Fₒ b

open ProductsH ⦃ … ⦄ public

id-ProductsH : ∀ {obj : Set o} ⦃ _ : Products obj ⦄
                 {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
             → ProductsH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄
id-ProductsH =
  record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id }

record StrongProductsH
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
    (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    {q} ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ pH : ProductsH obj₁ _⇨₂′_ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field

    ε⁻¹∘ε : ε⁻¹ ∘ ε ≈ id
    ε∘ε⁻¹ : ε ∘ ε⁻¹ ≈ id

    μ⁻¹∘μ : {a b : obj₁} → μ⁻¹ ∘ μ {a = a}{b} ≈ id
    μ∘μ⁻¹ : {a b : obj₁} → μ ∘ μ⁻¹ {a = a}{b} ≈ id

open StrongProductsH ⦃ … ⦄ public

id-StrongProductsH :
  ∀ {obj : Set o} ⦃ _ : Products obj ⦄
  {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
  {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄
  → StrongProductsH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ pH = id-ProductsH ⦄
id-StrongProductsH =
  record { ε⁻¹∘ε = L.identityˡ ; ε∘ε⁻¹ = L.identityˡ
         ; μ⁻¹∘μ = L.identityˡ ; μ∘μ⁻¹ = L.identityˡ
         }

-- TODO: Try defining id-ProductsH via id-ProductsH′.

-- TODO: Try defining an instance module in place of id-ProductsH′ and
-- id-StrongProductsH′. Ditto for id-ProductsH and id-StrongProductsH.

-- Cartesian homomorphism (cartesian functor)
record CartesianH
         {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄ (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
         {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
         {q} ⦃ _ : Equivalent q _⇨₂_ ⦄
         ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₁_ ⦄
         ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
         ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
         ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
         ⦃ pH : ProductsH obj₁ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  field
    F-!   : ∀ {a : obj₁} → Fₘ {a = a} ! ≈ ε ∘ !
    F-▵   : ∀ {a c d} {f : a ⇨₁ c}{g : a ⇨₁ d} → Fₘ (f ▵ g) ≈ μ ∘ (Fₘ f ▵ Fₘ g)
    F-exl : ∀ {a b : obj₁} → Fₘ exl ∘ μ {a = a}{b} ≈ exl
    F-exr : ∀ {a b : obj₁} → Fₘ exr ∘ μ {a = a}{b} ≈ exr

  module _ ⦃ _ : L.Category _⇨₂_ ⦄ ⦃ spH : StrongProductsH obj₁ _⇨₂_ ⦄ where

    F-!′ : {a : obj₁} → ε⁻¹ ∘ Fₘ {a = a} ! ≈ !
    F-!′ = ∘≈ʳ F-! ; ∘-assoc-elimˡ ε⁻¹∘ε

    F-▵′ : {f : a ⇨₁ c}{g : a ⇨₁ d} → μ⁻¹ ∘ Fₘ (f ▵ g) ≈ Fₘ f ▵ Fₘ g
    F-▵′ = ∘≈ʳ F-▵ ; ∘-assoc-elimˡ μ⁻¹∘μ

    F-exl′ : {a b : obj₁} → Fₘ exl ≈ exl ∘ μ⁻¹ {a = a}{b}
    F-exl′ = introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exl

    F-exr′ : {a b : obj₁} → Fₘ exr ≈ exr ∘ μ⁻¹ {a = a}{b}
    F-exr′ = introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exr

    module _ ⦃ _ : L.Cartesian _⇨₂_ ⦄ ⦃ _ : CategoryH _⇨₁_ _⇨₂_ ⦄ where

      F-⊗ : ∀ {a b c d}{f : a ⇨₁ c}{g : b ⇨₁ d} → Fₘ (f ⊗ g) ∘ μ ≈ μ ∘ (Fₘ f ⊗ Fₘ g)
      F-⊗ {f = f}{g} =
        begin
          Fₘ (f ∘ exl ▵ g ∘ exr) ∘ μ
        ≈⟨ ∘≈ˡ (F-▵ ; ∘≈ʳ (▵≈ F-∘ F-∘)) ⟩
          (μ ∘ (Fₘ f ∘ Fₘ exl ▵ Fₘ g ∘ Fₘ exr)) ∘ μ
        ≈⟨ ∘-assocʳ ⟩
          μ ∘ ((Fₘ f ∘ Fₘ exl ▵ Fₘ g ∘ Fₘ exr) ∘ μ)
        ≈⟨ ∘≈ʳ (▵∘ ; ▵≈ (∘-assocʳ′ F-exl) (∘-assocʳ′ F-exr)) ⟩
          μ ∘ (Fₘ f ∘ exl ▵ Fₘ g ∘ exr)
        ∎

      -- I wonder whether proofs become simpler and/or more regular if we switch
      -- all axioms and lemmas to the form "Fₘ ... ≈ ...". One experiment:
      F-⊗′ : ∀ {a b c d}{f : a ⇨₁ c}{g : b ⇨₁ d} → Fₘ (f ⊗ g) ≈ μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹
      F-⊗′ {f = f}{g} =
        begin
          Fₘ (f ∘ exl ▵ g ∘ exr)
        ≈⟨ F-▵ ; ∘≈ʳ (▵≈ F-∘ F-∘) ⟩
          μ ∘ (Fₘ f ∘ Fₘ exl ▵ Fₘ g ∘ Fₘ exr)
        ≈⟨ ∘≈ʳ (▵≈ (∘≈ʳ F-exl′ ; ∘-assocˡ) (∘≈ʳ F-exr′ ; ∘-assocˡ)) ⟩
          μ ∘ ((Fₘ f ∘ exl) ∘ μ⁻¹ ▵ (Fₘ g ∘ exr) ∘ μ⁻¹)
        ≈⟨ ∘≈ʳ (sym ▵∘) ⟩
          μ ∘ (Fₘ f ∘ exl ▵ Fₘ g ∘ exr) ∘ μ⁻¹
        ∎

      F-first : ∀ {a b c : obj₁}{f : a ⇨₁ c}
               → Fₘ (first {b = b} f) ∘ μ ≈ μ ∘ first (Fₘ f)
      F-first = F-⊗ ; ∘≈ʳ (⊗≈ʳ F-id)

      F-first′ : ∀ {a b c : obj₁}{f : a ⇨₁ c}
               → Fₘ (first {b = b} f) ≈ μ ∘ first (Fₘ f) ∘ μ⁻¹
      F-first′ = introʳ μ∘μ⁻¹ ; ∘-assocˡʳ′ F-first

      F-second : ∀ {a b d : obj₁}{g : b ⇨₁ d}
               → Fₘ (second {a = a} g) ∘ μ ≈ μ ∘ second (Fₘ g)
      F-second = F-⊗ ; ∘≈ʳ (⊗≈ˡ F-id)

      F-second′ : ∀ {a b d : obj₁}{g : b ⇨₁ d}
                → Fₘ (second {a = a} g) ≈ μ ∘ second (Fₘ g) ∘ μ⁻¹
      F-second′ = F-⊗′ ; ∘≈ʳ (∘≈ˡ (⊗≈ˡ F-id))

      F-assocˡ : ∀ {a b c : obj₁}
         → Fₘ (assocˡ {a = a}{b}{c}) ∘ μ ∘ second μ ≈ μ ∘ first μ ∘ assocˡ
      F-assocˡ =
        begin
          Fₘ assocˡ ∘ μ ∘ second μ
        ≡⟨⟩
          Fₘ (second exl ▵ exr ∘ exr) ∘ μ ∘ second μ
        ≈⟨ ∘≈ˡ F-▵ ⟩
          (μ ∘ (Fₘ (second exl) ▵ Fₘ (exr ∘ exr))) ∘ μ ∘ second μ
        ≈⟨ ∘-assocˡ′ (∘-assocʳ′ ▵∘ ; ∘≈ʳ (▵≈ʳ (∘≈ˡ F-∘ ; ∘-assocʳ′ F-exr))) ⟩
          (μ ∘ (Fₘ (second exl) ∘ μ ▵ Fₘ exr ∘ exr)) ∘ second μ
        ≈⟨ ∘-assocʳ′ (▵∘ ; ▵≈ ∘-assocʳ ∘-assocʳ ; ▵≈ʳ (∘≈ʳ exr∘▵ ; ∘-assocˡ′ F-exr)) ⟩
          μ ∘ (Fₘ (second exl) ∘ μ ∘ second μ ▵ exr ∘ exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘-assocˡ′ F-second)) ⟩
          μ ∘ ((μ ∘ second (Fₘ exl)) ∘ second μ ▵ exr ∘ exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘-assocʳ′ (second∘⊗ ; ⊗≈ʳ F-exl))) ⟩
          μ ∘ (μ ∘ second exl ▵ exr ∘ exr)
        ≈⟨ ∘≈ʳ (sym first∘▵) ⟩
          μ ∘ first μ ∘ (second exl ▵ exr ∘ exr)
        ≡⟨⟩
          μ ∘ first μ ∘ assocˡ
        ∎

      F-assocˡ′ : ∀ {a b c : obj₁}
         → Fₘ (assocˡ {a = a}{b}{c}) ≈ μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
      F-assocˡ′ =
        begin
          Fₘ assocˡ
        ≈⟨ sym (∘≈ʳ (∘≈ʳ (∘-assocˡ ; elimˡ (second-inverse μ∘μ⁻¹))) ; elimʳ μ∘μ⁻¹) ⟩
          Fₘ assocˡ ∘ μ ∘ second μ ∘ second μ⁻¹ ∘ μ⁻¹
        ≈⟨ ∘-assocˡ³ ; ∘≈ˡ F-assocˡ ; ∘-assocʳ³ ⟩
          μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
        ∎

      F-assocʳ : ∀ {a b c : obj₁}
         → Fₘ (assocʳ {a = a}{b}{c}) ∘ μ ∘ first μ ≈ μ ∘ second μ ∘ assocʳ
      F-assocʳ =
        begin
          Fₘ assocʳ ∘ μ ∘ first μ
        ≡⟨⟩
          Fₘ (exl ∘ exl ▵ first exr) ∘ μ ∘ first μ
        ≈⟨ ∘≈ˡ F-▵ ⟩
          (μ ∘ (Fₘ (exl ∘ exl) ▵ Fₘ (first exr))) ∘ μ ∘ first μ
        ≈⟨ ∘-assocʳ ⟩
          μ ∘ (Fₘ (exl ∘ exl) ▵ Fₘ (first exr)) ∘ μ ∘ first μ
        ≈⟨ ∘≈ʳ ∘-assocˡ ⟩
          μ ∘ ((Fₘ (exl ∘ exl) ▵ Fₘ (first exr)) ∘ μ) ∘ first μ
        ≈⟨ ∘≈ʳ (∘≈ˡ ▵∘) ⟩
          μ ∘ (Fₘ (exl ∘ exl) ∘ μ ▵ Fₘ (first exr) ∘ μ) ∘ first μ
        ≈⟨ ∘≈ʳ (∘≈ˡ (▵≈ (∘≈ˡ F-∘ ; ∘-assocʳ) F-first)) ⟩
          μ ∘ (Fₘ exl ∘ Fₘ exl ∘ μ ▵ μ ∘ first (Fₘ exr)) ∘ first μ
        ≈⟨ ∘≈ʳ ▵∘ ⟩
          μ ∘ ((Fₘ exl ∘ Fₘ exl ∘ μ) ∘ first μ ▵ (μ ∘ first (Fₘ exr)) ∘ first μ)
        ≈⟨ ∘≈ʳ (▵≈ ∘-assocʳ³ ∘-assocʳ) ⟩
          μ ∘ (Fₘ exl ∘ Fₘ exl ∘ μ ∘ first μ ▵ μ ∘ first (Fₘ exr) ∘ first μ)
        ≈⟨ ∘≈ʳ (▵≈ʳ (∘≈ʳ first∘first)) ⟩
          μ ∘ (Fₘ exl ∘ Fₘ exl ∘ μ ∘ first μ ▵ μ ∘ first (Fₘ exr ∘ μ))
        ≈⟨ ∘≈ʳ (▵≈ (∘≈ʳ ( ∘-assocˡ′ F-exl)) (∘≈ʳ (⊗≈ˡ F-exr))) ⟩
          μ ∘ (Fₘ exl ∘ exl ∘ first μ ▵ μ ∘ first exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘≈ʳ exl∘first)) ⟩
          μ ∘ (Fₘ exl ∘ μ ∘ exl ▵ μ ∘ first exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘-assocˡ′ F-exl)) ⟩
          μ ∘ (exl ∘ exl ▵ μ ∘ first exr)
        ≈⟨ ∘≈ʳ (sym second∘▵) ⟩
          μ ∘ second μ ∘ (exl ∘ exl ▵ first exr)
        ≡⟨⟩
          μ ∘ second μ ∘ assocʳ
        ∎

      F-assocʳ′ : ∀ {a b c : obj₁}
         → Fₘ (assocʳ {a = a}{b}{c}) ≈ μ ∘ second μ ∘ assocʳ ∘ first μ⁻¹ ∘ μ⁻¹
      F-assocʳ′ =
        begin
          Fₘ assocʳ
        ≈⟨ sym (∘≈ʳ (∘≈ʳ (∘-assocˡ ; elimˡ (first-inverse μ∘μ⁻¹))) ; elimʳ μ∘μ⁻¹) ⟩
          Fₘ assocʳ ∘ μ ∘ first μ ∘ first μ⁻¹ ∘ μ⁻¹
        ≈⟨ (∘-assocˡ³ ; ∘≈ˡ F-assocʳ ; ∘-assocʳ³) ⟩
          μ ∘ second μ ∘ assocʳ ∘ first μ⁻¹ ∘ μ⁻¹
        ∎

open CartesianH ⦃ … ⦄ public

id-CartesianH :
    {obj : Set o} {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Products obj ⦄
    {q : Level} ⦃ _ : Equivalent q _⇨_ ⦄
    ⦃ _ :   Category _⇨_ ⦄ ⦃ _ :   Cartesian _⇨_ ⦄
    ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄
  → CartesianH _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ H = id-H ⦄ ⦃ pH = id-ProductsH ⦄
id-CartesianH = record
  { F-!   = sym identityˡ
  ; F-▵   = sym identityˡ
  ; F-exl = identityʳ
  ; F-exr = identityʳ
  }


record MonoidObjH
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄ ⦃ _ : MonoidObj obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ ⦃ _ : MonoidObj obj₂ ⦄
    (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄ : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    δ   : M ⇨₂ Fₒ M
    δ⁻¹ : Fₒ M ⇨₂ M

open MonoidObjH ⦃ … ⦄ public

id-MonoidObjH : ∀ {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : MonoidObj obj ⦄
                   {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
               → MonoidObjH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄
id-MonoidObjH = record { δ = id ; δ⁻¹ = id }

record StrongMonoidObjH
   (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄ ⦃ _ : MonoidObj obj₁ ⦄
   {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ ⦃ _ : MonoidObj obj₂ ⦄
   (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂′_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₂′_ ⦄
   ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄ ⦃ pH : MonoidObjH obj₁ _⇨₂′_ ⦄
   : Set (o₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    δ⁻¹∘δ : δ⁻¹ ∘ δ ≈ id
    δ∘δ⁻¹ : δ ∘ δ⁻¹ ≈ id

open StrongMonoidObjH ⦃ … ⦄ public

id-StrongMonoidObjH :
    ∀ {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : MonoidObj obj ⦄
    {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
    {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄ →
  StrongMonoidObjH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ pH = id-MonoidObjH ⦄
id-StrongMonoidObjH = record { δ⁻¹∘δ = L.identityˡ ; δ∘δ⁻¹ = L.identityˡ }

-- TODO: explicit vs implicit M in id-StrongMonoidObjH & id-StrongMonoidObjH?


-- Semigroup homomorphism
record SemigroupH
         {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄ ⦃ _ : MonoidObj obj₁ ⦄
         {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ ⦃ _ : MonoidObj obj₂ ⦄
         (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₁_ ⦄
         (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
         {q} ⦃ _ : Equivalent q _⇨₂_ ⦄
         ⦃ _ : Semigroup _⇨₁_ ⦄
         ⦃ _ : Semigroup _⇨₂_ ⦄
         ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
         ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
         ⦃ pH : ProductsH obj₁ _⇨₂_ ⦄
         ⦃ _ : MonoidObjH obj₁ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  field
    F-⟨∙⟩ : Fₘ ⟨∙⟩ ∘ μ ∘ (δ ⊗ δ) ≈ δ ∘ ⟨∙⟩

  module _
    ⦃ _ : StrongProductsH obj₁ _⇨₂_ ⦄ ⦃ _ : StrongMonoidObjH obj₁ _⇨₂_ ⦄
    ⦃ _ : L.Category _⇨₂_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
    where

    F-⟨∙⟩′ : Fₘ ⟨∙⟩ ≈ δ ∘ ⟨∙⟩ ∘ (δ⁻¹ ⊗ δ⁻¹) ∘ μ⁻¹
    F-⟨∙⟩′ =
      ( sym (cancelInner (⊗-inverse δ∘δ⁻¹ δ∘δ⁻¹) ; ∘-assoc-elimʳ μ∘μ⁻¹)
      ; ∘≈ˡ (∘-assocʳ ; F-⟨∙⟩)
      ; ∘-assocʳ )

    -- F-⟨∙⟩′ =
    --   begin
    --     Fₘ ⟨∙⟩
    --   ≈˘⟨ elimʳ μ∘μ⁻¹ ⟩
    --     Fₘ ⟨∙⟩ ∘ μ ∘ μ⁻¹
    --   ≈˘⟨ ∘-assocʳ ⟩
    --     (Fₘ ⟨∙⟩ ∘ μ) ∘ μ⁻¹
    --   ≈˘⟨ cancelInner (⊗-inverse δ∘δ⁻¹ δ∘δ⁻¹) ⟩
    --     ((Fₘ ⟨∙⟩ ∘ μ) ∘ (δ ⊗ δ)) ∘ (δ⁻¹ ⊗ δ⁻¹) ∘ μ⁻¹
    --   ≈˘⟨ ∘≈ˡ ∘-assocˡ ⟩
    --     (Fₘ ⟨∙⟩ ∘ μ ∘ (δ ⊗ δ)) ∘ (δ⁻¹ ⊗ δ⁻¹) ∘ μ⁻¹
    --   ≈⟨ ∘≈ˡ F-⟨∙⟩ ⟩
    --     (δ ∘ ⟨∙⟩) ∘ (δ⁻¹ ⊗ δ⁻¹) ∘ μ⁻¹
    --   ≈⟨ ∘-assocʳ ⟩
    --     δ ∘ ⟨∙⟩ ∘ (δ⁻¹ ⊗ δ⁻¹) ∘ μ⁻¹
    --   ∎

open SemigroupH ⦃ … ⦄ public


-- Monoid homomorphism
record MonoidH
         {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄ ⦃ _ : MonoidObj obj₁ ⦄
         {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ ⦃ _ : MonoidObj obj₂ ⦄
         (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₁_ ⦄
         (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
         {q} ⦃ _ : Equivalent q _⇨₂_ ⦄
         ⦃ _ : Semigroup _⇨₁_ ⦄ ⦃ _ : Monoid _⇨₁_ ⦄
         ⦃ _ : Semigroup _⇨₂_ ⦄ ⦃ _ : Monoid _⇨₂_ ⦄
         ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
         ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
         ⦃ pH : ProductsH obj₁ _⇨₂_ ⦄ ⦃ _ : MonoidObjH obj₁ _⇨₂_ ⦄
         ⦃ _ : SemigroupH _⇨₁_ _⇨₂_ ⦄  -- Not strictly necessary
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  field
    F-⟨ι⟩ : Fₘ ⟨ι⟩ ∘ ε ≈ δ ∘ ⟨ι⟩

  module _
    ⦃ _ : StrongProductsH obj₁ _⇨₂_ ⦄ ⦃ _ : StrongMonoidObjH obj₁ _⇨₂_ ⦄
    ⦃ _ : L.Category _⇨₂_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
    where

    F-⟨ι⟩′ : Fₘ ⟨ι⟩ ≈ δ ∘ ⟨ι⟩ ∘ ε⁻¹
    F-⟨ι⟩′ = sym (elimʳ ε∘ε⁻¹) ; ∘-assocˡʳ′ F-⟨ι⟩

    -- F-⟨ι⟩′ : Fₘ ⟨ι⟩ ≈ δ ∘ ⟨ι⟩ ∘ ε⁻¹
    -- F-⟨ι⟩′ =
    --   begin
    --     Fₘ ⟨ι⟩
    --   ≈⟨ sym (elimʳ ε∘ε⁻¹) ⟩
    --     Fₘ ⟨ι⟩ ∘ ε ∘ ε⁻¹
    --   ≈⟨ ∘-assocˡʳ′ F-⟨ι⟩ ⟩
    --     δ ∘ ⟨ι⟩ ∘ ε⁻¹
    --   ∎

open MonoidH ⦃ … ⦄ public

{-
⟨ι⟩ : ⊤ ⇨₁ M₁
⟨ι⟩ : ⊤ ⇨₂ M₂

δ ∘ ⟨ι⟩ : ⊤ ⇨₂ Fₒ M₁
Fₘ ⟨ι⟩ ∘ ε : ⊤ ⇨₂ Fₒ M₁
-}


record ExponentialsH
    (obj₁ : Set o₁) ⦃ _ : Exponentials obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Exponentials obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ν : {a b : obj₁} → (Fₒ a ⇛ Fₒ b) ⇨₂ Fₒ (a ⇛ b)
    -- *Strong*?
    ν⁻¹ : {a b : obj₁} → Fₒ (a ⇛ b) ⇨₂ (Fₒ a ⇛ Fₒ b)

open ExponentialsH ⦃ … ⦄ public

-- TODO: CartesianClosedH

record BooleanH
    (obj₁ : Set o₁) ⦃ _ : Boolean obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Boolean obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    -- {q : Level} ⦃ _ : Equivalent q _⇨₂′_ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β   : Bool ⇨₂ Fₒ Bool
    β⁻¹ : Fₒ Bool ⇨₂ Bool

open BooleanH ⦃ … ⦄ public

id-BooleanH : {obj₂ : Set o} ⦃ _ : Boolean obj₂ ⦄
              {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
              ⦃ _ : Category _⇨₂_ ⦄
              -- {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
              -- ⦃ _ : L.Category _⇨₂_ ⦃ rcat = cat₂ ⦄ ⦄
            → BooleanH obj₂ _⇨₂_ ⦃ Hₒ = id-Hₒ ⦄
id-BooleanH = record { β = id ; β⁻¹ = id }

record StrongBooleanH
    (obj₁ : Set o₁) ⦃ _ : Boolean obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Boolean obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    {q : Level} ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Category _⇨₂′_ ⦄
    ⦃ booleanH : BooleanH obj₁ _⇨₂′_  ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β⁻¹∘β : β⁻¹ ∘ β ≈ id
    β∘β⁻¹ : β ∘ β⁻¹ ≈ id

open StrongBooleanH ⦃ … ⦄ public

id-StrongBooleanH :
      {obj₂ : Set o}  ⦃ _ : Boolean obj₂ ⦄
      {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
      ⦃ _ : Category _⇨₂_ ⦄
      {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
      ⦃ _ : BooleanH obj₂ _⇨₂_ ⦃ Hₒ = id-Hₒ ⦄ ⦄
      ⦃ _ : L.Category _⇨₂_ ⦄
  → StrongBooleanH obj₂ _⇨₂_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ booleanH = id-BooleanH ⦄
id-StrongBooleanH = record
    { β⁻¹∘β = identityˡ
    ; β∘β⁻¹ = identityˡ
    }

record LogicH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    {q} ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Logic _⇨₁′_ ⦄
    ⦃ _ : Boolean obj₂ ⦄ ⦃ _ : Products obj₂ ⦄ ⦃ _ : Logic _⇨₂′_ ⦄
    ⦃ _ : Category _⇨₂′_ ⦄ ⦃ _ : Cartesian _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
    ⦃ pH : ProductsH obj₁ _⇨₂′_ ⦄
    ⦃ spH : StrongProductsH obj₁ _⇨₂′_ ⦄
    ⦃ booleanH  : BooleanH obj₁ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_

  field
    F-false : Fₘ false ∘ ε ≈ β ∘ false
    F-true  : Fₘ true  ∘ ε ≈ β ∘ true
    F-not   : Fₘ not   ∘ β ≈ β ∘ not
    F-∧     : Fₘ  ∧  ∘ μ ∘ (β ⊗ β) ≈ β ∘ ∧
    F-∨     : Fₘ  ∨  ∘ μ ∘ (β ⊗ β) ≈ β ∘ ∨
    F-xor   : Fₘ xor ∘ μ ∘ (β ⊗ β) ≈ β ∘ xor
    F-cond  : ∀ {a : obj₁} → Fₘ cond ∘ μ ∘ (β ⊗ μ {a = a} {a}) ≈ cond

  module _ ⦃ _ : L.Category _⇨₂_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
           ⦃ _ : StrongBooleanH obj₁ _⇨₂_ ⦄ where

    F-false′ : Fₘ false ≈ β ∘ false ∘ ε⁻¹
    F-false′ = sym (∘-assoc-elimʳ ε∘ε⁻¹) ; ∘≈ˡ F-false ; ∘-assocʳ

    -- F-false′ =
    --   begin
    --     Fₘ false
    --   ≈⟨ sym (∘-assoc-elimʳ ε∘ε⁻¹) ⟩
    --     (Fₘ false ∘ ε) ∘ ε⁻¹
    --   ≈⟨ ∘≈ˡ F-false ⟩
    --     (β ∘ false) ∘ ε⁻¹
    --   ≈⟨ ∘-assocʳ ⟩
    --     β ∘ false ∘ ε⁻¹
    --   ∎

    F-true′ : Fₘ true ≈ β ∘ true ∘ ε⁻¹
    F-true′ = sym (∘-assoc-elimʳ ε∘ε⁻¹) ; ∘≈ˡ F-true ; ∘-assocʳ

    F-not′ : Fₘ not ≈ β ∘ not ∘ β⁻¹
    F-not′ = sym (∘-assoc-elimʳ β∘β⁻¹) ; ∘≈ˡ F-not ; ∘-assocʳ

    -- F-not′ =
    --   begin
    --     Fₘ not
    --   ≈⟨ sym (∘-assoc-elimʳ β∘β⁻¹) ⟩
    --     (Fₘ not ∘ β) ∘ β⁻¹
    --   ≈⟨ ∘≈ˡ F-not ⟩
    --     (β ∘ not) ∘ β⁻¹
    --   ≈⟨ ∘-assocʳ ⟩
    --     β ∘ not ∘ β⁻¹
    --   ∎

    F-∧′ : Fₘ ∧ ≈ β ∘ ∧ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    F-∧′ = sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹)))
         ; ∘≈ˡ F-∧ ; ∘-assocʳ

    -- F-∧′ : Fₘ ∧ ≈ β ∘ ∧ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    -- F-∧′ =
    --   begin
    --     Fₘ ∧
    --   ≈⟨ sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹))) ⟩
    --     (Fₘ ∧ ∘ μ ∘ (β ⊗ β)) ∘ ((β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    --   ≈⟨ ∘≈ˡ F-∧ ⟩
    --     (β ∘ ∧) ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    --   ≈⟨ ∘-assocʳ ⟩
    --     β ∘ ∧ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    --   ∎

    F-∨′ : Fₘ ∨ ≈ β ∘ ∨ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    F-∨′ = sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹)))
         ; ∘≈ˡ F-∨ ; ∘-assocʳ

    F-xor′ : Fₘ xor ≈ β ∘ xor ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    F-xor′ = sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹)))
           ; ∘≈ˡ F-xor ; ∘-assocʳ

    F-cond′  : ∀ {a : obj₁} → Fₘ cond ≈ cond ∘ (β⁻¹ ⊗ μ⁻¹ {a = a} {a}) ∘ μ⁻¹
    F-cond′ = sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ μ∘μ⁻¹)))
            ; ∘≈ˡ F-cond

    -- F-cond′  : ∀ {a : obj₁} → Fₘ cond ≈ cond ∘ (β⁻¹ ⊗ μ⁻¹ {a = a} {a}) ∘ μ⁻¹
    -- F-cond′ =
    --   begin
    --     Fₘ cond
    --   ≈⟨ sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ μ∘μ⁻¹))) ⟩
    --     (Fₘ cond ∘ μ ∘ (β ⊗ μ)) ∘ ((β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹)
    --   ≈⟨ ∘≈ˡ F-cond ⟩
    --     cond ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹
    --   ∎

open LogicH ⦃ … ⦄ public

id-LogicH : {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
            {_⇨_ : obj → obj → Set ℓ}
            {q : Level} ⦃ _ : Equivalent q _⇨_ ⦄
            ⦃ _ :   Category _⇨_ ⦄ ⦃ _ :   Cartesian _⇨_ ⦄ ⦃ _ :   Logic _⇨_ ⦄
            ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄ ⦃ _ : L.Logic _⇨_ ⦄
          → LogicH _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ H = id-H ⦄
               ⦃ pH = id-ProductsH ⦄ ⦃ spH = id-StrongProductsH ⦄
               ⦃ booleanH = id-BooleanH ⦄
id-LogicH = record
              { F-false = identityʳ ; sym identityˡ
              ; F-true  = identityʳ ; sym identityˡ
              ; F-not   = identityʳ ; sym identityˡ
              ; F-∧     = elimʳ (identityˡ ; id⊗id) ; sym identityˡ
              ; F-∨     = elimʳ (identityˡ ; id⊗id) ; sym identityˡ
              ; F-xor   = elimʳ (identityˡ ; id⊗id) ; sym identityˡ
              ; F-cond  = elimʳ (identityˡ ; id⊗id)
              }
