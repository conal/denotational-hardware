{-# OPTIONS --safe --without-K #-}

open import Categorical.Homomorphism
import Categorical.Laws as L

open import Ty

module Ty.CartesianH {o}{obj′ : Set o}
   ⦃ _ : Products obj′ ⦄ ⦃ _ : Boolean obj′ ⦄ ⦃ _ : Exponentials obj′ ⦄
   (_⇨_ : Ty → Ty → Set) {ℓ′} (_↠_ : obj′ → obj′ → Set ℓ′)
   {q} ⦃ _ : Equivalent q _↠_ ⦄
   ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Cartesian _⇨_ ⦄
   ⦃ _ : Category _↠_ ⦄ ⦃ _ : Cartesian _↠_ ⦄
   ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄
   ⦃ _ : Homomorphism _⇨_ _↠_ ⦄
   ⦃ _ : CategoryH _⇨_ _↠_ ⦄ ⦃ _ : CartesianH _⇨_ _↠_ ⦄
  where


open ≈-Reasoning
open L hiding (Category; Cartesian)

-- F̂-! {a} = F-! ; identityˡ
--   begin
--     Fₘ (! {a = a})
--   ≈⟨ F-! ⟩
--     ε ∘ !
--   ≡⟨⟩
--     id ∘ !
--   ≈⟨ identityˡ ⟩
--     !
--   ∎

private
  variable
    a b c d e : Ty

F̂-id : Fₘ (id {a = a}) ≈ id
F̂-id = F-id

F̂-∘ : ∀ {f : a ⇨ b}{g : b ⇨ c}{f′ : Fₒ a ↠ Fₒ b}{g′ : Fₒ b ↠ Fₒ c}
    → Fₘ g ≈ g′ → Fₘ f ≈ f′ → Fₘ (g ∘ f) ≈ g′ ∘ f′
F̂-∘ Fₘg≈g′ Fₘf≈f′ = F-∘ ; ∘≈ Fₘg≈g′ Fₘf≈f′

-- I think a new category is emerging. Generalize from Ty by adding a little
-- more flexibility, so f′ : a′ ↠ b′, along with proofs that Fₒ a ≅ a′ and
-- Fₒ b ≅ b′. An object is a an object from each category. A morphism from
-- (a , a′) to (b , b′) a pair of morphisms (f , f′) with f : a ⇨ b and f′ :
-- a′ ↠ b′ such that Fₒ a ≅ a′ and Fₒ b ≅ b′ and Fₘ f ≈ f′. I think this
-- morphism equivalence property must be restated via the object isomorphism
-- properties.

F̂-! : Fₘ (! {a = a}) ≈ !
F̂-! = F-! ; identityˡ

F̂-▵ : ∀ {f : a ⇨ c}{g : a ⇨ d}{f′ : Fₒ a ↠ Fₒ c}{g′ : Fₒ a ↠ Fₒ d}
    → Fₘ f ≈ f′ → Fₘ g ≈ g′ → Fₘ (f ▵ g) ≈ f′ ▵ g′
F̂-▵ Fₘf≈f′ Fₘg≈g′ = F-▵ ; identityˡ ; ▵≈ Fₘf≈f′ Fₘg≈g′

F̂-exl : Fₘ (exl {a = a}{b}) ≈ exl
F̂-exl = sym identityʳ ; F-exl

F̂-exr : Fₘ (exr {a = a}{b}) ≈ exr
F̂-exr = sym identityʳ ; F-exr

-- dup = id ▵ id
F̂-dup : Fₘ (dup {a = a}) ≈ dup
F̂-dup = F̂-▵ F-id F-id

-- f ⊗ g = f ∘ exl ▵ g ∘ exr
F̂-⊗ : ∀ {f : a ⇨ c}{g : b ⇨ d} {f′ : Fₒ a ↠ Fₒ c}{g′ : Fₒ b ↠ Fₒ d}
    → Fₘ f ≈ f′ → Fₘ g ≈ g′ → Fₘ (f ⊗ g) ≈ f′ ⊗ g′
F̂-⊗ Fₘf≈f′ Fₘg≈g′ = F̂-▵ (F-∘ ; ∘≈ʳ F̂-exl) (F-∘ ; ∘≈ʳ F̂-exr) ; ⊗≈ Fₘf≈f′ Fₘg≈g′

-- first f = f ⊗ id
F̂-first : {f : a ⇨ c} {f′ : Fₒ a ↠ Fₒ c}
        → Fₘ f ≈ f′ → Fₘ (first {b = b} f) ≈ first f′
F̂-first Fₘf≈f′ = F̂-⊗ Fₘf≈f′ F-id

-- second g = id ⊗ g
F̂-second : {g : b ⇨ d} {g′ : Fₒ b ↠ Fₒ d}
         → Fₘ g ≈ g′ → Fₘ (second {a = a} g) ≈ second g′
F̂-second Fₘg≈g′ = F̂-⊗ F-id Fₘg≈g′

-- twice f = f ⊗ f
F̂-twice : {f : a ⇨ c} {f′ : Fₒ a ↠ Fₒ c}
        → Fₘ f ≈ f′ → Fₘ (twice f) ≈ twice f′
F̂-twice Fₘf≈f′ = F̂-⊗ Fₘf≈f′ Fₘf≈f′

-- unitorᵉˡ = exr
F̂-unitorᵉˡ : Fₘ (unitorᵉˡ {a = a}) ≈ unitorᵉˡ
F̂-unitorᵉˡ = F̂-exr

-- unitorᵉʳ = exl
F̂-unitorᵉʳ : Fₘ (unitorᵉʳ {a = a}) ≈ unitorᵉʳ
F̂-unitorᵉʳ = F̂-exl

-- unitorⁱˡ = ! ▵ id
F̂-unitorⁱˡ : Fₘ (unitorⁱˡ {a = a}) ≈ unitorⁱˡ
F̂-unitorⁱˡ = F̂-▵ F̂-! F-id

-- unitorⁱʳ = id ▵ !
F̂-unitorⁱʳ : Fₘ (unitorⁱʳ {a = a}) ≈ unitorⁱʳ
F̂-unitorⁱʳ = F̂-▵ F-id F̂-!

-- assocˡ = second exl ▵ exr ∘ exr
F̂-assocˡ : Fₘ (assocˡ {a = a}{b}{c}) ≈ assocˡ
F̂-assocˡ = F̂-▵ (F̂-second F̂-exl) (F̂-∘ F̂-exr F̂-exr)

-- assocʳ = exl ∘ exl ▵ first exr
F̂-assocʳ : Fₘ (assocʳ {a = a}{b}{c}) ≈ assocʳ
F̂-assocʳ = F̂-▵ (F̂-∘ F̂-exl F̂-exl) (F̂-first F̂-exr)

-- inAssocˡ′ f = assocʳ ∘ f ∘ assocˡ
-- inAssocˡ′ : ((a × b) × c ⇨ (a′ × b′) × c′) → (a × (b × c) ⇨ a′ × (b′ × c′))
-- inAssocˡ′ f = assocʳ ∘ f ∘ assocˡ


-- inAssocˡ : (a × b ⇨ a′ × b′) → (a × (b × c) ⇨ a′ × (b′ × c))
-- inAssocˡ = inAssocˡ′ ∙ first

-- inAssocʳ′ : (a × (b × c) ⇨ a′ × (b′ × c′)) → ((a × b) × c ⇨ (a′ × b′) × c′)
-- inAssocʳ′ f = assocˡ ∘ f ∘ assocʳ

-- inAssocʳ : (b × c ⇨ b′ × c′) → ((a × b) × c ⇨ (a × b′) × c′)
-- inAssocʳ = inAssocʳ′ ∙ second

-- swap : a × b ⇨ b × a
-- swap = exr ▵ exl

-- transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
-- transpose = inAssocʳ (inAssocˡ swap)
