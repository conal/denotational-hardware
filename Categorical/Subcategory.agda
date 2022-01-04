-- *Full* subcategory or something like it. Note that the I → obj homomorphism
-- needn't be injective.
{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Homomorphism
open import Categorical.Laws as L
       hiding (Category; Cocartesian; Cartesian; Semigroup; Monoid; CartesianClosed; Logic)
open import Categorical.Reasoning

module Categorical.Subcategory
  {i} (I : Set i)
  {o ℓ} {obj : Set o}
  (_↠_ : obj → obj → Set ℓ) (let infix 0 _↠_; _↠_ = _↠_)
  ⦃ _ : Category _↠_ ⦄ {q : Level} ⦃ _ : Equivalent q _↠_ ⦄
  ⦃ _ : Homomorphismₒ I obj ⦄
 where

infix 0 _⇨_
record _⇨_ (a b : I) : Set ℓ where
  constructor mk
  field
    un : Fₒ a ↠ Fₒ b
open _⇨_ public

module subcategory-instances where

  refl↠ : ∀ {a b}{f : a ↠ b} → f ≈ f
  refl↠ = refl

  instance
    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    cocartesian : ⦃ _ : Coproducts obj ⦄ ⦃ _ : Cocartesian _↠_ ⦄
                  ⦃ _ : Coproducts I ⦄ → -- ⦃ _ : ProductsH I _↠_ ⦄ →
                  Cocartesian _⇨_
    cocartesian = {!!}


    cartesian : ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄
                ⦃ _ : Products I ⦄ ⦃ _ : ProductsH I _↠_ ⦄ →
                Cartesian _⇨_
    cartesian = record { !   = mk (ε ∘ !)
                       ; _▵_ = λ (mk f) (mk g) → mk (μ ∘ (f ▵ g))
                       ; exl = mk (exl ∘ μ⁻¹)
                       ; exr = mk (exr ∘ μ⁻¹)
                       }

    semigroup : ⦃ _ : Products obj ⦄ ⦃ _ : MonoidObj obj ⦄
                ⦃ _ : Products I   ⦄ ⦃ _ : MonoidObj I ⦄
                ⦃ _ : ProductsH I _↠_ ⦄ ⦃ _ : MonoidObjH I _↠_ ⦄
                ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Semigroup _↠_ ⦄ →
                Semigroup _⇨_
    semigroup = record { ⟨∙⟩ = mk (δ ∘ ⟨∙⟩ ∘ (δ⁻¹ ⊗ δ⁻¹) ∘ μ⁻¹) }

    monoid : ⦃ _ : Products obj ⦄ ⦃ _ : MonoidObj obj ⦄
             ⦃ _ : Products I   ⦄ ⦃ _ : MonoidObj I ⦄
             ⦃ _ : ProductsH I _↠_ ⦄ ⦃ _ : MonoidObjH I _↠_ ⦄
             ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Semigroup _↠_ ⦄ ⦃ _ : Monoid _↠_ ⦄ →
             Monoid _⇨_
    monoid = record { ⟨ι⟩ = mk (δ ∘ ⟨ι⟩ ∘ ε⁻¹) }

    logic : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
            ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
            ⦃ _ : Products I ⦄  ⦃ _ : Boolean I ⦄ ⦃ _ : ProductsH I _↠_ ⦄
            ⦃ _ : BooleanH I _↠_ ⦄
          → Logic _⇨_
    logic = record
              { false = mk (β ∘ false ∘ ε⁻¹)
              ; true  = mk (β ∘ true  ∘ ε⁻¹)
              ; not   = mk (β ∘ not ∘ β⁻¹)
              ; ∧     = mk (β ∘  ∧  ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
              ; ∨     = mk (β ∘  ∨  ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
              ; xor   = mk (β ∘ xor ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
              ; cond  = mk (cond ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹)
              }

    H : Homomorphism _⇨_ _↠_
    H = record { Fₘ = λ (mk f) → f }

    equivalent : Equivalent q _⇨_
    equivalent = H-equiv

    categoryH : CategoryH _⇨_ _↠_
    categoryH = record { F-id = refl↠ ; F-∘ = refl↠ }

    cartesianH :
      ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : L.Category _↠_ ⦄
      ⦃ _ : Products I ⦄ ⦃ _ : ProductsH I _↠_ ⦄ ⦃ _ : StrongProductsH I _↠_ ⦄
      → CartesianH _⇨_ _↠_
    cartesianH = record { F-! = refl↠
                        ; F-▵ = refl↠
                        ; F-exl = ∘-assoc-elimʳ μ⁻¹∘μ   -- (exl ∘ μ⁻¹) ∘ μ ≈ exl
                        ; F-exr = ∘-assoc-elimʳ μ⁻¹∘μ   -- (exr ∘ μ⁻¹) ∘ μ ≈ exr
                        }

    logicH :
             ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
             ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
             ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄
             ⦃ _ : Boolean I ⦄ ⦃ _ : Products I ⦄
             ⦃ _ : ProductsH I _↠_ ⦄ ⦃ _ : StrongProductsH I _↠_ ⦄
             ⦃ _ : BooleanH I _↠_ ⦄ ⦃ _ : StrongBooleanH I _↠_ ⦄ →
             LogicH _⇨_ _↠_
    logicH = record
               { F-false = F-0
               ; F-true  = F-0
               ; F-not   = F-1
               ; F-∧     = F-2
               ; F-∨     = F-2
               ; F-xor   = F-2
               ; F-cond  = F-c
               }
        where
              F-0 : ∀ {f : ⊤ ↠ Bool} → (β ∘ f ∘ ε⁻¹) ∘ ε ≈ β ∘ f
              F-0 = ∘-assocʳ³ ; ∘-assocˡ ; elimʳ ε⁻¹∘ε

              -- F-0 {f} = let open ≈-Reasoning in
              --  begin
              --    (β ∘ f ∘ ε⁻¹) ∘ ε
              --  ≈⟨ ∘-assocʳ³ ⟩
              --    β ∘ f ∘ (ε⁻¹ ∘ ε)
              --  ≈⟨ ∘-assocˡ ⟩
              --    (β ∘ f) ∘ (ε⁻¹ ∘ ε)
              --  ≈⟨ elimʳ ε⁻¹∘ε ⟩
              --    β ∘ f
              --  ∎

              F-1 : ∀ {f : Bool ↠ Bool} → (β ∘ f ∘ β⁻¹) ∘ β ≈ β ∘ f
              F-1 = ∘-assocʳ³ ; ∘-assocˡ ; elimʳ β⁻¹∘β

              F-2 : ∀ {f : Bool × Bool ↠ Bool} →
                (β ∘ f ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹) ∘ μ ∘ (β ⊗ β) ≈ β ∘ f
              F-2 = ∘-assocˡ′ ∘-assocʳ⁴
                  ; ∘≈ˡ (∘-assocˡ³ ; elimʳ μ⁻¹∘μ ; ∘-assocˡ)
                  ; ∘-assoc-elimʳ (⊗-inverse β⁻¹∘β β⁻¹∘β)

              -- F-2 {f} = let open ≈-Reasoning in
              --           begin
              --             (β ∘ f ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹) ∘ μ ∘ (β ⊗ β)
              --           ≈⟨ ∘-assocˡ′ ∘-assocʳ⁴ ⟩
              --             (β ∘ f ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹ ∘ μ) ∘ (β ⊗ β)
              --           ≈⟨ ∘≈ˡ (∘-assocˡ³ ; elimʳ μ⁻¹∘μ ; ∘-assocˡ) ⟩
              --             ((β ∘ f) ∘ (β⁻¹ ⊗ β⁻¹)) ∘ (β ⊗ β)
              --           ≈⟨ ∘-assoc-elimʳ (⊗-inverse β⁻¹∘β β⁻¹∘β) ⟩
              --             β ∘ f
              --           ∎

              F-c  : ∀ {a : I} →
                (cond ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹) ∘ μ ∘ (β ⊗ μ {a = a}) ≈ cond
              F-c = ∘-assocˡ′ (∘-assocʳ³ ; ∘≈ʳ (elimʳ μ⁻¹∘μ))
                  ; ∘-assoc-elimʳ (⊗-inverse β⁻¹∘β μ⁻¹∘μ)

              -- F-c =
              --   let open ≈-Reasoning in
              --   begin
              --     (cond ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹) ∘ μ ∘ (β ⊗ μ)
              --   ≈⟨ ∘-assocˡ′ (∘-assocʳ³ ; ∘≈ʳ (elimʳ μ⁻¹∘μ)) ⟩
              --     (cond ∘ (β⁻¹ ⊗ μ⁻¹)) ∘ (β ⊗ μ)
              --   ≈⟨ ∘-assoc-elimʳ (⊗-inverse β⁻¹∘β μ⁻¹∘μ) ⟩
              --     cond
              --   ∎

    open import Categorical.MakeLawful _⇨_ _↠_

    l-category : ⦃ _ : L.Category _↠_ ⦄ → L.Category _⇨_
    l-category = LawfulCategoryᶠ
