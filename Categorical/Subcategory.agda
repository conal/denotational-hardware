-- *Full* subcategory or something like it. Note that the I → obj homomorphism
-- needn't be injective.
{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Homomorphism
open import Categorical.Laws as L
       hiding (Category; Cartesian; Monoid; CartesianClosed; Logic)
open import Categorical.Reasoning

module Categorical.Subcategory
  {j} (J : Set j)
  {o ℓ} {obj : Set o}
  (_↠_ : obj → obj → Set ℓ) (let infix 0 _↠_; _↠_ = _↠_)
  ⦃ _ : Category _↠_ ⦄
  ⦃ Hₒ : Homomorphismₒ J obj ⦄
 where

infix 0 _⇨_
record _⇨_ (a b : J) : Set ℓ where
  constructor mk
  field
    un : Fₒ a ↠ Fₒ b
open _⇨_ public

-- I occassionally need to exclude this one instance.
instance
  subcat-logic : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
                 ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
                 ⦃ _ : Products J ⦄  ⦃ _ : Boolean J ⦄ ⦃ _ : ProductsH J _↠_ ⦄
                 ⦃ _ : BooleanH J _↠_ ⦄
               → Logic _⇨_
  subcat-logic = record
    { false = mk (β ∘ false ∘ ε⁻¹)
    ; true  = mk (β ∘ true  ∘ ε⁻¹)
    ; not   = mk (β ∘ not ∘ β⁻¹)
    ; ∧     = mk (β ∘  ∧  ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    ; ∨     = mk (β ∘  ∨  ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    ; xor   = mk (β ∘ xor ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    ; cond  = mk (cond ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹)
    }

module subcategory-instances where instance

  category : Category _⇨_
  category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

  cartesian : ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄
              ⦃ _ : Products J ⦄ ⦃ _ : ProductsH J _↠_ ⦄ →
              Cartesian _⇨_
  cartesian = record { !   = mk (ε ∘ !)
                     ; _▵_ = λ (mk f) (mk g) → mk (μ ∘ (f ▵ g))
                     ; exl = mk (exl ∘ μ⁻¹)
                     ; exr = mk (exr ∘ μ⁻¹)
                     }

  traced : ⦃ _ : Products obj ⦄ ⦃ _ : Traced _↠_ ⦄
           ⦃ _ : Products J ⦄ ⦃ _ : ProductsH J _↠_ ⦄ →
           Traced _⇨_
  traced = record
    { WF = λ (mk f) → WF (μ⁻¹ ∘ f ∘ μ)
    ; trace = λ (mk f) wf → mk (trace (μ⁻¹ ∘ f ∘ μ) wf)
    }

  module _ where

    open import HasAlgebra

    monoid : {i : Level} {I : Set i} ⦃ _ : HasRawMonoid I ⦄
             ⦃ _ : Products obj ⦄ (M : I → obj)
             ⦃ _ : Products  J  ⦄ (N : I →  J )
             ⦃ _ : ProductsH J _↠_ ⦄ ⦃ _ : MonoidObjH N M _↠_ ⦄
             ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Monoid M _↠_ ⦄ →
             Monoid N _⇨_
    monoid M N = record
      { ⟨ι⟩ = mk (δ ∘ ⟨ι⟩ ∘ ε⁻¹)
      ; ⟨∙⟩ = mk (δ ∘ ⟨∙⟩ ∘ (δ⁻¹ ⊗ δ⁻¹) ∘ μ⁻¹)
      }

  H : Homomorphism _⇨_ _↠_
  H = record { Fₘ = λ (mk f) → f }

  module _ {q : Level} ⦃ _ : Equivalent q _↠_ ⦄ where

    refl↠ : ∀ {a b}{f : a ↠ b} → f ≈ f
    refl↠ = refl

    instance

      equivalent : Equivalent q _⇨_
      equivalent = H-equiv

      categoryH : CategoryH _⇨_ _↠_
      categoryH = record { F-id = refl↠ ; F-∘ = refl↠ }

      cartesianH :
        ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : L.Category _↠_ ⦄
        ⦃ _ : Products J ⦄ ⦃ _ : ProductsH J _↠_ ⦄ ⦃ _ : StrongProductsH J _↠_ ⦄
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
               ⦃ _ : Boolean J ⦄ ⦃ _ : Products J ⦄
               ⦃ _ : ProductsH J _↠_ ⦄ ⦃ _ : StrongProductsH J _↠_ ⦄
               ⦃ _ : BooleanH J _↠_ ⦄ ⦃ _ : StrongBooleanH J _↠_ ⦄ →
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

                F-c  : ∀ {a : J} →
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
