{-# OPTIONS --safe --without-K #-}

open import Function using (id) renaming (_∘_ to _∙_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

module Routing.Homomorphism where

open import Functions.Raw
open import Functions.Laws
open import Routing.Raw public
open import Ty
open import Index

open import Categorical.Homomorphism hiding (id)
open import Categorical.Laws

lookup∘tabulate : ∀{a}{f : Indexer Fₒ a} → ∀{z}(i : Index z a)
                → lookup (tabulate f) i ≡ f i
lookup∘tabulate bit       = ≡-refl
lookup∘tabulate fun       = ≡-refl
lookup∘tabulate (left  i) = lookup∘tabulate i
lookup∘tabulate (right j) = lookup∘tabulate j

tabulate∘lookup : {a : Ty}(x : Fₒ a) → tabulate {a = a} (lookup x) ≡ x
tabulate∘lookup {a = `⊤}     tt      = ≡-refl
tabulate∘lookup {a = `Bool}   _      = ≡-refl
tabulate∘lookup {a = a `⇛ b} f       = ≡-refl
tabulate∘lookup {a = a `× b} (x , y) =
  cong₂ _,_ (tabulate∘lookup {a} x) (tabulate∘lookup {b} y)

≈-tabulate : {a : Ty}{f g : Indexer Fₒ a} → (∀{z}(i : Index z a) → f i ≡ g i)
           → tabulate f ≡ tabulate g
≈-tabulate {`⊤}     f≈g = ≡-refl
≈-tabulate {`Bool}  f≈g = f≈g bit
≈-tabulate {_ `⇛ _} f≈g = f≈g fun
≈-tabulate {_ `× _} f≈g = cong₂ _,_ (≈-tabulate (f≈g ∙ left))
                                    (≈-tabulate (f≈g ∙ right))

lookup-swizzle-∘ : {b c a : Ty}(g : Swizzle b c)(f : Swizzle a b){x : Fₒ a}
                 → ∀{z}(i : Index z c)
                 → lookup (swizzle f x) (g i) ≡ lookup (tabulate (lookup x ∘ f ∘ g)) i
lookup-swizzle-∘ g f i = ≡-trans (lookup∘tabulate (g i)) (≡-sym (lookup∘tabulate i))

swizzle-id : (a : Ty) → swizzle {a = a} id ≈ id
swizzle-id `⊤       _       = ≡-refl
swizzle-id `Bool    _       = ≡-refl
swizzle-id (a `⇛ b) _       = ≡-refl
swizzle-id (a `× b) (x , y) = cong₂ _,_ (swizzle-id a x) (swizzle-id b y)

swizzle-∘ : {b c a : Ty}(g : Swizzle b c)(f : Swizzle a b)
          → swizzle (f ∘ g) ≈ swizzle g ∘ swizzle f
swizzle-∘ g f x =
  begin
    swizzle (f ∘ g) x
  ≡⟨⟩
    tabulate ((lookup x ∘ f) ∘ g)
  ≡˘⟨ ≈-tabulate (λ i → ≡-trans (lookup-swizzle-∘ g f i) (lookup∘tabulate i)) ⟩
    tabulate (lookup (tabulate (lookup x ∘ f)) ∘ g)
  ≡⟨⟩
    (swizzle g ∘ swizzle f) x
  ∎
 where open ≡-Reasoning

instance

  categoryH : CategoryH _⇨_ Function
  categoryH = record
    { F-id = λ {a} → swizzle-id a
    ; F-∘  = λ { {g = mk g} {mk f} → swizzle-∘ g f }
    }

  cartesianH : CartesianH _⇨_ Function
  cartesianH = record
    { F-!   = λ _ → ≡-refl
    ; F-exl = λ {a b} (x , y) → tabulate∘lookup {a = a} x
    ; F-exr = λ {a b} (x , y) → tabulate∘lookup {a = b} y
    ; F-▵   = λ _ → ≡-refl
    }
