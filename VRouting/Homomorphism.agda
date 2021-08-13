{-# OPTIONS --safe --without-K #-}

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)

module VRouting.Homomorphism {A : Set} where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Vec.Properties

open import Function using (_∘′_) -- TEMP

open import Functions.Raw
open import Functions.Laws
open import Vector.Laws {A} renaming (_⇨_ to _↠_)
open import VRouting.Raw {A} public ; open _⇨_

open import Categorical.Laws
open import Categorical.Homomorphism

open ≡-Reasoning

private

  swizzle-allFin : {a : ℕ} → swizzle (allFin a) ≈ id
  swizzle-allFin = map-lookup-allFin

  swizzle-map-lookup : {a b c : ℕ}(g : Swizzle b c)(f : Swizzle a b)
                     → swizzle (map (lookup f) g) ≈ swizzle g ∘ swizzle f
  swizzle-map-lookup g f xs =
    begin
      swizzle (map (lookup f) g) xs
    ≡⟨⟩
      map (lookup xs) (map (lookup f) g)
    ≡˘⟨ map-∘ (lookup xs) (lookup f) g ⟩
      map (lookup xs ∘ lookup f) g
    ≡˘⟨ map-cong (λ i → lookup-map i (lookup xs) f) g ⟩
      map (lookup (map (lookup xs) f)) g
    ≡⟨⟩
      (swizzle g ∘ swizzle f) xs
    ∎

  swizzle-tabulate-inject+ : ∀ {m n} → swizzle (tabulate (inject+ n)) ≈ take m
  swizzle-tabulate-inject+ {m}{n} xs =
    begin
      swizzle (tabulate (inject+ n)) xs
    ≡⟨⟩
      map (lookup xs) (tabulate (inject+ n))
    ≡˘⟨ tabulate-∘ (lookup xs) (inject+ n) ⟩
      tabulate (lookup xs ∘ inject+ n)
    ≡˘⟨ cong (λ z → tabulate (lookup z ∘ inject+ n)) (take-drop-id m xs) ⟩
      tabulate (lookup (take m xs ++ drop m xs) ∘ inject+ n)
    ≡⟨ tabulate-cong (lookup-++ˡ (take m xs) (drop m xs)) ⟩
      tabulate (lookup (take m xs))
    ≡⟨ tabulate∘lookup _ ⟩
      take m xs
    ∎

  swizzle-tabulate-raise : ∀ {m n} → swizzle (tabulate (raise {n} m)) ≈ drop m
  swizzle-tabulate-raise {m}{n} xs =
    begin
      swizzle (tabulate (raise m)) xs
    ≡⟨⟩
      map (lookup xs) (tabulate (raise m))
    ≡˘⟨ tabulate-∘ (lookup xs) (raise m) ⟩
      tabulate (lookup xs ∘ raise m)
    ≡˘⟨ cong (λ z → tabulate (lookup z ∘ raise m)) (take-drop-id m xs) ⟩
      tabulate (lookup (take m xs ++ drop m xs) ∘ raise m)
    ≡⟨ tabulate-cong (lookup-++ʳ (take m xs) (drop m xs)) ⟩
      tabulate (lookup (drop m xs))
    ≡⟨ tabulate∘lookup _ ⟩
      drop m xs
    ∎

  -- Oddly, I didn't find this lemma in agda-stdlib
  map-++ : ∀ {ℓ}{A B : Set ℓ}(f : A → B){m n}(u : Vec A m)(v : Vec A n)
         → map f (u ++ v) ≡ map f u ++ map f v
  map-++ f [] v = refl≡
  map-++ f (x ∷ u) v = cong (f x ∷_) (map-++ f u v)

  swizzle-++ : ∀ {a c d} (f : Swizzle a c)(g : Swizzle a d)
             → swizzle (f ++ g) ≈ uncurry _++_ ∘ (swizzle f ▵ swizzle g)
  swizzle-++ f g xs =
    begin
      swizzle (f ++ g) xs
    ≡⟨⟩
      map (lookup xs) (f ++ g)
    ≡⟨ map-++ (lookup xs) f g ⟩
      map (lookup xs) f ++ map (lookup xs) g
    ≡⟨⟩
      swizzle f xs ++ swizzle g xs
    ≡⟨⟩
      (uncurry _++_ ∘ (swizzle f ▵ swizzle g)) xs
    ∎

module vrouting-homomorphism-instances where

  instance

    categoryH : CategoryH _⇨_ _↠_
    categoryH = record
      { F-id = swizzle-allFin
      ; F-∘  = λ { {g = mk g} {mk f} → swizzle-map-lookup g f }
      }

    pH : ProductsH ℕ _↠_
    pH = id-ProductsH

    cartesianH : CartesianH _⇨_ _↠_
    cartesianH = record
      { F-!   = λ _ → refl≡
      ; F-exl = swizzle-tabulate-inject+
      ; F-exr = swizzle-tabulate-raise
      ; F-▵   = λ {a c d}{(mk f) (mk g)} → swizzle-++ f g
      }

