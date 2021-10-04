{-# OPTIONS --safe --without-K #-}

module Routing.Swizzle.Properties {A : Set} where

open import Data.Product using (uncurry) renaming (<_,_> to _▵_)
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality ; open ≡-Reasoning
open import Function

open import Routing.Swizzle

swizzle-allFin : ∀ {a} → swizzle {A} (allFin a) ≗ id
swizzle-allFin = map-lookup-allFin

swizzle-swizzle : {a b c : ℕ}(g : Swizzle b c)(f : Swizzle a b)
                → swizzle {A} (swizzle g f) ≗ swizzle g ∘ swizzle f
swizzle-swizzle g f xs =
  begin
    swizzle (swizzle g f) xs
  ≡⟨⟩
    map (lookup xs) (map (lookup f) g)
  ≡˘⟨ map-∘ (lookup xs) (lookup f) g ⟩
    map (lookup xs ∘ lookup f) g
  ≡˘⟨ map-cong (λ i → lookup-map i (lookup xs) f) g ⟩
    map (lookup (map (lookup xs) f)) g
  ≡⟨⟩
    (swizzle g ∘ swizzle f) xs
  ∎

swizzle-tabulate-inject+ : ∀ {m n} → swizzle {A} (tabulate (inject+ n)) ≗ take m
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

swizzle-tabulate-raise : ∀ {m n} → swizzle {A} (tabulate (raise {n} m)) ≗ drop m
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

swizzle-[] : ∀ {m} → swizzle {A}{m} [] ≗ const []
swizzle-[] xs = refl

-- Oddly, I didn't find this lemma in agda-stdlib
map-++ : ∀ {ℓ}{A B : Set ℓ}(f : A → B){m n}(u : Vec A m)(v : Vec A n)
       → map f (u ++ v) ≡ map f u ++ map f v
map-++ f [] v = refl
map-++ f (x ∷ u) v = cong (f x ∷_) (map-++ f u v)

swizzle-++ : ∀ {a c d} (f : Swizzle a c)(g : Swizzle a d)
           → swizzle {A} (f ++ g) ≗ uncurry _++_ ∘ (swizzle f ▵ swizzle g)
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
