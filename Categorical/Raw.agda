{-# OPTIONS --safe --without-K #-}

module Categorical.Raw where

open import Level
open import Function using (const) renaming (_∘_ to _∙_)

open import Categorical.Object public

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : {a b c : obj} → (g : b ⇨ c) (f : a ⇨ b) → (a ⇨ c)

open Category ⦃ … ⦄ public

record Cocartesian {obj : Set o} ⦃ _ : Coproducts obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _▿_
  field
    void : ⊥ ⇨ a
    _▿_  : (a ⇨ c) → (b ⇨ c) → (a + b ⇨ c)
    inl  : a ⇨ a + b
    inr  : b ⇨ a + b

  codup : a + a ⇨ a
  codup = id ▿ id

  coswap : a + b ⇨ b + a
  coswap = inr ▿ inl

  infixr 7 _⊕_
  _⊕_ : (a ⇨ c) → (b ⇨ d) → (a + b ⇨ c + d)
  f ⊕ g = inl ∘ f ▿ inr ∘ g

open Cocartesian ⦃ … ⦄ public

record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _▵_
  field
    !   : a ⇨ ⊤
    _▵_ : (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
    exl : a × b ⇨ a
    exr : a × b ⇨ b

  dup : a ⇨ a × a
  dup = id ▵ id

  -- The following operations will probably move to Monoidal or Braided

  infixr 7 _⊗_
  _⊗_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)
  f ⊗ g = f ∘ exl ▵ g ∘ exr

  first : (a ⇨ c) → (a × b ⇨ c × b)
  first f = f ⊗ id

  second : (b ⇨ d) → (a × b ⇨ a × d)
  second g = id ⊗ g

  twice : (a ⇨ c) → (a × a ⇨ c × c)
  twice f = f ⊗ f

  unitorᵉˡ : ⊤ × a ⇨ a
  unitorᵉˡ = exr

  unitorᵉʳ : a × ⊤ ⇨ a
  unitorᵉʳ = exl

  unitorⁱˡ : a ⇨ ⊤ × a
  unitorⁱˡ = ! ▵ id

  unitorⁱʳ : a ⇨ a × ⊤
  unitorⁱʳ = id ▵ !

  assocˡ : a × (b × c) ⇨ (a × b) × c
  assocˡ = second exl ▵ exr ∘ exr

  assocʳ : (a × b) × c ⇨ a × (b × c)
  assocʳ = exl ∘ exl ▵ first exr

  inAssocˡ′ : ((a × b) × c ⇨ (a′ × b′) × c′) → (a × (b × c) ⇨ a′ × (b′ × c′))
  inAssocˡ′ f = assocʳ ∘ f ∘ assocˡ

  inAssocˡ : (a × b ⇨ a′ × b′) → (a × (b × c) ⇨ a′ × (b′ × c))
  inAssocˡ = inAssocˡ′ ∙ first

  inAssocʳ′ : (a × (b × c) ⇨ a′ × (b′ × c′)) → ((a × b) × c ⇨ (a′ × b′) × c′)
  inAssocʳ′ f = assocˡ ∘ f ∘ assocʳ

  inAssocʳ : (b × c ⇨ b′ × c′) → ((a × b) × c ⇨ (a × b′) × c′)
  inAssocʳ = inAssocʳ′ ∙ second

  swap : a × b ⇨ b × a
  swap = exr ▵ exl

  transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
  transpose = inAssocʳ (inAssocˡ swap)

  infixr 4 _⦂_
  -- _⦂_ : ⌞ a ⌟ → ⌞ b ⌟ → ⌞ a × b ⌟
  _⦂_ : (⊤ ⇨ a) → (⊤ ⇨ b) → (⊤ ⇨ a × b)
  a ⦂ b = (a ⊗ b) ∘ unitorⁱˡ

  open import Data.Nat

  mapⱽ : ∀ n → (a ⇨ b) → (V a n ⇨ V b n)
  mapⱽ  zero   f = !
  mapⱽ (suc n) f = f ⊗ mapⱽ n f

  zipⱽ : ∀ n → (V a n × V b n ⇨ V (a × b) n)
  zipⱽ  zero   = !
  zipⱽ (suc n) = second (zipⱽ n) ∘ transpose

  unzipⱽ : ∀ n → (V (a × b) n ⇨ V a n × V b n)
  unzipⱽ  zero   = ! ▵ !
  unzipⱽ (suc n) = transpose ∘ second (unzipⱽ n)

  replicateⱽ : ∀ n → a ⇨ V a n
  replicateⱽ zero    = !
  replicateⱽ (suc n) = id ▵ replicateⱽ n

  -- (a × b) × (V a n × V b n) ⇨ (a × V a n) × (b × V b n)

  mapᵀ : ∀ n → (a ⇨ b) → (T a n ⇨ T b n)
  mapᵀ  zero   f = f
  mapᵀ (suc n) f = mapᵀ n f ⊗ mapᵀ n f

  zipᵀ : ∀ n → (T a n × T b n ⇨ T (a × b) n)
  zipᵀ  zero   = id
  zipᵀ (suc n) = (zipᵀ n ⊗ zipᵀ n) ∘ transpose

  unzipᵀ : ∀ n → (T (a × b) n ⇨ T a n × T b n)
  unzipᵀ  zero   = id
  unzipᵀ (suc n) = transpose ∘ (unzipᵀ n ⊗ unzipᵀ n)

  replicateᵀ : ∀ n → a ⇨ T a n
  replicateᵀ zero    = id
  replicateᵀ (suc n) = replicateᵀ n ▵ replicateᵀ n

open Cartesian ⦃ … ⦄ public

record Semigroup {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : MonoidObj obj ⦄
    (_⇨′_ : obj → obj → Set ℓ) ⦃ _ : Category _⇨′_ ⦄
   : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⟨∙⟩ : M × M ⇨ M

open Semigroup ⦃ … ⦄ public

record Monoid {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : MonoidObj obj ⦄
    (_⇨′_ : obj → obj → Set ℓ) ⦃ _ : Category _⇨′_ ⦄
    ⦃ _ : Semigroup _⇨′_ ⦄  -- not strictly necessary
   : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⟨ι⟩ : ⊤ ⇨ M

open Monoid ⦃ … ⦄ public


{-
record IndexedCartesian
    {obj : Set o} {ℓᵢ} (I : Set ℓᵢ) ⦃ _ : IndexedProducts obj I ⦄
    (_⇨′_ : obj → obj → Set ℓ) ⦃ _ : Category _⇨′_ ⦄
   : Set (o ⊔ ℓ ⊔ ℓᵢ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    △  : {B : I → obj} → (∀ i → a ⇨ B i) → (a ⇨ Π B)
    ex : {A : I → obj} → (i : I) → (Π A ⇨ A i)

  -- Replicate
  rep : a ⇨ Π (const a)
  rep = △ (const id)

  ⨂ : {A B : I → obj} → (∀ i → A i ⇨ B i) → Π A ⇨ Π B
  ⨂ fs = △ λ i → fs i ∘ ex i

  map : (a ⇨ b) → Π (const a) ⇨ Π (const b)
  map f = ⨂ (const f)

open IndexedCartesian ⦃ … ⦄ public
-}


record CartesianClosed {obj : Set o}
         ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
         ⦃ _ : Cartesian _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field

    curry : (a × b ⇨ c) → (a ⇨ (b ⇛ c))
    apply : (a ⇛ b) × a ⇨ b

  uncurry : (a ⇨ (b ⇛ c)) → (a × b ⇨ c)
  uncurry f = apply ∘ first f

open CartesianClosed ⦃ … ⦄ public


record Logic {obj : Set o} ⦃ products : Products obj ⦄ ⦃ boolean : Boolean obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    false true : ⊤ ⇨ Bool
    not : Bool ⇨ Bool
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    cond : Bool × (a × a) ⇨ a

open Logic ⦃ … ⦄ public
