{-# OPTIONS --safe --without-K #-}

module Categorical.Raw where

open import Level
open import Function using () renaming (_∘′_ to _∙_)

open import Categorical.Object public

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e j : obj
    a′ b′ c′ d′ e′ j′ : obj

record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : {a b c : obj} → (g : b ⇨ c) (f : a ⇨ b) → (a ⇨ c)

open Category ⦃ … ⦄ public

module Cartesian where

  record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
           (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
    private infix 0 _⇨_; _⇨_ = _⇨′_
    infixr 7 _▵_
    field
      ⦃ ⇨Category ⦄ : Category _⇨_
      !   : a ⇨ ⊤
      _▵_ : ∀ {a c d} → (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
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

    unzipᵀ : ∀ n → (T (a × b) n ⇨ T a n × T b n)
    unzipᵀ  zero   = id
    unzipᵀ (suc n) = transpose ∘ (unzipᵀ n ⊗ unzipᵀ n)

    replicateᵀ : ∀ n → a ⇨ T a n
    replicateᵀ zero    = id
    replicateᵀ (suc n) = replicateᵀ n ▵ replicateᵀ n

  open Cartesian ⦃ … ⦄ public


  record CartesianClosed {obj : Set o}
           ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄
           (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
    private infix 0 _⇨_; _⇨_ = _⇨′_
    field
      ⦃ ⇨Cartesian ⦄ : Cartesian _⇨_
      curry : (a × b ⇨ c) → (a ⇨ (b ⇛ c))
      apply : (a ⇛ b) × a ⇨ b

    uncurry : (a ⇨ (b ⇛ c)) → (a × b ⇨ c)
    uncurry f = apply ∘ first f

  open CartesianClosed ⦃ … ⦄ public

module CoCartesian where

  record CoCartesian {obj : Set o} ⦃ _ : CoProducts obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
    private infix 0 _⇨_; _⇨_ = _⇨′_
    infixr 7 _▿_
    field
      ⦃ ⇨Category ⦄ : Category _⇨_
      const   : ⊥ ⇨ a
      _▿_ : ∀ {a c d} → (c ⇨ a) → (d ⇨ a) → (c + d ⇨ a)
      inl : a ⇨ a + b
      inr : b ⇨ a + b

    collapse : a + a ⇨ a
    collapse = id ▿ id

    -- The following operations will probably move to Monoidal or Braided

    infixr 7 _⊕_
    _⊕_ : (a ⇨ c) → (b ⇨ d) → (a + b ⇨ c + d)
    f ⊕ g = inl ∘ f ▿ inr ∘ g

    first : a ⇨ c → a + b ⇨ c + b
    first f = f ⊕ id

    second : b ⇨ d → a + b ⇨ a + d
    second g = id ⊕ g

    unitorᵉˡ : ⊥ + a ⇨ a
    unitorᵉˡ = const ▿ id

    unitorᵉʳ : a + ⊥ ⇨ a
    unitorᵉʳ = id ▿ const

    unitorⁱˡ : a ⇨ ⊥ + a
    unitorⁱˡ = inr

    unitorⁱʳ : a ⇨ a + ⊥
    unitorⁱʳ = inl

    assocˡ : a + (b + c) ⇨ (a + b) + c
    assocˡ = inl ∘ inl ▿ first inr

    assocʳ : (a + b) + c ⇨ a + (b + c)
    assocʳ = second inl ▿ inr ∘ inr

    inAssocˡ′ : ((a + b) + c ⇨ (a′ + b′) + c′) → (a + (b + c) ⇨ a′ + (b′ + c′))
    inAssocˡ′ f = assocʳ ∘ f ∘ assocˡ

    inAssocˡ : (a + b ⇨ a′ + b′) → (a + (b + c) ⇨ a′ + (b′ + c))
    inAssocˡ =  inAssocˡ′ ∙ first 

    inAssocʳ′ : (a + (b + c) ⇨ a′ + (b′ + c′)) → ((a + b) + c ⇨ (a′ + b′) + c′)
    inAssocʳ′ f = assocˡ ∘ f ∘ assocʳ

    inAssocʳ : (b + c ⇨ b′ + c′) → ((a + b) + c ⇨ (a + b′) + c′)
    inAssocʳ =  inAssocʳ′ ∙ second

    swap : a + b ⇨ b + a
    swap = inr ▿ inl

    transpose : (a + b) + (c + d) ⇨ (a + c) + (b + d)
    transpose = inAssocʳ (inAssocˡ swap)

  open CoCartesian ⦃ … ⦄ public

  -- CoCartesian Closed ??

-- BiCartesianClosed ??

record BiCartesian {obj : Set o}
           (_⇨′_ : obj → obj → Set ℓ)
           ⦃ _ : Products obj ⦄
           ⦃ _ : CoProducts obj ⦄
           ⦃ _ : Exponentials obj ⦄
           ⦃ cat : Category _⇨′_ ⦄
           ⦃ _ : Cartesian.CartesianClosed _⇨′_ ⦄
           ⦃ _ : CoCartesian.CoCartesian _⇨′_ ⦄
           : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_

  idᶜ : a ⇨ a
  idᶜ = Category.id cat

  infixr 9 _∘ᶜ_
  _∘ᶜ_ : {a b c : obj} → (g : b ⇨ c) (f : a ⇨ b) → (a ⇨ c)
  _∘ᶜ_ = _∘_ ⦃ cat ⦄

  open Cartesian using (exl; exr; _▵_; _⊗_; first; second; swap; curry; apply)
  open CoCartesian using (inl; inr; _▿_; collapse)

  ×+-distˡ : a × (b + c) ⇨ (a × b) + (a × c)
  ×+-distˡ = apply ∘ᶜ (first (curry (inl ∘ᶜ swap) ▿ curry (inr ∘ᶜ swap))) ∘ᶜ swap

  +×-distˡ : a + (b × c) ⇨ (a + b) × (a + c)
  +×-distˡ = (inl ▵ inl) ▿ (inr ⊗ inr)

  ×+-distʳ : (a × b) + (a × c) ⇨ a × (b + c)
  ×+-distʳ = second inl ▿ second inr

  -- Is this possible ?
  -- +×-distʳ : (a + b) × (a + c) ⇨ a + (b × c)

  {- /home/bolt/Desktop/Bolt/Playground/Agda/agda-hardware/Categorical/Raw.agda:234,66-81
     Set ℓ != Set o
     when checking that the expression (f ▵ g) ▿ h ▵ k has type obj

     Should this go to BiCartesian.Laws ?

  ▿▵-dist : ∀ {f : a ⇨ b} {g : a ⇨ c} {h : d ⇨ e} {k : j ⇨ e} → (f ▵ g) ▿ (h ▵ k) ⇨ (f ▿ h) ▵ (g ▿ k)
  ▿▵-dist = ?
  -}

record Logic {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    false true : ⊤ ⇨ Bool
    not : Bool ⇨ Bool
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    cond : Bool × (a × a) ⇨ a

open Logic ⦃ … ⦄ public
