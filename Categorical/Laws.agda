{-# OPTIONS --safe --without-K #-}

module Categorical.Laws where

open import Level

open import Categorical.Raw as R hiding (Category; Cartesian; CartesianClosed; Logic)
open import Categorical.Equiv
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Function.Equality using (_⟨$⟩_)
open import Functions.Raw

open Equivalence
open ≈-Reasoning

private
  variable
    o ℓ : Level
    obj : Set o
    a b c d e : obj

record Category {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                {q} ⦃ equiv : Equivalent q _⇨′_ ⦄
                ⦃ rcat : R.Category _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    identityˡ : {f : a ⇨ b} → id ∘ f ≈ f
    identityʳ : {f : a ⇨ b} → f ∘ id ≈ f
    assoc     : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    -- TODO: infix?
    ∘≈ : ∀ {f g : a ⇨ b} {h k : b ⇨ c} → h ≈ k → f ≈ g → h ∘ f ≈ k ∘ g

  -- TODO: replace the assoc field after I've inspected all uses
  ∘-assocʳ : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
  ∘-assocʳ = assoc

  ∘-assocˡ : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
  ∘-assocˡ = sym ∘-assocʳ

  ∘≈ˡ : ∀ {f : a ⇨ b} {h k : b ⇨ c} → h ≈ k → h ∘ f ≈ k ∘ f
  ∘≈ˡ h≈k = ∘≈ h≈k refl

  ∘≈ʳ : ∀ {f g : a ⇨ b} {h : b ⇨ c} → f ≈ g → h ∘ f ≈ h ∘ g
  ∘≈ʳ f≈g = ∘≈ refl f≈g

  -- Taken from Categories.Morphism.Reasoning.Core in agda-categories.
  -- I'll probably add more and move them to another module.

  center : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{i : d ⇨ e}{hg : b ⇨ d}
         → h ∘ g ≈ hg → (i ∘ h) ∘ (g ∘ f) ≈ i ∘ hg ∘ f
  center {f = f}{g}{h}{i}{hg} h∘g≈hg =
    begin
      (i ∘ h) ∘ (g ∘ f)
    ≈⟨ assoc ⟩
      i ∘ h ∘ (g ∘ f)
    ≈˘⟨ ∘≈ʳ assoc ⟩
      i ∘ (h ∘ g) ∘ f
    ≈⟨ ∘≈ʳ (∘≈ˡ h∘g≈hg) ⟩
      i ∘ hg ∘ f
    ∎

  cancelInner : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ b}{i : b ⇨ d}
              → h ∘ g ≈ id → (i ∘ h) ∘ (g ∘ f) ≈ i ∘ f
  cancelInner {f = f}{g}{h}{i} h∘g≈id =
    begin
      (i ∘ h) ∘ (g ∘ f)
    ≈⟨ center h∘g≈id ⟩
      i ∘ id ∘ f
    ≈⟨ ∘≈ʳ identityˡ ⟩
      i ∘ f
    ∎

open Category ⦃ … ⦄ public

open import Data.Product using (_,_) renaming (_×_ to _×ₚ_)

record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
                 (_⇨′_ : obj → obj → Set ℓ)
                 {q} ⦃ _ : Equivalent q _⇨′_ ⦄
                 ⦃ _ : R.Category _⇨′_ ⦄ ⦃ _ : R.Cartesian _⇨′_ ⦄
                 ⦃ ⇨Category : Category _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_

  field
    ∀⊤ : ∀ {f : a ⇨ ⊤} → f ≈ !

    ∀× : ∀ {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
       → k ≈ f ▵ g ⇔ (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g)

    -- TODO: infix?
    ▵≈ : ∀ {f g : a ⇨ c} {h k : a ⇨ d} → h ≈ k → f ≈ g → h ▵ f ≈ k ▵ g

  ∀×→ : ∀ {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
     → k ≈ f ▵ g → (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g)
  ∀×→ = to ∀× ⟨$⟩_

  ∀×← : ∀ {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
     → (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g) → k ≈ f ▵ g
  ∀×← = from ∀× ⟨$⟩_

  ▵≈ˡ : ∀ {f : a ⇨ c} {h k : a ⇨ d} → h ≈ k → h ▵ f ≈ k ▵ f
  ▵≈ˡ h≈k = ▵≈ h≈k refl

  ▵≈ʳ : ∀ {f g : a ⇨ c} {h : a ⇨ d} → f ≈ g → h ▵ f ≈ h ▵ g
  ▵≈ʳ f≈g = ▵≈ refl f≈g

  open import Data.Product using (proj₁; proj₂)
  -- TODO: Generalize Function category from level 0, and use exl & exr in place
  -- of proj₁ & proj₂

  exl∘▵ : ∀ {f : a ⇨ b}{g : a ⇨ c} → exl ∘ (f ▵ g) ≈ f
  exl∘▵ = proj₁ (∀×→ refl)

  exr∘▵ : ∀ {f : a ⇨ b}{g : a ⇨ c} → exr ∘ (f ▵ g) ≈ g
  exr∘▵ = proj₂ (∀×→ refl)

  -- Specializing:
  -- exl∘▵ : ∀ {f : a ⇨ c}{g : b ⇨ d} → exl ∘ (f ⊗ g) ≈ f ∘ exl
  -- exr∘▵ : ∀ {f : a ⇨ c}{g : b ⇨ d} → exr ∘ (f ⊗ g) ≈ g ∘ exr

  exl▵exr : ∀ {a b : obj} → exl ▵ exr ≈ id {a = a × b}
  exl▵exr = sym (∀×← (identityʳ , identityʳ))

  id⊗id : ∀ {a b : obj} → id ⊗ id ≈ id {a = a × b}
  id⊗id = exl▵exr • ▵≈ identityˡ identityˡ

  ▵∘ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : b ⇨ d} → (g ▵ h) ∘ f ≈ g ∘ f ▵ h ∘ f
  ▵∘ {f = f}{g}{h}= ∀×← (∘≈ˡ exl∘▵ • sym assoc , ∘≈ˡ exr∘▵ • sym assoc)
  -- exl ∘ ((g ▵ h) ∘ f) ≈ g ∘ f

  ⊗∘▵ : ∀ {f : a ⇨ b}{g : a ⇨ c}{h : b ⇨ d}{k : c ⇨ e}
      → (h ⊗ k) ∘ (f ▵ g) ≈ h ∘ f ▵ k ∘ g
  ⊗∘▵ {f = f}{g}{h}{k} =
    begin
      (h ⊗ k) ∘ (f ▵ g)
    ≡⟨⟩
      (h ∘ exl ▵ k ∘ exr) ∘ (f ▵ g)
    ≈⟨ ▵∘ ⟩
      (h ∘ exl) ∘ (f ▵ g) ▵ (k ∘ exr) ∘ (f ▵ g)
    ≈⟨ ▵≈ assoc assoc ⟩
      h ∘ exl ∘ (f ▵ g) ▵ k ∘ exr ∘ (f ▵ g)
    ≈⟨ ▵≈ (∘≈ʳ exl∘▵) (∘≈ʳ exr∘▵) ⟩
      h ∘ f ▵ k ∘ g
    ∎

  swap-▵ : ∀ { f : a ⇨ b } { g : a ⇨ c } → swap ∘ (f ▵ g) ≈ (g ▵ f)
  swap-▵ {f = f} {g} =
    begin
      swap ∘ (f ▵ g)
    ≡⟨⟩
      (exr ▵ exl) ∘ (f ▵ g)
    ≈⟨ ▵∘ ⟩
      (exr ∘ (f ▵ g) ▵ exl ∘ (f ▵ g))
    ≈⟨ ▵≈ exr∘▵ exl∘▵ ⟩
      g ▵ f
    ∎

open Cartesian ⦃ … ⦄ public

record CartesianClosed {obj : Set o} ⦃ _ : Products obj ⦄
                       ⦃ _ : Exponentials obj ⦄ (_⇨′_ : obj → obj → Set ℓ)
                       {q} ⦃ _ : Equivalent q _⇨′_ ⦄
                       ⦃ _ : Products (Set q) ⦄
                       ⦃ _ : R.Category _⇨′_ ⦄
                       ⦃ _ : R.Cartesian _⇨′_ ⦄
                       ⦃ _ : R.CartesianClosed _⇨′_ ⦄
                       ⦃ ⇨Category : Category _⇨′_ ⦄ ⦃ ⇨Cartesian : Cartesian _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ∀⇛ : ∀ {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)} → (g ≈ curry f) ⇔ (f ≈ uncurry g)
    -- Note: uncurry g ≡ apply ∘ first g ≡ apply ∘ (g ⊗ id)
    -- RHS is often written "apply ∘ (g ⊗ id)"

    curry≈ : ∀ {f g : a × b ⇨ c} → f ≈ g → curry f ≈ curry g

  ∀⇛→ : ∀ {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)}
      → g ≈ curry f → f ≈ uncurry g
  ∀⇛→ = to ∀⇛ ⟨$⟩_

  ∀⇛← : ∀ {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)}
      → f ≈ uncurry g → g ≈ curry f
  ∀⇛← = from ∀⇛ ⟨$⟩_

  curry-apply : ∀ {a b : obj} → id { a = a ⇛ b } ≈ curry apply
  curry-apply = ∀⇛← (begin
                       apply
                     ≈˘⟨ identityʳ ⟩
                       apply ∘ id
                     ≈˘⟨ ∘≈ʳ id⊗id ⟩
                       apply ∘ (id ⊗ id)
                     ≡⟨⟩
                       apply ∘ first id
                     ≡⟨⟩
                       uncurry id
                     ∎)

open CartesianClosed ⦃ … ⦄ public

record Logic {obj : Set o} ⦃ _ : Products obj ⦄
             ⦃ _ : Boolean obj ⦄ (_⇨′_ : obj → obj → Set ℓ)
             {q} ⦃ _ : Equivalent q _⇨′_ ⦄
             ⦃ _ : R.Cartesian _⇨′_ ⦄
             ⦃ _ : Cartesian _⇨′_ ⦄
             ⦃ _ : R.Logic _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
    infix 4 _≋_
    _≋_ : (f g : a ⇨ b) → Set q -- Forces _≈_ to use the correct _⇨_ type
    _≋_ = _≈_

  field
    ∨-commutative : ∨ ∘ swap ≋ ∨
    ∧-commutative : ∧ ∘ swap ≋ ∧
    xor-commutative : xor ∘ swap ≋ xor

    ∨-annihilatorˡ : ∀ { any : ⊤ ⇨ Bool } → ∨ ∘ (true ▵ any) ≋ true
    ∧-annihilatorˡ : ∀ { any : ⊤ ⇨ Bool } → ∧ ∘ (false ▵ any) ≋ false

    ∨-idˡ : ∀ {g : ⊤ ⇨ Bool} → ∨ ∘ (false ▵ g) ≋ g
    ∧-idˡ : ∀ {g : ⊤ ⇨ Bool} → ∧ ∘ (true  ▵ g) ≋ g

    ∨-idempotence : ∨ ∘ dup ≋ id
    ∧-idempotence : ∧ ∘ dup ≋ id

    -- TODO: Once we have CoCartesian Categories
    -- ∨-dist-∧ : x ∨ (y ∧ z) ≋ (x ∨ y) ∧ (x ∨ z)
    -- ∧-dist-∨ : x ∧ (y ∧ z) ≋ (x ∧ y) ∨ (x ∧ z)

    de-morganŝ : not ∘ ∨ ≋ ∧ ∘ (not ⊗ not)
    de-morganš : not ∘ ∧ ≋ ∨ ∘ (not ⊗ not)

    not∘not≈id : not ∘ not ≋ id

    -- A xor B ≋ ( A ∨ B ) ∧ (not ( A ∧ B ))
    ∧∨-xor : xor ≋ ∧ ∘ (∨ ▵ not ∘ ∧)

    condˡ : ∀ { a : obj } → cond ∘ first false ≋ exl {a = a} ∘ unitorᵉˡ
    condʳ : ∀ { a : obj } → cond ∘ first true  ≋ exr {a = a} ∘ unitorᵉˡ


  ∨-annihilatorʳ : ∀ { any : ⊤ ⇨ Bool } → ∨ ∘ (any ▵ true) ≋ true
  ∨-annihilatorʳ {any} =
    begin
      ∨ ∘ (any ▵ true)
    ≈⟨ ∘≈ˡ (sym ∨-commutative) ⟩
      (∨ ∘ swap) ∘ (any ▵ true)
    ≈⟨ ∘-assocʳ ⟩
      ∨ ∘ (swap ∘ (any ▵ true))
    ≈⟨ ∘≈ʳ swap-▵ ⟩
      ∨ ∘ (true ▵ any)
    ≈⟨ ∨-annihilatorˡ ⟩
      true
    ∎

  ∧-annihilatorʳ : ∀ { any : ⊤ ⇨ Bool } → ∧ ∘ (any ▵ false) ≋ false
  ∧-annihilatorʳ {any} =
    begin
      ∧ ∘ (any ▵ false)
    ≈⟨ ∘≈ˡ (sym ∧-commutative) ⟩
      (∧ ∘ swap) ∘ (any ▵ false)
    ≈⟨ ∘-assocʳ ⟩
      ∧ ∘ (swap ∘ (any ▵ false))
    ≈⟨ ∘≈ʳ swap-▵ ⟩
      ∧ ∘ (false ▵ any)
    ≈⟨ ∧-annihilatorˡ ⟩
      false
    ∎

  ∨-idʳ : ∀ {f : ⊤ ⇨ Bool} → ∨ ∘ (f ▵ false) ≋ f
  ∨-idʳ {f} =
    begin
      ∨ ∘ (f ▵ false)
    ≈⟨ ∘≈ˡ (sym ∨-commutative) ⟩
      (∨ ∘ swap) ∘ (f ▵ false)
    ≈⟨ ∘-assocʳ ⟩
      ∨ ∘ (swap ∘ (f ▵ false))
    ≈⟨ ∘≈ʳ swap-▵ ⟩
      ∨ ∘ (false ▵ f)
    ≈⟨ ∨-idˡ ⟩
      f
    ∎

  ∧-idʳ : ∀ {f : ⊤ ⇨ Bool} → ∧ ∘ (f ▵ true) ≋ f
  ∧-idʳ {f} =
    begin
      ∧ ∘ (f ▵ true)
    ≈⟨ ∘≈ˡ (sym ∧-commutative) ⟩
      (∧ ∘ swap) ∘ (f ▵ true)
    ≈⟨ ∘-assocʳ ⟩
      ∧ ∘ (swap ∘ (f ▵ true))
    ≈⟨ ∘≈ʳ swap-▵ ⟩
      ∧ ∘ (true ▵ f)
    ≈⟨ ∧-idˡ ⟩
      f
    ∎
