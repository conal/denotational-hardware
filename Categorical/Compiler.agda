open import Level

open import Functions
import Functions.Raw as F
open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L
  hiding (Category; Cartesian; CartesianClosed; Logic)
open import Categorical.Homomorphism

module Categorical.Compiler
  {o}{obj : Set o}{ℓ}(_⇨_ : obj → obj → Set ℓ)
    ⦃ c : Category _⇨_ ⦄
    {q} ⦃ _ : Equivalent q _⇨_ ⦄
    ⦃ _ : L.Category _⇨_ ⦄
    {ℓₛ}⦃ hₒ : Homomorphismₒ obj (Set ℓₛ) ⦄ ⦃ h : Homomorphism _⇨_ (Function ℓₛ) ⦄
    ⦃ H : CategoryH _⇨_ (Function ℓₛ) {_}
           ⦃ F.→-raw-instances.equivalent ℓₛ ⦄ ⦃ c ⦄ ⦃ F.→-raw-instances.category ℓₛ ⦄ ⦄
 where

open import Data.Product
open import Data.Unit renaming (⊤ to Top)
open import Data.List using (List; []; _∷_)
open import Axiom.Extensionality.Propositional
import Relation.Binary.PropositionalEquality as PEq

open import Reflection
open import Reflection.TypeChecking.Monad.Syntax

-- First, we somehow need a mapping from Sets into the objects of the category
-- we're compiling to
module WithInv
  ⦃ inv-hₒ : Homomorphismₒ (Set ℓₛ) obj ⦄
  ( is-inv : {A : Set ℓₛ} → Fₒ (Fₒ A) PEq.≡ A )
  where

  cast : {A : Set ℓₛ} → F.Function _ A (Fₒ (Fₒ A))
  cast {A} x = PEq.subst (λ P → F.Function _ A P) (PEq.sym is-inv) (λ x → x) x

  uncast : {A : Set ℓₛ} → F.Function _ (Fₒ (Fₒ A)) A
  uncast {A} x = PEq.subst (λ P → F.Function _ P A) (PEq.sym is-inv) (λ x → x) x

  open F.→-raw-instances ℓₛ

  record C2C {A B : Set ℓₛ}(g : Function _ A B) : Set (ℓ ⊔ ℓₛ) where
    field
      result  : Fₒ A ⇨ Fₒ B
      correct : Fₘ result ≈ (cast ∘ g ∘ uncast)

  -- Calling "invert g", for instance, should unify the hole with: Σ obj (λ f → Hₒ obj ≈ g)
  macro
    invert : ∀{a} → (A : Set a) → Term → TC Top
    invert g hole = {!!}
