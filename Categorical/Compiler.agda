open import Level

-- Here we import all the needed categorical machinery under the C namespace
import Categorical.Raw as C
import Categorical.Equiv as C
import Categorical.Laws as C renaming (Category to CategoryLaws)
import Categorical.Homomorphism as C

-- And the category of sets and functions under F
import Functions as F

module Categorical.Compiler
  {o}{obj : Set o}{ℓ}(_⇨_ : obj → obj → Set ℓ)
    ⦃ c : C.Category _⇨_ ⦄
    {q} ⦃ cEq : C.Equivalent q _⇨_ ⦄
    ⦃ cLaws : C.CategoryLaws _⇨_ ⦄
    {ℓₛ}⦃ hₒ : C.Homomorphismₒ obj (Set ℓₛ) ⦄ ⦃ h : C.Homomorphism _⇨_ (F.Function ℓₛ) ⦄
    ⦃ H : C.CategoryH _⇨_ (F.Function ℓₛ) {_}
           ⦃ F.→-raw-instances.equivalent ℓₛ ⦄ ⦃ c ⦄ ⦃ F.→-raw-instances.category ℓₛ ⦄ ⦄
 where

open import Data.Product
open import Data.Unit renaming (⊤ to Top)
open import Data.List using (List; []; _∷_)
open import Axiom.Extensionality.Propositional
import Relation.Binary.PropositionalEquality as PEq

open import Reflection
open import Reflection.Name
open import Reflection.Term
open import Reflection.Argument
open import Reflection.DeBruijn
open import Reflection.TypeChecking.Monad.Syntax

open F.→-raw-instances ℓₛ

-- The output of our compiling some g into its categorical representation must be
-- an inhabitant of (ResultType g). Note that we require g to be of type `H P -> H Q ∈ Arr Sets`,
-- this makes sure that we know the type of the resulting arrow, f, beforehand: `P ⇨ Q ∈ Arr C`
ResultType : {P Q : obj} → F.Function _ (C.Fₒ P) (C.Fₒ Q) → Set (ℓ ⊔ ℓₛ)
ResultType {P} {Q} g = Σ (P ⇨ Q) (λ f → C.Fₘ f C.≈ g)

transform : Term → Term × Term
transform t = (t , con (quote tt) [])

mkProd : Term × Term → Term
mkProd (a , b) = con (quote _,_) (vArg a ∷ vArg b ∷ [])

macro
  invert : {P Q : obj} → F.Function _ (C.Fₒ P) (C.Fₒ Q) → Term → TC Top
  invert g hole = do
    (g' , prf) ← transform <$> quoteTC g
    unify hole (mkProd (g' , prf))

  Q : ∀ {a}{A : Set a} → A → Term → TC Top
  Q x hole = quoteTC x >>= quoteTC >>= unify hole

  QQ : ∀ {a}{A : Set a} → A → Term → TC Top
  QQ x hole = quoteTC x >>= normalise >>= quoteTC >>= unify hole

{-
  mkTopMacro : Term → TC Top
  mkTopMacro hole = do
    qtt ← quoteTC tt
    unify hole (mkProd (qtt , qtt))

a : Top × Top
a = mkTopMacro
-}
