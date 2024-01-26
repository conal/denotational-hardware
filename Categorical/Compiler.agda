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

open import Function
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Unit renaming (⊤ to Top)
open import Data.List using (List; []; _∷_)
open import Axiom.Extensionality.Propositional
open import Agda.Builtin.String
import Agda.Builtin.Nat as BN
import Relation.Binary.PropositionalEquality as PEq
import Relation.Binary.Structures as Structures

import Reflection as R
open R hiding (_>>=_; _>>_)
open import Reflection.Name
open import Reflection.Term
open import Reflection.Argument
open import Reflection.DeBruijn

open F.→-raw-instances ℓₛ

-- The output of our compiling some g into its categorical representation must be
-- an inhabitant of (ResultType g). Note that we require g to be of type `H P -> H Q ∈ Arr Sets`,
-- this makes sure that we know the type of the resulting arrow, f, beforehand: `P ⇨ Q ∈ Arr C`
ResultType : {P Q : obj} → F.Function _ (C.Fₒ P) (C.Fₒ Q) → Set (ℓ ⊔ ℓₛ)
ResultType {P} {Q} g = Σ (P ⇨ Q) (λ f → C.Fₘ f C.≈ g)

pattern vlam x b = lam visible (abs x b)
pattern hlam x b = lam hidden  (abs x b)
pattern hcons¹ x = _ ⟅∷⟆ x
pattern hcons² x = hcons¹ (hcons¹ x)
pattern hcons³ x = hcons¹ (hcons² x)
pattern hcons⁴ x = hcons¹ (hcons³ x)
pattern hcons⁵ x = hcons¹ (hcons⁴ x)

module Pure where
  open import Category.Monad
  open import Data.Sum.Categorical.Left (List ErrorPart) 0ℓ
  open RawMonad monad

  trBody : String → Term → Sumₗ Term

  transform : Term → Sumₗ Term
  transform e@(vlam x body) with strengthen body
  ...| just body' = inj₂ (def (quote const) (vArg body' ∷ []))
  ...| nothing = trBody x body
  transform e = inj₁ (strErr "term is not vlam:" ∷ termErr e ∷ [])

  trBody x (var BN.zero [])
    = inj₂ (def (quote C.id) [])
  trBody x (con (quote _,_) (hcons⁴ (vArg u ∷ vArg v ∷ [])))
    = do tu ← transform (vlam x u)
         tv ← transform (vlam x v)
         inj₂ (def (quote C._▵_) (vArg tu ∷ vArg tv ∷ []))
  trBody _ body = inj₁ (strErr "trBody incomplete:" ∷ termErr body ∷ [])

mkProd : Term × Term → Term
mkProd (a , b) = con (quote _,_) (vArg a ∷ vArg b ∷ [])

mkRefl : Term
mkRefl = vlam "x" (con (quote PEq.refl) [])

ctxToError : List (Arg Type) → List ErrorPart
ctxToError [] = []
ctxToError (arg (arg-info visible r) x ∷ xs) = strErr "V " ∷ termErr x ∷ ctxToError xs
ctxToError (arg (arg-info hidden r) x ∷ xs) = strErr "H " ∷ termErr x ∷ ctxToError xs
ctxToError (arg (arg-info instance′ r) x ∷ xs) = strErr "I " ∷ termErr x ∷ ctxToError xs

open import Reflection.TypeChecking.Monad.Syntax
macro
  invert : Bool → {P Q : obj} → F.Function _ (C.Fₒ P) (C.Fₒ Q) → Term → TC Top
  invert dbg q hole = do
    th ← inferType hole
    qg ← withNormalisation true (quoteTC q)
    inj₂ g' ← Pure.transform <$> return qg
      where
        inj₁ errs → typeError ( strErr "Could not convert term:"
                              ∷ termErr qg
                              ∷ strErr "; where:"
                              ∷ errs)
    let res = mkProd (g' , mkRefl)
    if dbg then typeError (strErr "qg: " ∷ termErr qg ∷ strErr "Result: " ∷ termErr res ∷ [])
           else unify hole res

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
