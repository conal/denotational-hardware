{-# OPTIONS --safe --without-K #-}
-- Showable types

module Show where

open import Level
open import Data.String as S using (String)

private variable o : Level

-- Not really about categories, so maybe move elsewhere
record Show (A : Set o) : Set (suc o) where
  field
    show : A → String

open Show ⦃ … ⦄ public

instance

  import Data.Bool as B
  import Data.Bool.Show as BS
  Bool-Show : Show B.Bool
  Bool-Show = record { show = BS.show }

  open import Data.Nat
  import Data.Nat.Show as NS

  ℕ-Show : Show ℕ
  ℕ-Show = record { show = NS.show }

  open import Data.Rational
  import Data.Rational.Show as QS

  ℚ-Show : Show ℚ
  ℚ-Show = record { show = QS.show }

  open import Data.Fin using (Fin)
  import Data.Fin.Show as FS

  Fin-Show : ∀ {n} → Show (Fin n)
  Fin-Show = record { show = FS.show }

  String-Show : Show String
  String-Show = record { show = S.show }

  -- etc
