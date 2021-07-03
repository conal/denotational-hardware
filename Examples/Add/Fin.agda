module Examples.Add.Fin where

open import Data.Product using (_,_)
open import Data.Fin hiding (_+_)
open import Data.Nat as ℕ -- hiding (_+_; _*_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Categorical.Raw
open import Functions

-- private variable m n : ℕ  -- TODO

infixl 6 _⊹_
_⊹_ : ∀ {m n} → Fin (suc m) → Fin n → Fin (m + n)
_⊹_ {m}{n}   zero   j = subst Fin (+-comm n m) (inject+ m j)
_⊹_ {suc _} (suc i) j = suc (i ⊹ j)

-- TODO: redefine _⊹_ via Fin._+_.

-- TODO: Could we work with Fin._+_ instead of _⊹_? What would we learn?

-- -- I haven't gotten toℕ-⊹ below to work out with this variant.
-- _⊹_ {m}{n}   zero   j rewrite +-comm m n = inject+ m j

open import Data.Fin.Properties

toℕ-subst : ∀ {m n} {eq : m ≡ n} {i : Fin m} → toℕ (subst Fin eq i) ≡ toℕ i
toℕ-subst {eq = refl} = refl

toℕ-⊹ : ∀ {m n} (i : Fin (suc m)) (j : Fin n)
      → toℕ (i ⊹ j) ≡ toℕ i + toℕ j
toℕ-⊹ {m} zero j = trans toℕ-subst (sym (toℕ-inject+ m j))
toℕ-⊹ {suc _} (suc i) j rewrite toℕ-⊹ i j = refl

-- toℕ-⊹ {m} {n} zero j =
--     begin
--       toℕ (zero ⊹ j)
--     ≡⟨⟩
--       toℕ (subst Fin (+-comm n m) (inject+ m j))
--     ≡⟨ toℕ-subst ⟩
--       toℕ (inject+ m j)
--     ≡⟨ sym (toℕ-inject+ m j) ⟩
--       toℕ j
--     ≡⟨⟩
--       zero + toℕ j
--     ≡⟨⟩
--       toℕ (zero {suc m}) + toℕ j
--     ∎

-- toℕ-⊹ {suc m} {n} (suc i) j =
--     begin
--       toℕ (suc i ⊹ j)
--     ≡⟨⟩
--       toℕ (suc (i ⊹ j))
--     ≡⟨⟩
--       suc (toℕ (i ⊹ j))
--     ≡⟨ cong suc (toℕ-⊹ i j) ⟩
--       suc (toℕ i + toℕ j)
--     ≡⟨⟩
--       toℕ (suc i) + toℕ j
--     ∎

open import Categorical.Arrow Function

-- Arrow category morphism
+⇉ : ∀ {m n} → toℕ {suc m} ⊗ toℕ {n} ⇉ toℕ {m + n}
+⇉ = mk (uncurry _⊹_) (uncurry _+_) λ (a , b) → toℕ-⊹ a b

-- addition with carry-in
addℕ : ℕ × ℕ × ℕ → ℕ
addℕ (c , a , b) = c + a + b

addFin : ∀ {m n} → Fin 2 × Fin m × Fin n → Fin (m + n)
addFin (cᵢ , a , b) = cᵢ ⊹ a ⊹ b

toℕ-addFin : ∀ {m n} ((cᵢ , a , b) : Fin 2 × Fin m × Fin n)
           → toℕ (addFin (cᵢ , a , b)) ≡ toℕ cᵢ + toℕ a + toℕ b
toℕ-addFin (cᵢ , a , b) rewrite toℕ-⊹ (cᵢ ⊹ a) b | toℕ-⊹ cᵢ a = refl

-- toℕ-addFin (cᵢ , a , b) =
--   begin
--     toℕ (addFin (cᵢ , a , b))
--   ≡⟨⟩
--     toℕ (cᵢ ⊹ a ⊹ b)
--   ≡⟨ toℕ-⊹ (cᵢ ⊹ a) b ⟩
--     toℕ (cᵢ ⊹ a) + toℕ b
--   ≡⟨ cong (_+ toℕ b) (toℕ-⊹ cᵢ a) ⟩
--     toℕ cᵢ + toℕ a + toℕ b
--   ∎

addFin⇉ : ∀ {m n} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ {m + n}
addFin⇉ = mk addFin addℕ toℕ-addFin


-- Next, specialize to m ≡ n.

-- Add like-bounded numbers
addFin≡ : ∀ {m} → Fin 2 × Fin m × Fin m → Fin (2 * m)
addFin≡ {m} w rewrite +-identityʳ m = addFin w

toℕ-addFin≡ : ∀ {m} ((cᵢ , a , b) : Fin 2 × Fin m × Fin m)
            → toℕ (addFin≡ (cᵢ , a , b)) ≡ toℕ cᵢ + toℕ a + toℕ b
toℕ-addFin≡ {m} rewrite +-identityʳ m = toℕ-addFin

addFin≡⇉ : ∀ {m} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {m} ⇉ toℕ {2 * m}
addFin≡⇉ = mk addFin≡ addℕ toℕ-addFin≡


-- Make carries more explicit

𝟚 : Set
𝟚 = Fin 2

Cⁱ Cᵒ : Set → Set
Cⁱ = 𝟚 ×_
Cᵒ = _× 𝟚

-- Compute with carry-in & carry-out
infix 0 _→ᶜ_
_→ᶜ_ : Set → Set → Set
a →ᶜ b = Cⁱ a → Cᵒ b

-- ⟦_⟧ᵒ : ∀ {m} → Cᵒ (Fin m) → Fin (2 * m)
-- ⟦ cᵢ , i ⟧ᵒ = {!i ⊹ cᵢ * m!}

-- quotRem : ∀ {n} k → Fin (n * k) → Fin k × Fin n

-- quotRem⁻¹ : ∀ {n} k → Fin k × Fin n → Fin (n * k)
-- quotRem⁻¹ k (i%k , i/k) = {!i/k ⊹ k * i/k!}

-- quotRem⁻¹ {.(suc _)} k (j , zero ) = {!!}
-- quotRem⁻¹ {.(suc _)} k (j , suc i) = {!!}

-- -- quotRem k "i" = "i % k" , "i / k"
-- quotRem : ∀ {n} k → Fin (n * k) → Fin k × Fin n
-- quotRem {suc n} k i with splitAt k i
-- ... | inj₁ j = j , zero
-- ... | inj₂ j = Product.map₂ suc (quotRem {n} k j)

-- addFinᶜ : ∀ {m} → 𝟚 × Fin m × Fin m → Fin m × 𝟚
-- addFinᶜ : ∀ {m} → Cⁱ (Fin m × Fin m) → Cᵒ (Fin m)

addFinᶜ : ∀ {m} → Fin m × Fin m →ᶜ Fin m
addFinᶜ w = quotRem _ (addFin≡ w)


-- WORKING HERE

addFin₃ : ∀ {m n o} → Fin 3 × Fin m × Fin n × Fin o → Fin (m + n + o)
addFin₃ (i , a , b , c) = i ⊹ a ⊹ b ⊹ c

addFin₄ : ∀ {m n o p} → Fin 4 × Fin m × Fin n × Fin o × Fin p → Fin (m + n + o + p)
addFin₄ (i , a , b , c , d) = i ⊹ a ⊹ b ⊹ c ⊹ d

open import Data.Vec

-- addFins : ∀ {k n} → Fin k × Vec (Fin n) k → Fin (k * n)

-- addFins {suc zero} {n} (zero , a ∷ []) rewrite +-identityʳ n = a
-- addFins {suc (suc k)} (cᵢ , a ∷ as) = {!addFins (cᵢ ⊹ a , as)!}

-- addFins {suc k} (cᵢ , a ∷ as) = {!addFins {k} (cᵢ ⊹ a) as!}

-- Goal: Fin (n + (n + k * n))
-- ————————————————————————————————————————————————————————————
-- as : Vec (Fin n) (suc k)
-- a  : Fin n
-- cᵢ : Fin (suc (suc k))
-- n  : ℕ   (not in scope)
-- k  : ℕ

-- cᵢ ⊹ a : Fin (suc k + n)
--        : Fin (suc (k + n))

-- Of course---I need to introduce carry-out.

-- Or maybe a different kind of carry-in! Generalize `Fin k` to `Fin (i + k)`


addFin₂′ : ∀ {i m n} → Fin (i + 2) × Fin m × Fin n → Fin (i + m + n)
addFin₂′ {i} (cᵢ , a , b) rewrite +-comm i 2 = cᵢ ⊹ a ⊹ b

addFin₂′′ : ∀ {i m n} → Fin (2 + i) × Fin m × Fin n → Fin (i + m + n)
addFin₂′′ {i} (cᵢ , a , b) = cᵢ ⊹ a ⊹ b

addFin₃′ : ∀ {i m n o}
         → Fin (i + 3) × Fin m × Fin n × Fin o → Fin (i + m + n + o)
addFin₃′ {i} (cᵢ , a , b , c) rewrite +-comm i 3 = cᵢ ⊹ a ⊹ b ⊹ c

addFin₃′′ : ∀ {i m n o}
          → Fin (3 + i) × Fin m × Fin n × Fin o → Fin (i + m + n + o)
addFin₃′′ {i} (cᵢ , a , b , c) = cᵢ ⊹ a ⊹ b ⊹ c


addFins′ : ∀ {k i m} → Fin (k + i) × Vec (Fin m) k → Fin (k * m + i)
addFins′ {zero}  (cᵢ ,   []  ) = cᵢ
addFins′ {suc k}{i}{m} (cᵢ , a ∷ as) =
  subst Fin eq
    (addFins′ (subst Fin (+-assoc k i m) (cᵢ ⊹ a) , as))
 where
   eq : k * m + (i + m) ≡ suc k * m + i
   eq = begin
          k * m + (i + m)
        ≡⟨ cong (k * m +_) (+-comm i m) ⟩
          k * m + (m + i)
        ≡⟨ sym (+-assoc (k * m) m i) ⟩
          k * m + m + i
        ≡⟨ cong (_+ i) (+-comm (k * m) m) ⟩
          m + k * m + i
        ≡⟨⟩
          suc k * m + i
        ∎

addFins′′ : ∀ {k i m} → Fin (i + k) × Vec (Fin m) k → Fin (i + k * m)
addFins′′ {k}{i}{m} rewrite +-comm i k | +-comm i (k * m) = addFins′

addFins : ∀ {k m} → Fin k × Vec (Fin m) k → Fin (k * m)
addFins = addFins′′

-- -- Doesn't get there:
-- addFins {k}{m} rewrite +-identityʳ k | +-identityʳ (k * m) = addFins′ {k}{zero}{m}


-- Now specialize to m ≡ n ≡ 2^k.
 

infix 10 𝟚^_
𝟚^_ : ℕ → Set
𝟚^_ k = Fin (2 ^ k)

-- k-bit addition with carry-in
add𝟚^ : ∀ k → 𝟚 × 𝟚^ k × 𝟚^ k → 𝟚^ suc k
add𝟚^ k (cᵢ , a , b) rewrite +-identityʳ (2 ^ k) = cᵢ ⊹ a ⊹ b

toℕ-add𝟚^ : ∀ k ((cᵢ , a , b) : 𝟚 × 𝟚^ k × 𝟚^ k)
          → toℕ (add𝟚^ k (cᵢ , a , b)) ≡ toℕ cᵢ + toℕ a + toℕ b
toℕ-add𝟚^ k rewrite +-identityʳ (2 ^ k) = toℕ-addFin


add𝟚^⇉ : ∀ k → toℕ {2} ⊗ toℕ {2 ^ k} ⊗ toℕ {2 ^ k} ⇉ toℕ {2 ^ suc k}
add𝟚^⇉ k = mk (add𝟚^ k) addℕ (toℕ-add𝟚^ k)


-- It might be handy to move the carry-out bit to the right.

add𝟚^′ : ∀ k → 𝟚 × 𝟚^ k × 𝟚^ k → 𝟚^ (k + 1)
add𝟚^′ k rewrite +-comm k 1 = add𝟚^ k

toℕ-add𝟚^′ : ∀ k ((cᵢ , a , b) : 𝟚 × 𝟚^ k × 𝟚^ k)
           → toℕ (add𝟚^′ k (cᵢ , a , b)) ≡ toℕ cᵢ + toℕ a + toℕ b
toℕ-add𝟚^′ k rewrite (+-comm k 1) = toℕ-add𝟚^ k

add𝟚^′⇉ : ∀ k → toℕ {2} ⊗ toℕ {2 ^ k} ⊗ toℕ {2 ^ k} ⇉ toℕ {2 ^ (k + 1)}
add𝟚^′⇉ k = mk (add𝟚^′ k) addℕ (toℕ-add𝟚^′ k)


-- Next: Represent Fin 2 by Bool and Fin (2 ^ k) by Vec Bool k. Define add𝔹^1⇉ and then add𝔹^⇉
