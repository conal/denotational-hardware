module Examples.Add.Fin where

open import Data.Product using (_,_; uncurry)
open import Data.Fin as 𝔽 hiding (_+_)
open import Data.Fin.Properties
open import Data.Nat as ℕ -- hiding (_+_; _*_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Categorical.Raw hiding (uncurry)
open import Functions
open import Categorical.Arrow Function

-- private variable m n : ℕ  -- TODO

toℕ-subst : ∀ {m n} {eq : m ≡ n} {i : Fin m} → toℕ (subst Fin eq i) ≡ toℕ i
toℕ-subst {eq = refl} = refl

-- inject+ : ∀ {m} n → Fin m → Fin (m ℕ.+ n)

inject+′ : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
inject+′ {m} n j = subst Fin (+-comm m n) (inject+ n j)

toℕ-inject+′ : ∀ {m} n (j : Fin m) → toℕ j ≡ toℕ (inject+′ n j)
toℕ-inject+′ {m} n j = trans (toℕ-inject+ n j) (sym toℕ-subst)

-- toℕ-inject+′ {m} n j =
--     begin
--       toℕ j
--     ≡⟨ toℕ-inject+ n j ⟩
--       toℕ (inject+ n j)
--     ≡⟨ sym toℕ-subst ⟩
--       toℕ (subst Fin (+-comm m n) (inject+ n j))
--     ≡⟨⟩
--       toℕ (inject+′ n j)
--     ∎

-- toℕ-inject+ : ∀ {m} n (i : Fin m) → toℕ i ≡ toℕ (inject+ n i)

infixl 6 _⊹_
_⊹_ : ∀ {m n} → Fin (suc m) → Fin n → Fin (m + n)
_⊹_ {m}{n}   zero   j = inject+′ m j
_⊹_ {suc _} (suc i) j = suc (i ⊹ j)

-- TODO: try redefining _⊹_ via Fin._+_.

-- TODO: Could we work with Fin._+_ instead of _⊹_? What would we learn?

-- -- I haven't gotten toℕ-⊹ below to work out with this variant.
-- _⊹_ {m}{n}   zero   j rewrite +-comm m n = inject+ m j

toℕ-⊹ : ∀ {m n} (i : Fin (suc m)) (j : Fin n)
      → toℕ (i ⊹ j) ≡ toℕ i + toℕ j
toℕ-⊹ {m} zero j = sym (toℕ-inject+′ m j)
toℕ-⊹ {suc _} (suc i) j rewrite toℕ-⊹ i j = refl

-- Arrow category morphism
⊹⇉ : ∀ {m n} → toℕ {suc m} ⊗ toℕ {n} ⇉ toℕ {m + n}
⊹⇉ = mk (uncurry _⊹_) (uncurry _+_) (uncurry toℕ-⊹)

-- addition with carry-in
addℕ : ℕ × ℕ × ℕ → ℕ
addℕ (c , a , b) = c + a + b

addFin : ∀ {m n} → Fin 2 × Fin m × Fin n → Fin (m + n)
addFin (cᵢ , a , b) = cᵢ ⊹ a ⊹ b

toℕ-addFin : ∀ {m n} → toℕ ∘ addFin {m}{n} ≗ addℕ ∘ (toℕ ⊗ toℕ ⊗ toℕ)
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

addFin⇉ : ∀ {m n} → toℕ ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ
addFin⇉ = mk addFin addℕ toℕ-addFin


-- Next, specialize to m ≡ n.

-- Add like-bounded numbers
addFin≡ : ∀ {m} → Fin 2 × Fin m × Fin m → Fin (2 * m)
addFin≡ {m} w rewrite +-identityʳ m = addFin w

-- toℕ-addFin≡ : ∀ {m} ((cᵢ , a , b) : Fin 2 × Fin m × Fin m)
--             → toℕ (addFin≡ (cᵢ , a , b)) ≡ toℕ cᵢ + toℕ a + toℕ b

-- toℕ-addFin≡ : ∀ {m} ((cᵢ , a , b) : Fin 2 × Fin m × Fin m)
--             → toℕ (addFin≡ (cᵢ , a , b)) ≡ addℕ ((toℕ ⊗ toℕ ⊗ toℕ) (cᵢ , a , b))

toℕ-addFin≡ : ∀ {m} → toℕ ∘ addFin≡ {m} ≗ addℕ ∘ (toℕ ⊗ toℕ ⊗ toℕ)
toℕ-addFin≡ {m} rewrite +-identityʳ m = toℕ-addFin

addFin≡⇉ : ∀ {m} → toℕ ⊗ toℕ {m} ⊗ toℕ {m} ⇉ toℕ
addFin≡⇉ = mk addFin≡ addℕ toℕ-addFin≡


-- Make carries more explicit

Cⁱ Cᵒ : ℕ → Set → Set
Cⁱ k = Fin k ×_
Cᵒ k = _× Fin k

-- Compute with carry-in & carry-out
infix 0 _→ᶜ_
_→ᶜ_ : {ℕ} → Set → Set → Set
_→ᶜ_ {k} a b = Cⁱ k a → Cᵒ k b

addFinᶜ : ∀ {m} → Fin m × Fin m →ᶜ Fin m
addFinᶜ = quotRem _ ∘ addFin≡

-- -- quotRem k "i" = "i % k" , "i / k"
-- quotRem : ∀ {n} k → Fin (n * k) → Fin k × Fin n

-- For inspiration, let's next consider adding more than two numbers:

addFin₃ : ∀ {m n o} → Fin 3 × Fin m × Fin n × Fin o → Fin (m + n + o)
addFin₃ (i , a , b , c) = i ⊹ a ⊹ b ⊹ c

addFin₄ : ∀ {m n o p} → Fin 4 × Fin m × Fin n × Fin o × Fin p → Fin (m + n + o + p)
addFin₄ (i , a , b , c , d) = i ⊹ a ⊹ b ⊹ c ⊹ d

-- Aha! The carry in bound/type is the number of addends.
-- Can we extend to a vector of addends? We'll want to accumulate from left to right (i.e., a left fold)

-- Next, let's generalize this carry-in to a sum accumulator

addFin₂′ : ∀ {i m n} → Fin (i + 2) × Fin m × Fin n → Fin (i + m + n)
addFin₂′ {i} (cᵢ , a , b) rewrite +-comm i 2 = cᵢ ⊹ a ⊹ b

addFin₂″ : ∀ {i m n} → Fin (2 + i) × Fin m × Fin n → Fin (i + m + n)
addFin₂″ {i} (cᵢ , a , b) = cᵢ ⊹ a ⊹ b

addFin₃′ : ∀ {i m n o}
         → Fin (i + 3) × Fin m × Fin n × Fin o → Fin (i + m + n + o)
addFin₃′ {i} (cᵢ , a , b , c) rewrite +-comm i 3 = cᵢ ⊹ a ⊹ b ⊹ c

addFin₃″ : ∀ {i m n o}
         → Fin (3 + i) × Fin m × Fin n × Fin o → Fin (i + m + n + o)
addFin₃″ {i} (cᵢ , a , b , c) = cᵢ ⊹ a ⊹ b ⊹ c

-- Extend to vectors summands

open import Data.Vec

adds : ∀ {k} → ℕ × Vec ℕ k → ℕ
adds (cᵢ , as) = cᵢ + sum as

-- TODO: try re-defining `adds` as a *left* fold, initialized to cᵢ, to match
-- the recursion structure of Fin sum. I bet the proofs below will simplify.

addFins′ : ∀ {k i m} → Fin (k + i) × Vec (Fin m) k → Fin (k * m + i)
addFins′ {zero}  (cᵢ ,   []  ) = cᵢ
addFins′ {suc k}{i}{m} (cᵢ , a ∷ as) =
  subst Fin eq (addFins′ (subst Fin (+-assoc k i m) (cᵢ ⊹ a) , as))
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

-- The _+ i in the domain and codomain of addFins′ is fairly convenient to
-- define, but it's less convenient to use, so commute them.

addFins″ : ∀ {k i m} → Fin (i + k) × Vec (Fin m) k → Fin (i + k * m)
addFins″ {k}{i}{m} rewrite +-comm i k | +-comm i (k * m) = addFins′

-- Specialize to i = 0
addFins : ∀ {k m} → Fin k × Vec (Fin m) k → Fin (k * m)
addFins = addFins″

-- -- Doesn't get there:
-- addFins {k}{m} rewrite +-identityʳ k | +-identityʳ (k * m) = addFins′ {k}{zero}{m}

toℕ-addFins′ : ∀ {k i m} → toℕ ∘ addFins′ {k}{i}{m} ≗ adds ∘ (toℕ ⊗ map toℕ)
toℕ-addFins′ {zero}  {i} {m} (cᵢ , []) rewrite +-identityʳ (toℕ cᵢ) = refl
toℕ-addFins′ {suc k} {i} {m} (cᵢ , a ∷ as) =
  begin
    toℕ (addFins′ (cᵢ , a ∷ as))
  ≡⟨⟩
    toℕ (subst Fin _ (addFins′ (subst Fin (+-assoc k i m) (cᵢ ⊹ a) , as)))
  ≡⟨ toℕ-subst ⟩
    toℕ (addFins′ (subst Fin (+-assoc k i m) (cᵢ ⊹ a) , as))
  ≡⟨ toℕ-addFins′ (subst Fin (+-assoc k i m) (cᵢ ⊹ a) , as) ⟩
    adds (toℕ (subst Fin (+-assoc k i m) (cᵢ ⊹ a)) , map toℕ as)
  ≡⟨ cong (λ z → adds (z , map toℕ as)) toℕ-subst ⟩
    adds (toℕ (cᵢ ⊹ a) , map toℕ as)
 ≡⟨⟩
    toℕ (cᵢ ⊹ a) + sum (map toℕ as)
  ≡⟨ cong (_+ sum (map toℕ as)) (toℕ-⊹ cᵢ a) ⟩
    (toℕ cᵢ + toℕ a) + sum (map toℕ as)
  ≡⟨ +-assoc (toℕ cᵢ) (toℕ a) (sum (map toℕ as)) ⟩
    toℕ cᵢ + (toℕ a + sum (map toℕ as))
  ≡⟨⟩
    toℕ cᵢ + sum (map toℕ (a ∷ as))
  ≡⟨⟩
    adds (toℕ cᵢ , map toℕ (a ∷ as))
  ∎

-- TODO: Retry these proofs with a *left*-folding ℕ sum.

toℕ-addFins″ : ∀ {k i m} → toℕ ∘ addFins″ {k}{i}{m} ≗ adds ∘ (toℕ ⊗ map toℕ)
toℕ-addFins″ {k}{i}{m} rewrite +-comm i k | +-comm i (k * m) = toℕ-addFins′

addFins″⇉ : ∀ {k i m} → toℕ {i + k} ⊗ map (toℕ {m}) ⇉ toℕ {i + k * m}
addFins″⇉ {k} = mk addFins″ adds (toℕ-addFins″ {k})

toℕ-addFins : ∀ {k m} → toℕ ∘ addFins {k}{m} ≗ adds ∘ (toℕ ⊗ map toℕ)
toℕ-addFins = toℕ-addFins″

addFins⇉ : ∀ {k m} → toℕ {k} ⊗ map (toℕ {m}) ⇉ toℕ {k * m}
addFins⇉ = mk addFins adds toℕ-addFins

-- -- Or skip explicitly specializing toℕ-addFins″ to toℕ-addFins:
-- addFins⇉ : ∀ {k m} → toℕ {k} ⊗ map (toℕ {m}) ⇉ toℕ {k * m}
-- addFins⇉ = mk addFins adds toℕ-addFins″


-- Next, make the carry-out explicit in addFins by reshaping Fin (k * m) to the
-- isomorphic type Fin m × Fin k, i.e., Cᵒ k (Fin m).

addFinsᶜ : ∀ {k m} → Vec (Fin m) k →ᶜ Fin m
addFinsᶜ = quotRem _ ∘ addFins

-- quotRem⁻¹ n%k n/k ≡ n%k + k * n/k ≡ n

-- quotRem⁻¹ : ∀ {m k} → Fin m × Fin k → Fin (k * m)

quotRem⁻¹ : ∀ {m k} → Cᵒ k (Fin m) → Fin (k * m)
quotRem⁻¹ (j , i) = addFins (i , replicate j)

-- quotRem⁻¹ = addFins ∘ second replicate ∘ swap

toℕᶜ : ∀ {k m} → Cᵒ k (Fin m) → ℕ
toℕᶜ = toℕ ∘ quotRem⁻¹

toℕ-addFinsᶜ : ∀ {k m} → toℕᶜ ∘ addFinsᶜ {k}{m} ≗ adds ∘ (toℕ ⊗ map toℕ)
toℕ-addFinsᶜ = {!!}

addFinsᶜ⇉ : ∀ {k m} → toℕ {k} ⊗ map (toℕ {m}) ⇉ toℕᶜ {k}{m}
addFinsᶜ⇉ = mk addFinsᶜ adds toℕ-addFinsᶜ


-------------------------------------------------------------------------------
-- Rethinking the rest
-------------------------------------------------------------------------------

-- Then specialize to m ≡ n ≡ 2^k.

-- Or maybe not. Revisit after we've made carry-out explicit in addFins
-- variants. I don't think 2 has any important role to play until we decide to
-- go with boolean vectors and use logic to implement one-bit addition.

𝟚 : Set
𝟚 = Fin 2

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

-- Even more explicitly

add𝟚^″ : ∀ k → 𝟚^ k × 𝟚^ k →ᶜ 𝟚^ k
add𝟚^″ k = quotRem _ ∘ add𝟚^ k

-- toℕ-add𝟚^″ : ∀ k ((cᵢ , a , b) : 𝟚 × 𝟚^ k × 𝟚^ k)
--            → toℕ (add𝟚^″ k (cᵢ , a , b)) ≡ toℕ cᵢ + toℕ a + toℕ b
-- toℕ-add𝟚^″ k rewrite (+-comm k 1) = toℕ-add𝟚^ k

-- add𝟚^″⇉ : ∀ k → toℕ {2} ⊗ toℕ {2 ^ k} ⊗ toℕ {2 ^ k} ⇉ toℕ {2 ^ (k + 1)}
-- add𝟚^″⇉ k = mk (add𝟚^″ k) addℕ (toℕ-add𝟚^″ k)



-- Next: Represent Fin 2 by Bool and Fin (2 ^ k) by Vec Bool k. Define add𝔹^1⇉ and then add𝔹^⇉
