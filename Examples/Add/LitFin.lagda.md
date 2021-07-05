```agda
module Examples.Add.LitFin where

open import Data.Product using (_,_; uncurry)
open import Data.Fin as 𝔽 hiding (_+_) renaming (Fin to 𝔽)
open import Data.Fin.Properties
open import Data.Nat as ℕ -- hiding (_+_; _*_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Categorical.Raw hiding (uncurry)
open import Functions
open import Categorical.Arrow Function
```

Some utilities:

```agda
toℕ-subst : ∀ {m n} {eq : m ≡ n} {i : 𝔽 m} → toℕ (subst 𝔽 eq i) ≡ toℕ i
toℕ-subst {eq = refl} = refl

-- inject+ : ∀ {m} n → 𝔽 m → 𝔽 (m ℕ.+ n)
-- toℕ-inject+ : ∀ {m} n (i : 𝔽 m) → toℕ i ≡ toℕ (inject+ n i)

inject+′ : ∀ {m} n → 𝔽 m → 𝔽 (n ℕ.+ m)
inject+′ {m} n j = subst 𝔽 (+-comm m n) (inject+ n j)

toℕ-inject+′ : ∀ {m} n (j : 𝔽 m) → toℕ j ≡ toℕ (inject+′ n j)
toℕ-inject+′ {m} n j = trans (toℕ-inject+ n j) (sym toℕ-subst)
```

Let's start with `𝔽` addition and its relationship to `ℕ` addition:

```agda
infixl 6 _⊹_
_⊹_ : ∀ {m n} → 𝔽 (suc m) → 𝔽 n → 𝔽 (m + n)
_⊹_ {m}{n}   zero   j = inject+′ m j
_⊹_ {suc _} (suc i) j = suc (i ⊹ j)

toℕ-⊹ : ∀ {m n} (i : 𝔽 (suc m)) (j : 𝔽 n)
      → toℕ (i ⊹ j) ≡ toℕ i + toℕ j
toℕ-⊹ {m} zero j = sym (toℕ-inject+′ m j)
toℕ-⊹ {suc _} (suc i) j rewrite toℕ-⊹ i j = refl
```

Now assemble the implementation, specification, and proof into a category morphism:

```agda
⊹⇉ : ∀ {m n} → toℕ {suc m} ⊗ toℕ {n} ⇉ toℕ {m + n}
⊹⇉ = mk (uncurry _⊹_) (uncurry _+_) (uncurry toℕ-⊹)
```

*To do:* define `mk′` to take curried ops, and use in place of `mk` & `uncurry`.

Next, play the same game with carry-in:

```agda
addℕ : ℕ × ℕ × ℕ → ℕ
addℕ (c , a , b) = c + a + b

add𝔽 : ∀ {m n} → 𝔽 2 × 𝔽 m × 𝔽 n → 𝔽 (m + n)
add𝔽 (cᵢ , a , b) = cᵢ ⊹ a ⊹ b

toℕ-add𝔽 : ∀ {m n} → toℕ ∘ add𝔽 {m}{n} ≗ addℕ ∘ (toℕ ⊗ toℕ ⊗ toℕ)
toℕ-add𝔽 (cᵢ , a , b) rewrite toℕ-⊹ (cᵢ ⊹ a) b | toℕ-⊹ cᵢ a = refl

add𝔽′⇉ : ∀ {m n} → toℕ ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ
add𝔽′⇉ = mk add𝔽 addℕ toℕ-add𝔽
```

Now note that each component of `add𝔽⇉` can be built from the corresponding component of `⊹⇉`, using essentially the same recipe:

*   Left-associate `(cᵢ , a , b)` to `((cᵢ , a) , b)`.
*   Add the first pair, yielding `(cᵢ + a , b)`.
*   Add the result, yielding `(cᵢ + a) + b`.

Using categorical operations, we can thus define `add𝔽⇉` directly via `⊹⇉` (rather than via ingredients of `⊹⇉`), as follows:

```agda
add𝔽⇉ : ∀ {m n} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ {m + n}
add𝔽⇉ = ⊹⇉ ∘ first ⊹⇉ ∘ assocˡ
```

Whee! We've used the `Category` and `Cartesian` instances for comma categories (including their arrow category specialization) to simultaneously combine implementations, specifications, and proofs.

Next, specialize to `m ≡ n`:

```agda
add𝔽≡⇉′ : ∀ {m} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {m} ⇉ toℕ {2 * m}
add𝔽≡⇉′ {m} rewrite +-identityʳ m = add𝔽⇉
```

Next, let's extend from to summands (and carry-in) to any number of summands:

```agda
open import Data.Vec

adds : ∀ {k} → ℕ × Vec ℕ k → ℕ
adds = uncurry (foldl _ _+_)

add𝔽s : ∀ {k i m} → 𝔽 (k + i) × Vec (𝔽 m) k → 𝔽 (k * m + i)
add𝔽s {zero} (cᵢ , []) = cᵢ
add𝔽s {suc k}{i}{m} (cᵢ , a ∷ as) =
  subst 𝔽 eq (add𝔽s (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as))
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

toℕ-add𝔽s : ∀ {k i m} → toℕ ∘ add𝔽s {k}{i}{m} ≗ adds ∘ (toℕ ⊗ map toℕ)
toℕ-add𝔽s {zero } {i} {m} (cᵢ , []) rewrite +-identityʳ (toℕ cᵢ) = refl
toℕ-add𝔽s {suc k} {i} {m} (cᵢ , a ∷ as) =
  begin
    toℕ (add𝔽s (cᵢ , a ∷ as))
  ≡⟨⟩
    toℕ (subst 𝔽 _ (add𝔽s (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as)))
  ≡⟨ toℕ-subst ⟩
    toℕ (add𝔽s (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as))
  ≡⟨ toℕ-add𝔽s (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as) ⟩
    adds (toℕ (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a)) , map toℕ as)
  ≡⟨ cong (λ z → adds (z , map toℕ as)) toℕ-subst ⟩
    adds (toℕ (cᵢ ⊹ a) , map toℕ as)
  ≡⟨⟩
    foldl _ _+_ (toℕ (cᵢ ⊹ a)) (map toℕ as)
  ≡⟨ cong (λ z → foldl _ _+_ z (map toℕ as)) (toℕ-⊹ cᵢ a) ⟩
    foldl _ _+_ (toℕ cᵢ + toℕ a) (map toℕ as)
  ≡⟨⟩
    foldl _ _+_ (toℕ cᵢ) (map toℕ (a ∷ as))
  ≡⟨⟩
    adds (toℕ cᵢ , map toℕ (a ∷ as))
  ∎

add𝔽s′⇉ : ∀ {k i m} → toℕ {k + i} ⊗ map {n = k} (toℕ {m}) ⇉ toℕ {k * m + i}
add𝔽s′⇉ = mk add𝔽s adds toℕ-add𝔽s

add𝔽s⇉ : ∀ {k i m} → toℕ {i + k} ⊗ map {n = k} (toℕ {m}) ⇉ toℕ {i + k * m}
add𝔽s⇉ {k}{i}{m} rewrite +-comm i k | +-comm i (k * m)= add𝔽s′⇉
```

Yow!
Those definitions far too complicated for my taste.
I want instead to build up `add𝔽s⇉` from `⊹⇉`, compositionally.
Look for more decomposable formulations.

First, try changing the carry-in to account for being partway into a summation, having accumulated `j` addends with `k` more to go.

```agda
add𝔽s₂ : ∀ {j k m} → 𝔽 (j * m + k) × Vec (𝔽 m) k → 𝔽 ((j + k) * m)
add𝔽s₂ {j} {zero } {m} (cᵢ , [])
  rewrite +-identityʳ j | +-identityʳ (j * m) = cᵢ
add𝔽s₂ {j} {suc k} {m} (cᵢ , a ∷ as) =
   subst 𝔽 eq₃ (add𝔽s₂ {suc j}{k}{m} (cᵢ′ , as))
 where
   eq₁ : j * m + suc k ≡ suc (j * m + k)
   eq₁ = +-suc (j * m) k
   eq₂ : (j * m + k) + m ≡ suc j * m + k
   eq₂ = trans (+-comm (j * m + k) m) (sym (+-assoc m (j * m) k))
   eq₃ : (suc j + k) * m ≡ (j + suc k) * m
   eq₃ = cong (_* m) (sym (+-suc j k))
   cᵢ′ : 𝔽 (suc j * m + k)
   cᵢ′ = subst 𝔽 eq₂ (subst 𝔽 eq₁ cᵢ ⊹ a)
```

Still not as simple as I want.

Here's an idea: write `adds` (the specification) in categorical style.
Then imitate for the `𝔽` version and its correctness proof.

First, write out the left fold explicitly:

```agda
adds₂ : ∀ {k} → ℕ × Vec ℕ k → ℕ
adds₂ {zero } (cᵢ ,   []  ) = cᵢ
adds₂ {suc k} (cᵢ , a ∷ as) = adds₂ (cᵢ + a , as)

-- TODO: Rename adds to _+Σ_ and add𝔽s to _⊹Σ_.
-- Oops: if I switch from Vec to V, I'll have to make k explicit.
-- Maybe I can insert V/Vec adapters instead.

open import Data.Unit

adds₃ : ∀ k → ℕ × V ℕ k → ℕ
adds₃ zero (cᵢ , tt) = cᵢ
adds₃ (suc k) (cᵢ , a , as) = adds₃ k (cᵢ + a , as)

-- In categorical language

adds₄ : ∀ k → ℕ × V ℕ k → ℕ
adds₄  zero   = unitorᵉʳ
adds₄ (suc k) = adds₄ k ∘ first (uncurry _+_) ∘ assocˡ

-- Overall: unitorᵉʳ ∘ first ⟨+⟩ ∘ assocˡ ∘ ⋯ ∘ first ⟨+⟩ ∘ assocˡ


-- Convert Vec to V incrementally

un[] : ∀ {a} → Vec a zero → V a zero
un[] [] = tt

un∷ : ∀ {a n} → Vec a (suc n) → a × Vec a n
un∷ (a ∷ as) = a , as

adds₅ : ∀ k → ℕ × Vec ℕ k → ℕ
adds₅  zero   = unitorᵉʳ ∘ second un[]
adds₅ (suc k) = adds₅ k ∘ first (uncurry _+_) ∘ assocˡ ∘ second un∷

-- Convert Vec to V up front

toV : ∀ {k}{a} → Vec a k → V a k
toV [] = tt
toV (a ∷ as) = a , toV as

adds₆ : ∀ {k} → ℕ × Vec ℕ k → ℕ
adds₆ {k} = adds₄ k ∘ second toV

-- Restyled

toV′ : ∀ {k}{a} → Vec a k → V a k
toV′ {zero } = un[]
toV′ {suc k} = second toV′ ∘ un∷

adds₇ : ∀ {k} → ℕ × Vec ℕ k → ℕ
adds₇ {k} = adds₄ k ∘ second toV′
```
Okay, back to it.

First define *one step* of `add𝔽s`.

```agda
add𝔽ᶜ-suc : ∀ {j k m : ℕ}
          → 𝔽 (suc k + j * m) × V (𝔽 m) (suc k)
          → 𝔽 (k + suc j * m) × V (𝔽 m) k
add𝔽ᶜ-suc {j}{k}{m} rewrite sym (+-comm (j * m) m) | sym (+-assoc k (j * m) m) =
  first (uncurry _⊹_) ∘ assocˡ
```

Use `add𝔽ᶜ-suc` to redefine `add𝔽s`:

```agda
add𝔽s₃ : ∀ {j k m} → 𝔽 (k + j * m) × V (𝔽 m) k → 𝔽 ((k + j) * m)
add𝔽s₃ {j}{zero }{m} = unitorᵉʳ
add𝔽s₃ {j}{suc k}{m} = id≡ eq ∘ add𝔽s₃ {suc j}{k}{m} ∘ add𝔽ᶜ-suc {j}
 where
   eq : 𝔽 ((k + suc j) * m) ≡ 𝔽 ((suc k + j) * m)
   eq rewrite +-suc k j = refl
   -- eq = cong (λ i → 𝔽 (i * m)) (+-suc k j)
```

Hm! `add𝔽ᶜ-suc` is a *dependently typed state transition function*
Correspondingly, `add𝔽s₃` is almost the dependently typed execution of the corresponding Mealy machine, but it generates the final state instead of the intermediate outputs.

I guess a better description is a *dependently typed left fold*.

We could eliminate `id≡ eq` here with the help of a somewhat hairy `subst`.
Alternatively, try `rewrite`.
After a few attempts, I came up with the following:

```agda
add𝔽s₄ : ∀ {j k m} → 𝔽 (k + j * m) × V (𝔽 m) k → 𝔽 ((k + j) * m)
add𝔽s₄ {j}{zero }{m} = unitorᵉʳ
add𝔽s₄ {j}{suc k}{m} rewrite sym (cong (_* m) (+-suc k j)) =
  add𝔽s₄ {suc j}{k}{m} ∘ add𝔽ᶜ-suc {j}
```

Without the `cong`, type-checking failed.
Maybe it needed just a bit more context to avoid some harmful rewrites.

Keep both `add𝔽s₃` and `add𝔽s₄` for now, and evaluate their merits in usage.

From `Data.Vec.Base`:
```agdaQ
foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs
```

This pattern doesn't seem quite general enough, since we're simultaneously decreasing `k` and increasing `j`.
I bet `add𝔽s₄` could be rephrased.
