---
title: Adding many numbers
author: Conal Elliott
---

```agda
module Examples.Add.ManyFin where

open import Data.Unit
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; uncurry)
  renaming (_×_ to _×′_) -- makes type hints easier to read
open import Data.Fin as 𝔽 hiding (_+_; quotRem) renaming (Fin to 𝔽)
open import Data.Fin.Properties
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Vec hiding (splitAt)

open import Categorical.Raw hiding (uncurry)
open import Functions
open import Categorical.Arrow Function

open import Examples.Add.Fin
```

# Adding many numbers

Next, let's extend our ambition from two summands (and carry-in) to any number of them, collected in a vector.
To simplify matters, assume that vector is uniformly bounded, i.e., all addends other than carry-in have the same bound.

::: aside
This assumption lets us use a uniform vector type (all elements having the same type and hence bound).
Dependent types are sufficiently expressive for nonuniform vectors, however, and I bet that the exploration below generalizes in lovely ways.
:::

One motivation to reach for adding many numbers is simply the challenge---to up our game.
As we'll see, though, interesting and useful insights will emerge from the effort.
The essential challenge is in expressing clearly the bounds involved.

For any `m : ℕ`, the sum of two values bounded by `m` is at most `2 * (m - 1) ≡ 2 * m - 2`.
Well, not exactly (as we noted above), because `ℕ` lacks a suitable notion of subtraction (i.e., one that has the relationship to substitution on `ℤ` that makes reasoning easy and useful).
We got around that problem neatly by introducing a carry-in bit, which happens to be needed for efficient, positional number systems.

When we're adding not just two but three `m`-bounded numbers, the sum is at most `3 * m - 3`.
When adding `k` such numbers, the sum is at most `k * m - k`.
Oh dear---subtraction again :scream_cat:.
Can we extend the carry-in trick to find our way back to type simplicity?
Yes, by allowing the carry-in to be at most `k - 1`, i.e., to have type `Fin k`.
Then the sum is at most `(k * m - k) + (k - 1) ≡ k * m - 1` and so has type `Fin (k * m)`:

```agdaQ
add𝔽s : ∀ {k m} → 𝔽 k × Vec (𝔽 m) k → 𝔽 (k * m)
```

::: aside
What we've discovered here is that the carry-in bound has nothing to do with the addend (e.g., digit) bounds, but rather is the number of addends.
As a special case, for a single "summand" (`k ≡ 1`), the carry-in type is `𝔽 1`, which contains only `zero`.
The result has the same bound and the same value as the lonely summand, since `(𝔽 1 × Vec (𝔽 m) 1 → 𝔽 (1 * m)) ≅ (𝔽 m → 𝔽 m)`.
An even weirder special case is no summands at all, for which the carry-bit type `𝔽 0` is uninhabited.
This case "works", too, since `(𝔽 0 × Vec (𝔽 m) 0 → 𝔽 (0 * m)) ≅ ⊥ → ⊥`, which has just one inhabitant.
:::

As we move rightward through the vector (which, confusingly, corresponds to moving *leftward* in our familiar positional numeric notations), the "carry-in" value grows by absorbing successive summands.
For this reason, while initially of type `𝔽 k`, we will have to leave room to grow (even as `k` shrinks).
As a first guess, let's try the following type, adding a new parameter `i` to help bound the accumulator.

```agda
add𝔽s₀ : ∀ {k i m} → 𝔽 (k + i) × Vec (𝔽 m) k → 𝔽 (k * m + i)
```

This signature gives us the flexibility needed to accommodate summand accumulation and will specialize to `add𝔽s` above when `i ≡ 0` (with help from `+-identityʳ`).

Things are about to get wild :grimacing:, but I promise you that they'll calm down soon.
Feel free to read the next few definitions carefully or breeze through them, as pleases you.
(Agda's type-checker already pointed out my many mistakes and eventually approved the revision below.)

```agda
add𝔽s₀ {zero} (cᵢ , []) = cᵢ

add𝔽s₀ {suc k}{i}{m} (cᵢ , a ∷ as) =
  subst 𝔽 eq (add𝔽s₀ (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as))
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

addℕs₀ : ∀ {k} → ℕ × Vec ℕ k → ℕ
addℕs₀ = uncurry (foldl _ _+_)

toℕ-add𝔽s₀ : ∀ {k i m} → toℕ ∘ add𝔽s₀ {k}{i}{m} ≗ addℕs₀ ∘ (toℕ ⊗ map toℕ)
toℕ-add𝔽s₀ {zero } {i} {m} (cᵢ , []) rewrite +-identityʳ (toℕ cᵢ) = refl
toℕ-add𝔽s₀ {suc k} {i} {m} (cᵢ , a ∷ as) =
  begin
    toℕ (add𝔽s₀ (cᵢ , a ∷ as))
  ≡⟨⟩
    toℕ (subst 𝔽 _ (add𝔽s₀ (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as)))
  ≡⟨ toℕ-subst ⟩
    toℕ (add𝔽s₀ (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as))
  ≡⟨ toℕ-add𝔽s₀ (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a) , as) ⟩
    addℕs₀ (toℕ (subst 𝔽 (+-assoc k i m) (cᵢ ⊹ a)) , map toℕ as)
  ≡⟨ cong (λ z → addℕs₀ (z , map toℕ as)) toℕ-subst ⟩
    addℕs₀ (toℕ (cᵢ ⊹ a) , map toℕ as)
  ≡⟨⟩
    foldl _ _+_ (toℕ (cᵢ ⊹ a)) (map toℕ as)
  ≡⟨ cong (λ z → foldl _ _+_ z (map toℕ as)) (toℕ-⊹ cᵢ a) ⟩
    foldl _ _+_ (toℕ cᵢ + toℕ a) (map toℕ as)
  ≡⟨⟩
    foldl _ _+_ (toℕ cᵢ) (map toℕ (a ∷ as))
  ≡⟨⟩
    addℕs₀ (toℕ cᵢ , map toℕ (a ∷ as))
  ∎

add𝔽s⇉₀ : ∀ {k i m} → toℕ {k + i} ⊗ map {n = k} (toℕ {m}) ⇉ toℕ {k * m + i}
add𝔽s⇉₀ = mk add𝔽s₀ addℕs₀ toℕ-add𝔽s₀
```

Phew!

# Seeking simplicity

The definitions above are far too complicated for my tastes; perhaps for yours as well.
Seeking simplicity, we can look for ways to build up `add𝔽s⇉` from `⊹⇉` *compositionally*, as we did when rewriting `add𝔽₀` as `add𝔽`.
Following our earlier success, let's pursue the following plan:

*   Rewrite `addℕs` (part 2 of the packing list above) in categorical style.
*   Imitate the new form in the `𝔽` counterpart (part 1) and correctness proof (part 3) for appropriate data interpretations (parts 4 & 5).
*   Combine all five parts into a single package.
*   Review what we've done, and replace it all with a single categorical recipe that assembles the package compositionally.

First, switch from `Vec` to `V` (an isomorphic, recursively defined type made with standard products), and write out the left fold explicitly:

```agda
addℕs₁ : ∀ k → ℕ × V ℕ k → ℕ
addℕs₁ zero (cᵢ , tt) = cᵢ
addℕs₁ (suc k) (cᵢ , a , as) = addℕs₁ k (cᵢ + a , as)
```

Now switch to categorical language:

```agda
addℕs₂ : ∀ k → ℕ × V ℕ k → ℕ
addℕs₂  zero   = unitorᵉʳ
addℕs₂ (suc k) = addℕs₂ k ∘ first (uncurry _+_) ∘ assocˡ
```

We could have used `exl` (left projection) for the `zero` case, but `unitorᵉʳ` (right unit elimination) emphasizes that we are discarding only the value `tt : ⊤`, which contains no information.

::: aside
Unitors are available in monoidal categories, which do not provide for duplicating or discarding information.
Non-cartesian, monoidal categories include reversible computations, which suggest a remedy for the [unavoidably heat-generating](https://en.wikipedia.org/wiki/Landauer%27s_principle) (diabatic) nature of the current dominant paradigm of irreversible computing.
:::

Unrolling the loop, we get `unitorᵉʳ ∘ first ⟨+⟩ ∘ assocˡ ∘ ⋯ ∘ first ⟨+⟩ ∘ assocˡ`, where `⟨+⟩ = uncurry _+_`.

Can we imitate this form for `𝔽`?

We can start by defining *one step* of `add𝔽s`, going from the sum of `k` addends (in addition to carry-in) to the sum of `k+1`.
For additional precision, we can replace the accumulated `i` from above with `j * m`.

```agda
add𝔽ᶜ-suc : ∀ {j k m : ℕ}
          → 𝔽 (suc k + j * m) × V (𝔽 m) (suc k)
          → 𝔽 (k + suc j * m) × V (𝔽 m) k
add𝔽ᶜ-suc {j}{k}{m} rewrite sym (+-comm (j * m) m) | sym (+-assoc k (j * m) m) =
  first (uncurry _⊹_) ∘ assocˡ
```

Now, we can use `add𝔽ᶜ-suc` to redefine `add𝔽s`, this time imitating the simple, left-fold form of `addsℕ`:

```agda
add𝔽s₁ : ∀ {j k m} → 𝔽 (k + j * m) × V (𝔽 m) k → 𝔽 ((k + j) * m)
add𝔽s₁ {j}{zero } = unitorᵉʳ
add𝔽s₁ {j}{suc k}{m} = id≡ eq ∘ add𝔽s₁ {suc j}{k} ∘ add𝔽ᶜ-suc {j}
 where
   eq : 𝔽 ((k + suc j) * m) ≡ 𝔽 ((suc k + j) * m)
   eq rewrite +-suc k j = refl
```

(We could phrase that last line more explicitly as `eq = cong (λ i → 𝔽 (i * m)) (+-suc k j)`.)

As we march forward, `j` counts how many vector elements we've met and gratefully absorbed, while `k` counts how many more we can gleefully anticipate.
As `j` ascends from `zero`, `k` descends to `zero`, always in perfect balance ☯.
Ultimately, we offer a well-digested summary of our encounters.

These new definitions are much simpler!
I think we're getting somewhere.

The `id≡` function  used here (a definition---not field---in the `Category` class) provides an alternative to `subst` and `rewrite`:

```agdaQ
  id≡ : a ≡ b → a ⇨ b
  id≡ refl = id
```

We can eliminate `id≡ eq` here with the help of a somewhat hairy `subst` or via `rewrite`.
After a few attempts, I came up with the following:

```agda
add𝔽s₂ : ∀ {j k m} → 𝔽 (k + j * m) × V (𝔽 m) k → 𝔽 ((k + j) * m)
add𝔽s₂ {j}{zero }{m} = unitorᵉʳ
add𝔽s₂ {j}{suc k}{m} rewrite sym (cong (_* m) (+-suc k j)) =
  add𝔽s₂ {suc j}{k} ∘ add𝔽ᶜ-suc {j}
```

Without the `cong`, type-checking fails.
Maybe it needed just a bit more context to avoid some harmful uses.

```agda
add𝔽s : ∀ {k m} → 𝔽 k × V (𝔽 m) k → 𝔽 (k * m)
add𝔽s {k}{m} = subst (λ z → 𝔽 z × V (𝔽 m) k → 𝔽 (z * m)) (+-identityʳ k)
                 (add𝔽s₂ {0}{k}{m})
```

I hoped for a simpler-looking version using `rewrite` instead of `subst`.
The following attempt doesn't type-check:
```agdaQ
add𝔽s {k}{m} rewrite +-identityʳ k = add𝔽s₂ {0}{k}{m}
```

::: aside
It feels right to me that this `add𝔽s₁` definition looks like a *dependently typed left fold*, since its purpose is to implement the simply typed left fold in the definition of `addℕs`, while refining (the simply typed) `ℕ` into (the dependently typed) `𝔽`.

The `foldl` we used above from `Data.Vec.Base` already does have a dependent type:
```agdaQ
foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m}
      → (∀ {n} → B n → A → B (suc n))
      → B zero
      → Vec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs
```

This pattern doesn't seem quite general enough, since we're simultaneously decreasing `k` and increasing `j`.
On the other hand, maybe `add𝔽s₁` could be rephrased to fit comfortably.
:::

The recipes for `add𝔽ᶜ-suc` and `add𝔽s₂` are written in a form that contains only categorical operations and basic addition.
Since we have arrow (`⇉`) versions of all of these building blocks, we can use these same recipes to build arrow versions of `add𝔽ᶜ-suc` and `add𝔽s₁`, thus establishing the meaning of `add𝔽s₂` as `addℕs`:

```agda
add𝔽ᶜ-suc⇉ : ∀ {j k m}
           →   toℕ {suc k + j * m} ⊗ mapⱽ (suc k) (toℕ {m})
             ⇉ toℕ {k + suc j * m} ⊗ mapⱽ k (toℕ {m})
add𝔽ᶜ-suc⇉ {j}{k}{m} rewrite sym (+-comm (j * m) m) | sym (+-assoc k (j * m) m) =
  first ⊹⇉ ∘ assocˡ

add𝔽s⇉′ : ∀ {j k m} → toℕ {k + j * m} ⊗ mapⱽ k (toℕ {m}) ⇉ toℕ {(k + j) * m}
add𝔽s⇉′ {j} {zero } {m} = unitorᵉʳ
add𝔽s⇉′ {j} {suc k} {m} rewrite sym (cong (_* m) (+-suc k j)) =
  add𝔽s⇉′ {suc j}{k} ∘ add𝔽ᶜ-suc⇉ {j}
```

Then specialize with `j ≡ zero`:
```agda
add𝔽s⇉ : ∀ {k m} → toℕ {k} ⊗ mapⱽ k (toℕ {m}) ⇉ toℕ {k * m}
add𝔽s⇉ {k}{m} = subst (λ z → toℕ {z} ⊗ mapⱽ k (toℕ {m}) ⇉ toℕ {z * m})
                      (+-identityʳ k)
                  (add𝔽s⇉′ {0})
```

As intended, `add𝔽s⇉` contains `addℕs` and `add𝔽s` (which can now be discarded), and the proof of their relationship.
The representation of `add𝔽s⇉` comprises exactly these three aspects (as record fields), and its signature contains the data mappings.
The implementation and specification extractors [are cartesian functors](https://en.wikipedia.org/wiki/Comma_category#Properties), mirroring the repeated use of a single categorical recipe.

# Juxtaposing digits

Positional number systems assign different weights to digits, depending on their position.
Usually, there's a single radix (digit bound) `m` for all positions, but there needn't be.
To start, let's consider just two digits with possibly different bounds `m` and `n`.

Assuming we write least significant bits on the left, a pair `(i , j) : 𝔽 n × 𝔽 m` will denote `i ⊹ n ✫ j : 𝔽 (n * m)`, where `⊹` is addition on `𝔽` as defined above, and `✫` is an multiplication of an `𝔽` by an `ℕ`.
Reasoning our way to the bound `m * n` goes exactly as we did above for adding `cᵢ : 𝔽 n` to a vector `v : V (𝔽 m) n`.
For good reason, too, because `i ⊹ n ✫ j` is a special case of what we've already done---with the vector elements all equal, when we called "`k`" in place of "`n`" and thought of it as the number of addends (and hence the carry-in bound):
```agda
𝔽² : ℕ → ℕ → Set
𝔽² n m = 𝔽 n × 𝔽 m

⊹✫ : ∀ {n m} → 𝔽² n m → 𝔽 (n * m)
⊹✫ {n} (i , j) = add𝔽s (i , replicateⱽ n j)
```

where `replicateⱽ : ∀ n → a ⇨ V a n`.
The function `⊹✫` interprets juxtaposed digits in a mixed-radix number system.

Now suppose we want to add two numbers represented in this way.
Since we're adding just two of them, we'll also want an `𝔽 2` carry-in (to use our result type fully).

```agdaQ
add₁⊹✫ : ∀ {n m} → 𝔽 2 × 𝔽² n m × 𝔽² n m → 𝔽² n m × 𝔽 2
```

```agda

```

<!--

:::banner
working here
:::

# Carrying out

Addition in positional number systems need to carry *out* as well as *in*.
Our `add𝔽s` function above, which is also reconstructed in `add𝔽s⇉`, 

Adapted from `quotRem` in `Data.Fin` with some convenient alterations:
```agda
remQuot : ∀ {k m} → 𝔽 (k * m) → 𝔽 m × 𝔽 k
remQuot {suc _}{m} i with splitAt m i
... | inj₁ a = a , zero
... | inj₂ b = second suc (remQuot b)
```

where
```agdaQ
splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
```

As the name `remQuot` suggests, it takes `i : 𝔽 (k * m)` and yields the remainder `i % m : Fin m` and the quotient `i / m : k`.

In fact, `splitAt` and `remQuot` are halves of two isomorphisms.
The inverse for `remQuot` for a divisor `m` takes a remainder `i%m` and quotient `i/m` and yields the dividend `i%m + k * i/m`.
Remember, however, that `i%m` and `i/m` are `𝔽`s, `k` is an `ℕ`, and the combination is an `𝔽`.
Defining this combination is almost as tricky as what we just did with `add𝔽s`.
Fortunately, it is a special case of `add𝔽s`, in which the `k` addends are all identical.
We can thus give a very simple inverse definition (having already done the hard work):

```agda
remQuot⁻¹ : ∀ {k m} → 𝔽 k × 𝔽 m → 𝔽 (k * m)
remQuot⁻¹ {k} (i%m , i/m) = add𝔽s (i%m , replicateⱽ k i/m)
```

-->

# Still to come

There are more places to visit on our journey.
Some we can imagine from here:

*   Revealing carry-out and its use in decomposing addition
*   Efficient addition via positional number representations
*   Various recipes for sequential and parallel addition and their hybrids
*   Multiplication
*   Circuit design and verification

These adventures and more await us.
