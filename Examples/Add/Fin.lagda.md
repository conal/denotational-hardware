# Fun with finites!

This chapter is one step in a journey to construct machine-verified hardware design in a simple, principled manner.

We'll start with addition on statically bounded natural numbers, as provided by the [`Data.Fin`](https://agda.github.io/agda-stdlib/Data.Fin.html) module in [the Agda standard library](https://github.com/agda/agda-stdlib).
(Most of the functionality is re-exported from [`Data.Fin.Base`](https://agda.github.io/agda-stdlib/Data.Fin.Base.html).)
The defining module calls these types `Fin n` (for `n : ℕ`), but we'll rename them to `𝔽 n` for the code below.

## Some preliminaries

First declare our module and import needed functionality from other modules:

```agda
module Examples.Add.Fin where

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

`Data.Fin` provides a way to increase a number's bound:

```agdaQ
inject+ : ∀ {m} n → 𝔽 m → 𝔽 (m ℕ.+ n)
```

(Decreasing is trickier.)
`Data.Fin.Properties` tells us that `inject+` only changes the upper bound, while leaving value of that number unchanged:

```agdaQ
toℕ-inject+ : ∀ {m} n (i : 𝔽 m) → toℕ i ≡ toℕ (inject+ n i)
```

It will be convenient to use a tweaked signature for `inject+`, and to reverse the direction of `toℕ-inject+`.

```agda
inject+′ : ∀ {m} n → 𝔽 m → 𝔽 (n ℕ.+ m)
inject+′ {m} n j = subst 𝔽 (+-comm m n) (inject+ n j)

toℕ-subst : ∀ {m n} {eq : m ≡ n} {i : 𝔽 m} → toℕ (subst 𝔽 eq i) ≡ toℕ i
toℕ-subst {eq = refl} = refl

toℕ-inject+′ : ∀ {m} n (j : 𝔽 m) → toℕ (inject+′ n j) ≡ toℕ j
toℕ-inject+′ {m} n j = trans toℕ-subst (sym (toℕ-inject+ n j))
```

## Adding two numbers

A bounded number `a : 𝔽 n` can be any of `0, ..., n - 1`.
If we add `a : 𝔽 m` to `b : 𝔽 n`, so `a ≤ m - 1` and `b ≤ n - 1` and thus `a + b ≤ m + n - 2`, i.e., has type `𝔽 (m + n - 1)`.

Well, not exactly, because `ℕ` has no negatives and so does not have subtraction in the way we might expect.
Instead, we'll require `m > 0` (although we could instead require `n > 0`).
We could tweak addition to ask for a proof that `m > 0`, but we'd need to make the result more complex as well.
Instead, we can choose a *simpler* type:

```agda
infixl 6 _⊹_
_⊹_ : ∀ {m n} → 𝔽 (suc m) → 𝔽 n → 𝔽 (m + n)
_⊹_ {m}      zero   j = inject+′ m j
_⊹_ {suc _} (suc i) j = suc (i ⊹ j)
```

The name of this function suggests that it implements addition, and indeed it does, in the following sense:

```agda
toℕ-⊹ : ∀ {m n} (i : 𝔽 (suc m)) (j : 𝔽 n) → toℕ (i ⊹ j) ≡ toℕ i + toℕ j
toℕ-⊹ {m} zero j = toℕ-inject+′ m j
toℕ-⊹ {suc _} (suc i) j rewrite toℕ-⊹ i j = refl
```

Let's consider the *meaning* of an `𝔽` value to be the corresponding `ℕ`, as given by `toℕ`.
Then `toℕ-⊹` says that the meaning of an sum of `𝔽` values is the sum of the meanings of those values.
The property has a sort of rhyme to it that may sound familiar if you've seen abstract algebra and various examples of *homomorphisms*.

## Packaging it all up to go

We now have five crucial pieces of information:

1.  an *implementation* (`_⊹_`),
2.  a specification (`_+_`), and
3.  a proof of their consistency with respect to
4.  a mapping of implementation input to specification input and
5.  a mapping of implementation output to specification output.

These five pieces are all aspects of a single, meaningful assembly, so let's package them to be convenient to take with us and relate to other such assemblies.
Parts 4 and 5 are about the inputs and outputs and their semantic relationship, so we'll make them the domain and codomain of the assembly, i.e., its interface.
Parts 1, 2, and 3 become the details behind that interface:

```agda
⊹⇉ : ∀ {m n} → toℕ {suc m} ⊗ toℕ {n} ⇉ toℕ {m + n}
⊹⇉ = mk (uncurry _⊹_) (uncurry _+_) (uncurry toℕ-⊹)
```

*To do:* define `mk′` to take curried ops, and use in place of `mk` & `uncurry`.

The symbol "`_⇉_`" was chosen to suggest a kind of mapping, and belongs to a category such that

*   *objects* (the sorts of inputs and outputs for the category) are data mappings (parts 4 & 5 above); and
*   *morphisms* (the connections/mappings in the category) are pairs of functions (parts 1 and 2 above)---which can really be morphisms from *any* category---that satisfy a "commuting diagram" (part 3 above).

This construction is known as an "[arrow category](https://en.wikipedia.org/wiki/Comma_category#Arrow_category)".

## A dance for three

The `ℕ` and `𝔽` types are *unary* representations, built up from `zero` by repeated applications of `suc`(cessor), as defined by Giuseppe Peano in the late 19th century.
This representation is convenient for reasoning but computationally inefficient in size of representation and cost of arithmetic operations.

In [positional number systems](https://en.wikipedia.org/wiki/Positional_notation) (such as base ten or base two), representations are succinct, and operations are efficient---at the cost of some complexity.
For this reason, we will work our way toward implementing positional systems, defining their meanings via `𝔽`, which itself is defined via its meaning `ℕ`.
We could relate positional systems to `ℕ` directly, but there are useful insights to be gained in each step of the journey.
Giving each our focused attention fosters our understanding and appreciation of the jewels we encounter.

When we add two digits (whether in base ten or base two), the result can be too large to denote with a single digit.
For this reason, digit addition produces not only a digit but a "carry-out" value.
No matter what the base, the carry-out is either zero or one, which is to say it has type `𝔽 2`, or a "bit", not a digit.
(Digits and bits only coincide in base two.)

When we move *leftward* from digit to digit (since we write the least significant digit on the right and most significant on the left), we "carry out" the carry-out bit into the next digit addition, where it becomes a "carry-in" bit of the next (more significant) digit addition.

In this way, digit addition becomes "a dance for three" (as Carlo Rovelli [says](https://www.goodreads.com/book/show/55801224-helgoland) of quantum entanglement and relative information), not two:


```agda
add𝔽₀ : ∀ {m n} → 𝔽 2 × 𝔽 m × 𝔽 n → 𝔽 (m + n)
add𝔽₀ (cᵢ , a , b) = cᵢ ⊹ a ⊹ b
```

Note how `add𝔽₀` replaces the `𝔽 (suc m)` argument to `_⊹_` by a `𝔽 2` and a `𝔽 m`.
These two arguments then get added to yield `𝔽 (suc m)` (since `2 ≡ suc (suc zero)`), which is then added to a `𝔽 n` to get a `F (m + n)`.

We'll want to know that `add𝔽₀` correctly implements something and what that something is, so let's repeat our packaging game.
A natural meaning is adding three unfettered natural numbers (not troubling them or ourselves with bounds), which we can prove correct and tie up in a neat package:

```agda
addℕ : ℕ × ℕ × ℕ → ℕ
addℕ (c , a , b) = c + a + b

toℕ-add𝔽₀ : ∀ {m n} → toℕ ∘ add𝔽₀ {m}{n} ≗ addℕ ∘ (toℕ ⊗ toℕ ⊗ toℕ)
toℕ-add𝔽₀ (cᵢ , a , b) rewrite toℕ-⊹ (cᵢ ⊹ a) b | toℕ-⊹ cᵢ a = refl

add𝔽⇉₀ : ∀ {m n} → toℕ ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ
add𝔽⇉₀ = mk add𝔽₀ addℕ toℕ-add𝔽₀
```

This time the correctness condition (the type of `toℕ-add𝔽`) in given in succinct, point-free style, using sequential composition (`_∘_`), parallel composition (`_⊗_`), and existential equality of functions (`_≗_`).

When reading the definitions above, it helps to know that `_+_` is left-associative, while `_×_`, `_,_`, and `_⊗_` are all right-associative.

Now note that each aspect of `add𝔽⇉₀` is made from the corresponding component of `⊹⇉`, using essentially the same recipe:

*   Left-associate `(cᵢ , a , b)` to `((cᵢ , a) , b)`.
*   Add the first pair, yielding `(cᵢ + a , b)`.
*   Add the result, yielding `(cᵢ + a) + b`.

Using categorical operations, we can thus define `add𝔽⇉` directly via `⊹⇉` rather than via ingredients of `⊹⇉`:

```agda
add𝔽⇉ : ∀ {m n} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ {m + n}
add𝔽⇉ = ⊹⇉ ∘ first ⊹⇉ ∘ assocˡ
```

*Whee!*
We've used the `Category` and `Cartesian` instances for comma categories (including their arrow category specialization) to combine our implementation-specification-proof packages, both in sequence and in parallel.
Those two instances encapsulate the knowledge of how to perform these two kinds of compositions and a few other useful operations as well.

::: aside
*To do*: define a cartesian category of equality proofs, and rewrite `addℕ`, `add𝔽`, `toℕ-add𝔽` (renamed "`add≡`"), *and* `add𝔽⇉` all in the same form.
:::

## Adding many numbers

Next, let's extend from two summands (and carry-in) to any number of summands, collected in a vector.
To simplify matters, let's assume that vector is uniformly bounded, i.e., all addends other than carry-in have the same bound.

::: aside
This assumption allows for uniform vector (all elements having the same type).
Dependent types are sufficiently expressive for nonuniform vectors, however, and I bet that the exploration below generalizes in lovely ways.
:::

One reason to take this step is simply as a challenge, to up our game.
As we'll see, though, interesting and useful insights will emerge from the effort.
The essential challenge is in expressing clearly the bounds involved.

For any `m : ℕ`, the sum of two values bounded by `m` is at most `2 * m - 1`.
Well, not exactly (as we noted above), because `ℕ` lacks suitable notion of subtraction (i.e., one that has the relationship to substitution on `ℤ` that makes reasoning easy and useful).
We got around that problem neatly by introducing of a carry-in bit, which happens to be needed for efficient, positional number systems.

When we're adding not just two but three `m`-bounded numbers, the sum is at most `3 * m - 2`.
When adding `k` such number, the sum is at most `k * m - (k - 1)`.
Oh dear---subtraction again.

Can we extend the carry-in trick to find our way back to type simplicity?
Yes, by allowing the carry-in to be at most `k - 1`, i.e., to have type `Fin k`.
What we've discovered is that carry-in bound has nothing to do with the bounds of the numbers (or digits) being added, but rather is the number of addends.

Because we are accumulating from the left, the "carry-in" value grows by absorbing successive summands as we move through the vector.
For this reason, while initially of type `𝔽 k`, we will have to leave room to grow.
As a first guess, let's try the following type, adding a new parameter `i`, which will help bound the accumulator.

```agda
open import Data.Vec

add𝔽s₀ : ∀ {k i m} → 𝔽 (k + i) × Vec (𝔽 m) k → 𝔽 (k * m + i)
```

Things are about to get wild, but I promise you that they'll calm down soon.
You don't need to read the next few definitions carefully.

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
With considerable effort, we made it.

Unfortunately, math and code are not things we put behind us once written.
In addition to purchase cost, we now have an ongoing paid subscription to complexity :grimacing:.
We must reason through it over and over---both individually and collectively---as we build from here.

Or cancel the subscription, learn from experience, and try something else.

## Seeking simplicity

The definitions above are far too complicated for my tastes.
In seeking simplicity, let's look for ways to build up `add𝔽s⇉` from `⊹⇉` *compositionally*, as we did we rewrote `add𝔽₀` as `add𝔽`.

Here's an idea: rewrite `addℕs` in categorical style (part 2 of the enumeration above).
Then imitate for the `𝔽` counterpart (part 1) and correctness proof (part 3) for appropriate data interpretations (parts 4 & 5).
Then combine all five parts into a single package.

First, switch from `Vec` to `V` (since `V` is made of standard products), and write out the left fold explicitly:

```agda
open import Data.Unit

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

We could have used `exl` (left projection) for the `zero` case, but `unitorᵉʳ` (right unitor elimination) emphasizes that we are discarding only the value `tt : ⊤`, which contains no information.

::: aside
Unitors are available in monoidal categories, which do not provide for duplicating or destroying information.
Non-cartesian, monoidal categories include reversible computations, which suggest an answer to the [unavoidably heat-generating](https://en.wikipedia.org/wiki/Landauer%27s_principle) (diabatic) nature of the current dominant paradigm of irreversible computing.
:::

Unrolling the loop, we have `unitorᵉʳ ∘ first ⟨+⟩ ∘ assocˡ ∘ ⋯ ∘ first ⟨+⟩ ∘ assocˡ`, where `⟨+⟩ = uncurry _+_`.

Can we imitate this form with `𝔽`?

We can start by defining *one step* of `add𝔽s`, going from the sum of `k` addends (in addition to carry-in) to the sum of `k+1`.
For additional precision, we can replace the accumulated `i` from above with `j * m`.
As we march forward, `j` counts how many vectors elements we've absorbed, and `k` counts how many more we have to go, with `j` beginning and `k` ending as `zero`.

```agda
add𝔽ᶜ-suc : ∀ {j k m : ℕ}
          → 𝔽 (suc k + j * m) × V (𝔽 m) (suc k)
          → 𝔽 (k + suc j * m) × V (𝔽 m) k
add𝔽ᶜ-suc {j}{k}{m} rewrite sym (+-comm (j * m) m) | sym (+-assoc k (j * m) m) =
  first (uncurry _⊹_) ∘ assocˡ
```

Then use `add𝔽ᶜ-suc` to redefine `add𝔽s`:

```agda
add𝔽s₁ : ∀ {j k m} → 𝔽 (k + j * m) × V (𝔽 m) k → 𝔽 ((k + j) * m)
add𝔽s₁ {j}{zero } = unitorᵉʳ
add𝔽s₁ {j}{suc k}{m} = id≡ eq ∘ add𝔽s₁ {suc j}{k} ∘ add𝔽ᶜ-suc {j}
 where
   eq : 𝔽 ((k + suc j) * m) ≡ 𝔽 ((suc k + j) * m)
   eq rewrite +-suc k j = refl
```

(We could phrase that last line more explicitly as `eq = cong (λ i → 𝔽 (i * m)) (+-suc k j)`.)

Much simpler!
I think we're getting somewhere.

The `id≡` function  used here (a definition---not field---in the `Category` class) provides an alternative to `subst` and `rewrite`


```agdaQ
  id≡ : a ≡ b → a ⇨ b
  id≡ refl = id
```

::: aside
This `add𝔽s₁` definition looks like a *dependently typed left fold*, which feels right, since its purpose is to implement the simply typed left fold in the definition of `addℕs`, but refining (the simply typed) `ℕ` into (the dependently typed) `𝔽`.

The `foldl` we used above from `Data.Vec.Base` indeed does have a dependent type:
```agdaQ
foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs
```

This pattern doesn't seem quite general enough, since we're simultaneously decreasing `k` and increasing `j`.
On the other hand, maybe `add𝔽s₁` could be rephrased to fit.
:::

::: aside
We could eliminate `id≡ eq` here with the help of a somewhat hairy `subst`.
Alternatively, try `rewrite`.
After a few attempts, I came up with the following:

```agda
add𝔽s₂ : ∀ {j k m} → 𝔽 (k + j * m) × V (𝔽 m) k → 𝔽 ((k + j) * m)
add𝔽s₂ {j}{zero }{m} = unitorᵉʳ
add𝔽s₂ {j}{suc k}{m} rewrite sym (cong (_* m) (+-suc k j)) =
  add𝔽s₂ {suc j}{k}{m} ∘ add𝔽ᶜ-suc {j}
```

Without the `cong`, type-checking failed.
Maybe it needed just a bit more context to avoid some harmful rewrites.

I'll keep both `add𝔽s₁` and `add𝔽s₂` for now, and evaluate their merits later in usage.
:::
