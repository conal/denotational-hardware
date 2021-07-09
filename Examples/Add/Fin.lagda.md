---
title: Composing correct constructions
author: Conal Elliott
---

# Composing correct constructions

This note takes a few small step in a journey to construct machine-verified hardware design in a simple, principled manner.

We'll start with addition on statically bounded natural numbers, as provided by the [`Data.Fin`](https://agda.github.io/agda-stdlib/Data.Fin.html) module in [the Agda standard library](https://github.com/agda/agda-stdlib).
(Most of the functionality is re-exported from [`Data.Fin.Base`](https://agda.github.io/agda-stdlib/Data.Fin.Base.html).)
The defining module calls these types "`Fin n`" (for `n : ℕ`), but we'll rename them to "`𝔽 n`" for the code below.

## Some preliminaries

First declare our module and import needed functionality from other modules:

```agda
module Examples.Add.Fin where

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
open import Function using (_∘′_)  -- TEMP

open import Categorical.Raw hiding (uncurry)
open import Functions
open import Categorical.Arrow Function
```

`Data.Fin` provides a way to increase a number's bound, while `Data.Fin.Properties` assures us that its value remains undisturbed:

```agdaQ
inject+ : ∀ {m} n → 𝔽 m → 𝔽 (m + n)

toℕ-inject+ : ∀ {m} n (i : 𝔽 m) → toℕ i ≡ toℕ (inject+ n i)
```

It will be convenient to tweak the signature of `inject+` and to reverse the direction of `toℕ-inject+`.

```agda
inject+′ : ∀ {m} n → 𝔽 m → 𝔽 (n + m)
inject+′ {m} n j = subst 𝔽 (+-comm m n) (inject+ n j)

toℕ-subst : ∀ {m n} {eq : m ≡ n} {i : 𝔽 m} → toℕ (subst 𝔽 eq i) ≡ toℕ i
toℕ-subst {eq = refl} = refl

toℕ-inject+′ : ∀ {m} n (j : 𝔽 m) → toℕ (inject+′ n j) ≡ toℕ j
toℕ-inject+′ {m} n j = trans toℕ-subst (sym (toℕ-inject+ n j))
```

## Adding two numbers

A (bounded) number `a : 𝔽 n` can be any of `0, ..., n - 1`.
If we add `a : 𝔽 m` to `b : 𝔽 n`, then `0 ≤ a ≤ m - 1` and `0 ≤ b ≤ n - 1`, so `0 ≤ a + b ≤ m + n - 2`, i.e., has type `𝔽 (m + n - 1)`.

Well, not exactly.
`ℕ` has no negatives and so does not have subtraction in the way we might expect.
Instead, we'll require `m > 0` (although one might require `n > 0` instead).
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
Then `toℕ-⊹` says that *the meaning of the sum* of `𝔽` values is *the sum of the meanings* of those values.
The property has a sort of rhyme to it that may sound familiar if you've seen abstract algebra and its various flavors of *homomorphisms*.

## Packaging it all up to go

We now have five crucial pieces of information:

1.  an *implementation* (`_⊹_`),
2.  a specification (`_+_`), and
3.  a proof of their consistency with respect to
4.  a mapping of implementation input to specification input and
5.  a mapping of implementation output to specification output.

These five pieces are all aspects of a single, meaningful assembly, so let's wrap them into a convenient package to take with us and relate to other such assemblies.
Parts 4 and 5 are about the inputs and outputs and their semantic relationship and so will become the domain and codomain of the assembly, i.e., its interface.
Parts 1, 2, and 3 become the details behind that interface:

```agda
⊹⇉ : ∀ {m n} → toℕ {suc m} ⊗ toℕ {n} ⇉ toℕ {m + n}
⊹⇉ = mk (uncurry _⊹_) (uncurry _+_) (uncurry toℕ-⊹)
```

::: aside
*To do:* define `mk′` to take curried operations, and use in place of `mk` & `uncurry`.
:::

The symbol "`_⇉_`" was chosen to suggest a kind of mapping, belonging to a category in which

*   *objects* (the sorts of inputs and outputs for the category) are data mappings (parts 4 & 5 above); and
*   *morphisms* (the connections/mappings in the category) are pairs of functions (parts 1 and 2 above)---which can really be morphisms from *any* category---that satisfy a "commuting diagram" (part 3 above).

This construction is known as an "[arrow category](https://en.wikipedia.org/wiki/Comma_category#Arrow_category)".

## A dance for three

The `ℕ` and `𝔽` types are *unary* representations, built up from `zero` by repeated applications of `suc`(cessor), as defined by Giuseppe Peano in the late 19th century.
This representation is logically convenient but computationally inefficient in size of representation and cost of arithmetic operations.

In [positional number systems](https://en.wikipedia.org/wiki/Positional_notation) (such as base ten or base two), representations are succinct, and operations are efficient---at the cost of some complexity.
For this reason, we will work our way toward implementing positional systems, defining their meanings via `𝔽`, which itself is defined via its meaning `ℕ`.
We could relate positional systems to `ℕ` directly, but there are useful insights to be gained in each step of the journey.
By pausing at each step and giving focused attention to our surroundings, we foster understanding and appreciation of the jewels we encounter.

When we add two digits (whether in base ten or base two), the result can be too large to denote with a single digit.
For this reason, digit addition produces not only a digit but an overflow---or "carry-out"---value as well.
No matter what the base, the carry-out is either zero or one, which is to say it is an `𝔽 2`, or a "bit", not a digit.
(Digits and bits coincide only in base two.)

When we move *leftward* from digit to digit (since we write the least significant digit on the right and most significant on the left), we "carry out" the carry-out bit into the next digit addition, where it becomes the "carry-in" bit of the next (more significant) digit addition.

In this way, digit addition becomes "a dance for three" (as [Carlo Rovelli says](https://www.goodreads.com/book/show/55801224-helgoland) of quantum entanglement and relative information):

```agda
add𝔽₀ : ∀ {m n} → 𝔽 2 × 𝔽 m × 𝔽 n → 𝔽 (m + n)
add𝔽₀ (cᵢ , a , b) = cᵢ ⊹ a ⊹ b
```

Note how `add𝔽₀` replaces the `𝔽 (suc m)` argument to `_⊹_` by `𝔽 2` *and* `𝔽 m`.
These two arguments are added to yield `𝔽 (suc m)` (since `2 ≡ suc (suc zero)`), which is then added to an `𝔽 n` to get an `F (m + n)`.

We'll want to know that `add𝔽₀` correctly implements something and what that something is, so let's repeat our packaging game.
A natural meaning is adding three unfettered natural numbers (not troubling them or ourselves with bounds), which we can prove correct and package up:

```agda
addℕ : ℕ × ℕ × ℕ → ℕ
addℕ (c , a , b) = c + a + b

toℕ-add𝔽₀ : ∀ {m n} → toℕ ∘ add𝔽₀ {m}{n} ≗ addℕ ∘ (toℕ ⊗ toℕ ⊗ toℕ)
toℕ-add𝔽₀ (cᵢ , a , b) rewrite toℕ-⊹ (cᵢ ⊹ a) b | toℕ-⊹ cᵢ a = refl

add𝔽⇉₀ : ∀ {m n} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ {m + n}
add𝔽⇉₀ = mk add𝔽₀ addℕ toℕ-add𝔽₀
```

This time the correctness condition (the type of `toℕ-add𝔽`) is given in succinct, point-free style, using sequential composition (`_∘_`), parallel composition (`_⊗_`), and existential equality on functions (`_≗_`).

When reading the definitions above, it helps to know that `_+_` is left-associative, while `_×_`, `_,_`, and `_⊗_` are all right-associative.

Now note that each aspect of `add𝔽⇉₀` is made from the corresponding component of `⊹⇉`, using essentially the same recipe:

*   Left-associate `(cᵢ , (a , b))` to `((cᵢ , a) , b)`.
*   Add the first pair, yielding `(cᵢ + a , b)`.
*   Add the result, yielding `(cᵢ + a) + b`.

Using categorical operations, we can thus define `add𝔽⇉` directly via `⊹⇉` rather than defining the ingredients of `add𝔽⇉` via the ingredients of `⊹⇉`:

```agda
add𝔽⇉ : ∀ {m n} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ {m + n}
add𝔽⇉ = ⊹⇉ ∘ first ⊹⇉ ∘ assocˡ
```

We've used the `Category` and `Cartesian` instances for comma categories (including their arrow category specialization) to compose our implementation-specification-proof packages, both in sequence and in parallel.
(There's only a hint of the parallel here yet, but eventually there will be much more.)
Those two instances encapsulate the knowledge of how to perform these two foundational kinds of compositions and a few other useful operations as well.

## Carrying out

Addition in positional number systems need to carry *out* as well as *in*.
If we specialize addition to `m ≡ n`, then we can write the result type as `𝔽 (2 * m)`

```agda
add𝔽≡₀⇉ : ∀ {m} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {m} ⇉ toℕ {2 * m}
add𝔽≡₀⇉ {m} rewrite (+-identityʳ m) = add𝔽⇉
```

If we think of our `m`-bounded numbers as *digits* in base/radix `m`, then the result is in base `2 * m`, which seem awkward.
On the other hand, for any `n` and `m`, `𝔽 (n * m)` is isomorphic to `𝔽 n × 𝔽 m` and hence to `𝔽 m × 𝔽 n`.
In particular, we can repackage `𝔽 (2 * m)` as `𝔽 m × 𝔽 2`, splitting our result into a base-`m` digit and a carry-out bit.

If we have a correct adder with carry-in and carry-out, we can convert it into an adder having the same type as `add𝔽≡₀⇉`.
Make clarify this claim, let's give a name to correct carry-in-out adders:

```agda
toℕ⊹☆ : ∀ {k m} → 𝔽 m × 𝔽 k → ℕ
toℕ⊹☆ {k}{m} (i , j) = toℕ i + m * toℕ j

Addᶜ : ℕ → Set
Addᶜ m = toℕ {2} ⊗ toℕ {m} ⊗ toℕ {m} ⇉ toℕ⊹☆ {2}{m}
```

I'll refer to these correct carry-in/carry-out adders as "digit adders" for base `m`.

Now let's suppose that we have digit adders for base `m` and base `n`.
How can we combine them into a digit adder for base `m * n`?

    infixr 4 _•ᶜ_
    _•ᶜ_ : ∀ {m n} → Addᶜ m → Addᶜ n → Addᶜ (m * n)
    +m •ᶜ +n = {!!}


I don't think this formulation is quite right.
Our adders won't operate on `𝔽 m` for some `m`, but rather on some other representation of `𝔽 m`.
The composite adder will operate on pairs of representations.

```agda
Addᶜ′ : ∀ {r : Set}{m} (f : r → 𝔽 m) → Set
Addᶜ′{r}{m} f = toℕ {2} ⊗ toℕ′ ⊗ toℕ′ ⇉ toℕ′ ⊗ toℕ {2} where toℕ′ = toℕ ∘ f
```

:::aside
Now show define pairings of `Addᶜ′`s and an `Addᶜ′` for `⊤`.
Could `Addᶜ′` be the objects of a cartesian or at least monoidal category?
What are the morphisms?
:::

Since the result must be a *correct* adder of ...

* * * * * * * * * * * * * * * * * * * *

Fortunately, `Data.Fin.Base` ([as of agda-stdlib version 1.6](https://github.com/agda/agda-stdlib/blob/master/CHANGELOG/v1.6.md)) defines two conversion functions:

```agdaQ
remQuot : ∀ k → Fin (n * k) → Fin n × Fin k
combine : Fin n → Fin k → Fin (n * k)
```

Moreover, `Data.Fin.Properties` proves that `remQuot` and `uncurry combine` are inverses:
```agdaQ
remQuot-combine : ∀ x y → remQuot k (combine x y) ≡ (x , y)
combine-remQuot : ∀ k i → uncurry combine (remQuot k i) ≡ i
```

These four parts get packaged up for us:
```agdaQ
*↔× : ∀ {m n} → Fin (m ℕ.* n) ↔ (Fin m × Fin n)
*↔× {m} {n} = mk↔′ (remQuot {m} n) (uncurry combine) (uncurry remQuot-combine) (combine-remQuot {m} n)
```

* * * * * * * * * * * * * * * * * * * *

Suppose I have any representation of `𝔽 m` and a corresponding correct implementation of addition with carry in & out on that representation.
Likewise for `𝔽 n`.
Then I can make a representation of 
