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

open import Data.Unit using (tt) renaming (⊤ to ⊤′)  -- for type hints
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; uncurry)
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

If we think of our `m`-bounded numbers as *digits* in base/radix `m`, then the result is in base `2 * m`.a
For any `n` and `m`, however, `𝔽 (n * m)` is isomorphic to `𝔽 n × 𝔽 m` and hence to `𝔽 m × 𝔽 n`.
In particular, we can repackage `𝔽 (2 * m)` as `𝔽 m × 𝔽 2`, splitting our result into a base-`m` digit and a carry-out bit.

If we have a correct adder with carry-in and carry-out, we can convert it into an adder having the same type as `add𝔽≡₀⇉`.
To clarify this claim, let's give a name to correct carry-in-out adders:

```agda

-- inject+ : ∀ {m} n → Fin m → Fin (m ℕ.+ n)

-- inject+′ : ∀ {m} n → 𝔽 m → 𝔽 (n + m)

-- combine : ∀ {k m} → 𝔽 k → 𝔽 m → 𝔽 (k * m)
-- combine {suc k} {m} zero j = inject+ (k * m) j
-- combine {suc k} {m} (suc i) j = raise m (combine i j)

-- toℕ-raise : ∀ {m} n (i : Fin m) → toℕ (raise n i) ≡ n + toℕ i

toℕ-combine : ∀ {k m} (j : 𝔽 k) (i : 𝔽 m)
            → toℕ (combine {k}{m} j i) ≡ toℕ j * m + toℕ i
toℕ-combine {suc k} {m}  zero   i = sym (toℕ-inject+ (k * m) i)
toℕ-combine {suc k} {m} (suc j) i =
    begin
      toℕ (combine {suc k}{m} (suc j) i)
    ≡⟨⟩
      toℕ (raise m (combine j i))
    ≡⟨ toℕ-raise m (combine j i) ⟩
      m + toℕ (combine j i)
    ≡⟨ cong (m +_) (toℕ-combine j i) ⟩
      m + (toℕ j * m + toℕ i)
    ≡⟨ sym (+-assoc m (toℕ j * m) (toℕ i)) ⟩
      m + toℕ j * m + toℕ i
    ≡⟨⟩
      toℕ (suc j) * m + toℕ i
    ∎

```

```agda

toℕ× : ∀ {m k} → 𝔽 m × 𝔽 k → ℕ
toℕ× {m}{k} (i , j) = toℕ i + toℕ j * m



-- Carry-out on right (and carry-in on left)
comb : ∀ {m k} → 𝔽 m × 𝔽 k → 𝔽 (m * k)
comb {m}{k} (i , j) = subst 𝔽 (*-comm k m) (combine j i)

-- comb-assoc : ∀ {m n k} {h : 𝔽 m}{i : 𝔽 n}{j : 𝔽 k}
--            → comb (comb (h , i) , j)
--            ≡ subst 𝔽 (sym (*-assoc m n k)) (comb (h , comb (i , j)))
-- comb-assoc {m}{n}{k}{h}{i}{j} =
--     begin
--       comb (comb (h , i) , j)
--     ≡⟨⟩
--       subst 𝔽 (*-comm k (m * n))
--         (combine j (subst 𝔽 (*-comm n m) (combine i h)))
--     ≡⟨ {!!} ⟩
--       {!!}
--     ≡⟨⟩
--       subst 𝔽 (sym (*-assoc m n k)) (comb (h , comb (i , j)))
--     ∎

toℕ-comb : ∀ {m k} → toℕ ∘ comb ≗ toℕ× {m}{k}
toℕ-comb {m}{k} (i , j) =
    begin
      toℕ (comb {m}{k} (i , j))
    ≡⟨⟩
      toℕ (subst 𝔽 (*-comm k m) (combine j i))
    ≡⟨ toℕ-subst ⟩
      toℕ (combine j i)
    ≡⟨ toℕ-combine j i ⟩
      toℕ j * m + toℕ i
    ≡⟨ +-comm (toℕ j * m) (toℕ i) ⟩
      toℕ× (i , j)
    ∎


toℕ-comb-assoc : ∀ {m n k} {h : 𝔽 m}{i : 𝔽 n}{j : 𝔽 k}
               → toℕ (comb (comb (h , i) , j)) ≡ toℕ (comb (h , comb (i , j)))
toℕ-comb-assoc {m}{n}{k}{h}{i}{j} =
  begin
    toℕ (comb (comb (h , i) , j))
  ≡⟨ toℕ-comb (comb (h , i) , j) ⟩
    toℕ× (comb (h , i) , j)
  ≡⟨⟩
    toℕ (comb (h , i)) + toℕ j * (m * n)
  ≡⟨ cong (_+ toℕ j * (m * n)) (toℕ-comb (h , i)) ⟩
    toℕ× (h , i) + toℕ j * (m * n)
  ≡⟨⟩
    toℕ h + toℕ i * m + toℕ j * (m * n)
  ≡⟨ {!!} ⟩
    toℕ h + (toℕ i + toℕ j * n) * m
  ≡⟨⟩
    toℕ h + toℕ× (i , j) * m
  ≡⟨ sym (cong (λ z → toℕ h + z * m) (toℕ-comb (i , j))) ⟩
    toℕ h + toℕ (comb (i , j)) * m
  ≡⟨⟩
    toℕ× (h , comb (i , j))
  ≡⟨ sym (toℕ-comb (h , comb (i , j))) ⟩
    toℕ (comb (h , comb (i , j)))
  ∎

    -- begin
    --   toℕ (comb (comb (h , i) , j))
    -- ≡⟨⟩
    --   toℕ (subst 𝔽 (*-comm k (m * n))
    --         (combine j (subst 𝔽 (*-comm n m) (combine i h))))
    -- ≡⟨ toℕ-subst ⟩
    --   toℕ (combine j (subst 𝔽 (*-comm n m) (combine i h)))
    -- ≡⟨ toℕ-combine j (subst 𝔽 (*-comm n m) (combine i h)) ⟩
    --   toℕ j * (m * n) + toℕ (subst 𝔽 (*-comm n m) (combine i h))
    -- ≡⟨ cong ((toℕ j * (m * n)) +_) toℕ-subst ⟩
    --   toℕ j * (m * n) + toℕ (combine i h)
    -- ≡⟨ cong (toℕ j * (m * n) +_) (toℕ-combine i h) ⟩
    --   toℕ j * (m * n) + (toℕ i * m + toℕ h)
    -- ≡⟨ {!!} ⟩
    --   toℕ (comb (h , comb (i , j)))
    -- ≡⟨⟩
    --   toℕ (comb (h , comb (i , j)))
    -- ∎


```

```agda

C : Set → Set
C r = 𝔽 2 × r × r → r × 𝔽 2

Addᶜ⇉ : ∀ {m}{r : Set} {μ : r → 𝔽 m} → Set
-- Addᶜ⇉ {m}{r}{μ} = toℕ {2} ⊗ twice (toℕ ∘ μ) ⇉ toℕ× {m}{2} ∘ first μ
Addᶜ⇉ {m} {μ = μ} = toℕ {2} ⊗ twice (toℕ ∘ μ) ⇉ toℕ {m * 2} ∘ comb ∘ first μ

Adder : ∀ {m}{r : Set} {μ : r → 𝔽 m} → Set
Adder {m}{r}{μ} = Σ[(mk _ f₂ _) ∈ Addᶜ⇉ {m}{r}{μ}] (f₂ ≡ addℕ)

-- Adder {m}{r}{μ} = Σ (Addᶜ⇉ {m}{r}{μ}) λ (mk _ f₂ _) → f₂ ≡ addℕ
       
adder : {m : ℕ} {r : Set} {μ : r → 𝔽 m}
        (+̂ : 𝔽 2 × r × r → r × 𝔽 2)
        -- (commute : (toℕ× ∘ first μ) ∘ +̂ ≗ addℕ ∘ (toℕ ⊗ twice (toℕ ∘ μ)) )
        (commute : (toℕ ∘ comb ∘ first μ) ∘ +̂ ≗ addℕ ∘ (toℕ ⊗ twice (toℕ ∘ μ)) )
      → Adder {m}{r}{μ}
adder +̂ commute = mk +̂ addℕ commute , refl

pattern adderᵖ +̂ commute = mk +̂ _ commute , refl

⊤ᶜ : Adder {1}
⊤ᶜ = adder {1}{⊤}{λ { tt → zero }}
           (λ (cᵢ , tt , tt) → tt , cᵢ)
           λ (cᵢ , tt , tt) →
       begin
         toℕ (comb (zero {zero} , cᵢ))
       ≡⟨ toℕ-comb (zero {zero} , cᵢ) ⟩
         toℕ× (zero {zero} , cᵢ)
       ≡⟨⟩
         toℕ cᵢ * 1
       ≡⟨ *-identityʳ (toℕ cᵢ) ⟩
         toℕ cᵢ
       ≡⟨ sym (+-identityʳ (toℕ cᵢ)) ⟩
         toℕ cᵢ + 0
       ≡⟨ sym (+-assoc (toℕ cᵢ) 0 0) ⟩
         toℕ cᵢ + 0 + 0
       ∎


_,̂_ : ∀ {r s} → C r → C s → C (r × s)
(+̂ᵣ ,̂ +̂ₛ) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) =
  let zᵣ , cₘ = +̂ᵣ (cᵢ , xᵣ , yᵣ)
      zₛ , cₒ = +̂ₛ (cₘ , xₛ , yₛ)
    in (zᵣ , zₛ) , cₒ

infixr 2 _ː_
_ː_ : ∀ {m n}{r s} (μᵣ : r → 𝔽 m) (μₛ : s → 𝔽 n) → (r × s → 𝔽 (m * n))
μᵣ ː μₛ = comb ∘ (μᵣ ⊗ μₛ)


infixr 2 _×ᶜ_
_×ᶜ_ : ∀ {m n} {r s} {μᵣ : r → 𝔽 m}{μₛ : s → 𝔽 n}
     → Adder {m}{r}{μᵣ} → Adder {n}{s}{μₛ} → Adder {m * n}{r × s}{μᵣ ː μₛ}

_×ᶜ_ {m}{n}{r}{s}{μᵣ}{μₛ} (adderᵖ +̂ᵣ +̃ᵣ) (adderᵖ +̂ₛ +̃ₛ) =
  adder (+̂ᵣ ,̂ +̂ₛ) λ (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) →
    let zᵣ , cₘ = +̂ᵣ (cᵢ , xᵣ , yᵣ)
        zₛ , cₒ = +̂ₛ (cₘ , xₛ , yₛ) in

-- (commute : (toℕ ∘ comb ∘ first μ) ∘ +̂ ≗ addℕ ∘ (toℕ ⊗ twice (toℕ ∘ μ)) )

-- toℕ× {m}{k} (i , j) = toℕ i + toℕ j * m

-- toℕ-comb : ∀ {m k} → toℕ ∘ comb ≗ toℕ× {m}{k}

      begin
        ((toℕ ∘ comb ∘ first (μᵣ ː μₛ)) ∘ (+̂ᵣ ,̂ +̂ₛ)) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
      ≡⟨⟩
        toℕ (comb (first (μᵣ ː μₛ) ((+̂ᵣ ,̂ +̂ₛ) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)))))
      ≡⟨⟩
        toℕ (comb (first (μᵣ ː μₛ) ((zᵣ , zₛ) , cₒ)))
      ≡⟨⟩
        toℕ (comb ((μᵣ ː μₛ) (zᵣ , zₛ) , cₒ))
      ≡⟨⟩
        toℕ (comb ((comb ∘ (μᵣ ⊗ μₛ)) (zᵣ , zₛ) , cₒ))
      ≡⟨⟩
        toℕ (comb (comb (μᵣ zᵣ , μₛ zₛ) , cₒ))

      -- Oho! Maybe the key is an associativity property for comb

      ≡⟨ toℕ-comb (comb (μᵣ zᵣ , μₛ zₛ) , cₒ) ⟩
        toℕ× (comb (μᵣ zᵣ , μₛ zₛ) , cₒ)
      ≡⟨⟩
        toℕ (comb (μᵣ zᵣ , μₛ zₛ)) + toℕ cₒ * (m * n)
      ≡⟨ cong (_+ toℕ cₒ * (m * n)) (toℕ-comb (μᵣ zᵣ , μₛ zₛ))⟩
        toℕ× (μᵣ zᵣ , μₛ zₛ) + toℕ cₒ * (m * n)
      ≡⟨ {!!} ⟩

        toℕ cᵢ + toℕ× (μᵣ xᵣ , μₛ xₛ) + toℕ× (μᵣ yᵣ , μₛ yₛ)
      ≡⟨ sym (cong₂ (λ p q → toℕ cᵢ + p + q)
               (toℕ-comb (μᵣ xᵣ , μₛ xₛ)) (toℕ-comb (μᵣ yᵣ , μₛ yₛ))) ⟩
        toℕ cᵢ + toℕ (comb (μᵣ xᵣ , μₛ xₛ)) + toℕ (comb (μᵣ yᵣ , μₛ yₛ))
      ≡⟨⟩
        toℕ cᵢ + (toℕ ∘ (μᵣ ː μₛ)) (xᵣ , xₛ) + (toℕ ∘ (μᵣ ː μₛ)) (yᵣ , yₛ)
      ≡⟨⟩
        addℕ ((toℕ ⊗ twice (toℕ ∘ (μᵣ ː μₛ))) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)))
      ≡⟨⟩
        (addℕ ∘ (toℕ ⊗ twice (toℕ ∘ (μᵣ ː μₛ)))) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
      ∎

     -- begin
     --   ((toℕ× ∘ first (μᵣ ː μₛ)) ∘ (+̂ᵣ ,̂ +̂ₛ)) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
     -- ≡⟨⟩
     --   (toℕ× ∘ first (μᵣ ː μₛ)) ((zᵣ , zₛ) , cₒ)
     -- ≡⟨⟩
     --   toℕ× ((μᵣ ː μₛ) (zᵣ , zₛ) , cₒ)
     -- ≡⟨⟩
     --   toℕ× (combine (μᵣ zᵣ) (μₛ zₛ) , cₒ)
     -- ≡⟨ {!!} ⟩
     --   toℕ cᵢ + toℕ (combine (μᵣ xᵣ) (μₛ xₛ)) + toℕ (combine (μᵣ yᵣ) (μₛ yₛ))
     -- ≡⟨⟩
     --   toℕ cᵢ + toℕ ((μᵣ ː μₛ) (xᵣ , xₛ)) + toℕ ((μᵣ ː μₛ) (yᵣ , yₛ))
     -- ≡⟨⟩
     --   (addℕ ∘ (toℕ ⊗ twice (toℕ ∘ (μᵣ ː μₛ)))) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
     -- ∎



-- mk {mᵣ}{r}{μᵣ} +̂ᵣ +̃ᵣ ×ᶜ mk {mₛ}{s}{μₛ} +̂ₛ +̃ₛ =
--   mk {mᵣ * mₛ} {r × s} {μᵣ ː μₛ} (+̂ᵣ ,̂ +̂ₛ) λ (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) → ?

--     let zᵣ , cₘ = +̂ᵣ (cᵢ , xᵣ , yᵣ)
--         zₛ , cₒ = +̂ₛ (cₘ , xₛ , yₛ) in

--      begin
--        ((toℕ× ∘ first (μᵣ ː μₛ)) ∘ (+̂ᵣ ,̂ +̂ₛ)) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
--      ≡⟨⟩
--        (toℕ× ∘ first (μᵣ ː μₛ)) ((zᵣ , zₛ) , cₒ)
--      ≡⟨⟩
--        toℕ× ((μᵣ ː μₛ) (zᵣ , zₛ) , cₒ)
--      ≡⟨⟩
--        toℕ× (combine (μᵣ zᵣ) (μₛ zₛ) , cₒ)
--      ≡⟨ {!!} ⟩
--        toℕ cᵢ + toℕ (combine (μᵣ xᵣ) (μₛ xₛ)) + toℕ (combine (μᵣ yᵣ) (μₛ yₛ))
--      ≡⟨⟩
--        toℕ cᵢ + toℕ ((μᵣ ː μₛ) (xᵣ , xₛ)) + toℕ ((μᵣ ː μₛ) (yᵣ , yₛ))
--      ≡⟨⟩
--        (addℕ ∘ (toℕ ⊗ twice (toℕ ∘ (μᵣ ː μₛ)))) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
--      ∎


```

```agdaQ

-- The parts of an adder ⇉
record Adder : Set₁ where
  constructor mk
  field
    {m} : ℕ
    {r} : Set
    {μ} : r → 𝔽 m
    +̂ : 𝔽 2 × r × r → r × 𝔽 2
    -- commute : (toℕ× ∘ first μ) ∘ +̂ ≗ addℕ ∘ (toℕ ⊗ twice (toℕ ∘ μ)) 
    commute : (toℕ ∘ comb ∘ first μ) ∘ +̂ ≗ addℕ ∘ (toℕ ⊗ twice (toℕ ∘ μ)) 

-- TODO: phase out if used only in Adder⇉
Addᶜ⇉ : ∀ {m}{r : Set} {μ : r → 𝔽 m} → Set
-- Addᶜ⇉ {μ = μ} = toℕ {2} ⊗ twice (toℕ ∘ μ) ⇉ toℕ× {2} ∘ first μ
Addᶜ⇉ {m} {μ = μ} = toℕ {2} ⊗ twice (toℕ ∘ μ) ⇉ toℕ {m * 2} ∘ comb ∘ first μ

-- Adder⇉ : (h : Adder) → let open Adder h using (μ) in
--                        toℕ {2} ⊗ twice (toℕ ∘ μ) ⇉ toℕ× {2} ∘ first μ

-- Adder⇉ : Adder → Addᶜ⇉  -- doesn't check

-- Wrap up as ⇉
Adder⇉ : (_ : Adder) → Addᶜ⇉
Adder⇉ (mk +̂ commute) = mk +̂ addℕ commute

⊤ᶜ : Adder
⊤ᶜ = mk {1}{⊤}{λ { tt → zero }}
        (λ (cᵢ , tt , tt) → tt , cᵢ)
        λ (cᵢ , tt , tt) →
          begin
            toℕ (comb {1} (zero , cᵢ))
          ≡⟨ toℕ-comb {1} (zero , cᵢ) ⟩
            toℕ× {2}{1} (zero , cᵢ)
          ≡⟨⟩
            0 + 1 * toℕ cᵢ
          ≡⟨⟩
            toℕ cᵢ + 0
          ≡⟨ cong (_+ 0) (sym (+-identityʳ (toℕ cᵢ))) ⟩
            toℕ cᵢ + 0 + 0
          ∎

_,̂_ : ∀ {r s} → (𝔽 2 × r × r → r × 𝔽 2)
              → (𝔽 2 × s × s → s × 𝔽 2)
              → (𝔽 2 × (r × s) × (r × s) → (r × s) × 𝔽 2) -- TODO: abbreviate
(+̂ᵣ ,̂ +̂ₛ) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) =
  let zᵣ , cₘ = +̂ᵣ (cᵢ , xᵣ , yᵣ)
      zₛ , cₒ = +̂ₛ (cₘ , xₛ , yₛ)
    in (zᵣ , zₛ) , cₒ

infixr 2 _ː_
_ː_ : ∀ {m n}{r s} (μᵣ : r → 𝔽 m) (μₛ : s → 𝔽 n) → (r × s → 𝔽 (m * n))
μᵣ ː μₛ = comb ∘ (μᵣ ⊗ μₛ)
-- (μᵣ ː μₛ) (zᵣ , zₛ) = combine (μᵣ zᵣ) (μₛ zₛ)

-- infixr 2 _×ᶜ_
-- _×ᶜ_ : Adder → Adder → Adder


-- toℕ× {k}{m} (i , cₒ) = toℕ i + m * toℕ cₒ

-- toℕ-comb : ∀ {m k} → toℕ ∘ comb ≡ toℕ× {k}{m}

-- commute : (toℕ ∘ comb ∘ first μ) ∘ +̂ ≗ addℕ ∘ (toℕ ⊗ twice (toℕ ∘ μ)) 


-- mk {mᵣ}{r}{μᵣ} +̂ᵣ +̃ᵣ ×ᶜ mk {mₛ}{s}{μₛ} +̂ₛ +̃ₛ =
--   mk {mᵣ * mₛ} {r × s} {μᵣ ː μₛ} (+̂ᵣ ,̂ +̂ₛ) λ (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) →
--     let zᵣ , cₘ = +̂ᵣ (cᵢ , xᵣ , yᵣ)
--         zₛ , cₒ = +̂ₛ (cₘ , xₛ , yₛ) in

--      begin
--        ((toℕ× ∘ first (μᵣ ː μₛ)) ∘ (+̂ᵣ ,̂ +̂ₛ)) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
--      ≡⟨⟩
--        (toℕ× ∘ first (μᵣ ː μₛ)) ((zᵣ , zₛ) , cₒ)
--      ≡⟨⟩
--        toℕ× ((μᵣ ː μₛ) (zᵣ , zₛ) , cₒ)
--      ≡⟨⟩
--        toℕ× (combine (μᵣ zᵣ) (μₛ zₛ) , cₒ)
--      ≡⟨ {!!} ⟩
--        toℕ cᵢ + toℕ (combine (μᵣ xᵣ) (μₛ xₛ)) + toℕ (combine (μᵣ yᵣ) (μₛ yₛ))
--      ≡⟨⟩
--        toℕ cᵢ + toℕ ((μᵣ ː μₛ) (xᵣ , xₛ)) + toℕ ((μᵣ ː μₛ) (yᵣ , yₛ))
--      ≡⟨⟩
--        (addℕ ∘ (toℕ ⊗ twice (toℕ ∘ (μᵣ ː μₛ)))) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
--      ∎


```

```agdaQ


infixr 2 _×ᶜ_
_×ᶜ_ : Adder → Adder → Adder

mk {mᵣ}{r}{μᵣ} +̂ᵣ +̃ᵣ ×ᶜ mk {mₛ}{s}{μₛ} +̂ₛ +̃ₛ =
  mk {mᵣ * mₛ} {r × s} {μᵣ ː μₛ} (+̂ᵣ ,̂ +̂ₛ) λ (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) →
    let zᵣ , cₘ = +̂ᵣ (cᵢ , xᵣ , yᵣ)
        zₛ , cₒ = +̂ₛ (cₘ , xₛ , yₛ) in

-- (+̂ᵣ ,̂ +̂ₛ) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) =
--   let zᵣ , cₘ = +̂ᵣ (cᵢ , xᵣ , yᵣ)
--       zₛ , cₒ = +̂ₛ (cₘ , xₛ , yₛ)
--     in (zᵣ , zₛ) , cₒ

     begin
       ((toℕ× ∘ first (μᵣ ː μₛ)) ∘ (+̂ᵣ ,̂ +̂ₛ)) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
     ≡⟨⟩
       (toℕ× ∘ first (μᵣ ː μₛ)) ((zᵣ , zₛ) , cₒ)
     ≡⟨⟩
       toℕ× ((μᵣ ː μₛ) (zᵣ , zₛ) , cₒ)
     ≡⟨⟩
       toℕ× (combine (μᵣ zᵣ) (μₛ zₛ) , cₒ)
     ≡⟨ {!!} ⟩
       toℕ cᵢ + toℕ (combine (μᵣ xᵣ) (μₛ xₛ)) + toℕ (combine (μᵣ yᵣ) (μₛ yₛ))
     ≡⟨⟩
       toℕ cᵢ + toℕ ((μᵣ ː μₛ) (xᵣ , xₛ)) + toℕ ((μᵣ ː μₛ) (yᵣ , yₛ))
     ≡⟨⟩
       (addℕ ∘ (toℕ ⊗ twice (toℕ ∘ (μᵣ ː μₛ)))) (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))
     ∎

    -- commute : (toℕ× ∘ first μ) ∘ +̂ ≗ addℕ ∘ (toℕ ⊗ twice (toℕ ∘ μ)) 


    -- (μᵣ ː μₛ) (xᵣ , xₛ) = combine (μᵣ xᵣ) (μₛ xₛ)

   
    -- combine (μᵣ xᵣ) (μₛ xₛ)

    -- toℕ× (combine i j , cₒ)


     -- (μᵣ ː μₛ) (zᵣ , zₛ) = combine (μᵣ zᵣ) (μₛ zₛ)
     


-- Goal: (toℕ× ∘′ first (μᵣ ː μₛ)) ∘′ (+̂ᵣ ,̂ +̂ₛ) ≗
--       addℕ ∘′ (toℕ ⊗ twice (toℕ ∘′ (μᵣ ː μₛ)))
-- ————————————————————————————————————————————————————————————
-- +̃ₛ : (toℕ× ∘′ first μₛ) ∘′ +̂ₛ ≗
--       addℕ ∘′ (toℕ ⊗ twice (toℕ ∘′ μₛ))
-- +̂ₛ : 𝔽 2 ×′ s ×′ s → s ×′ 𝔽 2
-- μₛ  : s → 𝔽 mₛ
-- s   : Set
-- mₛ  : ℕ
-- +̃ᵣ : (toℕ× ∘′ first μᵣ) ∘′ +̂ᵣ ≗
--       addℕ ∘′ (toℕ ⊗ twice (toℕ ∘′ μᵣ))
-- +̂ᵣ : 𝔽 2 ×′ r ×′ r → r ×′ 𝔽 2
-- μᵣ  : r → 𝔽 mᵣ
-- r   : Set
-- mᵣ  : ℕ

--                          -- Addᶜ (comb ∘ (μ ⊗ ν))
-- mk +̂ᵣ +ᵣ +̃ᵣ ×ᶜ mk +̂ₛ +ₛ +̃ₛ = mk (+̂ᵣ ,̂ +̂ₛ) addℕ {!!}

-- _×ᶜ_ : ∀ {m n}{r s} → {μ : r → 𝔽 m} → {ν : s → 𝔽 n}
--      → Addᶜ μ → Addᶜ ν → Addᶜ (μ ː ν)
--                          -- Addᶜ (comb ∘ (μ ⊗ ν))
-- mk +̂ᵣ +ᵣ +̃ᵣ ×ᶜ mk +̂ₛ +ₛ +̃ₛ = mk (+̂ᵣ ,̂ +̂ₛ) addℕ {!!}

```

```agdaQ

⊤ᶜ : Addᶜ {1}{⊤} (λ { tt → zero })
⊤ᶜ = mk (λ (cᵢ , tt , tt) → tt , cᵢ) -- or as unitors
        addℕ
        (λ (cᵢ , tt , tt) →
           begin
             toℕ cᵢ + 0
           ≡⟨ cong (_+ 0) (sym (+-identityʳ (toℕ cᵢ))) ⟩
             toℕ cᵢ + 0 + 0
           ∎)

infixr 4 _,̂_

_,̂_ : ∀ {r s} → (𝔽 2 × r × r → r × 𝔽 2)
              → (𝔽 2 × s × s → s × 𝔽 2)
              → (𝔽 2 × (r × s) × (r × s) → (r × s) × 𝔽 2) -- TODO: abbreviate
(+̂ᵣ ,̂ +̂ₛ) (cᵢ , (x₁ , x₂) , (y₁ , y₂)) =
  let z₁ , cₘ = +̂ᵣ (cᵢ , x₁ , y₁)
      z₂ , cₒ = +̂ₛ (cₘ , x₂ , y₂)
    in (z₁ , z₂) , cₒ

infixr 2 _×ᶜ_
_×ᶜ_ : ∀ {m n}{r s} → {μ : r → 𝔽 m} → {ν : s → 𝔽 n}
     → Addᶜ μ → Addᶜ ν → Addᶜ (μ ː ν)
                         -- Addᶜ (comb ∘ (μ ⊗ ν))
mk +̂ᵣ +ᵣ +̃ᵣ ×ᶜ mk +̂ₛ +ₛ +̃ₛ = mk (+̂ᵣ ,̂ +̂ₛ) addℕ {!!}

-- mk f f̂ f̃ ×ᶜ mk g ĝ g̃ =
--   mk (add× f g) addℕ {!!}
```

I'll refer to these correct carry-in/carry-out adders as "digit adders" for base `m`.

Now let's suppose that we have digit adders for base `m` and base `n`.
How can we combine them into a digit adder for base `m * n`?

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
