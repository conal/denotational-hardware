module Examples.Add.KFin where

open import Data.Unit using (tt) renaming (⊤ to ⊤′)  -- for type hints
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; uncurry)
  renaming (_×_ to _×′_; map to _⊗′_) -- makes type hints easier to read
open import Data.Fin as 𝔽 hiding (_+_) renaming (Fin to 𝔽)
open import Data.Fin.Properties
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open ≡-Reasoning
open import Data.Vec hiding (splitAt)
open import Function using (_∘′_) renaming (id to id′) -- TEMP
open import Data.Nat.Tactic.RingSolver

open import Categorical.Raw hiding (uncurry)
open import Functions
open import Categorical.Arrow Function ; open _⇨_

inject+′ : ∀ {m} n → 𝔽 m → 𝔽 (n + m)
inject+′ {m} n j = cast (+-comm m n) (inject+ n j)

toℕ-inject+′ : ∀ {m} n (j : 𝔽 m) → toℕ (inject+′ n j) ≡ toℕ j
toℕ-inject+′ {m} n j = trans (toℕ-cast _ _) (sym (toℕ-inject+ n j))

infixl 6 _⊹_
_⊹_ : ∀ {m n} → 𝔽 (suc m) → 𝔽 n → 𝔽 (m + n)
_⊹_ {m}      zero   j = inject+′ m j
_⊹_ {suc _} (suc i) j = suc (i ⊹ j)

⟨+⟩ : ℕ × ℕ → ℕ
⟨+⟩ = uncurry _+_

⟨⊹⟩ : ∀ {m n} → 𝔽 (suc m) × 𝔽 n → 𝔽 (m + n)
⟨⊹⟩ = uncurry _⊹_

toℕ-⊹ : ∀ {m n} ((i , j) : 𝔽 (suc m) × 𝔽 n) → toℕ (i ⊹ j) ≡ toℕ i + toℕ j
toℕ-⊹ {m} (zero , j) = toℕ-inject+′ m j
toℕ-⊹ {suc _} (suc i , j) rewrite toℕ-⊹ (i , j) = refl

⊹⇉ : ∀ {m n} → toℕ {suc m} ⊗ toℕ {n} ⇉ toℕ {m + n}
⊹⇉ = mk ⟨⊹⟩ ⟨+⟩ toℕ-⊹

-- file:///Users/conal/git-repos/quiver/src/index.html?q=WzAsNCxbMCwwLCJOIFxcdGltZXMgTiJdLFsyLDAsIk4iXSxbMCwyLCJGX3tzdWNcXCBtfSDDlyBGX24iXSxbMiwyLCJGX3ttICsgbn0iXSxbMCwxLCJcXGxhbmdsZStcXHJhbmdsZSIsMV0sWzIsMCwidG9OX3tzdWNcXCBtfSAgXFxvdGltZXMgdG9OX24iLDFdLFszLDEsInRvTl97bSArIG59IiwxXSxbMiwzLCJcXGxhbmdsZeKKuVxccmFuZ2xlIiwxXV0=

add𝔽⇉ : ∀ {m n} → toℕ {2} ⊗ toℕ {m} ⊗ toℕ {n} ⇉ toℕ {m + n}
add𝔽⇉ = ⊹⇉ ∘ first ⊹⇉ ∘ assocˡ

add𝔽 : ∀ {m n} → 𝔽 2 × 𝔽 m × 𝔽 n → 𝔽 (m + n)
add𝔽 = f₁ add𝔽⇉

combℕ : (n : ℕ) → ℕ × ℕ → ℕ
combℕ n (i , j) = i + j * n

open import Data.Nat.DivMod
open import Relation.Nullary.Decidable using (False)

infix 4 _≢0
_≢0 : ℕ → Set
m ≢0 = False (m ℕP.≟ 0)

-- quotRem k "i" = "i % k" , "i / k". Naming convention from agda-stdlib.
quotRemℕ : ∀ n → ⦃ n≢0 : n ≢0 ⦄ → ℕ → ℕ × ℕ
quotRemℕ (suc n) m = m % suc n , m / suc n

-- -- Equivalently,
-- quotRemℕ n ⦃ n≢0 ⦄ m = (m % n) {n≢0} , (m / n) {n≢0}

-- Alternatively,
quotRemℕ′ : ∀ n → ℕ → ℕ × ℕ
quotRemℕ′ n m = m % suc n , m / suc n
-- I'm leaning toward this simpler alternative.

qrℕ2 : ℕ → ℕ × ℕ
qrℕ2 = quotRemℕ 2

-- qrℕ0 : ℕ → ℕ × ℕ
-- qrℕ0 = quotRemℕ 0  -- "No instance of type 0 ≢0 was found in scope."

comb∘quotRemℕ : (n : ℕ) ⦃ n≢0 : n ≢0 ⦄ → combℕ n ∘ quotRemℕ n ≗ id
comb∘quotRemℕ (suc n) m = sym (m≡m%n+[m/n]*n m n)

inverse⇉ : ∀ {a b a′ b′ : Set} (f : a → b){i : a′ → a}{j : b′ → b}{j⁻¹ : b → b′}
         → j ∘ j⁻¹ ≗ id
         → i ⇉ j
inverse⇉ f {i}{j}{j⁻¹} j∘j⁻¹ = mk (j⁻¹ ∘ f ∘ i) f (λ a → j∘j⁻¹ (f (i a)))

addℕ : ℕ × ℕ × ℕ → ℕ
addℕ (cᵢ , a , b) = cᵢ + a + b

addcℕ⇉ : ∀ k → ⦃ _ : k ≢0 ⦄ → id {a = ℕ × ℕ × ℕ} ⇉ combℕ k
addcℕ⇉ k = inverse⇉ addℕ {j⁻¹ = quotRemℕ k} (comb∘quotRemℕ k)

addcℕ : ∀ k → ⦃ _ : k ≢0 ⦄ → ℕ × ℕ × ℕ → ℕ × ℕ
addcℕ k = quotRemℕ k ∘ addℕ

_ : ∀ {k} ⦃ _ : k ≢0 ⦄ → f₁ (addcℕ⇉ k) ≡ addcℕ k
_ = refl

B : Set
B = Bool

bval : B → ℕ
bval 𝕗 = 0
bval 𝕥 = 1

C : Set → Set
C r = B × r × r → r × B

addᶜ⇉ : ∀ k ⦃ _ : k ≢0 ⦄ {r : Set} {μ : r → ℕ} (+̂ : C r)
      → (μ ⊗ bval) ∘ +̂ ≗ addcℕ k ∘ (bval ⊗ twice μ)
      → bval ⊗ twice μ ⇉ μ ⊗ bval
addᶜ⇉ k +̂ = mk +̂ (addcℕ k)

record Adder k ⦃ _ : k ≢0 ⦄ {r : Set}{μ : r → ℕ} : Set where
  constructor mk
  field
    arr : bval ⊗ twice μ ⇉ μ ⊗ bval
    ⦃ isAdd ⦄ : f₂ arr ≡ addcℕ k

adder : ∀ {k} ⦃ _ : k ≢0 ⦄ {r : Set} {μ : r → ℕ} (+̂ : C r)
      → (μ ⊗ bval) ∘ +̂ ≗ addcℕ k ∘ (bval ⊗ twice μ)
      → Adder k {r}{μ}
adder {k} +̂ commute = mk (addᶜ⇉ k +̂ commute)

pattern adderᵖ +̂ commute = mk (mk +̂ _ commute)

-- Save some typing. Replace later.

F : ℕ → Set
F = 𝔽

N : Set
N = ℕ

0ᶜ : Adder 1 {⊤}{λ { tt → zero }}
0ᶜ = adder (λ (cᵢ , tt , tt) → tt , cᵢ)
           λ {(𝕗 , tt , tt) → refl ; (𝕥 , tt , tt) → refl}

import Data.Bool as B

1ᶜ : Adder 2
1ᶜ = adder +̂ comm
 where
   ½̂ : B × B → B × B
   ½̂ (a , b) = a B.xor b , a B.∧ b

   +̂ : C B
   +̂ (cᵢ , a , b) = let p , d = ½̂ (a , b) ; q , e = ½̂ (cᵢ , p) in
     q , e B.∨ d

   -- -- In categorical terms,
   -- ½̂ = xor ▵ ∧
   -- +̂ = second ∨ ∘ inAssocˡ ½̂ ∘ second ½̂

   comm : (bval ⊗ bval) ∘ +̂ ≗ addcℕ 2 ∘ (bval ⊗ twice bval)
   comm (𝕗 , 𝕗 , 𝕗) = refl
   comm (𝕗 , 𝕗 , 𝕥) = refl
   comm (𝕗 , 𝕥 , 𝕗) = refl
   comm (𝕗 , 𝕥 , 𝕥) = refl
   comm (𝕥 , 𝕗 , 𝕗) = refl
   comm (𝕥 , 𝕗 , 𝕥) = refl
   comm (𝕥 , 𝕥 , 𝕗) = refl
   comm (𝕥 , 𝕥 , 𝕥) = refl


step₁′ : ∀ kᵣ cᵢ xᵣ xₛ yᵣ yₛ
  → cᵢ + (xᵣ + xₛ * kᵣ) + (yᵣ + yₛ * kᵣ) ≡ (cᵢ + xᵣ + yᵣ) + (xₛ + yₛ) * kᵣ
step₁′ = solve-∀

step₁ : ∀ kᵣ ⦃ _ : kᵣ ≢0 ⦄ cᵢ xᵣ xₛ yᵣ yₛ →
  let zᵣ , cₘ = addcℕ kᵣ (cᵢ , xᵣ , yᵣ)
  in addℕ (cᵢ , combℕ kᵣ (xᵣ , xₛ) , combℕ kᵣ (yᵣ , yₛ))
       ≡ combℕ kᵣ (combℕ kᵣ (zᵣ , cₘ) , xₛ + yₛ)
step₁ kᵣ cᵢ xᵣ xₛ yᵣ yₛ =
  let zᵣ , cₘ = addcℕ kᵣ (cᵢ , xᵣ , yᵣ)
  in begin
       cᵢ + (xᵣ + xₛ * kᵣ) + (yᵣ + yₛ * kᵣ)
     ≡⟨ step₁′ kᵣ cᵢ xᵣ xₛ yᵣ yₛ ⟩
       (cᵢ + xᵣ + yᵣ) + (xₛ + yₛ) * kᵣ
     ≡⟨ cong (_+ (xₛ + yₛ) * kᵣ) (sym (comb∘quotRemℕ kᵣ (cᵢ + xᵣ + yᵣ))) ⟩
       combℕ kᵣ (quotRemℕ kᵣ (cᵢ + xᵣ + yᵣ)) + (xₛ + yₛ) * kᵣ
     ≡⟨⟩
       combℕ kᵣ (zᵣ , cₘ) + (xₛ + yₛ) * kᵣ
    ≡⟨⟩
      combℕ kᵣ (combℕ kᵣ (zᵣ , cₘ) , xₛ + yₛ)
     ∎

step₂′ : ∀ kᵣ kₛ zᵣ cₘ xₛ yₛ →
  zᵣ + cₘ * kᵣ + (xₛ + yₛ) * kᵣ ≡ zᵣ + (cₘ + xₛ + yₛ) * kᵣ
step₂′ = solve-∀

step₂ : ∀ kᵣ kₛ ⦃ _ : kᵣ ≢0 ⦄ ⦃ _ : kₛ ≢0 ⦄ zᵣ cₘ xₛ yₛ →
  combℕ kᵣ (combℕ kᵣ (zᵣ , cₘ) , xₛ + yₛ) ≡ combℕ kᵣ (zᵣ , combℕ kₛ (addcℕ kₛ (cₘ , xₛ , yₛ)))
step₂ kᵣ kₛ zᵣ cₘ xₛ yₛ =
    begin
      combℕ kᵣ (combℕ kᵣ (zᵣ , cₘ) , xₛ + yₛ)
    ≡⟨ step₂′ kᵣ kₛ zᵣ cₘ xₛ yₛ ⟩
      combℕ kᵣ (zᵣ , cₘ + xₛ + yₛ)
    ≡⟨ cong (λ z → combℕ kᵣ (zᵣ , z)) (sym (comb∘quotRemℕ kₛ (cₘ + xₛ + yₛ))) ⟩
      combℕ kᵣ (zᵣ , combℕ kₛ (quotRemℕ kₛ (cₘ + xₛ + yₛ)))
    ≡⟨⟩
      combℕ kᵣ (zᵣ , combℕ kₛ (addcℕ kₛ (cₘ , xₛ , yₛ)))
    ∎

add× : (kᵣ : ℕ) (kₛ : ℕ) ⦃ _ : kᵣ ≢0 ⦄ ⦃ _ : kₛ ≢0 ⦄
     → ℕ × (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) × ℕ
add× kᵣ kₛ (cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) =
  let zᵣ , cₘ = addcℕ kᵣ (cᵢ , xᵣ , yᵣ)
      zₛ , cₒ = addcℕ kₛ (cₘ , xₛ , yₛ)
  in (zᵣ , zₛ) , cₒ

step₃′ : ∀ kᵣ kₛ zᵣ zₛ cₒ →
  zᵣ + (zₛ + cₒ * kₛ) * kᵣ ≡ zᵣ + zₛ * kᵣ + cₒ * (kₛ * kᵣ)
step₃′ = solve-∀

step₃ : ∀ (kᵣ : ℕ) (kₛ : ℕ) ⦃ _ : kᵣ ≢0 ⦄ ⦃ _ : kₛ ≢0 ⦄
          ((cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ)) : ℕ × (ℕ × ℕ) × (ℕ × ℕ)) →
  let (zᵣ , zₛ) , cₒ = add× kᵣ kₛ ((cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))) in
    combℕ kᵣ (zᵣ , combℕ kₛ (zₛ , cₒ)) ≡ combℕ (kₛ * kᵣ) (combℕ kᵣ (zᵣ , zₛ) , cₒ)
step₃ kᵣ kₛ ((cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))) =
  let (zᵣ , zₛ) , cₒ = add× kᵣ kₛ ((cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))) in
    step₃′ kᵣ kₛ zᵣ zₛ cₒ

addℕ× : (kᵣ : ℕ) (kₛ : ℕ) ⦃ _ : kᵣ ≢0 ⦄ ⦃ _ : kₛ ≢0 ⦄ →
    addℕ ∘ second (twice (combℕ kᵣ))
  ≗ combℕ (kₛ * kᵣ) ∘ first (combℕ kᵣ) ∘ add× kᵣ kₛ

addℕ× kᵣ kₛ ((cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))) =
  let zᵣ , cₘ = addcℕ kᵣ (cᵢ , xᵣ , yᵣ)
      zₛ , cₒ = addcℕ kₛ (cₘ , xₛ , yₛ)
  in
    begin
      addℕ (cᵢ , combℕ kᵣ (xᵣ , xₛ) , combℕ kᵣ (yᵣ , yₛ))
    ≡⟨ step₁ kᵣ cᵢ xᵣ xₛ yᵣ yₛ ⟩
      combℕ kᵣ (combℕ kᵣ (zᵣ , cₘ) , xₛ + yₛ)
    ≡⟨ step₂ kᵣ kₛ zᵣ cₘ xₛ yₛ ⟩
      combℕ kᵣ (zᵣ , combℕ kₛ (zₛ , cₒ))
    ≡⟨ step₃ kᵣ kₛ ((cᵢ , (xᵣ , xₛ) , (yᵣ , yₛ))) ⟩
      combℕ (kₛ * kᵣ) (combℕ kᵣ (zᵣ , zₛ) , cₒ)
    ∎
