module plfa-exercises.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa-exercises.part1.Isomorphism using (_≃_; extensionality)

-- Proof by contradiction.
¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} →
  ¬ A                →
   A                 →
  ---                →
   ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_
-- Thus ¬ A × ¬ B parses as (¬ A) × (¬ B) and ¬ m ≡ n as ¬ (n ≡ m)

-- In agda we use intuinistic logic, where we have only half of this equivalence, namely
-- A implies ¬ ¬ A

¬¬-intro : ∀ {A : Set} →
    A                  →
  -----
  ¬ ¬ A                  -- ((A → ⊥) → ⊥)
¬¬-intro x = λ{ ¬x → ¬x x}

-- Let x be evidence of A. We show that assuming ¬ A leads to a contradiction, and hence
-- ¬ ¬ A must hold. Let ¬x be evidence of ¬ A. Then from A and ¬ A we have a contradiction,
-- evidenced by ¬x x . Hence, we have shown ¬ ¬ A

-- We cannot show that ¬ ¬ A implies A , but we can show ¬ ¬ ¬ A implies ¬ A

¬¬¬-elim : ∀ {A : Set} →
  ¬ ¬ ¬ A              → -- (((A → ⊥) → ⊥) → ⊥)
  -------
    ¬ A                  -- (A → ⊥)
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} →
    (A → B)                    →
  -----------
  (¬ B → ¬ A)                    -- ((B → ⊥) → (A → ⊥))
contraposition f ¬b a = ¬b (f a)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano ()

-- Indeed, there is exaclty one proof of ⊥ → ⊥. We can write proof two different ways:

id : ⊥ → ⊥
id x = x

id' : ⊥ → ⊥
id' ()

-- But, using extensionality, we can prove these equal:

id≡id' : id ≡ id'
id≡id' = extensionality λ ()

-- By extensionality, id ≡ id' holds if for every x in their domain we have id x ≡ id' x.
-- But there is no x in their domain, so the equality holds trivially.

assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality λ x → ⊥-elim (¬x x)

module exercises where

  open import   plfa-exercises.part1.Relations
       using    (_<_)
  open _<_

  <-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
  <-irreflexive (s<s n<n) = <-irreflexive n<n

  data Tri (m n : ℕ) : Set where

    forward :
      (m < n) × ¬ (m ≡ n) × ¬ (n < m) →
      -------------------------------
                  Tri m n

    fixed :
      ¬ (m < n) × (m ≡ n) × ¬ (n < m) →
      -------------------------------
                Tri m n

    backward :
      ¬ (m < n) × ¬ (m ≡ n) × (n < m) →
      -------------------------------
                Tri m n

  <-trichotomy : ∀ {m n : ℕ} → Tri m n
  <-trichotomy = {!!}

  ⊎-dual-x : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
  ⊎-dual-x = {!!}

  -- Do we have this?
  -- x-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
  -- if not can we give a relation weaker than isomorphism that relates
  -- the two sides?


