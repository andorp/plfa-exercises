module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_;_≡⟨⟩_;_≡⟨_⟩_;_∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Exercise: Give another example of a pair of operators that have an identity and are associative,
-- commutative, and distribute over one another.
-- Answer: Any ring setisfies these properties, such as n-by-n matrices with real numbers,
-- module n integers

-- Execrise: Give an example of an operator that has an identity and is associative
-- but is not commutative.
-- Answer: Hamilton product of the Quaternions.

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

{-

------
P zero

   P m
---------
P (suc m)

-}

{-
P m = (m + n) + p ≡ m + (n + p)

Proof by induction:

-------------------------------
(zero + n) + p ≡ zero + (n + p)

   (m + n) + p ≡ m + (n + p)
--------------------------------
(suc m + n) + p≡ suc m + (n + p)

-}

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- A relation is said to be a congruence for a given function if it is preserved
-- by applying that function. If e is evidence that x ≡ y, then cong f e is evidence
-- that f x ≡ f y, for any function f.

--    suc ((m + n) + p)               (m + n) + p ≡ m + (n + p)
--  ≡⟨ cong suc (+-assoc m n p) ⟩  ---------------------------------
--    suc (m + (n + p))            (suc m + n) + p ≡ suc m + (n + p)

{-
P m:
m + zero ≡ m

------------------
zero + zero ≡ zero

    m + zero ≡ m
--------------------
suc m + zero ≡ suc m

-}


+-identityʳ : forall (m : ℕ) -> m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩ -- by definition of (+)
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩ -- be definition
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc m + n)
  ∎

{-
-------------------
zero + n ≡ n + zero

    m + n ≡ n + m
---------------------
suc m + n ≡ n + suc m
-}

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n -- I started with this and the conclusion I had to check between ≡⟨ ? ⟩
              -- asked Adga, what is my goal. Looked into the already defined
              -- lemmas, if anything applies to the left hand side of the ≡, found one.
              -- Applied the lemma and inserted a new goal, checked if there is anything
              -- that leads closer to the desired source in the lemmas.
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m
  ∎

-- Sketch of the proof: First do the high level proof by hand, and after
-- validate it. Telling which are the applied steps.
-- (m + n) + (p + q) -- associvity m n (p + q)                      leads to
-- m + (n + (p + q)) -- reverse associvity n p q in the second part leads to
-- m + ((n + p) + q) -- reverse associtity m (n + p) q              leads to
-- (m + (n + p)) + q

+-rearrange : ∀ (m n p q : ℕ) -> (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero    n p                        = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero                          = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n                       = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero    rewrite +-identity' m            = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

-- recommended
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc' m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm' m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc' n m p ⟩
    n + (m + p)
  ∎

*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero    = refl
*-zeroʳ (suc m) = *-zeroʳ m

*-identityʳ : ∀ (m : ℕ) → m * 1 ≡ m
*-identityʳ zero                          = refl
*-identityʳ (suc m) rewrite *-identityʳ m = refl

lemma-*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
lemma-*-suc zero    n = refl
lemma-*-suc (suc m) n =
  begin
    suc (n + m * suc n)
  ≡⟨ cong suc (cong (n +_) (lemma-*-suc m n)) ⟩
    suc (n + (m + (m * n)))
  ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
    suc ((n + m) + (m * n))
  ≡⟨ cong suc (cong (_+ (m * n)) (+-comm n m)) ⟩
    suc ((m + n) + (m * n))
  ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
    suc (m + (n + m * n))
  ∎

-- recommended
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero =
  begin
    (m + n) * zero
  ≡⟨ *-zeroʳ (m + n) ⟩
    zero
  ≡⟨ +-identityʳ zero ⟩
    zero + zero
  ≡⟨ cong (_+ zero) (sym (*-zeroʳ m)) ⟩
    m * zero + zero
  ≡⟨ cong ((m * zero) +_) (sym (*-zeroʳ n)) ⟩
    m * zero + n * zero
  ∎
*-distrib-+ m n (suc p) =
  begin
    (m + n) * suc p
  ≡⟨ lemma-*-suc (m + n) p ⟩
    (m + n) + (m + n) * p
  ≡⟨ cong ((m + n) +_) (*-distrib-+ m n p) ⟩
    (m + n) + (m * p + n * p)
  ≡⟨ cong (_+ (m * p + n * p)) (+-comm m n) ⟩
    (n + m) + (m * p + n * p)
  ≡⟨ +-rearrange n m (m * p) (n * p) ⟩
    n + (m + (m * p)) + (n * p)
  ≡⟨ cong (_+ (n * p)) (+-comm n (m + (m * p))) ⟩
    ((m + m * p) + n) + (n * p)
  ≡⟨ +-assoc (m + m * p) n (n * p) ⟩
    (m + m * p) + (n + n * p)
  ≡⟨ cong (_+ (n + n * p)) (sym (lemma-*-suc m p)) ⟩
    (m * suc p) + (n + n * p)
  ≡⟨ cong ((m * suc p) +_) (sym (lemma-*-suc n p)) ⟩
    m * suc p + n * suc p
  ∎

-- recommended
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero    n p = refl
*-assoc (suc m) n p =
  begin
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p)+_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ∎

-- practice
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero    = *-zeroʳ m
*-comm m (suc n) =
  begin
    m * suc n
  ≡⟨ lemma-*-suc m n ⟩
    m + (m * n)
  ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + (n * m)
  ∎

-- practice
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 n = {!!}

-- practice
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc n m p = {!!}

-- +*^ strech
-- m ^ (n + p) ≡ (m ^ n) * (m ^ p) -- (^-distribˡ-+-*)
-- (m * n) ^ p ≡ (m ^ p) * (n ^ p) -- (^-distribʳ-*)
-- (m ^ n) ^ p ≡ m ^ (n * p)       -- (^-*-assoc)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

to : ℕ → Bin
to zero    = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩    = zero
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

-- strech
-- bin-from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
-- bin-from-inc b = {!!}

-- strech
-- bin-to-from : ∀ (b : Bin) → to (from b) ≡ b
-- bin-to-from b = {!!}

-- strech
-- bin-from-to : ∀ (n : ℕ) → from (to n) ≡ n
-- bin-from-to n = {!!}
