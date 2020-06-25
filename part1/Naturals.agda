module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

{-

--------
zero : ℕ

  m : ℕ
---------
suc m : ℕ

-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-
Inference rules:

Hypotheses
----------
Conclusion

-}

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩ -- inductive case
    (suc (suc zero + (suc (suc (suc zero)))))
  ≡⟨⟩ -- inductive case
    (suc (suc (zero + (suc (suc (suc zero))))))
  ≡⟨⟩ -- base case
    (suc (suc (suc (suc (suc zero)))))
  ≡⟨⟩ -- is longhand for
   5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc n * m = m + (n * m)

_ =
  begin
    2 * 3
  ≡⟨⟩ -- inductive case
    3 + (1 * 3)
  ≡⟨⟩ -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩ -- base case
    3 + (3 + 0)
  ≡⟨⟩ -- base case on +
    3 + 3
  ≡⟨⟩ -- simplify
    6
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    81
  ∎

-- ∸ = \.-
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩ -- inductive case
    2 ∸ 1
  ≡⟨⟩ -- inductive case
    1 ∸ 0
  ≡⟨⟩ -- base case
    1
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_

{-

First inference rule, base case.
   n : ℕ      Hypothesis
------------
zero + n = n  Conclusion

Second inference rule, inductive case.
    m + n = p      Hypothesis
-----------------
suc m + n = suc p  Conclusion

-}

{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

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

_ : 0 ≡ from (⟨⟩ O)
_ = refl

_ : 1 ≡ from (⟨⟩ I)
_ = refl

_ : 2 ≡ from (⟨⟩ I O)
_ = refl

_ : 3 ≡ from (⟨⟩ I I)
_ = refl

_ : 4 ≡ from (⟨⟩ I O O)
_ = refl

_ : to 0 ≡ ⟨⟩
_ = refl

_ : (to 1) ≡ (⟨⟩ I)
_ = refl

_ : to 2 ≡ (⟨⟩ I O)
_ = refl

_ : to 3 ≡ (⟨⟩ I I)
_ = refl

_ : to 4 ≡ (⟨⟩ I O O)
_ = refl
