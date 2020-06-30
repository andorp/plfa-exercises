module plfa.part1.Equality where

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} →
  x ≡ y                     →
  -----
  y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} →
  x ≡ y                         →
  y ≡ z                         →
  -----
  x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A -> B) {x y : A} →
    x ≡ y                                   →
  ---------
  f x ≡ f y
cong f refl = refl

cong-app : ∀ {A B : Set} {f g : A -> B} →
          f ≡ g                         →
  ---------------------
  ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A -> Set) →
    x ≡ y                                    →
  ----------
  P x -> P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} →
    x ≡ y              →
    -----
    x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} →
    x ≡ y                   →
    -----
    x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} →
    x ≡ y                      →
    y ≡ z                      →
    -----
    x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) →
    -----
    x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans-chain : ∀ {A : Set} {x y z : A} →
  x ≡ y                               →
  y ≡ z                               →
  -----
  x ≡ z
trans-chain {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero  + n = n
suc m + n = suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) -> m + zero ≡ m
  +-suc : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) →
  m + n ≡ n + m

+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎

+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m
  ∎

-- strech
-- ≤-Reasoning

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero :
    ---------
    even zero

  even-suc : ∀ {n : ℕ} →
       odd n           →
    ------------
    even (suc n)

data odd where

  odd-suc : ∀ {n : ℕ} →
       even n         →
    -----------
    odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) →
  even (m + n)          →
  ------------
  even (n + m)
even-comm m n ev rewrite +-comm n m = ev

+-comm-rw : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm-rw zero    n
  rewrite +-identity n = refl
+-comm-rw (suc m) n
  rewrite
    +-suc n m |
    +-comm-rw m n = refl

-- to be continued: Leibniz equality