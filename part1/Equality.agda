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

-- Leibniz equality
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} →
  x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} →
  x ≐ y                           →
  y ≐ z                           →
  -----
  x ≐ z
trans-≐ xy yz P Px = yz P (xy P Px)

sym-≐ : ∀ {A : Set} {x y : A} →
  x ≐ y                       →
  -----
  y ≐ x
sym-≐ {A} {x} {y} xy P = Qy
  where
    Q : A -> Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = xy Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A} →
  x ≡ y                             →
  -----
  x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} →
  x ≐ y                             →
  -----
  x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl' : x ≡' x

sym' : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} →
  x ≡' y                                  →
  ------
  y ≡' x
sym' refl' = refl'

_≐'_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐'_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_₀_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
  (B -> C) -> (A -> B) -> A -> C
(g ₀ f) x = g (f x)

