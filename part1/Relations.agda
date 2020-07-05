module plfa-exercises.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Indexed datatype to represent less-than-equal relation.
data _≤_ : ℕ → ℕ → Set where

        -- curly braces represent implicit arguments.
        -- these values are inferred by Agda's type
        -- checker.
  z≤n : ∀ {n : ℕ}   →
        ----------
         zero ≤ n

  s≤s : ∀ {m n : ℕ}   →
            m ≤ n     →
        -------------
        suc m ≤ suc n
        
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

-- No left or right as it makes no sense to parse 1 ≤ 2 ≤ 3 as either (1 ≤ 2) ≤ 3 or
-- 1 ≤ (2 ≤ 3)
infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} →
  suc m ≤ suc n       →
  -------------
      m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} →
  m ≤ zero          →
  --------
  m ≡ zero
inv-z≤n z≤n = refl

-- Reflexive : For all `n`, the relation `R n n` holds.
-- Transitive : For all `m n p`, if `R m n` and `R n p` hold, then `R m p` holds.
-- Anti-symmetric: For all `m n`, if both `R m n` and `R n m` hold, then `m ≡ n` holds.
-- Total: For all `m n` either `R m n` or `R n m` holds.

-- Preorder. Any relation that is reflexive and transitive.
-- Partial order. Any preorder that is also anti-symmetric.
-- Total order. Any partial order that is also total.

-- Example of a preorder relation:
-- {(a,a), (a,b), (b,a), (b,b)} on {a,b}
-- It is not anti-symmetric because R a b and R b a holds and a ≢ b

-- Example of a partial order:
-- {(a,a), (b,b), (a,b), (c,c)} on {a,b,c}
-- As the c is an exception from the total rule,
-- c is not in relation neither a nor b

≤-refl : ∀ {n : ℕ} →
  -----
  n ≤ n

≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} →
  m ≤ n                 →
  n ≤ p                 →
  -----
  m ≤ p
≤-trans z≤n      _        = z≤n
≤-trans (s≤s mn) (s≤s np) = s≤s (≤-trans mn np)

≤-antisym : ∀ {m n : ℕ} →
  m ≤ n                 →
  n ≤ m                 →
  -----
  m ≡ n
≤-antisym z≤n z≤n           = refl
≤-antisym (s≤s mn) (s≤s nm) = cong suc (≤-antisym mn nm)

-- datatype with parameters. Parameters must always be the same in the
-- type given for the constructors. In constrast of indexed datatypes where indexes can vary.
-- The advantage of parameterised data type are that they help Agda's termination
-- checker a lot.
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n    →
    ---------
    Total m n

  backward :
      n ≤ m   →
    ---------
    Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n       = forward z≤n
≤-total (suc m) zero    = backward z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward  x = forward  (s≤s x)
... | backward x = backward (s≤s x)

+-monoʳ-≤ : ∀ (n p q : ℕ) →
      p ≤ q               →
  -------------
  n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) →
      m ≤ n               →
  -------------
  m + p ≤ n + p
+-monoˡ-≤ m n p m≤n
  rewrite
    +-comm m p |
    +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) →
      m ≤ n                →
      p ≤ q                →
  -------------
  m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- strech
-- *-mono-≤ : ∀ (m n p q : ℕ) →
--      m ≤ n                 →
--      p ≤ q                 →
--  -------------
--  m * p ≤ n * q

infix 4 _<_

-- Indexed datatype
data _<_ : ℕ → ℕ → Set where

  z<s :   ∀ {n : ℕ}  →
        ------------
        zero < suc n

  s<s : ∀ {m n : ℕ}   →
            m < n     →
        -------------
        suc m < suc n

<-trans : ∀ {m n p : ℕ} →
  m < n                 →
  n < p                 →
  -----
  m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- TODO: Rename
data Triconomy (m n : ℕ) : Set where

  tri-left :
        m < n     →
    -------------
    Triconomy m n

  tri-right :
        n < m     →
    -------------
    Triconomy m n

  tri-refl :
        m ≡ n     →
    -------------
    Triconomy m n

<-triconomy : ∀ (m n : ℕ) -> Triconomy m n
<-triconomy zero    zero    = tri-refl refl
<-triconomy zero    (suc n) = tri-left z<s
<-triconomy (suc m) zero    = tri-right z<s
<-triconomy (suc m) (suc n) with <-triconomy m n
... | tri-left  x = tri-left  (s<s x)
... | tri-right x = tri-right (s<s x)
... | tri-refl  x = tri-refl  (cong suc x)

-- m + p < n + p
-- n + p < n + q

+-mono-r-< : ∀ (n p q : ℕ) →
      p < q                →
  -------------
  n + p < n + q
+-mono-r-< zero    p q p<q = p<q
+-mono-r-< (suc n) p q p<q = s<s (+-mono-r-< n p q p<q)

+-mono-l-< : ∀ (m n p : ℕ) →
      m < n                →
  -------------
  m + p < n + p
+-mono-l-< m n p m<n
  rewrite
    +-comm m p |
    +-comm n p
    = +-mono-r-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-mono-l-< m n p m<n) (+-mono-r-< n p q p<q)

≤-iff-<-l : ∀ (m n : ℕ) →
  suc m ≤ n             →
  ---------
    m < n
≤-iff-<-l zero    (suc n) sm≤n       = z<s
≤-iff-<-l (suc m) (suc n) (s≤s sm≤n) = s<s (≤-iff-<-l m n sm≤n)

≤-iff-<-r : ∀ (m n : ℕ) →
    m < n               →
  ---------
  suc m ≤ n
≤-iff-<-r zero    (suc n) z<s       = s≤s z≤n
≤-iff-<-r (suc m) (suc n) (s<s m<n) = s≤s (≤-iff-<-r m n m<n)

-- mutual definitions
data even : ℕ → Set
data odd  : ℕ → Set

-- with overloaded constructors.
data even where
  zero :
    ---------
    even zero

  suc :
    ∀ {n : ℕ}    →
    odd n        →
    ------------
    even (suc n)

data odd where
  suc :
    ∀ {n : ℕ}   →
    even n      →
    -----------
    odd (suc n)

e+e≡e : ∀ {m n : ℕ} →
  even m            →
  even n            →
  ------------
  even (m + n)

o+e≡o : ∀ {m n : ℕ} →
  odd m             →
  even n            →
  -----------
  odd (m + n)

e+e≡e zero     en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

-- strech
-- o+o≡e

-- strech
-- Bin-predicated

