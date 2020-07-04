module plfa-exercises.part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} →
    (∀ (x : A) → f x ≡ g x)                    →
    -----------------------
            f ≡ g

_+'_ : ℕ → ℕ → ℕ
m +' zero  = m
m +' suc n = suc (m +' n)

same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n
  rewrite
    +-comm m n = helper m n
  where
    helper : ∀ (m n : ℕ) → m +' n ≡ n + m
    helper m zero    = refl
    helper m (suc n) = cong suc (helper m n)

same : _+'_ ≡ _+_
same = extensionality \m → extensionality \n → same-app m n

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x} →
    (∀ (x : A) → f x ≡ g x)                                            →
    -----------------------
             f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set} →
  -----
  A ≃ A
to      ≃-refl = \x -> x
from    ≃-refl = \y -> y
from∘to ≃-refl = \x -> refl
to∘from ≃-refl = \y -> refl

≃-sym : ∀ {A B : Set} →
  A ≃ B               →
  -----
  B ≃ A
to      (≃-sym A≃B) = from A≃B
from    (≃-sym A≃B) = to A≃B
from∘to (≃-sym A≃B) = to∘from A≃B
to∘from (≃-sym A≃B) = from∘to A≃B

≃-trans : ∀ {A B C : Set} →
  A ≃ B                   →
  B ≃ C                   →
  -----
  A ≃ C
to (≃-trans A≃B B≃C) = to B≃C ∘ to A≃B
from (≃-trans A≃B B≃C) = from A≃B ∘ from B≃C
from∘to (≃-trans A≃B B≃C) = \x ->
  begin
    from A≃B (from B≃C (to B≃C (to A≃B x)))
  ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
    from A≃B (to A≃B x)
  ≡⟨ from∘to A≃B x ⟩
    x
  ∎
to∘from (≃-trans A≃B B≃C) = \y ->
  begin
    to B≃C (to A≃B (from A≃B (from B≃C y)))
  ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
    to B≃C (from B≃C y)
  ≡⟨ to∘from B≃C y ⟩
    y
  ∎

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} →
    A ≃ B                  →
    -----
    A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} →
   A ≃ B                           →
   B ≃ C                           →
   -----
   A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) →
    -----
    A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
to      ≲-refl = \x -> x
from    ≲-refl = \x -> x
from∘to ≲-refl = \x -> refl

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
to (≲-trans A≲B B≲C) = to B≲C ∘ to A≲B
from (≲-trans A≲B B≲C) = from A≲B ∘ from B≲C
from∘to (≲-trans A≲B B≲C) = \x ->
  begin
    from A≲B (from B≲C (to B≲C (to A≲B x)))
  ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
    from A≲B (to A≲B x)
  ≡⟨ from∘to A≲B x ⟩
    x
  ∎

≲-antisym : ∀ {A B : Set} →
  (A≲B : A ≲ B)           →
  (B≲A : B ≲ A)           →
  (to A≲B ≡ from B≲A)     →
  (from A≲B ≡ to B≲A)     →
  -------------------
  A ≃ B
to (≲-antisym A≲B B≲A to≡from from≡to) = to A≲B
from (≲-antisym A≲B B≲A to≡from from≡to) = from A≲B
from∘to (≲-antisym A≲B B≲A to≡from from≡to) = from∘to A≲B
to∘from (≲-antisym A≲B B≲A to≡from from≡to) = \y ->
  begin
    to A≲B (from A≲B y)
  ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
    to A≲B (to B≲A y)
  ≡⟨ cong-app to≡from (to B≲A y) ⟩
    from B≲A (to B≲A y)
  ≡⟨ from∘to B≲A y ⟩
    y
  ∎

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set} →
    A ≲ B                  →
    -----
    A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} →
    A ≲ B                          →
    B ≲ C                          →
    -----
    A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) →
    -----
    A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

≃-implies-≲ : ∀ {A B : Set} →
  A ≃ B                     →
  -----
  A ≲ B
to (≃-implies-≲ A≃B) = to A≃B
from (≃-implies-≲ A≃B) = from A≃B
from∘to (≃-implies-≲ A≃B) = from∘to A≃B

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set} →
  -----
  A ⇔ A
to   ⇔-refl = \x -> x
from ⇔-refl = \x -> x

⇔-sym : ∀ {A B : Set} →
  A ⇔ B               →
  -----
  B ⇔ A
to (⇔-sym A⇔B) = from A⇔B
from (⇔-sym A⇔B) = to A⇔B

⇔-trans : ∀ {A B C : Set} →
  A ⇔ B                   →
  B ⇔ C                   →
  -----
  A ⇔ C
to (⇔-trans A⇔B B⇔C) = to B⇔C ∘ to A⇔B
from (⇔-trans A⇔B B⇔C) = from A⇔B ∘ from B⇔C
