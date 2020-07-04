module plfa-exercises.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa-exercises.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa-exercises.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A   →
      B   →
    -----
    A × B

proj₁ : ∀ {A B : Set} →
  A × B               →
  -----
    A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} →
  A × B               →
  -----
    B
proj₂ ⟨ x , y ⟩ = y

record _×'_ (A B : Set) : Set where
  field
    proj₁' : A
    proj₂' : B
open _×'_

-- when <_,_> appears in a term on the right-hand-side of an equation we refer to it as
-- a constructor, and when it appears in a pattern on the left-hand side of an equation
-- we refer to it as a desctructor. We may also refer to proj1 and proj2 as destructors,
-- since they play a similar role.

-- Constructors introduces a datatype, destructors eliminate the datatypes.

-- An introduction rule describes under what conditions we say the connective holds
-- - how to define the connective. An elimination rule describes what we may conclude
-- when the connective holds - how to use the connective.
-- Read: Proposition as Types, Philip Wadler, 2015

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_
-- This m ≤ n × n ≤ m parses as (m ≤ n) × (n ≤ m)

-- Being commutative up to isomorphism!
×-comm : ∀ {A B : Set} → A × B ≃ B × A
_≃_.to      ×-comm = λ{⟨ x , y ⟩ → ⟨ y , x ⟩}
_≃_.from    ×-comm = λ{⟨ y , x ⟩ → ⟨ x , y ⟩}
_≃_.from∘to ×-comm = λ{ ⟨ x , y ⟩ → refl }
_≃_.to∘from ×-comm = λ{ ⟨ y , x ⟩ → refl  }

-- Being associative up to isomorphism!
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
_≃_.to      ×-assoc = λ{⟨ ⟨ A , B ⟩ , C ⟩ → ⟨ A , ⟨ B , C ⟩ ⟩}
_≃_.from    ×-assoc = λ{⟨ A , ⟨ B , C ⟩ ⟩ → ⟨ ⟨ A , B ⟩ , C ⟩}
_≃_.from∘to ×-assoc = λ{⟨ ⟨ A , B ⟩ , C ⟩ → refl} 
_≃_.to∘from ×-assoc = λ{⟨ A , ⟨ B , C ⟩ ⟩ → refl}

module exercise1 where
  open _⇔_

  -- ⇔ defines a pair of function which can be used in the × type.
  ⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) × (B → A)
  _≃_.to ⇔≃× = λ A⇔B → ⟨ to A⇔B , from A⇔B ⟩ 
  _≃_.from ⇔≃× = λ{ ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A } }
  _≃_.from∘to ⇔≃× = λ A⇔B → refl
  _≃_.to∘from ⇔≃× = λ{ ⟨ A→B , B→A ⟩ → refl }

data ⊤ : Set where

  tt :
   ---
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

-- We refer to ⊤ as the unit tupe. And indeed, type ⊤ has exactly one member, tt.

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
_≃_.to      ⊤-identityˡ = λ { ⟨ tt , A ⟩ → A }
_≃_.from    ⊤-identityˡ = λ A → ⟨ tt , A ⟩
_≃_.from∘to ⊤-identityˡ = λ { ⟨ tt , A ⟩ -> refl }
_≃_.to∘from ⊤-identityˡ = λ A -> refl

⊤-identityʳ : ∀ {A : Set} -> (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    ((⊤ × A))
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

-- Introducing disjunction
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A   →
    -----
    A ⊎ B

  inj₂ :
      B   →
    -----
    A ⊎ B

-- Eliminating disjunction
case-⊎ : ∀ {A B C : Set} →
  (A → C)                →
  (B → C)                →
   A ⊎ B                 →
  -------
     C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ x) = g x

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B)
       → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infixr 1 _⊎_
-- Thus A × C ⊎ B × C parses as (A × C) ⊎ (B × C)

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
_≃_.to      ⊎-comm = λ { (inj₁ A) → inj₂ A ; (inj₂ B) → inj₁ B }
_≃_.from    ⊎-comm = λ { (inj₁ B) → inj₂ B ; (inj₂ A) → inj₁ A }
_≃_.from∘to ⊎-comm = λ { (inj₁ A) → refl ; (inj₂ B) → refl }
_≃_.to∘from ⊎-comm = λ { (inj₁ B) → refl ; (inj₂ A) → refl }

-- Is there a better way to express the from-to and to-from equational reasoning?
⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc = record
  { to   = ⊎-assoc-to
  ; from = ⊎-assoc-from
  ; from∘to = λ { (inj₁ A) → refl
                ; (inj₂ (inj₁ B)) → refl
                ; (inj₂ (inj₂ C)) → refl
                }
  ; to∘from = λ { (inj₁ (inj₁ A)) → refl
                ; (inj₁ (inj₂ B)) → refl
                ; (inj₂ C) → refl
                }
  }
  where
   ⊎-assoc-to : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
   ⊎-assoc-to (inj₁ x)        = inj₁ (inj₁ x)
   ⊎-assoc-to (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
   ⊎-assoc-to (inj₂ (inj₂ x)) = inj₂ x

   ⊎-assoc-from : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
   ⊎-assoc-from (inj₁ (inj₁ x)) = inj₁ x
   ⊎-assoc-from (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
   ⊎-assoc-from (inj₂ x) = inj₂ (inj₂ x)

data ⊥ : Set where
  -- no clauses

-- Dual to ⊤, for ⊥ there is no introduction rule but an elimination. Since false never holds,
-- knowing that it holds tells us we are in a paradoxicial situation. Given that ⊥ holds,
-- we might conclude anything!

⊥-elim : ∀ {A : Set} →
   ⊥                 →
  ---
   A
⊥-elim () -- absurd pattern

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → A ≃ ⊥ ⊎ A
_≃_.to      ⊥-identityˡ          = inj₂
_≃_.from    ⊥-identityˡ (inj₂ x) = x
_≃_.from∘to ⊥-identityˡ x        = refl
_≃_.to∘from ⊥-identityˡ (inj₂ x) = refl

⊥-identityʳ : ∀ {A : Set} → A ≃ A ⊎ ⊥
⊥-identityʳ {A} =
  ≃-begin
    A
  ≃⟨ ⊥-identityˡ ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊎-comm ⟩
    (A ⊎ ⊥)
  ≃-∎

→-elim : ∀ {A B : Set} →
  (A → B)              →
     A                 →
  -------
     B
→-elim L M = L M

-- Defining a function , with a names definition or a lambda abstraction, is referred to
-- as introducing a function, while applying a function to as eliminating the function/

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

-- Implication binds less tightly than any other operator. Thus, A ⊎ B → B ⊎ A parses as
-- (A ⊎ B) → (B ⊎ A)

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
_≃_.to      currying f ⟨ x , y ⟩ = f x y
_≃_.from    currying g   x   y   = g ⟨ x , y ⟩
_≃_.from∘to currying f = refl
_≃_.to∘from currying g = extensionality λ { ⟨ x , y ⟩ → refl } 
  
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
_≃_.to      →-distrib-⊎ f = ⟨ (f ∘ inj₁) , f ∘ inj₂ ⟩
_≃_.from    →-distrib-⊎ ⟨ A→C , B→C ⟩ (inj₁ A) = A→C A
_≃_.from    →-distrib-⊎ ⟨ A→C , B→C ⟩ (inj₂ B) = B→C B
_≃_.from∘to →-distrib-⊎ f = extensionality λ { (inj₁ A) → refl ; (inj₂ B) → refl } 
_≃_.to∘from →-distrib-⊎ ⟨ A→C , B→C ⟩ = refl

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
_≃_.to      ×-distrib-⊎ ⟨ inj₁ a , c ⟩ = inj₁ ⟨ a , c ⟩
_≃_.to      ×-distrib-⊎ ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩
_≃_.from    ×-distrib-⊎ (inj₁ ⟨ a , c ⟩) = ⟨ inj₁ a , c ⟩
_≃_.from    ×-distrib-⊎ (inj₂ ⟨ b , c ⟩) = ⟨ inj₂ b , c ⟩
_≃_.from∘to ×-distrib-⊎ ⟨ inj₁ a , x ⟩ = refl
_≃_.from∘to ×-distrib-⊎ ⟨ inj₂ b , x ⟩ = refl
_≃_.to∘from ×-distrib-⊎ (inj₁ ⟨ a , c ⟩) = refl
_≃_.to∘from ×-distrib-⊎ (inj₂ ⟨ b , c ⟩) = refl

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
_≲_.to      ⊎-distrib-× (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
_≲_.to      ⊎-distrib-× (inj₂ c) = ⟨ inj₂ c , inj₂ c ⟩
_≲_.from    ⊎-distrib-× ⟨ inj₁ a , inj₁ b ⟩ = inj₁ ⟨ a , b ⟩
_≲_.from    ⊎-distrib-× ⟨ inj₁ a , inj₂ c ⟩ = inj₂ c
_≲_.from    ⊎-distrib-× ⟨ inj₂ c , inj₁ x ⟩ = inj₂ c
_≲_.from    ⊎-distrib-× ⟨ inj₂ c , inj₂ x ⟩ = inj₂ c
_≲_.from∘to ⊎-distrib-× (inj₁ ⟨ a , b ⟩) = refl
_≲_.from∘to ⊎-distrib-× (inj₂ c) = refl

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

