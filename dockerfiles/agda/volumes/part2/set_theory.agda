module part2.set_theory where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

infix 7 _∋_
infix 6 _U_
infix 5 _⊃_

data _∋_ (A : Set) (x : Set) : Set where
  _`∋_ : A → x → A ∋ x

data _⊃_ (A B : Set): Set₁ where
  `⊃ : ∀ {x : Set} → B ∋ x → A ∋ x → A ⊃ B

record _`=_ (A B : Set) : Set₁ where
  field
    A⊃B : A ⊃ B
    B⊃A : B ⊃ A
open _`=_

trans-⊃ : ∀ {A B C : Set}
  → A ⊃ B
  → B ⊃ C
    ------
  → A ⊃ C
trans-⊃ (`⊃ (B `∋ x) (A `∋ _)) (`⊃ (C `∋ _) (B′ `∋ _)) = `⊃ (C `∋ x) (A `∋ x)

data _U_ (A B : Set) : Set where
  inj₁ : ∀ {x} → A ∋ x → A U B
  inj₂ : ∀ {x} → B ∋ x → A U B

AUB⊃A : ∀ {A B : Set} → A U B ⊃ A
AUB⊃A = ?