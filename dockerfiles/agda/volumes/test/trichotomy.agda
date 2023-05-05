module test.trichotomy where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import test.relation using (_<_; _>_; Trichotomy)
open import test.connective using (_×_; ⟨_,_⟩)
open import test.negation using (¬_)

trichotomy-< : ∀ {m n : ℕ}
  → m < n
  → ¬ m > n × ¬ m ≡ n 
trichotomy-< m<n = {!   !}