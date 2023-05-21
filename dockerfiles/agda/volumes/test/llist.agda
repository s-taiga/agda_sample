module test.llist where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)

data LList (A : Set) : ℕ → Set where
  []  : LList A zero
  _∷_ : ∀ {n : ℕ} → A → LList A n → LList A (suc n)

infixr 5 _∷_

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} {n m : ℕ} → LList A n → LList A m → LList A (n + m)
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

head : ∀ {A : Set} {n : ℕ} → LList A (suc n) → A
head (x ∷ xs) = x

