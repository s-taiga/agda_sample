module test.relation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ}
        → zero ≤ n
    s≤s : ∀ {m n : ℕ}
        → m ≤ n
        → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
    → suc m ≤ suc n
    → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
    → m ≤ zero
    → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
    → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
      -----
    → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
    → m ≤ n
    → n ≤ m
      -----
    → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
    forward :
        m ≤ n
        -----
        → Total m n

    flipped :
        n ≤ m
        -----
        → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

+-monoᴿ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
      -----
    → n + p ≤ n + q
+-monoᴿ-≤ zero p q p≤q = p≤q
+-monoᴿ-≤ (suc n) p q p≤q = s≤s (+-monoᴿ-≤ n p q p≤q)

+-monoᴸ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
      -----
    → m + p ≤ n + p
+-monoᴸ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoᴿ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
      -----
    → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoᴸ-≤ m n p m≤n) (+-monoᴿ-≤ n p q p≤q)

*-monoᴿ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
      -----
    → n * p ≤ n * q
*-monoᴿ-≤ zero p q p≤q = z≤n
*-monoᴿ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoᴿ-≤ n p q p≤q)

*-monoᴸ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
      -----
    → m * p ≤ n * p
*-monoᴸ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoᴿ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
      -----
    → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoᴸ-≤ m n p m≤n) (*-monoᴿ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n : ℕ}
        ------------
        → zero < suc n

    s<s : ∀ {m n : ℕ}
        → m < n
          ------------
        → suc m < suc n

<-trans : ∀ {m n p : ℕ}
    → m < n
    → n < p
      -----
    → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

infix 4 _>_

data _>_ : ℕ → ℕ → Set where
    s>z : ∀ {n : ℕ}
        ------------
        → suc n > zero

    s>s : ∀ {m n : ℕ}
        → m > n
          ------------
        → suc m > suc n

data Trichotomy (m n : ℕ) : Set where
    <-forward :
        m < n
        -----
        → Trichotomy m n
    <-flipped :
        m > n
        -----
        → Trichotomy m n
    <-iso :
        m ≡ n
        -----
        → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = <-iso (≤-antisym z≤n z≤n)
<-trichotomy zero (suc n) = <-forward z<s
<-trichotomy (suc m) zero = <-flipped s>z
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | <-forward m<n = <-forward (s<s m<n)
...                             | <-flipped m>n = <-flipped (s>s m>n)
...                             | <-iso m≡n = <-iso (cong suc m≡n)

+-monoᴿ-< : ∀ (n p q : ℕ)
    → p < q
      -----
    → n + p < n + q
+-monoᴿ-< zero p q p<q = p<q
+-monoᴿ-< (suc n) p q p<q = s<s (+-monoᴿ-< n p q p<q)

+-monoᴸ-< : ∀ (m n p : ℕ)
    → m < n
      -----
    → m + p < n + p
+-monoᴸ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoᴿ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
    → m < n
    → p < q
      -----
    → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoᴸ-< m n p m<n) (+-monoᴿ-< n p q p<q)

≤-iffᴿ-< : ∀ (m n : ℕ)
    → suc m ≤ n
      ---------
    → m < n
≤-iffᴿ-< zero .(suc _) (s≤s sm≤n) = z<s
≤-iffᴿ-< (suc m) (suc n₁) (s≤s sm≤n) = s<s (≤-iffᴿ-< m n₁ sm≤n)

≤-iffᴸ-< : ∀ (m n : ℕ)
    → m < n
      -----
    → suc m ≤ n
≤-iffᴸ-< zero (suc n) m<n = s≤s z≤n
≤-iffᴸ-< (suc m) (suc n) (s<s m<n) = s≤s (≤-iffᴸ-< m n m<n)

<-trans-revisited : ∀ (m n p : ℕ)
    → m < n
    → n < p
      -----
    → m < p
<-trans-revisited m n p m<n n<p = ≤-iffᴿ-< m p (
    ≤-trans (≤-iffᴸ-< m n m<n) (
        ≤-trans (+-monoᴸ-≤ 0 1 n z≤n) (≤-iffᴸ-< n p n<p)))

data even : ℕ → Set
data odd : ℕ → Set

data even where
    zero :
        ---------
        even zero
    suc : ∀ {n : ℕ}
        → odd n
          ------------
        → even (suc n)

data odd where
    suc : ∀ {n : ℕ}
        → even n
          -----------
        → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
    → even m
    → even n
      ------------
    → even (m + n)

o+e≡o : ∀ {m n : ℕ}
    → odd m
    → even n
      -----------
    → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ}
    → odd m
    → odd n
      ------------
    → even (m + n)

e+o≡o : ∀ {m n : ℕ}
    → even m
    → odd n
      ------------
    → odd (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)

e+o≡o zero on = on
e+o≡o (suc x) on = suc (o+o≡e x on)
