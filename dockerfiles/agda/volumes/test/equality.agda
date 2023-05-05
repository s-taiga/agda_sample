module test.equality where

data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
    → x ≡ y
      -----
    → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl y≡z = y≡z

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    -----
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -----
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
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
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ}
        → zero ≤ n
    s≤s : ∀ {m n : ℕ}
        → m ≤ n
        → suc m ≤ suc n

infix 4 _≤_

module ≤-Reasoning where
  infix  1 begin-≤_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡-≤⟨⟩_ _≡-≤⟨_⟩_
  infix  3 _∎-≤

  begin-≤_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  begin-≤ x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≡-≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≡ y
      -----
    → x ≤ y
  zero ≡-≤⟨⟩ refl = z≤n
  (suc x) ≡-≤⟨⟩ refl = s≤s (x ≡-≤⟨⟩ refl)

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  zero ≤⟨ x≤y ⟩ y≤z = z≤n
  suc x ≤⟨ s≤s x≤y ⟩ s≤s y≤z = s≤s (x ≤⟨ x≤y ⟩ y≤z)

  _≡-≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≡ y
    → y ≤ z
      -----
    → x ≤ z
  x ≡-≤⟨ x≡y ⟩ y≤z = x ≤⟨ (x ≡-≤⟨⟩ x≡y) ⟩ y≤z

  _∎-≤ : ∀ (x : ℕ)
      -----
    → x ≤ x
  zero ∎-≤ = z≤n
  suc x ∎-≤ = s≤s (x ∎-≤)

open ≤-Reasoning

+-monoᴿ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -----
  → n + p ≤ n + q
+-monoᴿ-≤ zero p q p≤q = p≤q
+-monoᴿ-≤ (suc n) p q p≤q = 
  begin-≤
    suc n + p
  ≤⟨ s≤s (+-monoᴿ-≤ n p q p≤q) ⟩
    suc n + q
  ∎-≤

+-monoᴸ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -----
  → m + p ≤ n + p
+-monoᴸ-≤ m n p m≤n =
  begin-≤
    m + p
  ≡-≤⟨ +-comm m p ⟩
    p + m
  ≤⟨ +-monoᴿ-≤ p m n m≤n ⟩
    p + n
  ≡-≤⟨ +-comm p n ⟩
    n + p
  ∎-≤

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -----
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  begin-≤
    m + p
  ≤⟨ +-monoᴸ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoᴿ-≤ n p q p≤q ⟩
    n + q
  ∎-≤

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
  → even (m + n)
  → even (n + m)
even-comm m n ev rewrite +-comm n m = ev

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
-- ≡-implies-≐ x≡y P Px rewrite x≡y = Px
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qy : Q y
    Qy = x≐y Q refl

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl' : x ≡' x

sym' : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡' y
    ------
  → y ≡' x
sym' refl' = refl'

