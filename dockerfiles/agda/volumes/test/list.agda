module test.list where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-distribˡ-+; +-suc; *-suc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    ((x ∷ xs) ++ ys) ++ zs
  ≡⟨⟩
    (x ∷ (xs ++ ys)) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_ ) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) =
  begin
    x ∷ xs ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse (x ∷ xs ++ ys)
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ∎

reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-compose-each : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
  → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-each f g [] = refl
map-compose-each f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong ((g ∘ f) x ∷_) (map-compose-each f g xs) ⟩
    (g ∘ f) x ∷ (map g ∘ map f) xs
  ≡⟨⟩
    g (f x) ∷ map g (map f xs)
  ≡⟨⟩
    map g (f x ∷ map f xs)
  ≡⟨⟩
    map g (map f (x ∷ xs))
  ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
  ∎      

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C)
  → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality λ xs → (map-compose-each f g xs)

map-++-distribute : ∀ {A B : Set} (xs ys : List A) (f : A → B)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute [] ys f = refl
map-++-distribute (x ∷ xs) ys f =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-++-distribute xs ys f) ⟩
    f x ∷ map f xs ++ map f ys
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node left x right) = node (map-Tree f g left) (g x) (map-Tree f g right)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    x ⊗ foldr _⊗_ e (xs ++ ys)
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
  ∎

foldr-∷ : ∀ {A : Set} (xs : List A)
  → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) =
  begin
    foldr _∷_ [] (x ∷ xs)
  ≡⟨⟩
    x ∷ foldr _∷_ [] xs
  ≡⟨ cong (x ∷_) (foldr-∷ xs) ⟩
    x ∷ xs
  ∎

map-is-foldr-each : ∀ {A B : Set} (f : A → B) (xs : List A)
  → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
map-is-foldr-each f [] = refl
map-is-foldr-each f (x ∷ xs) =
  begin
    map f (x ∷ xs)
  ≡⟨⟩
    f x ∷ map f xs
  ≡⟨ cong (f x ∷_) (map-is-foldr-each f xs) ⟩
    f x ∷ (foldr (λ x xs → f x ∷ xs) [] xs)
  ≡⟨⟩
    (λ x xs → f x ∷ xs) x (foldr (λ x xs → f x ∷ xs) [] xs)
  ≡⟨⟩
    foldr (λ x xs → f x ∷ xs) [] (x ∷ xs)
  ∎

map-is-foldr : ∀ {A B : Set} (f : A → B)
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality λ xs → map-is-foldr-each f xs

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree l→c c→n→c→c (leaf x) = l→c x
fold-Tree l→c c→n→c→c (node left x right) = c→n→c→c (fold-Tree l→c c→n→c→c left) x (fold-Tree l→c c→n→c→c right)

map-is-fold-Tree-each : ∀ {A B C D : Set} (f : A → C) (g : B → D) (tr : Tree A B)
  → map-Tree f g tr ≡ fold-Tree (λ x → leaf (f x)) (λ left n right → node left (g n) right) tr
map-is-fold-Tree-each f g (leaf x) = refl
map-is-fold-Tree-each f g (node l n r) =
  begin
    map-Tree f g (node l n r)
  ≡⟨⟩
    node (map-Tree f g l) (g n) (map-Tree f g r)
  ≡⟨ cong (λ x → node x (g n) (map-Tree f g r)) (map-is-fold-Tree-each f g l) ⟩
    node
      (fold-Tree (λ x → leaf (f x)) (λ left n → node left (g n)) l)
      (g n)
      (map-Tree f g r)
  ≡⟨ cong (λ r₁ → node (fold-Tree (λ x → leaf (f x)) (λ left n → node left (g n)) l) (g n) r₁) (map-is-fold-Tree-each f g r) ⟩
    node
      (fold-Tree (λ x → leaf (f x)) (λ left n → node left (g n)) l)
      (g n)
      (fold-Tree (λ x → leaf (f x)) (λ left n → node left (g n)) r)
  ≡⟨⟩
    fold-Tree (λ x → leaf (f x)) (λ left n right → node left (g n) right) (node l n r)
  ∎

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

sum : List ℕ → ℕ
sum = foldr _+_ 0

sum-downFrom : (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom 1 = refl
sum-downFrom (suc (suc n)) =
  begin
    sum (downFrom (suc (suc n))) * 2
  ≡⟨⟩
    sum ((suc n) ∷ downFrom (suc n)) * 2
  ≡⟨⟩
    ((suc n) + sum (downFrom (suc n))) * 2
  ≡⟨ *-distribʳ-+ 2 (suc n) (sum (downFrom (suc n))) ⟩
    suc n * 2 + sum (downFrom (suc n)) * 2
  ≡⟨ cong (suc n * 2 +_) (sum-downFrom (suc n)) ⟩
    suc n * 2 + (suc n) * ((suc n) ∸ 1)
  ≡⟨⟩
    suc n * 2 + (suc n) * n
  ≡⟨ sym (*-distribˡ-+ (suc n) 2 n) ⟩
    suc n * (2 + n)
  ≡⟨⟩
    suc (suc (n + n * suc (suc n)))
  ≡⟨ cong suc (sym (+-suc n (n * suc (suc n)))) ⟩
    suc (n + suc (n * suc (suc n)))
  ≡⟨ cong (λ x → suc (n + suc x)) (*-suc n (suc n)) ⟩
    suc (n + suc (n + n * suc n))
  ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ foldr _⊗_ y xs
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ y []        =  y
foldl _⊗_ y (x ∷ xs)  =  foldl _⊗_ (y ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e ⊗-monoid [] y = sym (identityʳ ⊗-monoid y)
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldl _⊗_ y (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) ⟩
    (y ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ assoc ⊗-monoid y x (foldl _⊗_ e xs) ⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e ⊗-monoid xs x)) ⟩
    y ⊗ foldl _⊗_ x xs
  ≡⟨ cong (λ x₁ → y ⊗ foldl _⊗_ x₁ xs) (sym (identityˡ ⊗-monoid x)) ⟩
    y ⊗ foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    y ⊗ foldl _⊗_ e (x ∷ xs)
  ∎

foldr-monoid-foldl-each : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl-each _⊗_ e monoid-⊗ [] = refl
foldr-monoid-foldl-each _⊗_ e monoid-⊗ (x ∷ xs) =
  begin
    x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl-each _⊗_ e monoid-⊗ xs) ⟩
    x ⊗ foldl _⊗_ e xs
  ≡⟨ sym (foldl-monoid _⊗_ e monoid-⊗ xs x) ⟩
    foldl _⊗_ x xs
  ≡⟨ cong (λ x₁ → foldl _⊗_ x₁ xs) (sym (identityˡ monoid-⊗ x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ∎

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to   = to xs ys
    ; from = from xs ys
    }
    where
      to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
        All P (xs ++ ys) → (All P xs × All P ys)
      to [] ys Pys = ⟨ [] , Pys ⟩
      to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
      ... | ⟨ Pxs , Pys ⟩ = ⟨ (Px ∷ Pxs) , Pys ⟩

      from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
        (All P xs × All P ys) → All P (xs ++ ys)
      from [] ys ⟨ _ , Pys ⟩ = Pys
      from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to   = to xs ys
    ; from = from xs ys
    }
    where
      to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
        Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
      to [] ys Pys = inj₂ Pys
      to (x ∷ xs) ys (here Px) = inj₁ (here Px)
      to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
      ... | inj₁ Pxs = inj₁ (there Pxs)
      ... | inj₂ Pys = inj₂ Pys

      from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
        (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
      from [] ys (inj₂ Pys) = Pys
      from (x ∷ xs) ys (inj₁ (here Px)) = here Px
      from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
      from (x ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to   = to xs
    ; from = from xs
    }
    where
      to : ∀ {A : Set} {P : A → Set} (xs : List A) →
        (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
      to [] _ = []
      to (x ∷ xs) ¬Px∷xs = (λ Px → ¬Px∷xs (here Px)) ∷ (to xs (λ Pxs → ¬Px∷xs (there Pxs)))
      
      from : ∀ {A : Set} {P : A → Set} (xs : List A) →
        All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
      from [] p = λ ()
      from (x ∷ xs) (¬Px ∷ ¬Pxs) (here Px) = ¬Px Px
      from (x ∷ xs) (¬Px ∷ ¬Pxs) (there Pxs-any) = from xs ¬Pxs Pxs-any

-- All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) →
--   All P xs ≃ (∀ (x : A) → x ∈ xs → P x)
-- All-∀ [] =
--   record
--     { to      = λ{ [] x () }
--     ; from    = λ x → []
--     ; from∘to = λ{ [] → refl}
--     ; to∘from = λ y → {!  !}
--     }
-- All-∀ (x ∷ xs) =
--   record
--     { to      = to x xs
--     ; from    = {!   !}
--     ; from∘to = {!   !}
--     ; to∘from = {!   !}
--     }
--     where
--       to x xs = ?

