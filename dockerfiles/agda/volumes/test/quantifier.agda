module test.quantifier where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-assoc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    ---------------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to      = λ x→y×z → ⟨ proj₁ ∘ x→y×z , proj₂ ∘ x→y×z ⟩
    ; from    = λ x→y×x→z x → ⟨ (proj₁ x→y×x→z x) , (proj₂ x→y×x→z x) ⟩
    ; from∘to = λ x→y×z → refl
    ; to∘from = λ x→y×x→z → refl
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ x→y) = inj₁ ∘ x→y
⊎∀-implies-∀⊎ (inj₂ x→z) = inj₂ ∘ x→z

-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
--   (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- ∀⊎-implies-⊎∀ x→y⊎z = inj₁ λ x → x→y⊎z x
-- 最後の結果がB xとC xのどちらになるかわからない

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  extensionality-Tri : ∀ {B : Tri → Set} {f g : ∀(x : Tri) → B x}
    → (∀ (x : Tri) → f x ≡ g x)
      -----------------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set} →
  (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× =
  record
    { to      = λ t→bx → ⟨ (t→bx aa) , ⟨ (t→bx bb) , (t→bx cc) ⟩ ⟩
    ; from    = λ ba×bb×bc → λ{ aa → proj₁ ba×bb×bc
                              ; bb → proj₁ (proj₂ ba×bb×bc)
                              ; cc → proj₂ (proj₂ ba×bb×bc) }
    ; from∘to = λ t→bx → extensionality-Tri λ{ aa → refl
                                             ; bb → refl
                                             ; cc → refl }
    ; to∘from = λ ba×bb×bc → refl
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      = λ f → λ{ ⟨ x , y ⟩ → f x y}
    ; from    = λ g x y → g ⟨ x , y ⟩
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality λ{ ⟨ x , y ⟩ → refl}
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      = λ{ ⟨ x , inj₁ bx ⟩ → inj₁ ⟨ x , bx ⟩
                 ; ⟨ x , inj₂ cx ⟩ → inj₂ ⟨ x , cx ⟩}
    ; from    = λ{ (inj₁ ⟨ x , bx ⟩) → ⟨ x , (inj₁ bx) ⟩
                 ; (inj₂ ⟨ x , cx ⟩) → ⟨ x , (inj₂ cx) ⟩}
    ; from∘to = λ{ ⟨ x , inj₁ bx ⟩ → refl
                 ; ⟨ x , inj₂ cx ⟩ → refl}
    ; to∘from = λ{ (inj₁ ⟨ x , bx ⟩) → refl
                 ; (inj₂ ⟨ x , cx ⟩) → refl}
    }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , bx×cx ⟩ = ⟨ ⟨ x , (proj₁ bx×cx) ⟩ , ⟨ x , (proj₂ bx×cx) ⟩ ⟩

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
    { to      = λ{ ⟨ aa , bx ⟩ → inj₁ bx
                 ; ⟨ bb , bx ⟩ → inj₂ (inj₁ bx)
                 ; ⟨ cc , bx ⟩ → inj₂ (inj₂ bx)}
    ; from    = λ{ (inj₁ x) → ⟨ aa , x ⟩
                 ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩
                 ; (inj₂ (inj₂ y)) → ⟨ cc , y ⟩}
    ; from∘to = λ{ ⟨ aa , bx ⟩ → refl
                 ; ⟨ bb , bx ⟩ → refl
                 ; ⟨ cc , bx ⟩ → refl}
    ; to∘from = λ{ (inj₁ x) → refl
                 ; (inj₂ (inj₁ x)) → refl
                 ; (inj₂ (inj₂ y)) → refl}
    }

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

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc x) with odd-∃ x
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩
odd-∃ (odd-suc x) with even-∃ x
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc x , refl ⟩ = even-suc (∃-odd ⟨ x , refl ⟩)
∃-odd ⟨ x , refl ⟩ = odd-suc (∃-even ⟨ x , refl ⟩)

-- _lem : ∀ (x : ℕ) → 2 * x + 1 ≡ x + 1 * suc x
-- _lem x =
--   begin
--     2 * x + 1
--   ≡⟨⟩
--     x + (x + zero) + 1
--   ≡⟨ +-assoc x (x + zero) 1 ⟩
--     x + ((x + zero) + 1)
--   ≡⟨ cong (x +_) (+-comm (x + zero) 1) ⟩
--     x + suc (x + zero)
--   ∎

-- ∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
-- ∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n
-- -- termination checkがfailする
-- ∃-even′ ⟨ zero , refl ⟩ = even-zero
-- ∃-even′ ⟨ suc x , refl ⟩ = even-suc (∃-odd′ ⟨ x , _lem x ⟩)
-- ∃-odd′ ⟨ x , refl ⟩ rewrite +-comm (x + (x + zero)) 1 = odd-suc (∃-even′ ⟨ x , refl ⟩)

≡-implies-≤ : ∀ (x y : ℕ) → x ≡ y → x ≤ y
≡-implies-≤ zero zero x≡y = z≤n
≡-implies-≤ (suc x) (suc y) refl = s≤s (≡-implies-≤ x y refl)

∃-+-≤ : ∀ (y z : ℕ) → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤ y z ⟨ zero , y≡z ⟩ = ≡-implies-≤ y z y≡z
∃-+-≤ zero .(suc x + zero) ⟨ suc x , refl ⟩ = z≤n
∃-+-≤ (suc y) .(suc x + suc y) ⟨ suc x , refl ⟩ = s≤s {!   !}

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
  
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬y ⟩ x→y = ¬y (x→y x)

