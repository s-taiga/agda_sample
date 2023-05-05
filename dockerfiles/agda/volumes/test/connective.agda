module test.connective where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import test.isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open test.isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , x₁ ⟩ = refl

infixr 2 _×_

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩ = 1
×-count ⟨ true  , bb ⟩ = 2
×-count ⟨ true  , cc ⟩ = 3
×-count ⟨ false , aa ⟩ = 4
×-count ⟨ false , bb ⟩ = 5
×-count ⟨ false , cc ⟩ = 6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from    = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to      = λ{ record { to = A→B ; from = B→A } → ⟨ A→B , B→A ⟩ }
    ; from    = λ{ ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A } }
    ; from∘to = λ{ record { to = A→B ; from = B→A } → refl }
    ; to∘from = λ{ ⟨ A→B , B→A ⟩ → refl }
    }

data ⊤ : Set where
  tt : 
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityᴸ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityᴸ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl}
    }

⊤-identityᴿ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityᴿ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityᴸ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where
  inj₁ :
      A
      -----
    → A ⊎ B
  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    ------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = λ{ (inj₁ x) → inj₂ x
                 ; (inj₂ y) → inj₁ y }
    ; from    = λ{ (inj₁ y) → inj₂ y
                 ; (inj₂ x) → inj₁ x }
    ; from∘to = λ{ (inj₁ x) → refl
                 ; (inj₂ y) → refl }
    ; to∘from = λ{ (inj₁ y) → refl
                 ; (inj₂ x) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to      = λ{ (inj₁ (inj₁ x)) → inj₁ x
                 ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y)
                 ; (inj₂ z) → inj₂ (inj₂ z) }
    ; from    = λ{ (inj₁ x) → (inj₁ (inj₁ x))
                 ; (inj₂ (inj₁ y)) → (inj₁ (inj₂ y))
                 ; (inj₂ (inj₂ z)) → inj₂ z }
    ; from∘to = λ{ (inj₁ (inj₁ x)) → refl
                 ; (inj₁ (inj₂ y)) → refl
                 ; (inj₂ z) → refl }
    ; to∘from = λ{ (inj₁ x) → refl
                 ; (inj₂ (inj₁ y)) → refl
                 ; (inj₂ (inj₂ z)) → refl }
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

⊥-identityᴸ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityᴸ =
  record
    { to      = λ{ (inj₂ x) → x }
    ; from    = λ{ x → inj₂ x }
    ; from∘to = λ{ (inj₂ x) → refl }
    ; to∘from = λ{ x → refl }
    }

⊥-identityᴿ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityᴿ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityᴸ ⟩
    A
  ≃-∎

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      = λ{ f → λ{ ⟨ x , y ⟩ → f x y } }
    ; from    = λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ } } }
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl } }
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ h → ⟨ h ∘ inj₁ , h ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ f , g ⟩ → case-⊎ f g }
    ; from∘to = λ{ h → extensionality λ{ (inj₁ x) → refl
                                       ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ f , g ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ ((A → B) × (A → C))
→-distrib-× =
  record
    { to      = λ{ h → ⟨ proj₁ ∘ h , proj₂ ∘ h ⟩ }
    ; from    = λ{ ⟨ f , g ⟩ → λ{ x → ⟨ f x , g x ⟩ } }
    ; from∘to = λ{ h → extensionality λ{ x → η-× ((h x)) } }
    ; to∘from = λ{ ⟨ f , g ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ A × C ⊎ B × C
×-distrib-⊎ = 
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩
                 ; ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩ }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩ }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩ }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
                 ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
                 ; ⟨ inj₂ z , yz ⟩ → inj₂ z }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z) → refl }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ z , w ⟩) = ⟨ inj₂ z , inj₂ w ⟩
