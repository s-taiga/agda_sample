module test.negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; _>_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import test.isomorphism using (_≃_; extensionality)
open test.isomorphism.≃-Reasoning

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    --
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition x→y ¬y x = ¬y (x→y x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

decong : ∀ (m n : ℕ)
  → suc m ≡ suc n
  → m ≡ n
decong zero zero sm≡sn = refl
decong (suc m) (suc .m) refl = refl

_ : 1 ≢ 2
_ = λ 1≡2 → peano ((decong 0 1 1≡2))

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ{ x → ⊥-elim ((¬x x)) }

inv-s<s : ∀ {m n : ℕ}
  → suc m < suc n
  → m < n
inv-s<s (s≤s sm<sn) = sm<sn

<-irreflexive : ∀ (n : ℕ)
  → ¬ (n < n)
<-irreflexive zero = λ ()
<-irreflexive (suc n) = λ x → <-irreflexive n ((inv-s<s x))

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    ------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ h → ⟨ h ∘ inj₁ , h ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ f , g ⟩ → case-⊎ f g }
    ; from∘to = λ{ h → extensionality λ{ (inj₁ x) → refl
                                       ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ f , g ⟩ → refl }
    }

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {⊥}

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k ((inj₂ λ x → k (inj₁ x)))

apply : ∀ {A B : Set}
  → A
  → (A → B)
  → B
apply x f = f x

dm→em :
    (∀ {A B : Set} → (¬ (¬ A × ¬ B) → A ⊎ B))
  → (∀ {A : Set} → (A ⊎ ¬ A))
dm→em dm {A} = apply
  (dm {A} {¬ A})
  λ x → x λ x₁ → proj₂ x₁ (proj₁ x₁)

em→dne :
    (∀ {A : Set} → (A ⊎ ¬ A))
    ---------------------------
  → (∀ {A : Set} → (¬ ¬ A → A))
em→dne em {A} ¬¬x =
  -- すべてのAは真か偽なので場合分け
  case-⊎
    -- Aが真である場合はそのままAが導き出されるため成立
    (λ x → x)
    -- Aが偽である場合はAの二重否定と矛盾
    (λ ¬x → ⊥-elim (¬¬x ¬x)) (em {A})

dne→pl :
    (∀ {A : Set} → (¬ ¬ A → A))
    -------------------------------------
  → (∀ {A B : Set} → (((A → B) → A) → A))
dne→pl dne {A} xyx = apply
  (dne {A})
  (λ ¬¬x→x → ¬¬x→x λ ¬x → ¬x (xyx λ x → ⊥-elim (¬x x)))

-- わからん
pl→id :
    (∀ {A B : Set} → (((A → B) → A) → A))
    -------------------------------------
  → (∀ {A B : Set} → ((A → B) → ¬ A ⊎ B))
pl→id pl {A} {B} x→y = apply
  (pl {A} {⊥})
  (λ{ xyxx → inj₁ {!   !} })

id→dm :
    (∀ {A B : Set} → ((A → B) → ¬ A ⊎ B))
  → (∀ {A B : Set} → (¬ (¬ A × ¬ B) → A ⊎ B))
id→dm id_ {A} {B} ¬¬x×y = apply
  (id_ {¬ A} {B})
  λ id → {!   !}
