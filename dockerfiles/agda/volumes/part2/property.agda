module part2.property where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N vm = V¬—→ vm M—→N

infix 4 Cannonical_⦂_

data Cannonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
    → Cannonical (ƛ x ⇒ N) ⦂ (A ⇒ B)
  
  C-zero :
      Cannonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Cannonical V ⦂ `ℕ
    → Cannonical `suc V ⦂ `ℕ

Cannonical-≃ : ∀ {A : Type} {V : Term} →
  Cannonical V ⦂ A ≃ (∅ ⊢ V ⦂ A) × (Value V)
Cannonical-≃ {A} {V} =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
    where
    to : ∀ {A : Type} {V : Term} → Cannonical V ⦂ A → (∅ ⊢ V ⦂ A) × (Value V)
    to (C-ƛ x) = ⟨ (⊢ƛ x) , V-ƛ ⟩
    to C-zero = ⟨ ⊢zero , V-zero ⟩
    to (C-suc cva) with to cva
    ... | ⟨ ∅⊢V₁⦂`ℕ , ValueV₁ ⟩ = ⟨ (⊢suc ∅⊢V₁⦂`ℕ) , (V-suc ValueV₁) ⟩

    from : ∀ {A : Type} {V : Term} → (∅ ⊢ V ⦂ A) × (Value V) → Cannonical V ⦂ A
    from ⟨ ⊢ƛ ∅x⊢N , V-ƛ ⟩ = C-ƛ ∅x⊢N
    from ⟨ ⊢zero , V-zero ⟩ = C-zero
    from ⟨ ⊢suc ∅⊢V₁⦂`ℕ , V-suc ValueV₁ ⟩ = C-suc (from ⟨ ∅⊢V₁⦂`ℕ , ValueV₁ ⟩)
 
    from∘to : ∀ {A : Type} {V : Term} (C : Cannonical V ⦂ A) → from (to C) ≡ C
    from∘to (C-ƛ x) = refl
    from∘to C-zero = refl
    from∘to (C-suc C) = cong C-suc (from∘to C)

    to∘from : ∀ {A : Type} {V : Term} (p : (∅ ⊢ V ⦂ A) × (Value V)) → to (from p) ≡ p
    to∘from ⟨ ⊢ƛ fst , V-ƛ ⟩ = refl
    to∘from ⟨ ⊢zero , V-zero ⟩ = refl
    to∘from ⟨ ⊢suc ∅⊢M , V-suc VM ⟩ = cong (λ (⟨ f , s ⟩) → ⟨ ⊢suc f , V-suc s ⟩ ) (to∘from ⟨ ∅⊢M , VM ⟩)

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
    → Progress M

  done :
      Value M
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
  → Progress M
progress (⊢ƛ _)                             = done V-ƛ
progress (L · M) with progress L
... | step L—→L′                            = step (ξ-·₁ L—→L′)
... | done V-ƛ with progress M
...    | step M—→M′                         = step (ξ-·₂ V-ƛ M—→M′)
...    | done vm                            = step (β-ƛ vm)
progress ⊢zero                              = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M—→M′                            = step (ξ-suc M—→M′)
... | done VM                               = done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            = step (ξ-case L—→L′)
... | done V-zero                           = step β-zero
... | done (V-suc VL)                       = step (β-suc VL)
progress (⊢μ ctxt)                          = step β-μ

Progress-≃ : ∀ {M N : Term} →
  Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ =
  record
    { to      = λ{ (step {N₁} M—→N₁) → inj₂ ⟨ N₁ , M—→N₁ ⟩
                 ; (done VM) → inj₁ VM }
    ; from    = λ{ (inj₁ VM) → done VM
                 ; (inj₂ ⟨ N₁ , M—→N₁ ⟩) → step M—→N₁ }
    ; from∘to = λ{ (step x) → refl
                 ; (done x) → refl}
    ; to∘from = λ{ (inj₁ x) → refl
                 ; (inj₂ ⟨ N₁ , M—→N₁ ⟩) → refl}
    }

progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ M ∅⊢M = _≃_.to Progress-≃ (progress ∅⊢M)

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? {A} {M} ∅⊢M with progress′ M ∅⊢M
... | inj₁ VM = yes VM
... | inj₂ ⟨ N , M—→N ⟩ = no (—→¬V M—→N)

ext : ∀ {Γ Δ}
  → (∀ {x A}     → Γ ∋ x ⦂ A         → Δ ∋ x ⦂ A)
    ----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z = Z
ext ρ (S x≢y Γ∋x⦂A) = S x≢y (ρ Γ∋x⦂A)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ---------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` Γ∋x) = ⊢` (ρ Γ∋x)
rename ρ (⊢ƛ Γx⊢N) = ⊢ƛ (rename (ext ρ) Γx⊢N)
rename ρ (Γ⊢L · Γ⊢M) = rename ρ Γ⊢L · rename ρ Γ⊢M
rename ρ ⊢zero = ⊢zero
rename ρ (⊢suc Γ⊢M) = ⊢suc (rename ρ Γ⊢M)
rename ρ (⊢case Γ⊢L Γ⊢M Γ⊢N) = ⊢case (rename ρ Γ⊢L) (rename ρ Γ⊢M) (rename (ext ρ) Γ⊢N)
rename ρ (⊢μ Γx⊢M) = ⊢μ (rename (ext ρ) Γx⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ---------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {x A} → ∅ ∋ x ⦂ A → Γ ∋ x ⦂ A
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    ------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} Γxx⊢M = rename ρ Γxx⊢M
  where
  ρ : ∀ {z C} → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z = Z
  ρ (S x≢x Z) = ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ Γ∋z)) = S z≢x Γ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    ------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y Γxy⊢M = rename ρ Γxy⊢M
  where
  ρ : ∀ {z C} → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z = S x≢y Z
  ρ (S z≢x Z) = Z
  ρ (S z≢x (S z≢y Γ∋z)) = S z≢y (S z≢x Γ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ∅⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _ = weaken ∅⊢V
... | no x≢y = ⊥-elim (x≢y refl)
subst {x = y} ∅⊢V (⊢` {x = x} (S x≢y Γ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no _ = ⊢` Γ∋x
subst {x = y} ∅⊢V (⊢ƛ {x = x} Γyy⊢N) with x ≟ y
... | yes refl = ⊢ƛ (drop Γyy⊢N)
... | no x≢y = ⊢ƛ (subst ∅⊢V (swap x≢y Γyy⊢N))
subst ∅⊢V (Γx⊢L · Γx⊢M) = subst ∅⊢V Γx⊢L · subst ∅⊢V Γx⊢M
subst ∅⊢V ⊢zero = ⊢zero
subst ∅⊢V (⊢suc Γx⊢M) = ⊢suc (subst ∅⊢V Γx⊢M)
subst {x = y} ∅⊢V (⊢case {x = x} Γx⊢L Γx⊢M Γx⊢N) with x ≟ y
... | yes refl = ⊢case (subst ∅⊢V Γx⊢L) (subst ∅⊢V Γx⊢M) (drop Γx⊢N)
... | no x≢y = ⊢case (subst ∅⊢V Γx⊢L) (subst ∅⊢V Γx⊢M) (subst ∅⊢V (swap x≢y Γx⊢N))
subst {x = y} ∅⊢V (⊢μ {x = x} Γx⊢N) with x ≟ y
... | yes refl = ⊢μ (drop Γx⊢N)
... | no x≢y = ⊢μ (subst ∅⊢V (swap x≢y Γx⊢N))

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ---------
  → ∅ ⊢ N ⦂ A
preserve (∅⊢L · ∅⊢L′) (ξ-·₁ L—→L′) = preserve ∅⊢L L—→L′ · ∅⊢L′
preserve (∅⊢L · ∅⊢M) (ξ-·₂ ValueL M—→M′) = ∅⊢L · preserve ∅⊢M M—→M′
preserve (⊢ƛ ∅x⊢N · ∅⊢M) (β-ƛ ValueV) = subst ∅⊢M ∅x⊢N
preserve (⊢suc ∅⊢M) (ξ-suc M—→N) = ⊢suc (preserve ∅⊢M M—→N)
preserve (⊢case ∅⊢L ∅⊢M ∅⊢N) (ξ-case L—→L′) = ⊢case (preserve ∅⊢L L—→L′) ∅⊢M ∅⊢N
preserve (⊢case ∅⊢L ∅⊢M ∅⊢N) β-zero = ∅⊢M
preserve (⊢case (⊢suc ∅⊢L) ∅⊢M ∅⊢N) (β-suc ValueV) = subst ∅⊢L ∅⊢N
preserve (⊢μ ∅⊢M) β-μ = subst (⊢μ ∅⊢M) ∅⊢M

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N
  
data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero) ∅⊢L = steps (L ∎) out-of-gas
eval {L} (gas (suc n)) ∅⊢L with progress ∅⊢L
... | done ValueL = steps (L ∎) (done ValueL)
... | step {M} L—→M with eval (gas n) (preserve ∅⊢L L—→M)
...   | steps M—↠N (done ValueN) = steps (L —→⟨ L—→M ⟩ M—↠N) (done ValueN)
...   | steps M—↠N out-of-gas = steps (L —→⟨ L—→M ⟩ M—↠N) out-of-gas

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` Z))

-- subject-expansion : ∀ {M N A}
--   → ∅ ⊢ N ⦂ A
--   → M —→ N
--     ----------
--   → ∅ ⊢ M ⦂ A
-- -- subject-expansion (⊢L′ · ⊢M) (ξ-·₁ L—→L′) = subject-expansion ⊢L′ L—→L′ · ⊢M
-- subject-expansion (⊢N) (ξ-·₁ L—→L′) = {!   !}
-- subject-expansion (⊢L · ⊢M′) (ξ-·₂ VV M—→M′) = ⊢L · (subject-expansion ⊢M′ M—→M′)
-- subject-expansion (⊢N) (β-ƛ VV) = {!  !}
-- subject-expansion (⊢N) (ξ-suc M—→N) = {!   !}
-- subject-expansion (⊢N) (ξ-case M—→N) = {!   !}
-- subject-expansion (⊢N) β-zero = {!   !}
-- subject-expansion (⊢N) (β-suc x) = {!   !}
-- subject-expansion (⊢N) β-μ = {!   !}

Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M

unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
  → ¬ (Stuck M)
unstuck ⊢M ⟨ NormalM , ¬VM ⟩ with progress ⊢M
... | step M—→N = NormalM M—→N
... | done VM = ¬VM VM

preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves ⊢M (_ ∎) = ⊢M
preserves ⊢M (_ —→⟨ M—→N′ ⟩ N′—↠N) = preserves (preserve ⊢M M—→N′) N′—↠N

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs ⊢M M—↠N = unstuck (preserves ⊢M M—↠N)

cong₄ : ∀ {A B C D E : Set} {f : A → B → C → D → E}
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ refl refl refl refl = refl

det : ∀ {M M′ M̃}
  → (M —→ M′)
  → (M —→ M̃)
    --------
  → M′ ≡ M̃
det (ξ-·₁ L—→L′) (ξ-·₁ L—→L̃) rewrite det L—→L′ L—→L̃ = refl
det (ξ-·₁ L—→L′) (ξ-·₂ VL M—→M̃) = ⊥-elim (V¬—→ VL L—→L′)  -- L—→L′はLがreduce可能なことを表しているのに対してVLはLがValue(reduceできない)であることを表すため矛盾
det (ξ-·₂ VL M—→M′) (ξ-·₁ L—→L′) = ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₂ VL M—→M′) (ξ-·₂ _ M—→M̃) rewrite det M—→M′ M—→M̃ = refl
det (ξ-·₂ VƛN M—→M′) (β-ƛ VM) = ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ VM) (ξ-·₂ VƛN M—→M̃) = ⊥-elim (V¬—→ VM M—→M̃)
det (β-ƛ VV) (β-ƛ _) = refl
det (ξ-suc M—→M′) (ξ-suc M—→M̃) rewrite det M—→M′ M—→M̃ = refl
det (ξ-case L—→L′) (ξ-case L—→L̃) rewrite det L—→L′ L—→L̃ = refl
det (ξ-case (ξ-suc V—→L′)) (β-suc VV) = ⊥-elim (V¬—→ VV V—→L′)
det β-zero β-zero = refl
det (β-suc VV) (ξ-case (ξ-suc V—→M′)) = ⊥-elim (V¬—→ VV V—→M′)
det (β-suc VV) (β-suc _) = refl
det β-μ β-μ = refl

