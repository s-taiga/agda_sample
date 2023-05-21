module part2.lambda where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_ : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_ : Term → Term → Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_ : Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n") ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · (` "n" · ` "s") · (` "n" · ` "s" · ` "z")

var? : (t : Term) → Bool
var? (` _)  =  true
var? _      =  false

ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ′_⇒_ (` x) N = ƛ x ⇒ N

case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ m
          [zero⇒ `zero
          |suc m ⇒ plus · n · (* · m · n) ]
  where
  * = ` "*"
  m = ` "m"
  n = ` "n"

data Value : Term → Set where
  V-ƛ : ∀ {x N}
      ----------------
    → Value (ƛ x ⇒ N)
  
  V-zero :
      -----------
      Value `zero
  
  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no _          = ` x
(ƛ x ⇒ M) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ M
... | no _          = ƛ x ⇒ M [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
`zero [ y := V ]    = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no _          = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ M) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ M
... | no _          = μ x ⇒ M [ y := V ]

_[_:=_]′ : Term → (t : Term) → {_ : T (var? t)} → Term → Term
L [ ` x := M ]′ = L [ x := M ]

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M
  
  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      -----------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]
  
  ξ-suc : ∀ {M M′}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′
  
  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      ---------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      --------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M
  
  β-suc : ∀ {x V M N}
    → Value V
      --------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ------
    → M —↠ M
  
  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    -------
  → M —↠ N
begin M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

trans : ∀ {L M N}
  → L —↠ M
  → M —↠ N
    -------
  → L —↠ N
trans (_ ∎) L—↠N = L—↠N
trans (L —→⟨ L—→L′ ⟩ L′—↠M) M—↠N = L —→⟨ L—→L′ ⟩ (trans L′—↠M M—↠N)

—↠≲—↠′ : ∀ (L M : Term) →
  (L —↠ M) ≲ (L —↠′ M)
—↠≲—↠′ L M =
  record
    { to      = to L M
    ; from    = from L M
    ; from∘to = from∘to L M
    }
    where
    to : ∀ (L M : Term) → (L —↠ M) → (L —↠′ M)
    to L .L (.L ∎) = refl′
    to L M (_—→⟨_⟩_ .L {L′} {.M} L—→L′ L′—↠M) = trans′ (step′ L—→L′) (to L′ M L′—↠M)

    from : ∀ (L M : Term) → (L —↠′ M) → (L —↠ M)
    from L M (step′ L—→M) = L —→⟨ L—→M ⟩ M ∎
    from L .L refl′ = L ∎
    from L M (trans′ {.L} {L′} {.M} L—↠′L′ L′—↠′M) = trans (from L L′ L—↠′L′) (from L′ M L′—↠′M)

    from∘to : ∀ (L M : Term) (L—↠M : L —↠ M) → from L M (to L M L—↠M) ≡ L—↠M
    from∘to L .L (.L ∎) = refl
    from∘to L M (_—→⟨_⟩_ .L {L′} {.M} L—→L′ L′—↠M) = cong (λ lm → L —→⟨ L—→L′ ⟩ lm) (from∘to L′ M L′—↠M)

postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · (`suc `zero)
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `suc `zero
  ∎
_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
      case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · (`suc `zero) · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · (`suc `zero) · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc ((case (`suc `zero) [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]))
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc (`suc (plus · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
    · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc (`suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
     · two))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc (`suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]))
  —→⟨ ξ-suc (ξ-suc (β-zero)) ⟩
    `suc `suc `suc `suc `zero
  ∎ 

_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
    twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
    · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒
    twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z"))
    · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z"))
    · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
    · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc (`suc `zero))
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · (`suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc (`suc (`suc `zero)))
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc `suc `suc `suc `zero
  ∎

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5 _,_⦂_

data Context : Set  where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

Context-≃ : Context ≃ List (Id × Type)
Context-≃ =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
    where
    to : Context → List (Id × Type)
    to ∅ = []
    to (Γ , x ⦂ t) = ⟨ x , t ⟩ ∷ to Γ

    from : List (Id × Type) → Context
    from [] = ∅
    from (⟨ x , t ⟩ ∷ xs) = from xs , x ⦂ t

    from∘to : ∀ (Γ : Context) → from (to Γ) ≡ Γ
    from∘to ∅ = refl
    from∘to (Γ , x ⦂ t) = cong (_, x ⦂ t) (from∘to Γ)

    to∘from : ∀ (xs : List (Id × Type)) → to (from xs) ≡ xs
    to∘from [] = refl
    to∘from (⟨ x , t ⟩ ∷ xs) = cong (⟨ x , t ⟩ ∷_) (to∘from xs)

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      -----------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A

_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ ()) (S (λ ()) Z)

-- S′ : ∀ {Γ x y A B}
--   → {x≢y : False (x ≟ y)}
--   → Γ ∋ x ⦂ A
--   → Γ , y ⦂ B ∋ x ⦂ A
-- S′ {x≢y = x≢y} judge = S (toWitnessFalse {!  !}) judge

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  --Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A
  
  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      --------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      ----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (
  ⊢case
    (⊢` (S′ Z))
    (⊢` Z)
    (⊢suc (⊢` (S′ (S′ (S′ Z))) · ⊢` Z · ⊢` (S′ Z))))))

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢plusᶜ : ∀ {Γ A} → Γ ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (∋m · ∋s · (∋n · ∋s · ∋z)))))
  where
    ∋z = ⊢` Z
    ∋s = ⊢` (S′ Z)
    ∋n = ⊢` (S′ (S′ Z))
    ∋m = ⊢` (S′ (S′ (S′ Z)))

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero

∋-functional : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-functional Z Z = refl
∋-functional Z (S x≢ Γ∋x⦂B) = ⊥-elim (x≢ refl)
∋-functional (S x≢ Γ∋x⦂A) Z = ⊥-elim (x≢ refl)
∋-functional (S x Γ∋x⦂A) (S x₁ Γ∋x⦂B) = ∋-functional Γ∋x⦂A Γ∋x⦂B

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′)) = contradiction (∋-functional ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case ∋m ⊢zero (⊢plus · ∋n′ · (∋* · ∋m′ · ∋n′)))))
  where
  ∋m = ⊢` (S′ Z)
  ∋m′ = ⊢` Z
  ∋n′ = ⊢` (S′ Z)
  ∋* = ⊢` (S′ (S′ (S′ Z)))

