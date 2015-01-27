-- this agda module depends on https://github.com/copumpkin/categories

-- inspired by https://gist.github.com/aristidb/1746133

open import Level
open import Categories.Category
open import Categories.Functor.Core
open import Categories.Agda
open import Categories.Product
--open import Categories.Bifunctor
open import Data.Nat
open import Data.Vec
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary

-- Decidable equality is only a technical precondition to help deal with irrelevant propositional equality
module Categories.OTCategory (C : Set) (decEq : Decidable {A = C} _≡_) where

-- Irrelevant in ⊥
⊥-elim′ : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim′ ()
 
getPrf : {A : Set} → .A → Dec A → A
getPrf a (yes p) = p
getPrf a (no ¬p) = ⊥-elim′ (¬p a)

-- Uniqueness of identity proofs
uip : {A : Set} {a b : A} (eq₁ : a ≡ b) (eq₂ : a ≡ b) → eq₁ ≡ eq₂
uip refl refl = refl

subst′ : {A : Set} {a b : A} (de : Decidable {A = A} _≡_) (P : A → Set) → .(a ≡ b) → P a → P b
subst′ {A} {a} {b} de P eq = subst P (getPrf eq (de a b))

subst′-eq : {A : Set} {a b : A} (de : Decidable {A = A} _≡_) (P : A → Set) → (eq : (a ≡ b)) → (v : P a)
          → subst′ de P eq v ≡ subst P eq v
subst′-eq {A} {a} {b} de P eq v with de a b
... | yes eq₂ = cong (λ eq₃ → subst P eq₃ v) (uip eq₂ eq)
... | no ¬p = ⊥-elim′ (¬p eq)

subst₂′ : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} (deA : Decidable {A = A} _≡_) (deB : Decidable {A = B} _≡_) (P : A → B → Set)
        → .(a₁ ≡ a₂) → .(b₁ ≡ b₂) → P a₁ b₁ → P a₂ b₂
subst₂′ {A} {B} {a₁} {a₂} {b₁} {b₂} decA decB P eqa eqb v = subst′ decA (λ a → P a b₂) eqa (subst′ decB (P a₁) eqb v)

data DocCtx : Set where
  Tombstone : DocCtx → DocCtx
  Char : DocCtx → DocCtx
  Empty : DocCtx

injTombstone : ∀ {c d} → Tombstone c ≡ Tombstone d → c ≡ d
injTombstone {c} {.c} refl = refl

injChar : ∀ {c d} → Char c ≡ Char d → c ≡ d
injChar {c} {.c} refl = refl

docCtxDecEq : Decidable {A = DocCtx} _≡_
docCtxDecEq (Tombstone x) (Tombstone y) with docCtxDecEq x y
... | yes eq = yes (cong Tombstone eq)
... | no prf = no (λ eq → prf (injTombstone eq))
docCtxDecEq (Tombstone x) (Char y) = no (λ ())
docCtxDecEq (Tombstone x) Empty = no (λ ())
docCtxDecEq (Char x) (Tombstone y) = no (λ ())
docCtxDecEq (Char x) (Char y) with docCtxDecEq x y
... | yes eq = yes (cong Char eq)
... | no prf = no (λ eq → prf (injChar eq))
docCtxDecEq (Char x) Empty = no (λ ())
docCtxDecEq Empty (Tombstone y) = no (λ ())
docCtxDecEq Empty (Char y) = no (λ ())
docCtxDecEq Empty Empty = yes refl

charLength : DocCtx → ℕ
charLength (Tombstone ctx) = charLength ctx
charLength (Char ctx) = ℕ.suc (charLength ctx)
charLength Empty = 0

docCtxLength : DocCtx → ℕ
docCtxLength (Tombstone ctx) = ℕ.suc (docCtxLength ctx)
docCtxLength (Char ctx) = ℕ.suc (docCtxLength ctx)
docCtxLength Empty = 0

data Op : DocCtx → DocCtx → Set where
  Noop : Op Empty Empty
  InsertChar : {a b : DocCtx} → (c : C) → Op a b → Op a (Char b)
  RetainChar : {a b : DocCtx} → Op a b → Op (Char a) (Char b)
  DeleteChar : {a b : DocCtx} → Op a b → Op (Char a) (Tombstone b)
  InsertTombstone : {a b : DocCtx} → Op a b → Op a (Tombstone b)
  RetainTombstone : {a b : DocCtx} → Op a b → Op (Tombstone a) (Tombstone b)

injRetainChar : ∀ {a b} → (x y : Op a b) → RetainChar x ≡ RetainChar y → x ≡ y
injRetainChar x .x refl = refl

injDeleteChar : ∀ {a b} → (x y : Op a b) → DeleteChar x ≡ DeleteChar y → x ≡ y
injDeleteChar x .x refl = refl

injRetainTombstone : ∀ {a b} → (x y : Op a b) → RetainTombstone x ≡ RetainTombstone y → x ≡ y
injRetainTombstone x .x refl = refl

injInsertTombstone : ∀ {a b} → (x y : Op a b) → InsertTombstone x ≡ InsertTombstone y → x ≡ y
injInsertTombstone x .x refl = refl

injInsertChar : ∀ {a b} → (x y : Op a b) → (c d : C) → InsertChar c x ≡ InsertChar d y → (c ≡ d) × (x ≡ y)
injInsertChar x .x c .c refl = refl , refl

opDecEq : ∀ {a b} → Decidable {A = Op a b} _≡_
opDecEq Noop Noop = yes refl
opDecEq (InsertChar c x) (InsertChar d y) with decEq c d | opDecEq x y
... | yes eq₁ | yes eq₂ = yes (cong₂ InsertChar eq₁ eq₂)
... | no prf | _ = no (λ eq → prf (proj₁ (injInsertChar x y c d eq)))
... | _ | no prf = no (λ eq → prf (proj₂ (injInsertChar x y c d eq)))
opDecEq (InsertChar c x) (RetainChar y) = no (λ ())
opDecEq (RetainChar x) (InsertChar c y) = no (λ ())
opDecEq (RetainChar x) (RetainChar y) with opDecEq x y
... | yes eq = yes (cong RetainChar eq)
... | no prf = no (λ eq → prf (injRetainChar x y eq))
opDecEq (DeleteChar x) (DeleteChar y) with opDecEq x y
... | yes eq = yes (cong DeleteChar eq)
... | no prf = no (λ eq → prf (injDeleteChar x y eq))
opDecEq (DeleteChar x) (InsertTombstone y) = no (λ ())
opDecEq (InsertTombstone x) (DeleteChar y) = no (λ ())
opDecEq (InsertTombstone x) (InsertTombstone y) with opDecEq x y
... | yes eq = yes (cong InsertTombstone eq)
... | no prf = no (λ eq → prf (injInsertTombstone x y eq))
opDecEq (InsertTombstone x) (RetainTombstone y) = no (λ ())
opDecEq (RetainTombstone x) (InsertTombstone y) = no (λ ())
opDecEq (RetainTombstone x) (RetainTombstone y) with opDecEq x y
... | yes eq = yes (cong RetainTombstone eq)
... | no prf = no (λ eq → prf (injRetainTombstone x y eq))

compose : ∀ {a b c} → Op a b → Op b c → Op a c
compose a (InsertTombstone b) = InsertTombstone (compose a b)
compose a (InsertChar c b) = InsertChar c (compose a b)
compose (InsertChar c a) (DeleteChar b) = InsertTombstone (compose a b)
compose (InsertChar c a) (RetainChar b) = InsertChar c (compose a b)
compose (InsertTombstone a) (RetainTombstone b) = InsertTombstone (compose a b)
compose (RetainChar a) (RetainChar b) = RetainChar (compose a b)
compose (RetainChar a) (DeleteChar b) = DeleteChar (compose a b)
compose (DeleteChar a) (RetainTombstone b) = DeleteChar (compose a b)
compose (RetainTombstone a) (RetainTombstone b) = RetainTombstone (compose a b)
compose Noop Noop = Noop

assoc : ∀ {a b c d} → (x : Op a b) → (y : Op b c) → (z : Op c d)
      → compose x (compose y z) ≡ compose (compose x y) z
assoc (InsertChar c x) (RetainChar y) (RetainChar z) = cong (InsertChar c) (assoc x y z)
assoc (InsertChar c x) (RetainChar y) (DeleteChar z) = cong InsertTombstone (assoc x y z)
assoc (InsertChar c x) (DeleteChar y) (RetainTombstone z) = cong InsertTombstone (assoc x y z)
assoc (InsertTombstone x) (RetainTombstone y) (RetainTombstone z) = cong InsertTombstone (assoc x y z)
assoc x (InsertChar c y) (RetainChar z) = cong (InsertChar c) (assoc x y z)
assoc x (InsertChar c y) (DeleteChar z) = cong InsertTombstone (assoc x y z)
assoc x (InsertTombstone y) (RetainTombstone z) = cong InsertTombstone (assoc x y z)
assoc x y (InsertChar c z) = cong (InsertChar c) (assoc x y z)
assoc x y (InsertTombstone z) = cong InsertTombstone (assoc x y z)
assoc (RetainChar x) (RetainChar y) (RetainChar z) = cong RetainChar (assoc x y z)
assoc (RetainTombstone x) (RetainTombstone y) (RetainTombstone z) = cong RetainTombstone (assoc x y z)
assoc (RetainChar x) (RetainChar y) (DeleteChar z) = cong DeleteChar (assoc x y z)
assoc (RetainChar x) (DeleteChar y) (RetainTombstone z) = cong DeleteChar (assoc x y z)
assoc (DeleteChar x) (RetainTombstone y) (RetainTombstone z) = cong DeleteChar (assoc x y z)
assoc Noop Noop Noop = refl

identity : ∀ {a} → Op a a
identity {a = Tombstone a} = RetainTombstone identity
identity {a = Char a} = RetainChar identity
identity {a = Empty} = Noop

identityLeft : ∀ {a b} → (x : Op a b) → compose identity x ≡ x
identityLeft Noop = refl
identityLeft (InsertChar c x) = cong (InsertChar c) (identityLeft x)
identityLeft (RetainChar x) = cong RetainChar (identityLeft x)
identityLeft (DeleteChar x) = cong DeleteChar (identityLeft x)
identityLeft (InsertTombstone x) = cong InsertTombstone (identityLeft x)
identityLeft (RetainTombstone x) = cong RetainTombstone (identityLeft x)

identityRight : ∀ {a b} → (x : Op a b) → compose x identity ≡ x
identityRight Noop = refl
identityRight (InsertChar c x) = cong (InsertChar c) (identityRight x)
identityRight (RetainChar x) = cong RetainChar (identityRight x)
identityRight (DeleteChar x) = cong DeleteChar (identityRight x)
identityRight (InsertTombstone x) = cong InsertTombstone (identityRight x)
identityRight (RetainTombstone x) = cong RetainTombstone (identityRight x)

OT : Category _ _ _
OT = record
  { Obj       = DocCtx
  ; _⇒_       = Op
  ; id        = identity
  ; _∘_       = λ x y → compose y x
  ; _≡_       = _≡_
  ; equiv     = isEquivalence
  ; assoc     = λ {a} {b} {c} {d} {x} {y} {z} → assoc x y z
  ; identityˡ = identityRight _
  ; identityʳ = identityLeft _
  ; ∘-resp-≡  = cong₂ (λ x y → compose y x)
  }

apply : ∀ {a b} → (x : Op a b) → Vec C (charLength a) → Vec C (charLength b)
apply Noop cs = cs
apply (RetainTombstone x) cs = apply x cs
apply (InsertTombstone x) cs = apply x cs
apply (DeleteChar x) (c ∷ cs) = apply x cs
apply (RetainChar x) (c ∷ cs) = c ∷ apply x cs
apply (InsertChar c x) cs = c ∷ apply x cs

applyIdentity : (a : DocCtx) → (v : Vec C (charLength a)) → apply (identity {a}) v ≡ v
applyIdentity (Tombstone a) cs = applyIdentity a cs
applyIdentity (Char a) (c ∷ cs) = cong (λ cs' → c ∷ cs') (applyIdentity a cs)
applyIdentity Empty cs = refl

-- Functoriality
applyHomomorphism : ∀ {a b c} → (x : Op a b) → (y : Op b c) → (v : Vec C (charLength a))
                  → apply (compose x y) v ≡ apply y (apply x v)
applyHomomorphism x (InsertTombstone y) cs = applyHomomorphism x y cs
applyHomomorphism x (InsertChar c y) cs = cong (λ cs' → c ∷ cs') (applyHomomorphism x y cs)
applyHomomorphism (InsertChar c x) (DeleteChar y) cs = applyHomomorphism x y cs
applyHomomorphism (InsertChar c x) (RetainChar y) cs = cong (λ cs' → c ∷ cs') (applyHomomorphism x y cs)
applyHomomorphism (InsertTombstone x) (RetainTombstone y) cs = applyHomomorphism x y cs
applyHomomorphism (RetainChar x) (RetainChar y) (c ∷ cs) = cong (λ cs' → c ∷ cs') (applyHomomorphism x y cs)
applyHomomorphism (RetainChar x) (DeleteChar y) (c ∷ cs) = applyHomomorphism x y cs
applyHomomorphism (DeleteChar x) (RetainTombstone y) (c ∷ cs) = applyHomomorphism x y cs
applyHomomorphism (RetainTombstone x) (RetainTombstone y) cs = applyHomomorphism x y cs
applyHomomorphism Noop Noop v = refl

Apply : Functor OT (Sets Level.zero)
Apply = record
  { F₀ = λ ctx → Vec C (charLength ctx)
  ; F₁ = apply
  ; identity =  λ {a} {v} → applyIdentity a v
  ; homomorphism = λ {a} {b} {c} {x} {y} {v} → applyHomomorphism x y v
  ; F-resp-≡ = λ eq {v} → cong (λ y → apply y v) eq
  }

record Diamond {a b c} (x : Op a b) (y : Op a c) : Set where
  constructor ⋄
  field
    d : DocCtx
    x′ : Op c d
    y′ : Op b d
    .comm : compose x y′ ≡ compose y x′

transform : ∀ {a b c} → (x : Op a b) → (y : Op a c) → Diamond x y
transform (InsertChar c x) y =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Char s) (InsertChar c x′) (RetainChar y′) (cong (InsertChar c) eq)
transform (InsertTombstone x) y =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Tombstone s) (InsertTombstone x′) (RetainTombstone y′) (cong InsertTombstone eq)
transform x (InsertTombstone y) =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x′) (InsertTombstone y′) (cong InsertTombstone eq)
transform x (InsertChar c y) =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Char s) (RetainChar x′) (InsertChar c y′) (cong (InsertChar c) eq)
transform (RetainChar x) (RetainChar y) =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Char s) (RetainChar x′) (RetainChar y′) (cong RetainChar eq)
transform (RetainTombstone x) (RetainTombstone y) =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x′) (RetainTombstone y′) (cong RetainTombstone eq)
transform (RetainChar x) (DeleteChar y) =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x′) (DeleteChar y′) (cong DeleteChar eq)
transform (DeleteChar x) (RetainChar y) =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Tombstone s) (DeleteChar x′) (RetainTombstone y′) (cong DeleteChar eq)
transform (DeleteChar x) (DeleteChar y) =
  let ⋄ s x′ y′ eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x′) (RetainTombstone y′) (cong DeleteChar eq)
transform Noop Noop = ⋄ Empty Noop Noop refl

retainCharDiamond : ∀ {a b c} → {x : Op a b} → {y : Op a c} → Diamond x y → Diamond (RetainChar x) (RetainChar y)
retainCharDiamond (⋄ d x′ y′ eq) = ⋄ (Char d) (RetainChar x′) (RetainChar y′) (cong RetainChar eq)

insertCharDiamond₁ : ∀ {a b c} → {x : Op a b} → {y : Op a c} → (q : C) → Diamond x y → Diamond (InsertChar q x) y
insertCharDiamond₁ q (⋄ d x′ y′ eq) = ⋄ (Char d) (InsertChar q x′) (RetainChar y′) (cong (InsertChar q) eq)

insertCharDiamond₂ : ∀ {a b c} → {x : Op a b} → {y : Op a c} → (q : C) → Diamond x y → Diamond x (InsertChar q y)
insertCharDiamond₂ q (⋄ d x′ y′ eq) = ⋄ (Char d) (RetainChar x′) (InsertChar q y′) (cong (InsertChar q) eq)

retainTombstoneDiamond : ∀ {a b c} → {x : Op a b} → {y : Op a c} → Diamond x y → Diamond (RetainTombstone x) (RetainTombstone y)
retainTombstoneDiamond (⋄ d x′ y′ eq) = ⋄ (Tombstone d) (RetainTombstone x′) (RetainTombstone y′) (cong RetainTombstone eq)

insertTombstoneDiamond₁ : ∀ {a b c} → {x : Op a b} → {y : Op a c} → Diamond x y → Diamond (InsertTombstone x) y
insertTombstoneDiamond₁ (⋄ d x′ y′ eq) = ⋄ (Tombstone d) (InsertTombstone x′) (RetainTombstone y′) (cong InsertTombstone eq)

insertTombstoneDiamond₂ : ∀ {a b c} → {x : Op a b} → {y : Op a c} → Diamond x y → Diamond x (InsertTombstone y)
insertTombstoneDiamond₂ (⋄ d x′ y′ eq) = ⋄ (Tombstone d) (RetainTombstone x′) (InsertTombstone y′) (cong InsertTombstone eq)

deleteCharDiamond₁ : ∀ {a b c} → {x : Op a b} → {y : Op a c} → Diamond x y → Diamond (DeleteChar x) (RetainChar y)
deleteCharDiamond₁ (⋄ d x′ y′ eq) = ⋄ (Tombstone d) (DeleteChar x′) (RetainTombstone y′) (cong DeleteChar eq)

deleteCharDiamond₂ : ∀ {a b c} → {x : Op a b} → {y : Op a c} → Diamond x y → Diamond (RetainChar x) (DeleteChar y)
deleteCharDiamond₂ (⋄ d x′ y′ eq) = ⋄ (Tombstone d) (RetainTombstone x′) (DeleteChar y′) (cong DeleteChar eq)

deleteCharDiamond₃ : ∀ {a b c} → {x : Op a b} → {y : Op a c} → Diamond x y → Diamond (DeleteChar x) (DeleteChar y)
deleteCharDiamond₃ (⋄ d x′ y′ eq) = ⋄ (Tombstone d) (RetainTombstone x′) (RetainTombstone y′) (cong DeleteChar eq)

record DiamondGrid {a b₁ b₂ c₁ c₂} (x₁ : Op a b₁) (x₂ : Op b₁ b₂) (y₁ : Op a c₁) (y₂ : Op c₁ c₂) : Set where
  constructor ◆
  field
    D-top : Diamond x₁ y₁
    D-left : Diamond x₂ (Diamond.y′ D-top)
    D-right : Diamond (Diamond.x′ D-top) y₂
    D-bottom : Diamond (Diamond.x′ D-left) (Diamond.y′ D-right)

in-out : ∀ {a b c d e} → (w : Op a b) → (x : Op b c) → (y : Op c d) → (z : Op d e)
       → compose (compose w x) (compose y z) ≡ compose w (compose (compose x y) z)
in-out w x y z = trans (sym (assoc w x (compose y z)))
                       (cong (compose w) (assoc x y z))

outerDiamond : ∀ {a b₁ b₂ c₁ c₂} {x₁ : Op a b₁} {x₂ : Op b₁ b₂} {y₁ : Op a c₁} {y₂ : Op c₁ c₂}
             → DiamondGrid x₁ x₂ y₁ y₂
             → Diamond (compose x₁ x₂) (compose y₁ y₂)
outerDiamond {a} {b₁} {b₂} {c₁} {c₂} {x₁} {x₂} {y₁} {y₂} (◆ Dt Dl Dr Db) =
  let ⋄ dt x₁′ y₁′ commt = Dt
      ⋄ dl x₂′ y₁′′ comml = Dl 
      ⋄ dr x₁′′ y₂′ commr = Dr
      ⋄ db x₂′′ y₂′′ commb = Db
  in ⋄ db (compose x₁′′ x₂′′) (compose y₁′′ y₂′′)
       (begin
          compose (compose x₁ x₂) (compose y₁′′ y₂′′)
            ↓⟨ in-out x₁ x₂ y₁′′ y₂′′ ⟩
          compose x₁ (compose (compose x₂ y₁′′) y₂′′)
            ↓⟨ cong (λ w → compose x₁ (compose w y₂′′)) comml ⟩
          compose x₁ (compose (compose y₁′ x₂′) y₂′′)
            ↑⟨ in-out x₁ y₁′ x₂′ y₂′′ ⟩
          compose (compose x₁ y₁′) (compose x₂′ y₂′′)
            ↓⟨ cong₂ compose commt commb ⟩
          compose (compose y₁ x₁′) (compose y₂′ x₂′′)
            ↓⟨ in-out y₁ x₁′ y₂′ x₂′′ ⟩
          compose y₁ (compose (compose x₁′ y₂′) x₂′′)
            ↓⟨ cong (λ w → compose y₁ (compose w x₂′′)) commr ⟩
          compose y₁ (compose (compose y₂ x₁′′) x₂′′)
            ↑⟨ in-out y₁ y₂ x₁′′ x₂′′ ⟩
          compose (compose y₁ y₂) (compose x₁′′ x₂′′)
        ∎)
  where open Category.HomReasoning OT

transformGrid : ∀ {a b₁ b₂ c₁ c₂} → (x₁ : Op a b₁) (x₂ : Op b₁ b₂) (y₁ : Op a c₁) (y₂ : Op c₁ c₂)
              → DiamondGrid x₁ x₂ y₁ y₂
transformGrid x₁ x₂ y₁ y₂ =
  let Dt = transform x₁ y₁
      Dl = transform x₂ (Diamond.y′ Dt)
      Dr = transform (Diamond.x′ Dt) y₂
      Db = transform (Diamond.x′ Dl) (Diamond.y′ Dr)
  in ◆ Dt Dl Dr Db

-- cases generated by https://gist.github.com/timjb/89927f0b5938065dbe37
composeTransformCommutes : ∀ {a b₁ b₂ c₁ c₂} → (x₁ : Op a b₁) (x₂ : Op b₁ b₂) (y₁ : Op a c₁) (y₂ : Op c₁ c₂)
                         → outerDiamond (transformGrid x₁ x₂ y₁ y₂) ≡ transform (compose x₁ x₂) (compose y₁ y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong retainCharDiamond (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong deleteCharDiamond₂ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong deleteCharDiamond₂ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (RetainChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (RetainChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (DeleteChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (DeleteChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong deleteCharDiamond₁ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong deleteCharDiamond₃ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong deleteCharDiamond₃ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (RetainChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (RetainChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (DeleteChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (DeleteChar y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong deleteCharDiamond₁ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong deleteCharDiamond₃ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong deleteCharDiamond₃ (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (RetainChar y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (RetainChar y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (DeleteChar y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (DeleteChar y₁) y₂)
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) y₁ y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) y₁ y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₂ d₁) (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) y₁ y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (RetainChar x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) y₁ y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) y₁ y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₂ d₁) (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) y₁ y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainChar x₁) (DeleteChar x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) y₁ y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) y₁ y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₂ d₁) (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) y₁ y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (DeleteChar x₁) (RetainTombstone x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainChar x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainChar x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainChar x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (DeleteChar x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (DeleteChar x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (DeleteChar x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong retainTombstoneDiamond (composeTransformCommutes x₁ x₂ y₁ y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) y₂)
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) y₁ y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) y₁ y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₂ d₁) (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) y₁ y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes (RetainTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) y₂)
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (RetainTombstone x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (RetainTombstone x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) Noop (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) Noop (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ Noop (InsertTombstone y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) Noop Noop = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ Noop Noop)
composeTransformCommutes Noop (InsertTombstone x₂) Noop (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes Noop (InsertTombstone x₂) Noop (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ Noop (InsertTombstone y₂))
composeTransformCommutes Noop (InsertTombstone x₂) Noop Noop = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ Noop Noop)
composeTransformCommutes Noop Noop Noop (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes Noop Noop Noop y₂)
composeTransformCommutes Noop Noop Noop (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes Noop Noop Noop y₂)
composeTransformCommutes Noop Noop Noop Noop = 
  refl
composeTransformCommutes Noop (InsertChar c₂ x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes Noop (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes Noop x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes Noop (InsertTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes Noop (InsertTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes Noop (InsertTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes Noop (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes Noop (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes Noop (InsertTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes Noop (InsertTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes Noop x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes Noop Noop (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes Noop Noop y₁ y₂)
composeTransformCommutes Noop Noop (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes Noop Noop y₁ y₂)
composeTransformCommutes Noop Noop (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₂ d₁) (composeTransformCommutes Noop Noop y₁ y₂)
composeTransformCommutes Noop Noop (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes Noop Noop (InsertChar d₁ y₁) y₂)
composeTransformCommutes Noop Noop (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes Noop Noop (InsertChar d₁ y₁) y₂)
composeTransformCommutes Noop Noop (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₂ d₂) (composeTransformCommutes Noop Noop (InsertTombstone y₁) y₂)
composeTransformCommutes Noop Noop (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₂ (composeTransformCommutes Noop Noop (InsertTombstone y₁) y₂)
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (RetainChar y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (RetainChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (RetainChar y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (DeleteChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (DeleteChar y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (DeleteChar y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (RetainChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (DeleteChar y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (DeleteChar y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (DeleteChar y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (RetainTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (RetainTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (RetainTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (RetainTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) Noop (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) Noop (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ Noop (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) Noop Noop = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ Noop Noop)
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) Noop (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) Noop (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ Noop (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) Noop Noop = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ Noop Noop)
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) Noop (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) Noop (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ Noop (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) Noop Noop = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ Noop Noop)
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) Noop (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) Noop (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ Noop (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) Noop Noop = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ Noop Noop)
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) Noop (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) Noop (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ Noop (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) Noop Noop = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ Noop Noop)
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) Noop (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) Noop (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ Noop (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) Noop Noop = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ Noop Noop)
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) Noop (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ Noop (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) Noop (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ Noop (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) Noop Noop = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ Noop Noop)
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (DeleteChar x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (RetainTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (RetainChar x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₁) (composeTransformCommutes x₁ x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertChar c₁ x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertChar c₁ x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertChar c₂ x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong (insertCharDiamond₁ c₂) (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (DeleteChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (DeleteChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (InsertTombstone y₁) (RetainTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertTombstone y₁) (RetainTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (RetainChar y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (RetainChar y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (InsertChar d₁ y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertChar d₁ y₁) (InsertTombstone y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertChar d₂ y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertTombstone y₁) (InsertChar d₂ y₂))
composeTransformCommutes (InsertTombstone x₁) (InsertTombstone x₂) (InsertTombstone y₁) (InsertTombstone y₂) = 
  cong insertTombstoneDiamond₁ (composeTransformCommutes (InsertTombstone x₁) x₂ (InsertTombstone y₁) (InsertTombstone y₂))


open import Categories.Slice (Category.op OT) as Coslice

diag : ∀ {a b c} {x : Op a b} {y : Op a c} → (d : Diamond x y) → Op a (Diamond.d d)
diag {a} {b} {c} {x} {y} (⋄ d _ y′ _) = compose x y′

.diagCommutes : ∀ {a b₁ b₂ c₁ c₂} {x₁ : Op a b₁} {x₂ : Op b₁ b₂} {y₁ : Op a c₁} {y₂ : Op c₁ c₂}
              → (dg : DiamondGrid x₁ x₂ y₁ y₂)
              → compose (diag (DiamondGrid.D-top dg)) (diag (DiamondGrid.D-bottom dg)) ≡ diag (outerDiamond dg)
diagCommutes {a} {b₁} {b₂} {c₁} {c₂} {x₁} {x₂} {y₁} {y₂} (◆ Dt Dl Dr Db) =
  let ⋄ dt x₁′ y₁′ commt = Dt
      ⋄ dl x₂′ y₁′′ comml = Dl
      ⋄ dr x₁′′ y₂′ commr = Dr
      ⋄ db x₂′′ y₂′′ commb = Db
  in begin
       compose (compose x₁ y₁′) (compose x₂′ y₂′′)
         ↓⟨ in-out x₁ y₁′ x₂′ y₂′′ ⟩
       compose x₁ (compose (compose y₁′ x₂′) y₂′′)
         ↓⟨ cong (λ w → compose x₁ (compose w y₂′′)) (sym (irr comml)) ⟩
       compose x₁ (compose (compose x₂ y₁′′) y₂′′)
         ↑⟨ in-out x₁ x₂ y₁′′ y₂′′ ⟩
       compose (compose x₁ x₂) (compose y₁′′ y₂′′)
     ∎
  where open Category.HomReasoning OT



diagonal : ∀ {a b c} {x : Op a b} {y : Op a c} → Diamond x y → SliceObj a
diagonal {a} {b} {c} {x} {y} d = sliceobj (diag d)
-- alternative definition:
--diagonal {a} {b} {c} {x} {y} (⋄ d x′ _ _) = sliceobj (compose y x′)

Transform₀ : ∀ {a} → Category.Obj (Product (slice a) (slice a)) → Category.Obj (slice a)
Transform₀ (sliceobj x , sliceobj y) = diagonal (transform x y)

Hom : ∀ {o ℓ e} → (C : Category o ℓ e) → Category.Obj C → Category.Obj C → Set ℓ
Hom = _[_,_]

Transform₁ : ∀ {a} (x y : Category.Obj (Product (slice a) (slice a)))
           → Hom (Product (slice a) (slice a)) x y
           → Hom (slice a) (Transform₀ x) (Transform₀ y)
Transform₁ {a} (sliceobj {b₂} x₁x₂ , sliceobj {c₂} y₁y₂)
               (sliceobj {b₁} x₁ , sliceobj {c₁} y₁)
               (slicearr {x₂} e₁ , slicearr {y₂} e₂) = slicearr e₃
  where open Category.HomReasoning OT
        dg = transformGrid x₁ x₂ y₁ y₂
        d₁ = Diamond.d (DiamondGrid.D-top dg)
        d₂ = Diamond.d (DiamondGrid.D-bottom dg)
        d₂′ = Diamond.d (transform x₁x₂ y₁y₂)
        diag₁ : Op a d₁
        diag₁ = diag (DiamondGrid.D-top dg)
        diag₂ : Op d₁ d₂
        diag₂ = diag (DiamondGrid.D-bottom dg)
        .eq₁ : d₂ ≡ d₂′
        eq₁ = trans (cong Diamond.d (composeTransformCommutes x₁ x₂ y₁ y₂))
                   (cong₂ (λ x y → Diamond.d (transform x y)) e₁ e₂)
        diag₂′ : Op d₁ d₂′
        diag₂′ = subst′ docCtxDecEq (Op d₁) eq₁ diag₂
        .diag₂′′ : Op d₁ d₂′
        diag₂′′ = subst (Op d₁) eq₁ diag₂
        {-
        .et : (eqq : d₂ ≡ d₂′) → compose diag₁ (subst′ docCtxDecEq (Op d₁) eqq diag₂) ≡ diag (transform x₁x₂ y₁y₂)
        et refl =
        -}
        .e₃ : compose diag₁ diag₂′ ≡ diag (transform x₁x₂ y₁y₂)
        --e₃ = et eq
        e₃ =
          begin
            compose diag₁ diag₂′
              ↓⟨ cong (compose diag₁) eq₂ ⟩
            compose diag₁ diag₂′′
            {-
            subst′ docCtxDecEq (Op a) eq (compose diag₁ diag₂)
              ↓⟨ {!!} ⟩
            subst′ docCtxDecEq (Op a) eq (diag (outerDiamond dg))
            -}
              ↓⟨ {!!} ⟩
            diag (transform x₁x₂ y₁y₂)
          ∎
          where
            .eq₂ : diag₂′ ≡ diag₂′′
            eq₂ = subst′-eq docCtxDecEq (Op d₁) eq₁ diag₂
            --eq₃ : (eqq : d₂ ≡ d₂′) → compose diag₁ (subst (Op d₁) eqq diag₂) ≡ subst (Op a) eqq (compose diag₁ diag₂)
            --eq₃ eqq with subst (Op d₁) eqq diag₂
            --eq₃ refl | .diag₂ = ?
            


{-
Transform : ∀ {a} → Functor (Product (slice a) (slice a)) (slice a)
Transform = record
  { F₀ = Transform₀
  ; F₁ = {!!} -- apply
  ; identity =  {!!} -- λ {a} {v} → applyIdentity a v
  ; homomorphism = {!!} -- λ {a} {b} {c} {x} {y} {v} → applyHomomorphism x y v
  ; F-resp-≡ = {!!} -- λ eq {v} → cong (λ y → apply y v) eq
  }
  --where
    --fstOp : 
-}
