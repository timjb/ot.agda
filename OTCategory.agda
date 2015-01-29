-- this agda module depends on https://github.com/copumpkin/categories

-- inspired by https://gist.github.com/aristidb/1746133

module OTCategory (C : Set) where

open import Level
open import Categories.Category
open import Categories.Functor.Core
open import Categories.Agda
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data DocCtx : Set where
  Tombstone : DocCtx → DocCtx
  Char : DocCtx → DocCtx
  Empty : DocCtx

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

{-
Cancellation rules:

Neither

cancelRight : ∀ {a b c} (x₁ x₂ : Op a b) (y : Op b c)
            → compose x₁ y ≡ compose x₂ y → x₁ ≡ x₂

nor

cancelLeft : ∀ {a b c} (x : Op a b) (y₁ y₂ : Op b c)
           → compose xy₁ ≡ compose x y₂ → y₁ ≡ y₂

hold.

Counterexamples:

* x₁ = InsertChar c Noop
  x₂ = InsertChar d Noop
  y  = DeleteChar Noop
  where c != d
* x = InsertChar c Noop
  y₁ = RetainChar (InsertChar c Noop)
  y₂ = InsertChar c (RetainChar Noop)
-}
