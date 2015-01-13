module Categories.OTCategory where

-- inspired by https://gist.github.com/aristidb/1746133

open import Categories.Category
open import Data.Nat
open import Relation.Binary.PropositionalEquality

data DocCtx : Set where
  Tombstone : DocCtx → DocCtx
  Char : DocCtx → DocCtx
  Empty : DocCtx

docCtxLength : DocCtx → ℕ
docCtxLength (Tombstone ctx) = suc (docCtxLength ctx)
docCtxLength (Char ctx) = suc (docCtxLength ctx)
docCtxLength Empty = 0

data Op (C : Set) : DocCtx → DocCtx → Set where
  Noop : Op C Empty Empty
  InsertChar : {a b : DocCtx} → (c : C) → Op C a b → Op C a (Char b)
  RetainChar : {a b : DocCtx} → Op C a b → Op C (Char a) (Char b)
  DeleteChar : {a b : DocCtx} → Op C a b → Op C (Char a) (Tombstone b)
  InsertTombstone : {a b : DocCtx} → Op C a b → Op C a (Tombstone b)
  RetainTombstone : {a b : DocCtx} → Op C a b → Op C (Tombstone a) (Tombstone b)

compose : {C : Set} {a b c : DocCtx} → Op C a b → Op C b c → Op C a c
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

assoc : {C : Set} {a b c d : DocCtx} → (x : Op C a b) → (y : Op C b c) → (z : Op C c d)
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

identity : {C : Set} {a : DocCtx} → Op C a a
identity {a = Tombstone a} = RetainTombstone identity
identity {a = Char a} = RetainChar identity
identity {a = Empty} = Noop

identityLeft : {C : Set} {a b : DocCtx} → (x : Op C a b) → compose identity x ≡ x
identityLeft Noop = refl
identityLeft (InsertChar c x) = cong (InsertChar c) (identityLeft x)
identityLeft (RetainChar x) = cong RetainChar (identityLeft x)
identityLeft (DeleteChar x) = cong DeleteChar (identityLeft x)
identityLeft (InsertTombstone x) = cong InsertTombstone (identityLeft x)
identityLeft (RetainTombstone x) = cong RetainTombstone (identityLeft x)

identityRight : {C : Set} {a b : DocCtx} → (x : Op C a b) → compose x identity ≡ x
identityRight Noop = refl
identityRight (InsertChar c x) = cong (InsertChar c) (identityRight x)
identityRight (RetainChar x) = cong RetainChar (identityRight x)
identityRight (DeleteChar x) = cong DeleteChar (identityRight x)
identityRight (InsertTombstone x) = cong InsertTombstone (identityRight x)
identityRight (RetainTombstone x) = cong RetainTombstone (identityRight x)

OT : Set → Category _ _ _
OT C = record
  { Obj       = DocCtx
  ; _⇒_       = Op C
  ; id        = identity
  ; _∘_       = λ x y → compose y x
  ; _≡_       = _≡_
  ; equiv     = isEquivalence
  ; assoc     = λ {a} {b} {c} {d} {x} {y} {z} → assoc x y z
  ; identityˡ = identityRight _
  ; identityʳ = identityLeft _
  ; ∘-resp-≡  = cong₂ (λ x y → compose y x)
  }
