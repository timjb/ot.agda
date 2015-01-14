-- this agda module depends on https://github.com/copumpkin/categories

module Categories.OTCategory where

-- inspired by https://gist.github.com/aristidb/1746133

open import Level
open import Categories.Category
open import Categories.Functor.Core
open import Categories.Agda
open import Data.Nat
open import Data.Vec
open import Data.Product
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

data Op (C : Set) : DocCtx → DocCtx → Set where
  Noop : Op C Empty Empty
  InsertChar : {a b : DocCtx} → (c : C) → Op C a b → Op C a (Char b)
  RetainChar : {a b : DocCtx} → Op C a b → Op C (Char a) (Char b)
  DeleteChar : {a b : DocCtx} → Op C a b → Op C (Char a) (Tombstone b)
  InsertTombstone : {a b : DocCtx} → Op C a b → Op C a (Tombstone b)
  RetainTombstone : {a b : DocCtx} → Op C a b → Op C (Tombstone a) (Tombstone b)

compose : ∀ {C : Set} {a b c} → Op C a b → Op C b c → Op C a c
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

assoc : ∀ {C} {a b c d} → (x : Op C a b) → (y : Op C b c) → (z : Op C c d)
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

identity : ∀ {C} {a} → Op C a a
identity {a = Tombstone a} = RetainTombstone identity
identity {a = Char a} = RetainChar identity
identity {a = Empty} = Noop

identityLeft : ∀ {C} {a b} → (x : Op C a b) → compose identity x ≡ x
identityLeft Noop = refl
identityLeft (InsertChar c x) = cong (InsertChar c) (identityLeft x)
identityLeft (RetainChar x) = cong RetainChar (identityLeft x)
identityLeft (DeleteChar x) = cong DeleteChar (identityLeft x)
identityLeft (InsertTombstone x) = cong InsertTombstone (identityLeft x)
identityLeft (RetainTombstone x) = cong RetainTombstone (identityLeft x)

identityRight : ∀ {C} {a b} → (x : Op C a b) → compose x identity ≡ x
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

transform : ∀ {C} {a b c} → (x : Op C a b) → (y : Op C a c) → ∃ λ d → Op C c d × Op C b d
transform (InsertChar c x) y =
  let s , x' , y' = transform x y
  in Char s , InsertChar c x' , RetainChar y'
transform (InsertTombstone x) y =
  let s , x' , y' = transform x y
  in Tombstone s , InsertTombstone x' , RetainTombstone y'
transform x (InsertTombstone y) =
  let s , x' , y' = transform x y
  in Tombstone s , RetainTombstone x' , InsertTombstone y'
transform x (InsertChar c y) =
  let s , x' , y' = transform x y
  in Char s , RetainChar x' , InsertChar c y'
transform (RetainChar x) (RetainChar y) =
  let s , x' , y' = transform x y
  in Char s , RetainChar x' , RetainChar y'
transform (RetainTombstone x) (RetainTombstone y) =
  let s , x' , y' = transform x y
  in Tombstone s , RetainTombstone x' , RetainTombstone y'
transform (RetainChar x) (DeleteChar y) =
  let s , x' , y' = transform x y
  in Tombstone s , RetainTombstone x' , DeleteChar y'
transform (DeleteChar x) (RetainChar y) =
  let s , x' , y' = transform x y
  in Tombstone s , DeleteChar x' , RetainTombstone y'
transform (DeleteChar x) (DeleteChar y) =
  let s , x' , y' = transform x y
  in Tombstone s , RetainTombstone x' , RetainTombstone y'
transform Noop Noop = Empty , Noop , Noop

apply : ∀ {C} {a b} → (x : Op C a b) → Vec C (charLength a) → Vec C (charLength b)
apply Noop cs = cs
apply (RetainTombstone x) cs = apply x cs
apply (InsertTombstone x) cs = apply x cs
apply (DeleteChar x) (c ∷ cs) = apply x cs
apply (RetainChar x) (c ∷ cs) = c ∷ apply x cs
apply (InsertChar c x) cs = c ∷ apply x cs

applyIdentity : ∀ {C} → (a : DocCtx) → (v : Vec C (charLength a)) → apply (identity {C} {a}) v ≡ v
applyIdentity (Tombstone a) cs = applyIdentity a cs
applyIdentity (Char a) (c ∷ cs) = cong (λ cs' → c ∷ cs') (applyIdentity a cs)
applyIdentity Empty cs = refl

-- Functoriality
applyHomomorphism : ∀ {C} {a b c} → (x : Op C a b) → (y : Op C b c) → (v : Vec C (charLength a))
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

Apply : ∀ {C} → Functor (OT C) (Sets Level.zero)
Apply {C} = record
  { F₀ = λ ctx → Vec C (charLength ctx)
  ; F₁ = apply
  ; identity =  λ {a} {v} → applyIdentity a v
  ; homomorphism = λ {a} {b} {c} {x} {y} {v} → applyHomomorphism x y v
  ; F-resp-≡ = λ eq {v} → cong (λ y → apply y v) eq
  }
