-- this agda module depends on https://github.com/copumpkin/categories

module Categories.OTCategory (C : Set) where

-- inspired by https://gist.github.com/aristidb/1746133

open import Level
open import Categories.Category
open import Categories.Functor.Core
open import Categories.Agda
open import Categories.Product
--open import Categories.Bifunctor
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

record Diamond {a b c} (x : Op a b) (y : Op a c) : Set where
  constructor ⋄
  field
    d : DocCtx
    x' : Op c d
    y' : Op b d
    .comm : compose x y' ≡ compose y x'

transform : ∀ {a b c} → (x : Op a b) → (y : Op a c) → Diamond x y
transform (InsertChar c x) y =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Char s) (InsertChar c x') (RetainChar y') (cong (InsertChar c) eq)
transform (InsertTombstone x) y =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Tombstone s) (InsertTombstone x') (RetainTombstone y') (cong InsertTombstone eq)
transform x (InsertTombstone y) =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x') (InsertTombstone y') (cong InsertTombstone eq)
transform x (InsertChar c y) =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Char s) (RetainChar x') (InsertChar c y') (cong (InsertChar c) eq)
transform (RetainChar x) (RetainChar y) =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Char s) (RetainChar x') (RetainChar y') (cong RetainChar eq)
transform (RetainTombstone x) (RetainTombstone y) =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x') (RetainTombstone y') (cong RetainTombstone eq)
transform (RetainChar x) (DeleteChar y) =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x') (DeleteChar y') (cong DeleteChar eq)
transform (DeleteChar x) (RetainChar y) =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Tombstone s) (DeleteChar x') (RetainTombstone y') (cong DeleteChar eq)
transform (DeleteChar x) (DeleteChar y) =
  let ⋄ s x' y' eq = transform x y
  in ⋄ (Tombstone s) (RetainTombstone x') (RetainTombstone y') (cong DeleteChar eq)
transform Noop Noop = ⋄ Empty Noop Noop refl

composeThenTransform : ∀ {a b c d} → (x : Op a b) → (y : Op a c) → (z : Op c d) → Diamond x (compose y z)
composeThenTransform x y z = transform x (compose y z)

transformThenCompose : ∀ {a b c d} → (x : Op a b) → (y : Op a c) → (z : Op c d) → Diamond x (compose y z)
transformThenCompose x y z =
  let ⋄ d₁ x′ y′ eq₁ = transform x y
      ⋄ d₂ x′′ z′ eq₂ = transform x′ z
  in ⋄ d₂ x′′ (compose y′ z′)
       (begin
          compose x (compose y′ z′)
            ↓⟨ assoc x y′ z′ ⟩
          compose (compose x y′) z′
            ↓⟨ cong (λ w → compose w z′) eq₁ ⟩
          compose (compose y x′) z′
            ↑⟨ assoc y x′ z′ ⟩
          compose y (compose x′ z′)
            ↓⟨ cong (compose y) eq₂ ⟩
          compose y (compose z x′′)
            ↓⟨ assoc y z x′′ ⟩
          compose (compose y z) x′′
        ∎)
  where open Category.HomReasoning OT

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


transformComposeCommutative : ∀ {a b c d} → (x : Op a b) → (y : Op a c) → (z : Op c d)
                            → composeThenTransform x y z ≡ transformThenCompose x y z
transformComposeCommutative (RetainChar x) (RetainChar y) (RetainChar z) =
  cong retainCharDiamond (transformComposeCommutative x y z)
transformComposeCommutative (InsertChar q x) y z =
  cong (insertCharDiamond₁ q) (transformComposeCommutative x y z)
transformComposeCommutative (RetainTombstone x) (RetainTombstone y) (RetainTombstone z) =
  cong retainTombstoneDiamond (transformComposeCommutative x y z)
transformComposeCommutative (InsertTombstone x) y z =
  cong insertTombstoneDiamond₁ (transformComposeCommutative x y z)
transformComposeCommutative (DeleteChar x) (RetainChar y) (RetainChar z) =
  cong deleteCharDiamond₁ (transformComposeCommutative x y z)
transformComposeCommutative (RetainChar x) (DeleteChar y) (RetainTombstone z) =
  cong deleteCharDiamond₂ (transformComposeCommutative x y z)
transformComposeCommutative (RetainChar x) (RetainChar y) (DeleteChar z) =
  cong deleteCharDiamond₂ (transformComposeCommutative x y z)
transformComposeCommutative (DeleteChar x) (DeleteChar y) (RetainTombstone z) =
  cong deleteCharDiamond₃ (transformComposeCommutative x y z)
transformComposeCommutative (DeleteChar x) (RetainChar y) (DeleteChar z) =
  cong deleteCharDiamond₃ (transformComposeCommutative x y z)
transformComposeCommutative (RetainChar x) (InsertChar q y) (RetainChar z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainChar x) y z)
transformComposeCommutative (DeleteChar x) (InsertChar q y) (RetainChar z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (DeleteChar x) y z)
transformComposeCommutative (RetainChar x) (RetainChar y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainChar x) (RetainChar y) z)
transformComposeCommutative (DeleteChar x) (RetainChar y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (DeleteChar x) (RetainChar y) z)
transformComposeCommutative (RetainChar x) (DeleteChar y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainChar x) (DeleteChar y) z)
transformComposeCommutative (DeleteChar x) (DeleteChar y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (DeleteChar x) (DeleteChar y) z)
transformComposeCommutative (RetainChar x) (InsertChar p y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainChar x) (InsertChar p y) z)
transformComposeCommutative (DeleteChar x) (InsertChar p y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (DeleteChar x) (InsertChar p y) z)
transformComposeCommutative (RetainChar x) (InsertTombstone y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainChar x) (InsertTombstone y) z)
transformComposeCommutative (DeleteChar x) (InsertTombstone y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (DeleteChar x) (InsertTombstone y) z)
transformComposeCommutative (RetainTombstone x) (RetainTombstone y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainTombstone x) (RetainTombstone y) z)
transformComposeCommutative (RetainChar x) (InsertTombstone y) (RetainTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainChar x) y z)
transformComposeCommutative (RetainTombstone x) (InsertTombstone y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainTombstone x) (InsertTombstone y) z)
transformComposeCommutative (RetainTombstone x) (InsertChar q y) (RetainChar z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative (RetainTombstone x) y z)
transformComposeCommutative (RetainTombstone x) (InsertChar q y) (InsertChar p z) =
  cong (insertCharDiamond₂ p) (transformComposeCommutative (RetainTombstone x) (InsertChar q y) z)
transformComposeCommutative (RetainTombstone x) (InsertTombstone y) (RetainTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainTombstone x) y z)
transformComposeCommutative (DeleteChar x) (InsertChar q y) (DeleteChar z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (DeleteChar x) y z)
transformComposeCommutative (RetainChar x) (InsertChar q y) (DeleteChar z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainChar x) y z)
transformComposeCommutative (DeleteChar x) (InsertTombstone y) (RetainTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (DeleteChar x) y z)
transformComposeCommutative (RetainChar x) (RetainChar y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainChar x) (RetainChar y) z)
transformComposeCommutative (DeleteChar x) (RetainChar y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (DeleteChar x) (RetainChar y) z)
transformComposeCommutative (RetainChar x) (DeleteChar y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainChar x) (DeleteChar y) z)
transformComposeCommutative (DeleteChar x) (DeleteChar y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (DeleteChar x) (DeleteChar y) z)
transformComposeCommutative (RetainChar x) (InsertChar p y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainChar x) (InsertChar p y) z)
transformComposeCommutative (DeleteChar x) (InsertChar p y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (DeleteChar x) (InsertChar p y) z)
transformComposeCommutative (RetainTombstone x) (InsertChar p y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainTombstone x) (InsertChar p y) z)
transformComposeCommutative (RetainChar x) (InsertTombstone y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainChar x) (InsertTombstone y) z)
transformComposeCommutative (DeleteChar x) (InsertTombstone y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (DeleteChar x) (InsertTombstone y) z)
transformComposeCommutative (RetainTombstone x) (InsertTombstone y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainTombstone x) (InsertTombstone y) z)
transformComposeCommutative (RetainTombstone x) (RetainTombstone y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainTombstone x) (RetainTombstone y) z)
transformComposeCommutative (RetainTombstone x) (InsertChar q y) (DeleteChar z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative (RetainTombstone x) y z)
transformComposeCommutative Noop Noop (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative Noop Noop z)
transformComposeCommutative Noop (InsertChar q y) (RetainChar z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative Noop y z)
transformComposeCommutative Noop (InsertChar q y) (InsertChar p z) =
  cong (insertCharDiamond₂ p) (transformComposeCommutative Noop (InsertChar q y) z)
transformComposeCommutative Noop Noop (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative Noop Noop z)
transformComposeCommutative Noop (InsertTombstone y) (RetainTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative Noop y z)
transformComposeCommutative Noop (InsertChar q y) (DeleteChar z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative Noop y z)
transformComposeCommutative Noop (InsertChar q y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative Noop (InsertChar q y) z)
transformComposeCommutative Noop (InsertTombstone y) (InsertTombstone z) =
  cong insertTombstoneDiamond₂ (transformComposeCommutative Noop (InsertTombstone y) z)
transformComposeCommutative Noop (InsertTombstone y) (InsertChar q z) =
  cong (insertCharDiamond₂ q) (transformComposeCommutative Noop (InsertTombstone y) z)
transformComposeCommutative Noop Noop Noop = refl

open import Categories.Slice (Category.op OT) as Coslice

diagonal : ∀ {a b c} {x : Op a b} {y : Op a c} → Diamond x y → SliceObj a
diagonal {a} {b} {c} {x} {y} (⋄ d _ y' _) = sliceobj (compose x y')
-- alternative definition:
--diagonal {a} {b} {c} {x} {y} (⋄ d x' _ _) = sliceobj (compose y x')

Transform₀ : ∀ {a} → Category.Obj (Product (slice a) (slice a)) → Category.Obj (slice a)
Transform₀ (sliceobj x , sliceobj y) = diagonal (transform x y)

Hom : ∀ {o ℓ e} → (C : Category o ℓ e) → Category.Obj C → Category.Obj C → Set ℓ
Hom = _[_,_]

{-
Transform₁ : ∀ {a} (x y : Category.Obj (Product (slice a) (slice a)))
           → Hom (Product (slice a) (slice a)) x y
           → Hom (slice a) (Transform₀ x) (Transform₀ y)
Transform₁ {a} (sliceobj {b₂} _ , sliceobj {c₂} _) (sliceobj {b₁} x₁ , sliceobj {c₁} y₁) (slicearr {x₂} _ , slicearr {y₂} _) =
  let ⋄ _ x₁′ y₁′ _ = transform x₁ y₁
      ⋄ _ x₂′ _   _ = transform x₂ y₁′
      ⋄ _ _   y₂′ _ = transform x₁′ y₂
      ⋄ _ x₂′′ y₂′′ _ = transform x₂′ y₂′
  in {!slicearr (compose ) ?!}

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
