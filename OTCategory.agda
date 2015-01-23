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

open import Categories.Slice (Category.op OT) as Coslice

diagonal : ∀ {a b c} {x : Op a b} {y : Op a c} → Diamond x y → SliceObj a
diagonal {a} {b} {c} {x} {y} (⋄ d _ y' _) = sliceobj (compose x y')
-- alternative definition:
--diagonal {a} {b} {c} {x} {y} (⋄ d x' _ _) = sliceobj (compose y x')

Transform₀ : ∀ {a} → Category.Obj (Product (slice a) (slice a)) → Category.Obj (slice a)
Transform₀ (sliceobj x , sliceobj y) = diagonal (transform x y)

Hom : ∀ {o ℓ e} → (C : Category o ℓ e) → Category.Obj C → Category.Obj C → Set ℓ
Hom = _[_,_]

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



{-
Transform₁ : ∀ {a} (x y : Category.Obj (Product (slice a) (slice a)))
           → Hom (Product (slice a) (slice a)) x y
           → Hom (slice a) (Transform₀ x) (Transform₀ y)
Transform₁ {a} (sliceobj {b₂} x₁x₂ , sliceobj {c₂} y₁y₂)
               (sliceobj {b₁} x₁ , sliceobj {c₁} y₁)
               (slicearr {x₂} e₁ , slicearr {y₂} e₂)
                 with transformComposeCommutativeᵣ x₁ y₁ y₂
... | refl =
  let
    x = (sliceobj {b₂} x₁x₂ , sliceobj {c₂} y₁y₂)
    y = (sliceobj {b₁} x₁ , sliceobj {c₁} y₁)
    ⋄ d₁ x₁′ y₁′ _ = transform x₁ y₁
    ⋄ d₂ x₂′ _   _ = transform x₂ y₁′
    ⋄ d₃ _   y₂′ _ = transform x₁′ y₂
    ⋄ d₄ x₂′′ y₂′′ _ = transform x₂′ y₂′
    z : d₃ ≡ Diamond.d (transform x₁ (compose y₁ y₂))
    z = cong Diamond.d (sym (transformComposeCommutativeᵣ x₁ y₁ y₂))
    t₂ = transformThenComposeᵣ x₂ y₁′ y₂′
    t₃ = transformComposeCommutativel x₁ x₂ (compose y₁ y₂)
    h₁ : Diamond.d (transform (compose x₁ x₂) (compose y₁ y₂)) ≡ d₄
    h₁ = begin
          Diamond.d (composeThenTransforml x₁ x₂ (compose y₁ y₂))
            ≡⟨ cong Diamond.d (transformComposeCommutativel x₁ x₂ (compose y₁ y₂)) ⟩
          Diamond.d (transformThenComposel x₁ x₂ (compose y₁ y₂))
            ≡⟨ {!!} ⟩
          d₄
        ∎
    h₂ : SliceObj.Y (Transform₀ x) ≡ d₄
    h₂ = {!!}
    f : Op (SliceObj.Y (Transform₀ y)) (SliceObj.Y (Transform₀ x))
    f = subst₂ Op {!!} (sym h₂) (compose x₂′ y₂′′)
    eq : compose (SliceObj.arr (Transform₀ y)) f ≡ SliceObj.arr (Transform₀ x)
    eq = {!!}
  in slicearr eq
  where open ≡-Reasoning
-}

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
