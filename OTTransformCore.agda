module OTTransformCore (C : Set) where

open import OTCategory C
open import Categories.Category
open import Relation.Binary.PropositionalEquality
open import Categories.Product

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

-- cases generated by GenCases.hs
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
