module OTTransformAssociative (C : Set) where

open import OTCategory C
open import OTTransformCore C
open import Categories.Category
open import Relation.Binary.PropositionalEquality
open import Categories.Product

record ThreeDiamond {a b c d} (x₁ : Op a b) (y₁ : Op a c) (z₁ : Op a d) : Set where
  constructor ⋄₃
  field
    {e} : DocCtx
    x₂ : Op b e
    y₂ : Op c e
    z₂ : Op d e
    .comm-xy : compose x₁ x₂ ≡ compose y₁ y₂
    .comm-yz : compose y₁ y₂ ≡ compose z₁ z₂

transformThree₁ : ∀ {a b c d} (x₁ : Op a b) (y₁ : Op a c) (z₁ : Op a d)
                → ThreeDiamond x₁ y₁ z₁
transformThree₁ x₁ y₁ z₁ =
  let ⋄ _ x₁′ y₁′ e₁ = transform x₁ y₁
      ⋄ _ z₂ z₁′ e₂ = transform (compose y₁ x₁′) z₁
      x₂ = compose y₁′ z₁′
      y₂ = compose x₁′ z₁′
      .comm-xy : compose x₁ x₂ ≡ compose y₁ y₂
      comm-xy =
        begin
          compose x₁ (compose y₁′ z₁′)
            ↓⟨ assoc x₁ y₁′ z₁′ ⟩
          compose (compose x₁ y₁′) z₁′
            ↓⟨ cong (λ w → compose w z₁′) e₁ ⟩
          compose (compose y₁ x₁′) z₁′
            ↑⟨ assoc y₁ x₁′ z₁′ ⟩
          compose y₁ (compose x₁′ z₁′)
        ∎
      .comm-yz : compose y₁ y₂ ≡ compose z₁ z₂
      comm-yz =
        begin
          compose y₁ (compose x₁′ z₁′)
            ↓⟨ assoc y₁ x₁′ z₁′ ⟩
          compose (compose y₁ x₁′) z₁′
            ↓⟨ e₂ ⟩
          compose z₁ z₂
        ∎
  in  ⋄₃ x₂ y₂ z₂ comm-xy comm-yz
  where open Category.HomReasoning OT

transformThree₂ : ∀ {a b c d} (x₁ : Op a b) (y₁ : Op a c) (z₁ : Op a d)
                → ThreeDiamond x₁ y₁ z₁
transformThree₂ x₁ y₁ z₁ =
  let ⋄ _ y₁′ z₁′ e₁ = transform y₁ z₁
      ⋄ _ x₁′ x₂ e₂ = transform x₁ (compose y₁ z₁′)
      y₂ = compose z₁′ x₁′
      z₂ = compose y₁′ x₁′
      .comm-xy : compose x₁ x₂ ≡ compose y₁ y₂
      comm-xy =
        begin
          compose x₁ x₂
            ↓⟨ e₂ ⟩
          compose (compose y₁ z₁′) x₁′
            ↑⟨ assoc y₁ z₁′ x₁′ ⟩
          compose y₁ (compose z₁′ x₁′)
        ∎
      .comm-yz : compose y₁ y₂ ≡ compose z₁ z₂
      comm-yz =
        begin
          compose y₁ (compose z₁′ x₁′)
            ↓⟨ assoc y₁ z₁′ x₁′ ⟩
          compose (compose y₁ z₁′) x₁′
            ↓⟨ cong (λ w → compose w x₁′) e₁ ⟩
          compose (compose z₁ y₁′) x₁′
            ↑⟨ assoc z₁ y₁′ x₁′ ⟩
          compose z₁ (compose y₁′ x₁′)
        ∎
  in  ⋄₃ x₂ y₂ z₂ comm-xy comm-yz
  where open Category.HomReasoning OT


xInsertChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
            → (s : C) → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (InsertChar s x₁) y₁ z₁
xInsertChar s (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainChar x₂) (InsertChar s y₂) (InsertChar s z₂) (cong (InsertChar s) comm-xy) (cong (InsertChar s) comm-yz)

yInsertChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
            → (s : C) → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond x₁ (InsertChar s y₁) z₁
yInsertChar s (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (InsertChar s x₂) (RetainChar y₂) (InsertChar s z₂) (cong (InsertChar s) comm-xy) (cong (InsertChar s) comm-yz)

zInsertChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
            → (s : C) → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond x₁ y₁ (InsertChar s z₁)
zInsertChar s (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (InsertChar s x₂) (InsertChar s y₂) (RetainChar z₂) (cong (InsertChar s) comm-xy) (cong (InsertChar s) comm-yz)

xyzRetainChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
            → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (RetainChar x₁) (RetainChar y₁) (RetainChar z₁)
xyzRetainChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainChar x₂) (RetainChar y₂) (RetainChar z₂) (cong RetainChar comm-xy) (cong RetainChar comm-yz)

xInsertTombstone : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                 → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (InsertTombstone x₁) y₁ z₁
xInsertTombstone (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainTombstone x₂) (InsertTombstone y₂) (InsertTombstone z₂) (cong InsertTombstone comm-xy) (cong InsertTombstone comm-yz)

yInsertTombstone : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                 → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond x₁ (InsertTombstone y₁) z₁
yInsertTombstone (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (InsertTombstone x₂) (RetainTombstone y₂) (InsertTombstone z₂) (cong InsertTombstone comm-xy) (cong InsertTombstone comm-yz)

zInsertTombstone : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                 → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond x₁ y₁ (InsertTombstone z₁)
zInsertTombstone (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (InsertTombstone x₂) (InsertTombstone y₂) (RetainTombstone z₂) (cong InsertTombstone comm-xy) (cong InsertTombstone comm-yz)

xyzRetainTombstone : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                   → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (RetainTombstone x₁) (RetainTombstone y₁) (RetainTombstone z₁)
xyzRetainTombstone (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainTombstone x₂) (RetainTombstone y₂) (RetainTombstone z₂) (cong RetainTombstone comm-xy) (cong RetainTombstone comm-yz)

xDeleteYzRetainChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                    → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (DeleteChar x₁) (RetainChar y₁) (RetainChar z₁)
xDeleteYzRetainChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainTombstone x₂) (DeleteChar y₂) (DeleteChar z₂) (cong DeleteChar comm-xy) (cong DeleteChar comm-yz)

yDeleteXzRetainChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                    → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (RetainChar x₁) (DeleteChar y₁) (RetainChar z₁)
yDeleteXzRetainChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (DeleteChar x₂) (RetainTombstone y₂) (DeleteChar z₂) (cong DeleteChar comm-xy) (cong DeleteChar comm-yz)

zDeleteXyRetainChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                    → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (RetainChar x₁) (RetainChar y₁) (DeleteChar z₁)
zDeleteXyRetainChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (DeleteChar x₂) (DeleteChar y₂) (RetainTombstone z₂) (cong DeleteChar comm-xy) (cong DeleteChar comm-yz)

xyDeleteZRetainChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                    → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (DeleteChar x₁) (DeleteChar y₁) (RetainChar z₁)
xyDeleteZRetainChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainTombstone x₂) (RetainTombstone y₂) (DeleteChar z₂) (cong DeleteChar comm-xy) (cong DeleteChar comm-yz)

xzDeleteYRetainChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                    → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (DeleteChar x₁) (RetainChar y₁) (DeleteChar z₁)
xzDeleteYRetainChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainTombstone x₂) (DeleteChar y₂) (RetainTombstone z₂) (cong DeleteChar comm-xy) (cong DeleteChar comm-yz)

yzDeleteXRetainChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
                    → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (RetainChar x₁) (DeleteChar y₁) (DeleteChar z₁)
yzDeleteXRetainChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (DeleteChar x₂) (RetainTombstone y₂) (RetainTombstone z₂) (cong DeleteChar comm-xy) (cong DeleteChar comm-yz)

xyzDeleteChar : ∀ {a b c d} {x₁ : Op a b} {y₁ : Op a c} {z₁ : Op a d}
              → ThreeDiamond x₁ y₁ z₁ → ThreeDiamond (DeleteChar x₁) (DeleteChar y₁) (DeleteChar z₁)
xyzDeleteChar (⋄₃ x₂ y₂ z₂ comm-xy comm-yz) =
  ⋄₃ (RetainTombstone x₂) (RetainTombstone y₂) (RetainTombstone z₂) (cong DeleteChar comm-xy) (cong DeleteChar comm-yz)


transformAssociative : ∀ {a b c d} (x : Op a b) (y : Op a c) (z : Op a d)
                     → transformThree₁ x y z ≡ transformThree₂ x y z
transformAssociative Noop Noop Noop =
  refl
transformAssociative Noop Noop (InsertChar u z) =
  cong (zInsertChar u) (transformAssociative Noop Noop z)
transformAssociative Noop Noop (InsertTombstone z) =
  cong zInsertTombstone (transformAssociative Noop Noop z)
transformAssociative Noop (InsertChar t y) Noop =
  cong (yInsertChar t) (transformAssociative Noop y Noop)
transformAssociative Noop (InsertChar t y) (InsertChar u z) =
  cong (yInsertChar t) (transformAssociative Noop y (InsertChar u z))
transformAssociative Noop (InsertChar t y) (InsertTombstone z) =
  cong (yInsertChar t) (transformAssociative Noop y (InsertTombstone z))
transformAssociative Noop (InsertTombstone y) Noop =
  cong yInsertTombstone (transformAssociative Noop y Noop)
transformAssociative Noop (InsertTombstone y) (InsertChar u z) =
  cong yInsertTombstone (transformAssociative Noop y (InsertChar u z))
transformAssociative Noop (InsertTombstone y) (InsertTombstone z) =
  cong yInsertTombstone (transformAssociative Noop y (InsertTombstone z))
transformAssociative (InsertChar s x) Noop Noop =
  cong (xInsertChar s) (transformAssociative x Noop Noop)
transformAssociative (InsertChar s x) Noop (InsertChar u z) =
  cong (xInsertChar s) (transformAssociative x Noop (InsertChar u z))
transformAssociative (InsertChar s x) Noop (InsertTombstone z) =
  cong (xInsertChar s) (transformAssociative x Noop (InsertTombstone z))
transformAssociative (InsertChar s x) (InsertChar t y) Noop =
  cong (xInsertChar s) (transformAssociative x (InsertChar t y) Noop)
transformAssociative (InsertChar s x) (InsertChar t y) (InsertChar u z) =
  cong (xInsertChar s) (transformAssociative x (InsertChar t y) (InsertChar u z))
transformAssociative (InsertChar s x) (InsertChar t y) (RetainChar z) =
  cong (xInsertChar s) (transformAssociative x (InsertChar t y) (RetainChar z))
transformAssociative (InsertChar s x) (InsertChar t y) (DeleteChar z) =
  cong (xInsertChar s) (transformAssociative x (InsertChar t y) (DeleteChar z))
transformAssociative (InsertChar s x) (InsertChar t y) (InsertTombstone z) =
  cong (xInsertChar s) (transformAssociative x (InsertChar t y) (InsertTombstone z))
transformAssociative (InsertChar s x) (InsertChar t y) (RetainTombstone z) =
  cong (xInsertChar s) (transformAssociative x (InsertChar t y) (RetainTombstone z))
transformAssociative (InsertChar s x) (RetainChar y) (InsertChar u z) =
  cong (xInsertChar s) (transformAssociative x (RetainChar y) (InsertChar u z))
transformAssociative (InsertChar s x) (RetainChar y) (RetainChar z) =
  cong (xInsertChar s) (transformAssociative x (RetainChar y) (RetainChar z))
transformAssociative (InsertChar s x) (RetainChar y) (DeleteChar z) =
  cong (xInsertChar s) (transformAssociative x (RetainChar y) (DeleteChar z))
transformAssociative (InsertChar s x) (RetainChar y) (InsertTombstone z) =
  cong (xInsertChar s) (transformAssociative x (RetainChar y) (InsertTombstone z))
transformAssociative (InsertChar s x) (DeleteChar y) (InsertChar u z) =
  cong (xInsertChar s) (transformAssociative x (DeleteChar y) (InsertChar u z))
transformAssociative (InsertChar s x) (DeleteChar y) (RetainChar z) =
  cong (xInsertChar s) (transformAssociative x (DeleteChar y) (RetainChar z))
transformAssociative (InsertChar s x) (DeleteChar y) (DeleteChar z) =
  cong (xInsertChar s) (transformAssociative x (DeleteChar y) (DeleteChar z))
transformAssociative (InsertChar s x) (DeleteChar y) (InsertTombstone z) =
  cong (xInsertChar s) (transformAssociative x (DeleteChar y) (InsertTombstone z))
transformAssociative (InsertChar s x) (InsertTombstone y) Noop =
  cong (xInsertChar s) (transformAssociative x (InsertTombstone y) Noop)
transformAssociative (InsertChar s x) (InsertTombstone y) (InsertChar u z) =
  cong (xInsertChar s) (transformAssociative x (InsertTombstone y) (InsertChar u z))
transformAssociative (InsertChar s x) (InsertTombstone y) (RetainChar z) =
  cong (xInsertChar s) (transformAssociative x (InsertTombstone y) (RetainChar z))
transformAssociative (InsertChar s x) (InsertTombstone y) (DeleteChar z) =
  cong (xInsertChar s) (transformAssociative x (InsertTombstone y) (DeleteChar z))
transformAssociative (InsertChar s x) (InsertTombstone y) (InsertTombstone z) =
  cong (xInsertChar s) (transformAssociative x (InsertTombstone y) (InsertTombstone z))
transformAssociative (InsertChar s x) (InsertTombstone y) (RetainTombstone z) =
  cong (xInsertChar s) (transformAssociative x (InsertTombstone y) (RetainTombstone z))
transformAssociative (InsertChar s x) (RetainTombstone y) (InsertChar u z) =
  cong (xInsertChar s) (transformAssociative x (RetainTombstone y) (InsertChar u z))
transformAssociative (InsertChar s x) (RetainTombstone y) (InsertTombstone z) =
  cong (xInsertChar s) (transformAssociative x (RetainTombstone y) (InsertTombstone z))
transformAssociative (InsertChar s x) (RetainTombstone y) (RetainTombstone z) =
  cong (xInsertChar s) (transformAssociative x (RetainTombstone y) (RetainTombstone z))
transformAssociative (RetainChar x) (InsertChar t y) (InsertChar u z) =
  cong (yInsertChar t) (transformAssociative (RetainChar x) y (InsertChar u z))
transformAssociative (RetainChar x) (InsertChar t y) (RetainChar z) =
  cong (yInsertChar t) (transformAssociative (RetainChar x) y (RetainChar z))
transformAssociative (RetainChar x) (InsertChar t y) (DeleteChar z) =
  cong (yInsertChar t) (transformAssociative (RetainChar x) y (DeleteChar z))
transformAssociative (RetainChar x) (InsertChar t y) (InsertTombstone z) =
  cong (yInsertChar t) (transformAssociative (RetainChar x) y (InsertTombstone z))
transformAssociative (RetainChar x) (RetainChar y) (InsertChar u z) =
  cong (zInsertChar u) (transformAssociative (RetainChar x) (RetainChar y) z)
transformAssociative (RetainChar x) (RetainChar y) (RetainChar z) =
  cong xyzRetainChar (transformAssociative x y z)
transformAssociative (RetainChar x) (RetainChar y) (DeleteChar z) =
  cong zDeleteXyRetainChar (transformAssociative x y z)
transformAssociative (RetainChar x) (RetainChar y) (InsertTombstone z) =
  cong zInsertTombstone (transformAssociative (RetainChar x) (RetainChar y) z)
transformAssociative (RetainChar x) (DeleteChar y) (InsertChar u z) =
  cong (zInsertChar u) (transformAssociative (RetainChar x) (DeleteChar y) z)
transformAssociative (RetainChar x) (DeleteChar y) (RetainChar z) =
  cong yDeleteXzRetainChar (transformAssociative x y z)
transformAssociative (RetainChar x) (DeleteChar y) (DeleteChar z) =
  cong yzDeleteXRetainChar (transformAssociative x y z)
transformAssociative (RetainChar x) (DeleteChar y) (InsertTombstone z) =
  cong zInsertTombstone (transformAssociative (RetainChar x) (DeleteChar y) z)
transformAssociative (RetainChar x) (InsertTombstone y) (InsertChar u z) =
  cong yInsertTombstone (transformAssociative (RetainChar x) y (InsertChar u z))
transformAssociative (RetainChar x) (InsertTombstone y) (RetainChar z) =
  cong yInsertTombstone (transformAssociative (RetainChar x) y (RetainChar z))
transformAssociative (RetainChar x) (InsertTombstone y) (DeleteChar z) =
  cong yInsertTombstone (transformAssociative (RetainChar x) y (DeleteChar z))
transformAssociative (RetainChar x) (InsertTombstone y) (InsertTombstone z) =
  cong yInsertTombstone (transformAssociative (RetainChar x) y (InsertTombstone z))
transformAssociative (DeleteChar x) (InsertChar t y) (InsertChar u z) =
  cong (yInsertChar t) (transformAssociative (DeleteChar x) y (InsertChar u z))
transformAssociative (DeleteChar x) (InsertChar t y) (RetainChar z) =
  cong (yInsertChar t) (transformAssociative (DeleteChar x) y (RetainChar z))
transformAssociative (DeleteChar x) (InsertChar t y) (DeleteChar z) =
  cong (yInsertChar t) (transformAssociative (DeleteChar x) y (DeleteChar z))
transformAssociative (DeleteChar x) (InsertChar t y) (InsertTombstone z) =
  cong (yInsertChar t) (transformAssociative (DeleteChar x) y (InsertTombstone z))
transformAssociative (DeleteChar x) (RetainChar y) (InsertChar u z) =
  cong (zInsertChar u) (transformAssociative (DeleteChar x) (RetainChar y) z)
transformAssociative (DeleteChar x) (RetainChar y) (RetainChar z) =
  cong xDeleteYzRetainChar (transformAssociative x y z)
transformAssociative (DeleteChar x) (RetainChar y) (DeleteChar z) =
  cong xzDeleteYRetainChar (transformAssociative x y z)
transformAssociative (DeleteChar x) (RetainChar y) (InsertTombstone z) =
  cong zInsertTombstone (transformAssociative (DeleteChar x) (RetainChar y) z)
transformAssociative (DeleteChar x) (DeleteChar y) (InsertChar u z) =
  cong (zInsertChar u) (transformAssociative (DeleteChar x) (DeleteChar y) z)
transformAssociative (DeleteChar x) (DeleteChar y) (RetainChar z) =
  cong xyDeleteZRetainChar (transformAssociative x y z)
transformAssociative (DeleteChar x) (DeleteChar y) (DeleteChar z) =
  cong xyzDeleteChar (transformAssociative x y z)
transformAssociative (DeleteChar x) (DeleteChar y) (InsertTombstone z) =
  cong zInsertTombstone (transformAssociative (DeleteChar x) (DeleteChar y) z)
transformAssociative (DeleteChar x) (InsertTombstone y) (InsertChar u z) =
  cong yInsertTombstone (transformAssociative (DeleteChar x) y (InsertChar u z))
transformAssociative (DeleteChar x) (InsertTombstone y) (RetainChar z) =
  cong yInsertTombstone (transformAssociative (DeleteChar x) y (RetainChar z))
transformAssociative (DeleteChar x) (InsertTombstone y) (DeleteChar z) =
  cong yInsertTombstone (transformAssociative (DeleteChar x) y (DeleteChar z))
transformAssociative (DeleteChar x) (InsertTombstone y) (InsertTombstone z) =
  cong yInsertTombstone (transformAssociative (DeleteChar x) y (InsertTombstone z))
transformAssociative (InsertTombstone x) Noop Noop =
  cong xInsertTombstone (transformAssociative x Noop Noop)
transformAssociative (InsertTombstone x) Noop (InsertChar u z) =
  cong xInsertTombstone (transformAssociative x Noop (InsertChar u z))
transformAssociative (InsertTombstone x) Noop (InsertTombstone z) =
  cong xInsertTombstone (transformAssociative x Noop (InsertTombstone z))
transformAssociative (InsertTombstone x) (InsertChar t y) Noop =
  cong xInsertTombstone (transformAssociative x (InsertChar t y) Noop)
transformAssociative (InsertTombstone x) (InsertChar t y) (InsertChar u z) =
  cong xInsertTombstone (transformAssociative x (InsertChar t y) (InsertChar u z))
transformAssociative (InsertTombstone x) (InsertChar t y) (RetainChar z) =
  cong xInsertTombstone (transformAssociative x (InsertChar t y) (RetainChar z))
transformAssociative (InsertTombstone x) (InsertChar t y) (DeleteChar z) =
  cong xInsertTombstone (transformAssociative x (InsertChar t y) (DeleteChar z))
transformAssociative (InsertTombstone x) (InsertChar t y) (InsertTombstone z) =
  cong xInsertTombstone (transformAssociative x (InsertChar t y) (InsertTombstone z))
transformAssociative (InsertTombstone x) (InsertChar t y) (RetainTombstone z) =
  cong xInsertTombstone (transformAssociative x (InsertChar t y) (RetainTombstone z))
transformAssociative (InsertTombstone x) (RetainChar y) (InsertChar u z) =
  cong xInsertTombstone (transformAssociative x (RetainChar y) (InsertChar u z))
transformAssociative (InsertTombstone x) (RetainChar y) (RetainChar z) =
  cong xInsertTombstone (transformAssociative x (RetainChar y) (RetainChar z))
transformAssociative (InsertTombstone x) (RetainChar y) (DeleteChar z) =
  cong xInsertTombstone (transformAssociative x (RetainChar y) (DeleteChar z))
transformAssociative (InsertTombstone x) (RetainChar y) (InsertTombstone z) =
  cong xInsertTombstone (transformAssociative x (RetainChar y) (InsertTombstone z))
transformAssociative (InsertTombstone x) (DeleteChar y) (InsertChar u z) =
  cong xInsertTombstone (transformAssociative x (DeleteChar y) (InsertChar u z))
transformAssociative (InsertTombstone x) (DeleteChar y) (RetainChar z) =
  cong xInsertTombstone (transformAssociative x (DeleteChar y) (RetainChar z))
transformAssociative (InsertTombstone x) (DeleteChar y) (DeleteChar z) =
  cong xInsertTombstone (transformAssociative x (DeleteChar y) (DeleteChar z))
transformAssociative (InsertTombstone x) (DeleteChar y) (InsertTombstone z) =
  cong xInsertTombstone (transformAssociative x (DeleteChar y) (InsertTombstone z))
transformAssociative (InsertTombstone x) (InsertTombstone y) Noop =
  cong xInsertTombstone (transformAssociative x (InsertTombstone y) Noop)
transformAssociative (InsertTombstone x) (InsertTombstone y) (InsertChar u z) =
  cong xInsertTombstone (transformAssociative x (InsertTombstone y) (InsertChar u z))
transformAssociative (InsertTombstone x) (InsertTombstone y) (RetainChar z) =
  cong xInsertTombstone (transformAssociative x (InsertTombstone y) (RetainChar z))
transformAssociative (InsertTombstone x) (InsertTombstone y) (DeleteChar z) =
  cong xInsertTombstone (transformAssociative x (InsertTombstone y) (DeleteChar z))
transformAssociative (InsertTombstone x) (InsertTombstone y) (InsertTombstone z) =
  cong xInsertTombstone (transformAssociative x (InsertTombstone y) (InsertTombstone z))
transformAssociative (InsertTombstone x) (InsertTombstone y) (RetainTombstone z) =
  cong xInsertTombstone (transformAssociative x (InsertTombstone y) (RetainTombstone z))
transformAssociative (InsertTombstone x) (RetainTombstone y) (InsertChar u z) =
  cong xInsertTombstone (transformAssociative x (RetainTombstone y) (InsertChar u z))
transformAssociative (InsertTombstone x) (RetainTombstone y) (InsertTombstone z) =
  cong xInsertTombstone (transformAssociative x (RetainTombstone y) (InsertTombstone z))
transformAssociative (InsertTombstone x) (RetainTombstone y) (RetainTombstone z) =
  cong xInsertTombstone (transformAssociative x (RetainTombstone y) (RetainTombstone z))
transformAssociative (RetainTombstone x) (InsertChar t y) (InsertChar u z) =
  cong (yInsertChar t) (transformAssociative (RetainTombstone x) y (InsertChar u z))
transformAssociative (RetainTombstone x) (InsertChar t y) (InsertTombstone z) =
  cong (yInsertChar t) (transformAssociative (RetainTombstone x) y (InsertTombstone z))
transformAssociative (RetainTombstone x) (InsertChar t y) (RetainTombstone z) =
  cong (yInsertChar t) (transformAssociative (RetainTombstone x) y (RetainTombstone z))
transformAssociative (RetainTombstone x) (InsertTombstone y) (InsertChar u z) =
  cong yInsertTombstone (transformAssociative (RetainTombstone x) y (InsertChar u z))
transformAssociative (RetainTombstone x) (InsertTombstone y) (InsertTombstone z) =
  cong yInsertTombstone (transformAssociative (RetainTombstone x) y (InsertTombstone z))
transformAssociative (RetainTombstone x) (InsertTombstone y) (RetainTombstone z) =
  cong yInsertTombstone (transformAssociative (RetainTombstone x) y (RetainTombstone z))
transformAssociative (RetainTombstone x) (RetainTombstone y) (InsertChar u z) =
  cong (zInsertChar u) (transformAssociative (RetainTombstone x) (RetainTombstone y) z)
transformAssociative (RetainTombstone x) (RetainTombstone y) (InsertTombstone z) =
  cong zInsertTombstone (transformAssociative (RetainTombstone x) (RetainTombstone y) z)
transformAssociative (RetainTombstone x) (RetainTombstone y) (RetainTombstone z) =
  cong xyzRetainTombstone (transformAssociative x y z)
