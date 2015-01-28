open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Decidable equality is only a technical precondition to help deal with irrelevant propositional equality
module OTTransformFunctor (C : Set) (decEq : Decidable {A = C} _≡_) where

open import Relation.Nullary
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.HeterogeneousEquality using (_≅_)
open import Categories.Category
open import Categories.Functor.Core
open import Categories.Product
open import Data.Product
open import SubstIrrelevant

open import OTCategory C
open import OTTransformCore C

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

longDiag₁ : ∀ {a b₁ b₂ c₁ c₂} (x₁ : Op a b₁) (x₂ : Op b₁ b₂) (y₁ : Op a c₁) (y₂ : Op c₁ c₂)
          → Op a (Diamond.d (transform (compose x₁ x₂) (compose y₁ y₂)))
longDiag₁ x₁ x₂ y₁ y₂ = diag (transform (compose x₁ x₂) (compose y₁ y₂))

longDiag₂ : ∀ {a b₁ b₂ c₁ c₂} (x₁ : Op a b₁) (x₂ : Op b₁ b₂) (y₁ : Op a c₁) (y₂ : Op c₁ c₂)
          → Op a (Diamond.d (transform (compose x₁ x₂) (compose y₁ y₂)))
longDiag₂ {a} x₁ x₂ y₁ y₂ =
  subst (Op a) (cong Diamond.d (composeTransformCommutes x₁ x₂ y₁ y₂))
               (diag (outerDiamond (transformGrid x₁ x₂ y₁ y₂)))

longDiagEq : ∀ {a b₁ b₂ c₁ c₂} (x₁ : Op a b₁) (x₂ : Op b₁ b₂) (y₁ : Op a c₁) (y₂ : Op c₁ c₂)
           → (dg : DiamondGrid x₁ x₂ y₁ y₂) → (d : Diamond (compose x₁ x₂) (compose y₁ y₂))
           → (e : outerDiamond dg ≡ d) → diag (outerDiamond dg) ≅ diag d
longDiagEq x₁ x₂ y₁ y₂ dg d eq = HE.cong diag (HE.≡-to-≅ eq)

{-
longDiagEq : ∀ {a b₁ b₂ c₁ c₂} (x₁ : Op a b₁) (x₂ : Op b₁ b₂) (y₁ : Op a c₁) (y₂ : Op c₁ c₂)
           → longDiag₁ x₁ x₂ y₁ y₂ ≡ longDiag₂ x₁ x₂ y₁ y₂
longDiagEq x₁ x₂ y₁ y₂ = cong (compose (compose x₁ x₂)) {!cong Diamond.y′ (sym (composeTransformCommutes x₁ x₂ y₁ y₂))!}
-}

diagonal : ∀ {a b c} {x : Op a b} {y : Op a c} → Diamond x y → SliceObj a
diagonal {a} {b} {c} {x} {y} d = sliceobj (diag d)
-- alternative definition:
--diagonal {a} {b} {c} {x} {y} (⋄ d x′ _ _) = sliceobj (compose y x′)

Transform₀ : ∀ {a} → Category.Obj (Product (slice a) (slice a)) → Category.Obj (slice a)
Transform₀ (sliceobj x , sliceobj y) = diagonal (transform x y)

Hom : ∀ {o ℓ e} → (C : Category o ℓ e) → Category.Obj C → Category.Obj C → Set ℓ
Hom = _[_,_]

substCompose : ∀ {a b c₁ c₂} (e : c₁ ≡ c₂) (x : Op a b) (y : Op b c₁)
             → subst (Op a) e (compose x y) ≡ compose x (subst (Op b) e y)
substCompose refl x y = refl

Transform₁ : ∀ {a} {x y : Category.Obj (Product (slice a) (slice a))}
           → Hom (Product (slice a) (slice a)) x y
           → Hom (slice a) (Transform₀ x) (Transform₀ y)
Transform₁ {a} {sliceobj {b₂} x₁x₂ , sliceobj {c₂} y₁y₂}
               {sliceobj {b₁} x₁ , sliceobj {c₁} y₁}
               (slicearr {x₂} e₁ , slicearr {y₂} e₂) = slicearr {h = diag₂′} (HE.≅-to-≡ eq₃)
  where dg = transformGrid x₁ x₂ y₁ y₂
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
        .eq₃ : compose diag₁ diag₂′ ≅ diag (transform x₁x₂ y₁y₂)
        eq₃ =
          begin
            compose diag₁ diag₂′
              ≡⟨ cong (compose diag₁) (subst′-eq docCtxDecEq (Op d₁) eq₁ diag₂) ⟩
            compose diag₁ diag₂′′
              ≡⟨ sym (substCompose eq₁ diag₁ diag₂) ⟩
            subst (Op a) eq₁ (compose diag₁ diag₂)
              ≅⟨ HE.≡-subst-removable (Op a) eq₁ (compose diag₁ diag₂) ⟩
            compose diag₁ diag₂
              ≡⟨ diagCommutes dg ⟩
            diag (outerDiamond dg)
              ≅⟨ HE.cong diag (HE.≡-to-≅ (composeTransformCommutes x₁ x₂ y₁ y₂)) ⟩
            diag (transform (compose x₁ x₂) (compose y₁ y₂))
              ≅⟨ HE.cong₂ (λ x y → diag (transform x y)) (HE.≡-to-≅ e₁) (HE.≡-to-≅ e₂) ⟩
            diag (transform x₁x₂ y₁y₂)
          ∎
          where open HE.≅-Reasoning

identityDiamondLeft : ∀ {a c} (y : Op a c) → Diamond identity y
identityDiamondLeft {a} {c} y = ⋄ c identity y (trans (identityLeft y) (sym (identityRight y)))

transformIdentityLeft : ∀ {a c} (y : Op a c) → transform identity y ≡ identityDiamondLeft y
transformIdentityLeft {Empty} Noop = refl
transformIdentityLeft {Empty} (InsertChar c y) = cong (insertCharDiamond₂ c) (transformIdentityLeft y)
transformIdentityLeft {Char a} (InsertChar c y) = cong (insertCharDiamond₂ c) (transformIdentityLeft y)
transformIdentityLeft {Tombstone a} (InsertChar c y) = cong (insertCharDiamond₂ c) (transformIdentityLeft y)
transformIdentityLeft {Char a} (RetainChar y) = cong retainCharDiamond (transformIdentityLeft y)
transformIdentityLeft {Char a} (DeleteChar y) = cong deleteCharDiamond₂ (transformIdentityLeft y)
transformIdentityLeft {Empty} (InsertTombstone y) = cong insertTombstoneDiamond₂ (transformIdentityLeft y)
transformIdentityLeft {Char a} (InsertTombstone y) = cong insertTombstoneDiamond₂ (transformIdentityLeft y)
transformIdentityLeft {Tombstone a} (InsertTombstone y) = cong insertTombstoneDiamond₂ (transformIdentityLeft y)
transformIdentityLeft {Tombstone a} (RetainTombstone y) = cong retainTombstoneDiamond (transformIdentityLeft y)

identityDiamondRight : ∀ {a b} (x : Op a b) → Diamond x identity
identityDiamondRight {a} {b} x = ⋄ b x identity (trans (identityRight x) (sym (identityLeft x)))

transformIdentityRight : ∀ {a b} (x : Op a b) → transform x identity ≡ identityDiamondRight x
transformIdentityRight {Empty} Noop = refl
transformIdentityRight {Empty} (InsertChar c x) = cong (insertCharDiamond₁ c) (transformIdentityRight x)
transformIdentityRight {Char a} (InsertChar c x) = cong (insertCharDiamond₁ c) (transformIdentityRight x)
transformIdentityRight {Tombstone a} (InsertChar c x) = cong (insertCharDiamond₁ c) (transformIdentityRight x)
transformIdentityRight (RetainChar x) = cong retainCharDiamond (transformIdentityRight x)
transformIdentityRight (DeleteChar x) = cong deleteCharDiamond₁ (transformIdentityRight x)
transformIdentityRight {Empty} (InsertTombstone x) = cong insertTombstoneDiamond₁ (transformIdentityRight x)
transformIdentityRight {Char a} (InsertTombstone x) = cong insertTombstoneDiamond₁ (transformIdentityRight x)
transformIdentityRight {Tombstone a} (InsertTombstone x) = cong insertTombstoneDiamond₁ (transformIdentityRight x)
transformIdentityRight {Tombstone a} (RetainTombstone x) = cong retainTombstoneDiamond (transformIdentityRight x)

identityDiamond : ∀ {a} → Diamond (identity {a}) (identity {a})
identityDiamond {a} = ⋄ a identity identity refl

identityDiamondGrid : ∀ {a b c} → (x : Op a b) → (y : Op a c) → DiamondGrid x identity y identity
identityDiamondGrid x y =
  let dt = transform x y
  in ◆ dt (identityDiamondLeft (Diamond.y′ dt)) (identityDiamondRight (Diamond.x′ dt)) identityDiamond

◆-cong : ∀ {a b₁ b₂ c₁ c₂} {x₁ : Op a b₁} {x₂ : Op b₁ b₂} {y₁ : Op a c₁} {y₂ : Op c₁ c₂}
       → {dt  : Diamond x₁ y₁} {dl  : Diamond x₂ (Diamond.y′ dt)}  {dr  : Diamond (Diamond.x′ dt)  y₂} {db  : Diamond (Diamond.x′ dl)  (Diamond.y′ dr)}
       → {dt′ : Diamond x₁ y₁} {dl′ : Diamond x₂ (Diamond.y′ dt′)} {dr′ : Diamond (Diamond.x′ dt′) y₂} {db′ : Diamond (Diamond.x′ dl′) (Diamond.y′ dr′)}
       → dt ≅ dt′ → dl ≅ dl′ → dr ≅ dr′ → db ≅ db′
       → ◆ dt dl dr db ≡ ◆ dt′ dl′ dr′ db′
◆-cong HE.refl HE.refl HE.refl HE.refl = refl

transform-cong : ∀ {a b c b′ c′} {x : Op a b} {y : Op a c} {x′ : Op a b′} {y′ : Op a c′}
               → b ≡ b′ → c ≡ c′ → x ≅ x′ → y ≅ y′ → transform x y ≅ transform x′ y′
transform-cong refl refl HE.refl HE.refl = HE.refl

transformIdentityGrid : ∀ {a b c} → (x : Op a b) → (y : Op a c)
                      → transformGrid x identity y identity ≡ identityDiamondGrid x y
transformIdentityGrid x y =
  ◆-cong HE.refl
         (HE.≡-to-≅ (transformIdentityLeft (Diamond.y′ dt)))
         (HE.≡-to-≅ (transformIdentityRight (Diamond.x′ dt)))
         (begin
            transform (Diamond.x′ dl) (Diamond.y′ dr)
              ≅⟨ transform-cong (cong Diamond.d (transformIdentityLeft (Diamond.y′ dt)))
                                (cong Diamond.d (transformIdentityRight (Diamond.x′ dt)))
                                (HE.cong Diamond.x′ (HE.≡-to-≅ (transformIdentityLeft (Diamond.y′ dt))))
                                (HE.cong Diamond.y′ (HE.≡-to-≅ (transformIdentityRight (Diamond.x′ dt)))) ⟩
            transform (identity {d₁}) (identity {d₁})
              ≡⟨ transformIdentityRight (identity {d₁}) ⟩
            identityDiamond {d₁}
          ∎)
  where dt = transform x y
        dl = transform identity (Diamond.y′ dt)
        dr = transform (Diamond.x′ dt) identity
        d₁ = Diamond.d dt
        open HE.≅-Reasoning

TransformIdentity : ∀ {a} {A : Category.Obj (Product (slice a) (slice a))}
                  → _[_≡_] (slice a) (Transform₁ (Category.id (Product (slice a) (slice a)) {A}))
                                     (Category.id (slice a) {Transform₀ A})
TransformIdentity {a} {sliceobj {b} x , sliceobj {c} y} = {!!}
{-
Transform₁ {a} {sliceobj {b₂} x₁x₂ , sliceobj {c₂} y₁y₂}
               {sliceobj {b₁} x₁ , sliceobj {c₁} y₁}
               (slicearr {x₂} e₁ , slicearr {y₂} e₂) = slicearr {h = diag₂′} (HE.≅-to-≡ eq₃)
-}
{-
  where dg = transformGrid x identity y identity
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
        -}
        {-
        .eq₃ : compose diag₁ diag₂′ ≅ diag (transform x₁x₂ y₁y₂)
        eq₃ =
          begin
            compose diag₁ diag₂′
              ≡⟨ cong (compose diag₁) (subst′-eq docCtxDecEq (Op d₁) eq₁ diag₂) ⟩
            compose diag₁ diag₂′′
              ≡⟨ sym (substCompose eq₁ diag₁ diag₂) ⟩
            subst (Op a) eq₁ (compose diag₁ diag₂)
              ≅⟨ HE.≡-subst-removable (Op a) eq₁ (compose diag₁ diag₂) ⟩
            compose diag₁ diag₂
              ≡⟨ diagCommutes dg ⟩
            diag (outerDiamond dg)
              ≅⟨ HE.cong diag (HE.≡-to-≅ (composeTransformCommutes x₁ x₂ y₁ y₂)) ⟩
            diag (transform (compose x₁ x₂) (compose y₁ y₂))
              ≅⟨ HE.cong₂ (λ x y → diag (transform x y)) (HE.≡-to-≅ e₁) (HE.≡-to-≅ e₂) ⟩
            diag (transform x₁x₂ y₁y₂)
          ∎
          where open HE.≅-Reasoning
          -}


Transform-resp-≡ : ∀ {a} {A B : Category.Obj (Product (slice a) (slice a))}
                 → {f g : Hom (Product (slice a) (slice a)) A B}
                 → _[_≡_] (Product (slice a) (slice a)) f g
                 → _[_≡_] (slice a) (Transform₁ f) (Transform₁ g)
Transform-resp-≡ {a} {A} {B} {slicearr {f₁} _ , slicearr {f₂} _}
                             {slicearr {.f₁} _ , slicearr {.f₂} _}
                             (refl , refl) = refl

Transform : ∀ {a} → Functor (Product (slice a) (slice a)) (slice a)
Transform = record
  { F₀ = Transform₀
  ; F₁ = Transform₁
  ; identity = TransformIdentity
  ; homomorphism = {!!} -- λ {a} {b} {c} {x} {y} {v} → applyHomomorphism x y v
  ; F-resp-≡ = Transform-resp-≡
  }
