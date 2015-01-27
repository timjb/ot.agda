open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Decidable equality is only a technical precondition to help deal with irrelevant propositional equality
module OTTransformFunctor (C : Set) (decEq : Decidable {A = C} _≡_) where

open import Relation.Nullary
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
