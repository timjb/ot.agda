open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Decidable equality is only a technical precondition to help deal with irrelevant propositional equality
module OTTransformGrid (C : Set) (decEq : Decidable {A = C} _≡_) where

open import Data.Nat
open import Data.Fin

open import OTCategory C
open import OTTransformCore C
open import OTTransformFunctor C decEq

data OpSeq : DocCtx → ℕ → Set where
  OSNil : ∀ {a} → OpSeq a 0
  OSCons : ∀ {a} {b} {n} → Op a b → OpSeq b n → OpSeq a (suc n)

init : ∀ {a} {n} → (m : Fin (suc n)) → OpSeq a n → OpSeq a (toℕ m)
init zero _ = OSNil
init {n = zero} (suc ())
init {n = suc n} (suc m) (OSCons op os) = OSCons op (init m os)

getCtx : ∀ {a} {n} → (i : Fin (suc n)) → OpSeq a n → DocCtx
getCtx {a = a} zero _ = a
getCtx (suc ()) OSNil
getCtx (suc i) (OSCons x os) = getCtx i os

getOp : ∀ {a} {n} → (i : Fin n) → (os : OpSeq a n) → Op (getCtx (inject₁ i) os) (getCtx (suc i) os)
getOp zero (OSCons op _) = op
getOp (suc i) (OSCons op os) = getOp i os

{-
endCtx : ∀ {a} {n} → OpSeq a n → DocCtx
endCtx (OSNil {a}) = a
endCtx (OSCons _ os) = endCtx os

composeAll′ : ∀ {a b} {n} (x : Op a b) (os : OpSeq b n) → Op a (endCtx os)
composeAll′ x OSNil = x
composeAll′ x (OSCons y os) = composeAll′ (compose x y) os

composeAll : ∀ {a} {n} (os : OpSeq a n) → Op a (endCtx os)
composeAll = composeAll′ identity

composeAll₂ : ∀ {a} {n} (os : OpSeq a n) → Op a (endCtx os)
composeAll₂ OSNil = identity
composeAll₂ (OSCons op os) = compose op (composeAll os)
-}

composeInit′ : ∀ {a b} {n} (x : Op a b) (i : Fin (suc n)) (os : OpSeq b n) → Op a (getCtx i os)
composeInit′ x zero _ = x
composeInit′ x (suc ()) OSNil
composeInit′ x (suc i) (OSCons y os) = composeInit′ (compose x y) i os

composeInit : ∀ {a} {n} (i : Fin (suc n)) (os : OpSeq a n) → Op a (getCtx i os)
composeInit = composeInit′ identity

coord : {a : DocCtx} {n m : ℕ} (xs : OpSeq a n) (ys : OpSeq a m)
      → Fin (suc n) → Fin (suc m) → DocCtx
coord xs ys i j = transform-d (composeInit i xs) (composeInit j ys)

record OpGrid {a : DocCtx} {n m : ℕ} (xs : OpSeq a n) (ys : OpSeq a m) : Set where
  constructor OG
  field
    xs′ : (i : Fin n) (j : Fin m) → Op (coord xs ys (inject₁ i) (suc j))
                                       (coord xs ys (suc i) (suc j))
    ys′ : (i : Fin n) (j : Fin m) → Op (coord xs ys (suc i) (inject₁ j))
                                       (coord xs ys (suc i) (suc j))

transform-d-identity-left : ∀ {a b} → (y : Op a b) → transform-d identity y ≡ b
transform-d-identity-left y = cong Diamond.d (transformIdentityLeft y)

transform-d-identity-right : ∀ {a b} → (x : Op a b) → transform-d x identity ≡ b
transform-d-identity-right x = cong Diamond.d (transformIdentityRight x)

getXs : {a : DocCtx} {n m : ℕ} {xs : OpSeq a n} {ys : OpSeq a m}
      → OpGrid xs ys → (i : Fin n) → (j : Fin (suc m))
      → Op (coord xs ys (inject₁ i) j) (coord xs ys (suc i) j)
getXs {xs = xs} {ys = ys} og i zero = subst₂ Op eq₁ eq₂ (getOp i xs)
  where eq₁ = sym (transform-d-identity-right (composeInit (inject₁ i) xs))
        eq₂ = sym (transform-d-identity-right (composeInit (suc i) xs))
getXs og i (suc j) = OpGrid.xs′ og i j

getYs : {a : DocCtx} {n m : ℕ} {xs : OpSeq a n} {ys : OpSeq a m}
      → OpGrid xs ys → (i : Fin (suc n)) → (j : Fin m)
      → Op (coord xs ys i (inject₁ j)) (coord xs ys i (suc j))
getYs {xs = xs} {ys = ys} og zero j = subst₂ Op eq₁ eq₂ (getOp j ys)
  where eq₁ = sym (transform-d-identity-left (composeInit (inject₁ j) ys))
        eq₂ = sym (transform-d-identity-left (composeInit (suc j) ys))
getYs og (suc i) j = OpGrid.ys′ og i j

record CommOpGrid {a : DocCtx} {n m : ℕ} (xs : OpSeq a n) (ys : OpSeq a m) : Set where
  constructor COG
  field
    og : OpGrid xs ys
    comm : (i : Fin n) (j : Fin m) → compose (getXs og i (inject₁ j)) (getYs og (suc i) j) ≡ compose (getYs og (inject₁ i) j) (getXs og i (suc j))
