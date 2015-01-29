module SubstIrrelevant where

open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality using (_≅_)
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Nullary

-- Irrelevant in ⊥
⊥-elim′ : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim′ ()
 
getPrf : {A : Set} → .A → Dec A → A
getPrf a (yes p) = p
getPrf a (no ¬p) = ⊥-elim′ (¬p a)

-- Uniqueness of identity proofs
uip : {A : Set} {a b : A} (eq₁ : a ≡ b) (eq₂ : a ≡ b) → eq₁ ≡ eq₂
uip refl refl = refl

subst′ : {A : Set} {a b : A} (de : Decidable {A = A} _≡_) (P : A → Set) → .(a ≡ b) → P a → P b
subst′ {A} {a} {b} de P eq = subst P (getPrf eq (de a b))

subst′-eq : {A : Set} {a b : A} (de : Decidable {A = A} _≡_) (P : A → Set) → (eq : (a ≡ b)) → (v : P a)
          → subst′ de P eq v ≡ subst P eq v
subst′-eq {A} {a} {b} de P eq v with de a b
... | yes eq₂ = cong (λ eq₃ → subst P eq₃ v) (uip eq₂ eq)
... | no ¬p = ⊥-elim′ (¬p eq)

subst₂′ : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} (deA : Decidable {A = A} _≡_) (deB : Decidable {A = B} _≡_) (P : A → B → Set)
        → .(a₁ ≡ a₂) → .(b₁ ≡ b₂) → P a₁ b₁ → P a₂ b₂
subst₂′ {A} {B} {a₁} {a₂} {b₁} {b₂} decA decB P eqa eqb v = subst′ decA (λ a → P a b₂) eqa (subst′ decB (P a₁) eqb v)

≡-subst′-removable : ∀ {A : Set} (de : Decidable {A = A} _≡_)
                    (P : A → Set) {x y} (eq : x ≡ y) z →
                    subst′ de P eq z ≅ z
≡-subst′-removable de P eq v = HE.trans (HE.≡-to-≅ (subst′-eq de P eq v))
                                        (HE.≡-subst-removable P eq v)
