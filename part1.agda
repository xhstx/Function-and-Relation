-- {-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}

open import Data.Bool using (Bool; true; false)
open import Data.Nat
open import Data.Nat.Properties using  (_≟_; <-pred; ≤-step; ≤-trans; ≤-reflexive; ≤-pred; <⇒≤; <⇒≱; ≤⇒≯; ≤∧≢⇒<; 1+n≰n; 1+n≢n; n≮n; 0<1+n; m<1+n⇒m≤n; suc-injective; ≤-refl)
open import Data.List using (List; []; _∷_; length; _++_; zip)
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; _++_; map)
open import Data.Vec.Properties using (map-∘)
open import Data.Empty
open import Data.Product hiding (map; zip)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; module ≡-Reasoning)
open import Relation.Nullary.Decidable.Core
open import Function

open ≡-Reasoning

variable
  A B C : Set
  m n k : ℕ
  b     : Bool
  x x₂  : A
  xs ys : List A

-- Part 1. Unification (need more powerful automation)
-- (1) suc n ≡ suc (suc n) can unify with () but suc (length xs) ≡ suc (suc (length xs)) cannot unify with ()
no-suc-eq : ∀ n → suc n ≡ suc (suc n) → ⊥
no-suc-eq n ()

no-suc-length-eq : ∀ (xs : List A) → suc (length xs) ≡ suc (suc (length xs)) → ⊥
no-suc-length-eq xs eq = {!   !} 

-- (2) 1 ≢ 1 will lead to successful unification
1≢1 : 1 ≢ 1 → ⊥
1≢1 neq = {!   !}

-- (3) non-equality cannot automatically unify
2≢3 : 2 ≡ 3 → ⊥
2≢3 ()

3≰2 : 3 ≤ 2 → ⊥
3≰2 (s≤s (s≤s ()))

no-n-ineq : ∀ n → suc (suc (suc n)) ≤ suc (suc n) → ⊥
no-n-ineq zero (s≤s (s≤s ()))
no-n-ineq (suc n) (s≤s (s≤s (s≤s ineq))) = ⊥-elim (1+n≰n ineq)
