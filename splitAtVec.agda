-- {-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}
{-# OPTIONS --rewriting #-}

open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat
open import Data.Nat.Properties using  (_≟_; <-pred; ≤-step; ≤-trans; ≤-reflexive; ≤-pred; <⇒≤; <⇒≱; ≤⇒≯; ≤∧≢⇒<; 1+n≰n; 1+n≢n; n≮n; 0<1+n; m<1+n⇒m≤n; suc-injective; ≤-refl)
{-# REWRITE Data.Nat.Properties.+-identityʳ #-}
-- open import Data.List using (List; []; _∷_; map; length; _++_)
-- open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec hiding (split; init; reverse)
open import Data.Vec.Properties
-- using (Vec; []; _∷_; _++_; map)
open import Data.Vec.Properties using (map-∘)
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; module ≡-Reasoning)
open import Relation.Nullary.Decidable.Core
open import Function

open ≡-Reasoning

variable
  A B C : Set
  m m' n n' k k' l r : ℕ
  b                  : Bool
  x                  : A
  xs ys zs           : Vec A n

split : ∀ m {n} → (xs : Vec A (m + n)) → Vec A m × Vec A n
split  zero    xs      = [] , xs
split (suc m) (x ∷ xs) = let (ys , zs) = split m xs in ((x ∷ ys) , zs)

data Split {A : Set} : (m : ℕ) {n : ℕ} → Vec A (m + n) → Vec A m → Vec A n → Set where
    init : ∀ {n} {xs : Vec A n} → Split 0 xs [] xs
    step : ∀ {m n x} {xs : Vec A (m + n)} {ys : Vec A m} {zs : Vec A n}
         → Split  m       xs       ys      zs
         → Split (suc m) (x ∷ xs) (x ∷ ys) zs


reconstructSpec : ∀ m {n} (xs : Vec A (m + n)) → let (ys , zs) = split m {n = n} xs in ys ++ zs ≡ xs
reconstructSpec  zero    xs      = refl
reconstructSpec (suc m) (x ∷ xs) = cong (x ∷_) (reconstructSpec m xs)

reconstructSpec' : ∀ {m n ys zs} {xs : Vec A (m + n)} → Split m {n = n} xs ys zs → Split m (ys ++ zs) ys zs
reconstructSpec'  init     = init
reconstructSpec' (step sp) = step (reconstructSpec' sp)

mapSpec : ∀ (f : A → B) m {n} (xs : Vec A (m + n)) → let (ys , zs) = split m {n = n} xs in split m (map f xs) ≡ (map f ys , map f zs)
mapSpec f  zero    xs      = refl
mapSpec f (suc m) (x ∷ xs) = cong (λ (p : _ × _) → (f x ∷ proj₁ p , proj₂ p)) (mapSpec f m xs)

mapSpec' : ∀ {f : A → B} {m n ys zs} {xs : Vec A (m + n)} → Split m {n = n} xs ys zs → Split m (map f xs) (map f ys) (map f zs)
mapSpec'  init     = init
mapSpec' (step sp) = step (mapSpec' sp)

reverse : ∀ {m n} (xs : Vec A (m + n)) → Vec A (n + m)
reverse {m = zero}               []       = []
reverse {m = zero}  {n = suc n} (x ∷ xs) = reverse {m = zero} {n = n} xs ∷ʳ x 
reverse {m = suc m} {n = zero}  (x ∷ xs) = reverse {m = m} {n = zero} xs ∷ʳ x
reverse {m = suc m} {n = suc n} (x ∷ xs) = let (ys , zs) = split m {n = suc n} xs in (reverse {m = zero} {n = n} (proj₂ (split 1 {n = n} zs)) ++ ((proj₁ (split 1 {n = n} zs)) ++ reverse {m = m} {n = zero} ys)) ∷ʳ x -- let (ys , zs) = split m {n = suc n} xs in reverse {m = zero} {n = suc n} zs ++ (reverse {m = m} {n = zero} ys ∷ʳ x)

lemma₀ : ∀ {n} (xs : Vec A n) → reverse {m = zero} {n = n} xs ≡ drop n (reverse {m = zero} {n = n} xs) ++ take n {n = zero} (reverse {m = zero} {n = n} xs)
lemma₀ []       = refl
lemma₀ (x ∷ xs) = {! cong (_∷ʳ x) (lemma₀ xs)  !}

reverseSpec : ∀ m {n} (xs : Vec A (m + n)) → let (ys , zs) = split m {n = n} xs in reverse {m = m} {n = zero} ys ++ reverse {m = zero} {n = n} zs ≡ drop n (reverse {m = m} {n = n} xs) ++ take n {n = m} (reverse {m = m} {n = n} xs)
reverseSpec  zero    []      = refl
reverseSpec  zero   (x ∷ xs) = rotate-reverse (x ∷ xs)
reverseSpec (suc m) (x ∷ xs) = {! reverseSpec m xs  !}

reverseSpec' : ∀ {m n ys zs} {xs : Vec A (m + n)} → Split m {n = n} xs ys zs → reverse {m = m} {n = zero} ys ++ reverse {m = zero} {n = n} zs ≡ drop n (reverse {m = m} {n = n} xs) ++ take n {n = m} (reverse {m = m} {n = n} xs)
reverseSpec'             {n = n}               {xs = xs}      init     = lemma₀ xs
reverseSpec' {m = suc m} {n = n} {ys = x ∷ ys} {xs = x ∷ xs} (step sp) = {!    !}