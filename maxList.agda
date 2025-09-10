-- {-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}

open import Data.Bool using (Bool; true; false)
open import Data.Nat hiding (_+_)
open import Data.Nat.Properties using  (_≟_; <-pred; ≤-step; ≤-trans; ≤-reflexive; ≤-pred; <⇒≤; <⇒≱; ≤⇒≯; ≤∧≢⇒<; 1+n≰n; 1+n≢n; n≮n; 0<1+n; m<1+n⇒m≤n; suc-injective; ≤-refl)
-- open import Data.List using (List; []; _∷_; map; length; _++_)
-- open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec
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
  xs ys              : Vec A n

max : ℕ → ℕ → ℕ
max  zero    zero   = zero
max  zero   (suc n) = suc n
max (suc m)  zero   = suc m
max (suc m) (suc n) = suc (max m n)

max-lemₗ : ∀ {m n k} → k ≡ max m n → k ≡ max 0 (max m n)
max-lemₗ {zero}  {zero}  refl = refl
max-lemₗ {zero}  {suc n} refl = refl
max-lemₗ {suc m} {zero}  refl = refl
max-lemₗ {suc m} {suc n} refl = refl

max-lemᵣ : ∀ {m n k} → k ≡ max m n → k ≡ max (max m n) 0
max-lemᵣ {zero}  {zero}  refl = refl
max-lemᵣ {zero}  {suc n} refl = refl
max-lemᵣ {suc m} {zero}  refl = refl
max-lemᵣ {suc m} {suc n} refl = refl

max-lem₂ : ∀ {m n k} → max m (max n k) ≡ max (max m n) k
max-lem₂ {zero}  {zero}  {zero}  = refl
max-lem₂ {zero}  {zero}  {suc k} = refl
max-lem₂ {zero}  {suc n} {zero}  = refl
max-lem₂ {zero}  {suc n} {suc k} = refl
max-lem₂ {suc m} {zero}  {zero}  = refl
max-lem₂ {suc m} {zero}  {suc k} = refl
max-lem₂ {suc m} {suc n} {zero}  = refl
max-lem₂ {suc m} {suc n} {suc k} = cong suc max-lem₂

maxList : Vec ℕ (suc n) → ℕ
maxList (x ∷ []) = x
maxList (x ∷ xs@(x₁ ∷ _)) = max x (maxList xs)

data MaxList : Vec ℕ (suc n) → ℕ → Set where
    sin : MaxList (x ∷ []) x
    suc : ∀ {n m} {x : ℕ} {xs : Vec ℕ (suc n)}
        → MaxList xs m
        → MaxList (x ∷ xs) (max x m)

max-eq : ∀ {xs : Vec ℕ (suc n)} → MaxList xs m → MaxList xs m' → m ≡ m'
max-eq  sin      sin      = refl
max-eq (suc ml) (suc ml') = cong₂ max refl (max-eq ml ml')

max-suc : ∀ {m n} → suc (max m n) ≡ max (suc m) (suc n)
max-suc = refl

appendSpec : ∀ {xs : Vec ℕ (suc n)} {ys : Vec ℕ (suc m)} → maxList (xs ++ ys) ≡ max (maxList xs) (maxList ys)
appendSpec {xs = x ∷ []}      {ys = y ∷ []}      = refl
appendSpec {xs = x ∷ []}      {ys = y ∷ y₁ ∷ ys} = refl
appendSpec {xs = x ∷ x₁ ∷ xs} {ys = y ∷ []}      = trans (cong₂ max refl (appendSpec {xs = x₁ ∷ xs} {ys = y ∷ []})) max-lem₂
appendSpec {xs = x ∷ x₁ ∷ xs} {ys = y ∷ y₁ ∷ ys} = trans (cong₂ max refl (appendSpec {xs = x₁ ∷ xs} {ys = y ∷ y₁ ∷ ys})) max-lem₂ 

appendSpec' : ∀ {xs : Vec ℕ (suc n)} {ys : Vec ℕ (suc m)} → MaxList xs l → MaxList ys r → MaxList (xs ++ ys) k → k ≡ max l r
appendSpec'  sin      sin      (suc sin)        = refl
appendSpec'  sin     (suc ml') (suc (suc ml'')) = cong₂ max refl (cong₂ max refl (max-eq ml'' ml')) -- different : need to prove that k ≡ r
appendSpec' (suc ml)  sin      (suc ml'')       = trans (cong₂ max refl (appendSpec' ml sin ml'')) max-lem₂
appendSpec' (suc ml) (suc ml') (suc ml'')       = trans (cong₂ max refl (appendSpec' ml (suc ml') ml'')) max-lem₂

mapAppendSpec : ∀ {xs : Vec ℕ (suc n)} {ys : Vec ℕ (suc m)} → suc (maxList (xs ++ ys)) ≡ maxList (map suc (xs ++ ys))
mapAppendSpec {xs = x ∷ []}      {ys = y ∷ []}         = refl
mapAppendSpec {xs = x ∷ []}      {ys = y ∷ ys@(_ ∷ _)} = trans (trans (cong₂ max (refl {x = suc x}) (mapAppendSpec {xs = y ∷ []} {ys = ys})) max-lem₂) (sym max-lem₂)
mapAppendSpec {xs = x ∷ x₁ ∷ xs} {ys = y ∷ []}         = trans max-suc (cong₂ max (refl {x = suc x}) (mapAppendSpec {xs = x₁ ∷ xs} {ys = y ∷ []}))
mapAppendSpec {xs = x ∷ x₁ ∷ xs} {ys = y ∷ y₁ ∷ ys}    = trans max-suc (cong₂ max (refl {x = suc x}) (mapAppendSpec {xs = x₁ ∷ xs} {ys = y ∷ y₁ ∷ ys}))

mapAppendSpec' : ∀ {xs : Vec ℕ (suc n)} {ys : Vec ℕ (suc m)} → MaxList xs l → MaxList ys r → MaxList (xs ++ ys) k → MaxList (map suc (xs ++ ys)) (suc k)
mapAppendSpec'                                     sin      sin      (suc sin) = suc sin
mapAppendSpec' {xs = x ∷ []} {ys = y ∷ ys@(_ ∷ _)} sin     (suc ml') (suc s)   = suc (mapAppendSpec' {xs = y ∷ []} {ys = ys} sin ml' s)
mapAppendSpec'                                    (suc ml)  sin      (suc s)   = suc (mapAppendSpec' ml sin s)
mapAppendSpec'                                    (suc ml) (suc ml') (suc s)   = suc (mapAppendSpec' ml (suc ml') s)



-- In the maxList case
-- For appendSpec, the structure (case split) of proof for function and relation are same.
-- The only difference is in the second case, which the function ver. can unify with refl (automatically) while the relation ver. need to prove that k ≡ r.
-- For mapAppendSpec, the structure of proof for function and relation are also same.
-- However, the relation ver. can be proof only by doing induction on the indexed data type and thus finish with recursive call on data type,
-- while the relation ver. still need to done with the same pattern of the proof of appendSpec.
-- These observation may indicate that relation may be a better choice in a complicated spec. but no obvious effect on the simple one in compare with function.