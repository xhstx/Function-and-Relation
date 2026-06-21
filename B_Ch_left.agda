-- {-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}

open import Data.Bool using (Bool; true; false)
open import Data.Nat
open import Data.Nat.Properties using  (_≟_; <-pred; ≤-step; ≤-trans; ≤-reflexive; ≤-pred; <⇒≤; <⇒≱; ≤⇒≯; ≤∧≢⇒<; 1+n≰n; 1+n≢n; n≮n; 0<1+n; m<1+n⇒m≤n; suc-injective; ≤-refl)
-- open import Data.List using (List; []; _∷_; map; length; _++_)
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
  m n k : ℕ
  b     : Bool
  x x₂  : A
  xs ys : Vec A n

m≤n⇒m<1+n : ∀ {m n} → m ≤ n → m < suc n
m≤n⇒m<1+n {zero} {n} m≤n = 0<1+n
m≤n⇒m<1+n {suc m} {suc n} (s≤s m≤n) = s≤s (m≤n⇒m<1+n m≤n)

data BTree (A : Set) : (n k : ℕ) → Set where
  tip0 : A                               → BTree A n 0
  tipN : A                               → BTree A (suc k) (suc k)
  node : BTree A n k → BTree A n (suc k) → BTree A (suc n) (suc k)

-- Properties of BTree
bounded : BTree A n k → k ≤ n
bounded (tip0 _)  = z≤n
bounded (tipN _)  = ≤-refl
bounded (node t u) = s≤s (bounded t)

unbounded : BTree A k (suc k) → ⊥
unbounded (node t u) = unbounded t

onlyTipN : {A : Set} {n : ℕ} → (T : BTree A (suc n) (suc n)) → Σ[ x ∈ A ] (T ≡ tipN x)
onlyTipN (tipN x) = x , refl
onlyTipN (node t u) = ⊥-elim (unbounded u)

leftSub : {A : Set} {n k : ℕ} → BTree A (suc n) (suc k) → BTree A n k
leftSub (tipN x)   = {!   !}
leftSub (node t _) = t

rightSub : {A : Set} {n k : ℕ} → BTree A (suc n) (suc k) → BTree A n (suc k)
rightSub (tipN x)   = {!   !}
rightSub (node _ u) = u

-- Functions for BTree
mapB : (A → B) → BTree A n k → BTree B n k
mapB f (tip0 x)   = tip0 (f x)
mapB f (tipN x)   = tipN (f x)
mapB f (node t u) = node (mapB f t) (mapB f u)

mapB-∘ : ∀ {A B C} (f : B → C) (g : A → B) (t : BTree A n k) → mapB f (mapB g t) ≡ mapB (f ∘ g) t
mapB-∘ f g (tip0 x)   = refl
mapB-∘ f g (tipN x)   = refl
mapB-∘ f g (node t u) = cong₂ node (mapB-∘ f g t) (mapB-∘ f g u)

postulate
  mapB-app : ∀ {A B} {f g : A → B} {t : BTree A n k} → (∀ x → f x ≡ g x) → mapB f t ≡ mapB g t

unTip : BTree A (suc n) (suc n) → A
unTip (tipN x) = x
unTip (node t u) = ⊥-elim (unbounded u)

zipBW : (A → B → C) → BTree A n k → BTree B n k → BTree C n k
zipBW f (tip0 x) (tip0 y) = tip0 (f x y)
zipBW f (tipN x) (tipN y) = tipN (f x y)
zipBW f (tipN x) (node t u) = ⊥-elim (unbounded u)
zipBW f (node t u) (tipN x) = ⊥-elim (unbounded u)
zipBW f (node t u) (node t' u') = node (zipBW f t t') (zipBW f u u')

variable
  t t' u : BTree A n k

data Ch {A : Set} : (k : ℕ) → Vec A n → BTree (Vec A k) n k → Set where
  zero : Ch zero xs (tip0 [])
  suc≡ : Ch (suc k) xs (tipN xs)
  suc≢ : {xs : Vec A n}
       → suc k ≢ suc n
       → Ch k xs t
       → Ch (suc k) xs u
       → Ch (suc k) (x ∷ xs) (node (mapB (x ∷_) t) u)

subs : Vec A (suc n) → Vec (Vec A n) (suc n)
subs (x ∷ []) = [] ∷ []
subs (x ∷ xs@(y ∷ ys)) = (map (x ∷_) (subs xs)) ∷ʳ xs

subs-cons1 : {x : A} (xs : Vec A 1) → (λ q → (x ∷ []) ∷ q ∷ []) xs ≡ (subs ∘ (x ∷_)) xs
subs-cons1 (x ∷ []) = refl

lemma₀ : ∀ {k : ℕ} {xs : Vec A n} → k ≤ n → k ≢ n → suc k ≤ n
lemma₀ k≤len k≢len = ≤∧≢⇒< k≤len k≢len

-- lemma₁ : ∀ {k n : ℕ} {x : A} {xs : Vec A n} → k ≡ n → BTree (Vec A (suc k)) (suc n) (suc k)


ch : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vec A n) → (k≤len : k ≤ n) → BTree (Vec A k) n k
ch zero xs k≤len = tip0 []
ch (suc k) (x ∷ xs) k≤len with k ≟ length xs
... | yes refl    = tipN (x ∷ xs)
... | no  k≢len   = node (mapB (x ∷_) (ch k xs (≤-pred k≤len))) (ch (suc k) xs (lemma₀ {_} {_} {k} {xs} (≤-pred k≤len) k≢len))

up : {k : ℕ} → {z≤k : 0 < k} → {k < n} → BTree A n k → BTree (Vec A (suc k)) n (suc k) 
up {k = suc k}       {0<k} {k<n} (tipN x)                             = ⊥-elim (n≮n (suc k) k<n)
up                   {0<k} {k<n} (node (tip0 x) (tipN y))             = tipN (x ∷ y ∷ [])
up {_} {_} {_}       {0<k} {k<n} (node (tip0 x) u@(node x₀ x₁)) = node (mapB (λ q → x ∷ q ∷ []) u) (up {_} {_} {_} {0<k} {m≤n⇒m<1+n (bounded x₁)} u)
up {k = suc (suc k)} {0<k} {k<n} (node (tipN x) u)                    = ⊥-elim (n≮n (suc (suc k)) k<n)
up {_} {_} {_}       {0<k} {k<n} (node t@(node _ _) (tipN y))         = tipN ((unTip (up {_} {_} {_} {0<1+n} {(<-pred k<n)} t)) ∷ʳ y)
up {_} {_} {_}       {0<k} {k<n} (node t@(node _ _) u@(node _ u'))    = node (zipBW (_∷ʳ_) (up {_} {_} {_} {0<1+n} {(s<s⁻¹ k<n)} t) u) (up {_} {_} {_} {0<1+n} {(m≤n⇒m<1+n (bounded u'))} u)

-- upSpec : {k : ℕ} {xs : Vec A n} {t : BTree (Vec A k) n k} {t' : BTree (Vec A (suc k)) n (suc k)}
--        → Ch k xs t → Ch (suc k) xs t' → 2 ≤ suc k → (suc-k≤len : suc k ≤ n) → up t ≡ mapB subs t'
-- -- left : tip0 
-- upSpec                      zero                                              ch'              (s≤s ()) suc-k≤len -- In B_Ch_right, this case will be split into 2 cases (1 & 5).
-- -- left : tipN → up case 1.
-- upSpec                      suc≡                                              ch'               2≤suc-k suc-k≤len = ⊥-elim (1+n≰n suc-k≤len) -- Same with B_Ch_right case 6.
-- -- left : node t u → def. of up
-- -- node tip0 tipN → up case 2.
-- upSpec {xs = x₀ ∷ x₁ ∷ []} (suc≢ x  zero              suc≡)                   suc≡              2≤suc-k suc-k≤len = refl -- Same with B_Ch_right case 2.
-- upSpec                     (suc≢ x  zero              suc≡)                  (suc≢ x₁ ch' ch'') 2≤suc-k suc-k≤len = ⊥-elim (x₁ refl) -- Same with B_Ch_right case 7.
-- -- node tip0 (node t u) → up case 3.
-- upSpec                     (suc≢ x  zero              ch@(suc≢ x₁ zero ch₃)) (suc≢ x₂ ch' ch'') 2≤suc-k suc-k≤len = cong₂ node {!   !}  (upSpec ch ch'' ≤-refl (m<1+n⇒m≤n (≤∧≢⇒< suc-k≤len x₂))) -- Same with B_Ch_right case 8.
-- -- node tipN (node t u) → up case 4.
-- upSpec                     (suc≢ x  suc≡             (suc≢ x₁ ch₂ ch₃))       ch'               2≤suc-k suc-k≤len = ⊥-elim (1+n≰n suc-k≤len) -- Same with B_Ch_right case 9.
-- -- node (node t u) tipN → up case 5.
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃)  suc≡)                   suc≡              2≤suc-k suc-k≤len = cong tipN {!   !} -- Same with B_Ch_right case 3.
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃)  suc≡)                  (suc≢ x₂ ch' ch'') 2≤suc-k suc-k≤len = ⊥-elim (x₂ refl) -- Same with B_Ch_right case 10. 
-- -- node (node t u) (node t' u') → up case 6.
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃) (suc≢ x₂ ch₂ ch₄))       suc≡              2≤suc-k suc-k≤len = ⊥-elim (x₂ refl) -- Same with B_Ch_right case 4.
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃)  ch@(suc≢ x₂ ch₂ ch₄))  (suc≢ x₃ ch' ch'') 2≤suc-k suc-k≤len = cong₂ node {!   !} (upSpec ch ch'' (s≤s (s≤s z≤n)) (m<1+n⇒m≤n (≤∧≢⇒< suc-k≤len x₃))) -- Same with B_Ch_right case 11.