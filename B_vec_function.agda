-- {-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}

open import Data.Bool using (Bool; true; false)
open import Data.Nat
open import Data.Nat.Properties using  (_≟_; <-pred; ≤-step; ≤-trans; ≤-reflexive; ≤-pred; <⇒≤; <⇒≱; ≤⇒≯; ≤∧≢⇒<; 1+n≰n; 1+n≢n; n≮n; 0<1+n; suc-injective; ≤-refl; ≤-<-trans)
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
m≤n⇒m<1+n {zero}  {n}      m≤n      = 0<1+n
m≤n⇒m<1+n {suc m} {suc n} (s≤s m≤n) = s≤s (m≤n⇒m<1+n m≤n)

1+m≤n⇒m<n : ∀ {m n} → suc m ≤ n → m < n
1+m≤n⇒m<n {zero}  {n}      1+m≤n      = 1+m≤n
1+m≤n⇒m<n {suc m} {suc n} (s≤s 1+m≤n) = m≤n⇒m<1+n 1+m≤n

data BTree (A : Set) : (n k : ℕ) → Set where
  tip0 : A                               → BTree A  n       0
  tipN : A                               → BTree A (suc k) (suc k)
  node : BTree A n k → BTree A n (suc k) → BTree A (suc n) (suc k)

-- Properties of BTree
bounded : BTree A n k → k ≤ n
bounded (tip0 _)   = z≤n
bounded (tipN _)   = ≤-refl
bounded (node t u) = s≤s (bounded t)

unbounded : BTree A k (suc k) → ⊥
unbounded (node t u) = unbounded t

onlyTipN : {A : Set} {n : ℕ} → (T : BTree A (suc n) (suc n)) → Σ[ x ∈ A ] (T ≡ tipN x)
onlyTipN (tipN x)   = x , refl
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
unTip (tipN x)   = x
unTip (node t u) = ⊥-elim (unbounded u)

zipBW : (A → B → C) → BTree A n k → BTree B n k → BTree C n k
zipBW f (tip0 x)   (tip0 y)     = tip0 (f x y)
zipBW f (tipN x)   (tipN y)     = tipN (f x y)
zipBW f (tipN x)   (node t u)   = ⊥-elim (unbounded u)
zipBW f (node t u) (tipN x)     = ⊥-elim (unbounded u)
zipBW f (node t u) (node t' u') = node (zipBW f t t') (zipBW f u u')

variable
  t t' u : BTree A n k

data Ch {A : Set} : ℕ → Vec A n → BTree (Vec A k) n k → Set where
  zero : Ch zero xs (tip0 [])
  suc≡ : Ch (suc k) xs (tipN xs)
  suc≢ : {xs : Vec A n}
       → suc k ≢ suc n
       → Ch k xs t
       → Ch (suc k) xs u
       → Ch (suc k) (x ∷ xs) (node (mapB (x ∷_) t) u)

unboundedCh : ∀ {t : BTree (Vec A (suc n)) n (suc n)} → Ch k xs t  → ⊥
unboundedCh (suc≢ {t = t} x ch ch₁) = unbounded t

subs : Vec A (suc n) → Vec (Vec A n) (suc n)
subs (x ∷ [])          = [] ∷ []
subs (x ∷ xs@(y ∷ ys)) = (map (x ∷_) (subs xs)) ∷ʳ xs

subs-cons1 : {x : A} (xs : Vec A 1) → (λ q → (x ∷ []) ∷ q ∷ []) xs ≡ (subs ∘ (x ∷_)) xs
subs-cons1 (x ∷ []) = refl

lemma₀ : ∀ {k : ℕ} {xs : Vec A n} → k ≤ n → k ≢ n → suc k ≤ n
lemma₀ k≤len k≢len = ≤∧≢⇒< k≤len k≢len

ch : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vec A n) → (k≤len : k ≤ n) → BTree (Vec A k) n k
ch zero xs k≤len = tip0 []
ch (suc k) (x ∷ xs) k≤len with k ≟ length xs
... | yes refl   = tipN (x ∷ xs)
... | no  k≢len  = node (mapB (x ∷_) (ch k xs (≤-pred k≤len))) (ch (suc k) xs (lemma₀ {_} {_} {k} {xs} (≤-pred k≤len) k≢len))

up : {k : ℕ} → {0 < k} → {k < n} → BTree A n k → BTree (Vec A (suc k)) n (suc k)
up {_} {_} {_} {()} {k<n} (tip0 x)
up {k = suc k}       {0<k} {k<n} (tipN x)                          = {!   !} 
up                   {0<k} {k<n} (node (tip0 x) (tipN y))          = tipN (x ∷ y ∷ [])
up {_} {_} {_}       {0<k} {k<n} (node (tip0 x) u@(node _ u'))     = node (mapB (λ q → x ∷ q ∷ []) u) (up {_} {_} {_} {0<k} { m≤n⇒m<1+n (bounded u') } u)
up {k = suc (suc k)} {0<k} {k<n} (node (tipN x) u)                 = ⊥-elim (n≮n (suc (suc k)) k<n)
up {_} {_} {_}       {0<k} {k<n} (node t@(node _ _) (tipN y))      = tipN ((unTip (up {_} {_} {_} {0<1+n} {(<-pred k<n)} t)) ∷ʳ y)
up {_} {_} {_}       {0<k} {k<n} (node t@(node _ _) u@(node _ u')) = node (zipBW (_∷ʳ_) (up {_} {_} {_} {0<1+n} {(s<s⁻¹ k<n)} t) u) (up {_} {_} {_} {0<1+n} {(m≤n⇒m<1+n (bounded u'))} u)

up' : {n k : ℕ} → {0 < k} → {k < n} → BTree A n k → BTree (Vec A (suc k)) n (suc k)
up' {_} {n} {zero} {()} {k<n} t
up' {_} {zero} {suc k} {0<k} {k<n} ()
up' {_} {suc n} {suc .n} {0<k} {k<n} (tipN x) = {!   !}
up' {_} {suc .1} {suc .0} {0<k} {k<n} (node (tip0 x) (tipN x₁)) = {!   !}
up' {_} {suc .(suc _)} {suc .0} {0<k} {k<n} (node (tip0 x) (node u u₁)) = {!   !}
up' {_} {suc .(suc _)} {suc .(suc _)} {0<k} {k<n} (node (tipN x) u) = {!   !}
up' {_} {suc .(2+ _)} {suc .(suc _)} {0<k} {k<n} (node (node t t₁) (tipN x)) = {!   !}
up' {_} {suc .(suc _)} {suc .(suc _)} {0<k} {k<n} (node (node t t₁) (node u u₁)) = {!   !}

-- upSpec : {k : ℕ} {xs : Vec A n} {t : BTree (Vec A k) n k} {t' : BTree (Vec A (suc k)) n (suc k)}
--        → Ch k xs t → Ch (suc k) xs t' → (2≤suc-k : 2 ≤ suc k) → (suc-k≤len : suc k < suc n) → up {_} {_} {_} {1+m≤n⇒m<n (≤-pred 2≤suc-k)} {<-pred suc-k≤len} t ≡ mapB subs t'
-- upSpec {k = zero}        {xs = xs}                     ch                                            ch'              (s≤s ())  suc-k≤len -- B_Ch_left case 1.
-- upSpec {k = suc k}       {xs = x ∷ []}                 ch                                            ch'               2≤suc-k (s≤s (s≤s ()))
-- upSpec {k = suc zero}    {xs = x ∷ x₁ ∷ []}           (suc≢ x₂  zero              suc≡)              suc≡              2≤suc-k  suc-k≤len           = refl -- B_Ch_left case 3. 
-- upSpec {k = suc zero}    {xs = x ∷ x₁ ∷ []}           (suc≢ x₂  zero             (suc≢ x₃ ch₂ ch₃))  suc≡              2≤suc-k  suc-k≤len           = ⊥-elim (x₃ refl)
-- upSpec {k = 2+ k}        {xs = x ∷ x₁ ∷ xs}           (suc≢ x₂ (suc≢ x₃ ch₁ ch₂)  suc≡)              suc≡              2≤suc-k  suc-k≤len           = {!   !} -- B_Ch_left case 7.
-- upSpec {k = 2+ k}        {xs = x ∷ x₁ ∷ xs}           (suc≢ x₂  ch₁              (suc≢ x₃ ch₂ ch₃))  suc≡              2≤suc-k  suc-k≤len           = ⊥-elim (x₃ refl) -- B_Ch_left case 9.
-- upSpec {k = suc zero}    {xs = x ∷ x₁ ∷ []}            ch                                           (suc≢ x₂ ch' ch'') 2≤suc-k  suc-k≤len           = ⊥-elim (x₂ refl) -- B_Ch_left case 4.
-- upSpec {k = 2+ k}        {xs = x ∷ x₁ ∷ []}            ch                                           (suc≢ x₂ ch' ch'') 2≤suc-k (s≤s (s≤s (s≤s ())))
-- upSpec {k = suc zero}    {xs = x ∷ x₁ ∷ x₃ ∷ xs}      (suc≢ x₄  zero             (suc≢ x₅ ch₂ ch₃)) (suc≢ x₂ ch' ch'') 2≤suc-k  suc-k≤len           = {!   !} -- B_Ch_left case 5.
-- upSpec {k = 2+ .(suc _)} {xs = x ∷ x₁ ∷ x₃ ∷ xs}       suc≡                                         (suc≢ x₂ ch' ch'') 2≤suc-k  suc-k≤len           = ⊥-elim (1+n≰n suc-k≤len) -- B_Ch_left case 2.
-- upSpec {k = 2+ zero}     {xs = x ∷ x₁ ∷ x₃ ∷ []}      (suc≢ x₄  ch₁               ch₂)              (suc≢ x₂ ch' ch'') 2≤suc-k  suc-k≤len           = ⊥-elim (x₂ refl)
-- upSpec {k = 2+ (suc k)}  {xs = x ∷ x₁ ∷ x₃ ∷ []}      (suc≢ x₄  ch₁               ch₂)              (suc≢ x₂ ch' ch'') 2≤suc-k (s≤s (s≤s (s≤s (s≤s ()))))
-- upSpec {k = 2+ .(suc _)} {xs = x ∷ x₁ ∷ x₃ ∷ x₅ ∷ xs} (suc≢ x₄  ch₁               suc≡)             (suc≢ x₂ ch' ch'') 2≤suc-k  suc-k≤len           = ⊥-elim (x₂ refl) -- B_Ch_left case 8.
-- upSpec {k = 2+ .(2+ _)}  {xs = x ∷ x₁ ∷ x₃ ∷ x₅ ∷ xs} (suc≢ x₄  suc≡             (suc≢ x₆ ch₂ ch₃)) (suc≢ x₂ ch' ch'') 2≤suc-k  suc-k≤len           = ⊥-elim (1+n≰n suc-k≤len) -- B_Ch_left case 6.
-- upSpec {k = 2+ k}        {xs = x ∷ x₁ ∷ x₃ ∷ x₅ ∷ xs} (suc≢ x₄ (suc≢ x₇ ch₁ ch₄) (suc≢ x₆ ch₂ ch₃)) (suc≢ x₂ ch' ch'') 2≤suc-k  suc-k≤len           = {!   !} -- B_Ch_left case 10.



{-

-- perties of Ch
ch-to-tree : {tree : BTree (Vec A k) n k} → Ch k xs tree → BTree (Vec A k) n k  
ch-to-tree {tree = tree} _ = tree

tree-eq : Ch m xs t → Ch n ys t' → (m≡n : m ≡ n) → (xs≡ys : xs ≡ ys) → t ≡ t'
tree-eq zero            zero               m≡n xs≡ys = refl
tree-eq (suc≡ x)        (suc≡ x₁)          m≡n xs≡ys = cong tipN xs≡ys
tree-eq (suc≡ x)        (suc≢ x₁ ch' ch'') m≡n xs≡ys = ⊥-elim {!   !}
tree-eq (suc≢ x ch ch₁) (suc≡ x₁)          m≡n xs≡ys = ⊥-elim {!   !}
tree-eq (suc≢ x ch ch₁) (suc≢ x₁ ch' ch'') m≡n xs≡ys = cong₂ node {!    !} (tree-eq ch₁ ch'' m≡n {!   !})

-- Proof of upSpec

postulate
  up-natural : ∀ {A} (f : A → B) {t : BTree A n k} → up (mapB f t) ≡ mapB (map f) (up t)
  -- For Case 3.2 (lemma 4.4)
  lemma₄₄ : ∀ {t : BTree (Vec A (suc k)) n (suc k)} → {x : A} → zipBW _∷ʳ_ (mapB (map (x ∷_)) (mapB subs t)) t ≡ mapB subs (mapB (x ∷_) t)
  map-consr : ∀ {A} (f : A → B) → {x : A} {xs : Vec A n} → map f xs ∷ʳ f x ≡ map f (xs ∷ʳ x) 
  -- map-consr f {x} {[]}      = refl
  -- map-consr f {x} {x₀ ∷ xs} = cong ((f x₀) ∷_) (map-consr f {x} {xs})

-- -- -- Case 1. length xs ≡ 2
-- upSpec {xs = x₀ ∷ x₁ ∷ []}                                   (suc≢ x₂ zero (suc≡ x₃))                                (suc≡ x)                           2≤1+k suc-k≤len = refl
-- -- Case 2. length xs > 2, suc k ≡ length xs
-- -- Need to split into 2 cases:
-- -- (1) t = node (tip0 _) (tipN _)
-- upSpec {xs = x₀ ∷ x₁ ∷ x₂ ∷ []}                              (suc≢ x₆ (suc≢ x₄ zero (suc≡ x₅)) (suc≡ x₃))            (suc≡ x)                           2≤1+k suc-k≤len = refl
-- -- (2) t = node (node _ _) (tipN _)
-- upSpec {xs = x₀ ∷ x₁ ∷ x₂ ∷ xs} {t = node t (tipN (x₁ ∷ _))} (suc≢ x₆ (suc≢ x₄ ch@(suc≢ _ _ _) (suc≡ x₅)) (suc≡ x₃)) (suc≡ x)                           2≤1+k suc-k≤len =
-- ong tipN (cong (_∷ʳ (x₁ ∷ x₂ ∷ xs))
--  (begin
--       unTip (up t)
--        ≡⟨ cong unTip (proj₂ (onlyTipN (up t))) ⟩ 
--       (unTip (up (leftSub t))) ∷ʳ (x₀ ∷ x₂ ∷ xs)
--         ≡⟨ trans
--             (cong (_∷ʳ (x₀ ∷ x₂ ∷ xs)) (cong unTip (cong up (mapB-∘ (x₀ ∷_) (x₁ ∷_) (ch-to-tree ch))))) 
--             (trans
--               (cong (_∷ʳ (x₀ ∷ x₂ ∷ xs)) (cong unTip (up-natural {_} ((x₀ ∷_) ∘ (x₁ ∷_)) {ch-to-tree ch})))
--               (cong (_∷ʳ (x₀ ∷ x₂ ∷ xs)) (cong unTip (cong (mapB (map ((x₀ ∷_) ∘ (x₁ ∷_)))) (upSpec ch (suc≡ x₅) {!  !} ≤-refl))))) ⟩  
--       (unTip (mapB (map ((x₀ ∷_) ∘ (x₁ ∷_))) (tipN (subs (x₂ ∷ xs))))) ∷ʳ (x₀ ∷ x₂ ∷ xs)
--         ≡⟨ cong (_∷ʳ (x₀ ∷ x₂ ∷ xs)) (map-∘ (x₀ ∷_) (x₁ ∷_) (subs (x₂ ∷ xs))) ⟩ 
--       map (x₀ ∷_) (map (x₁ ∷_) (subs (x₂ ∷ xs))) ∷ʳ (x₀ ∷ (x₂ ∷ xs))
--         ≡⟨ map-consr (x₀ ∷_) {x₂ ∷ xs} {map (x₁ ∷_) (subs (x₂ ∷ xs))} ⟩ 
--       map (x₀ ∷_) (map (x₁ ∷_) (subs (x₂ ∷ xs)) ∷ʳ (x₂ ∷ xs)) ∎ ))
-- -- Case 3. length xs > 2, suc k < length xs
-- -- Case 3.1. k ≡ 0
-- upSpec {xs = x₀ ∷ x₁ ∷ x₂ ∷ xs} {t = t}                      (suc≢ x₄ zero ch@(suc≢ x₃ zero ch₃))                    (suc≢ x (suc≢ x₅ zero ch''') ch'') 2≤1+k suc-k≤len =
--   cong₂ node (cong₂ node refl (trans (cong (mapB (λ q → (x₀ ∷ []) ∷ q ∷ [])) (tree-eq ch₃ ch''' refl refl)) (trans (mapB-app subs-cons1) (sym (mapB-∘ subs (x₀ ∷_) (ch-to-tree ch''')))))) (upSpec ch ch'' 2≤1+k (s≤s (s≤s z≤n)))
-- -- Case 3.2. k > 0
-- upSpec {xs = x₀ ∷ x₁ ∷ x₂ ∷ xs} {t = t}                      (suc≢ x₃ ch₁ ch₂)                                       (suc≢ x ch' ch'')                  2≤1+k suc-k≤len =
--   begin 
--     up t
--      ≡⟨ {!   !} ⟩ 
--     node (zipBW (_∷ʳ_) (up (leftSub t)) (rightSub t)) (up (rightSub t))
--      ≡⟨ cong₂ node (cong (λ q → zipBW (_∷ʳ_) q (rightSub t)) (up-natural (x₀ ∷_) {t = ch-to-tree ch₁})) (refl {x = up (rightSub t)}) ⟩
--     node (zipBW _∷ʳ_ ((mapB (map (x₀ ∷_)) (up (ch-to-tree ch₁)))) (rightSub t)) (up (rightSub t))
--      ≡⟨ cong₂ node (cong (λ q → zipBW (_∷ʳ_) q (rightSub t)) (cong (mapB (map (x₀ ∷_))) (upSpec ch₁ ch₂ {!   !} (≤-pred suc-k≤len)))) (refl {x = up (rightSub t)}) ⟩
--     node (zipBW _∷ʳ_ (mapB (map (x₀ ∷_)) (mapB subs (rightSub t))) (rightSub t)) (up (rightSub t))
--      ≡⟨ cong₂ node (lemma₄₄ {t = rightSub t} {x = x₀}) (refl {x = up (rightSub t)}) ⟩
--     node (mapB subs (mapB (_∷_ x₀) (rightSub t))) (up (rightSub t))
--      ≡⟨ cong₂ node (cong (mapB subs) (cong (mapB (x₀ ∷_)) (tree-eq ch₂ ch' refl refl))) (upSpec ch₂ ch'' 2≤1+k {!   !}) ⟩
--     node (mapB subs (mapB (_∷_ x₀) (ch-to-tree ch'))) (mapB subs (ch-to-tree ch'')) ∎
-- upSpec {_} {_} {.(suc _)} {x ∷ []} ch ch' (s≤s (s≤s 2≤1+k)) (s≤s ())
-- upSpec {_} {_} {.(2+ _)} {x₀ ∷ x₁ ∷ .(_ ∷ _)} (suc≢ x₂ (suc≢ x₄ ch₁ (suc≢ x₅ ch₂ ch₃)) (suc≡ x₃)) (suc≡ x) 2≤1+k suc-k≤len = {!   !} -- impossible case
-- upSpec {_} {_} {.(suc _)} {x₀ ∷ x₁ ∷ xs} (suc≢ x₂ ch₁ (suc≢ x₃ ch₂ ch₃)) (suc≡ x) 2≤1+k suc-k≤len = {!   !} -- impossible case
-- upSpec {_} {_} {.zero} {x₀ ∷ x₁ ∷ xs} zero (suc≢ x ch' ch'') (s≤s ()) suc-k≤len
-- upSpec {_} {_} {.(2+ _)} {x₀ ∷ x₁ ∷ xs} (suc≡ x₂) (suc≢ x ch' ch'') 2≤1+k (s≤s (s≤s suc-k≤len)) = ⊥-elim (1+n≰n suc-k≤len)
-- upSpec {_} {_} {k = suc zero} {x₀ ∷ x₁ ∷ xs} (suc≢ x₂ zero (suc≡ x₃)) (suc≢ x ch' ch'') 2≤1+k suc-k≤len = {!   !} -- impossible case
-- upSpec {_} {_} {k = 2+ k} {x₀ ∷ x₁ ∷ []} (suc≢ x₂ ch₁ ch₂) (suc≢ x ch' ch'') 2≤1+k suc-k≤len = {!   !} -- impossible case
-- -- upSpec {_} {_} {k = 2+ k} {x₀ ∷ x₁ ∷ x₂ ∷ xs} {t = node .(mapB (_∷_ x₀) _) (tipN x₄)} (suc≢ x₃ ch₁ ch₂) (suc≢ x ch' ch'') 2≤1+k suc-k≤len = {!   !} -- impossible case

-}