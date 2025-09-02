-- {-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}

open import Data.Bool using (Bool; true; false)
open import Data.Nat
open import Data.Nat.Properties using  (_≟_; <-pred; ≤-step; ≤-trans; ≤-reflexive; ≤-pred; <⇒≤; <⇒≱; ≤⇒≯; ≤∧≢⇒<; 1+n≰n; 1+n≢n; n≮n; 0<1+n; m<1+n⇒m≤n; suc-injective; ≤-refl)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; length; _++_; map)
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

unboundedCh : ∀ {t : BTree (Vec A (suc n)) n (suc n)} → Ch (suc n) xs t  → ⊥
unboundedCh (suc≢ {t = t} x ch ch₁) = unbounded t

subs : Vec A (suc n) → Vec (Vec A n) (suc n)
subs (x ∷ []) = [] ∷ []
subs (x ∷ xs@(y ∷ ys)) = (map (x ∷_) (subs xs)) ∷ʳ xs

lemma₀ : ∀ {k : ℕ} {xs : Vec A n} → k ≤ n → k ≢ n → suc k ≤ n
lemma₀ k≤len k≢len = ≤∧≢⇒< k≤len k≢len

ch : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vec A n) → (k≤len : k ≤ n) → BTree (Vec A k) n k
ch zero xs k≤len = tip0 []
ch (suc k) (x ∷ xs) k≤len with k ≟ length xs
... | yes refl    = tipN (x ∷ xs)
... | no  k≢len   = node (mapB (x ∷_) (ch k xs (≤-pred k≤len))) (ch (suc k) xs (lemma₀ {_} {_} {k} {xs} (≤-pred k≤len) k≢len))

-- ------------------------------
-- Part 2. Function v.s. Relation
-- (1) ch k xs ≡ t ↔ Ch k xs t
-- Ch → ch
Ch-to-ch : ∀ {n k} {xs : Vec A n} {k≤len : k ≤ n} {t : BTree (Vec A k) n k} → Ch k xs t → ch k xs k≤len ≡ t
Ch-to-ch {k = zero}  {xs = xs}      zero = refl
Ch-to-ch {n = suc n} {k = suc k}  {xs = x ∷ xs}  suc≡             with n ≟ length xs
Ch-to-ch {n = suc n} {k = suc k}  {xs = x ∷ xs}  suc≡             | yes refl = refl
Ch-to-ch {n = suc n} {k = suc k}  {xs = x ∷ xs}  suc≡             | no  neq  = ⊥-elim (neq refl)
Ch-to-ch {k = suc k} {xs = x ∷ xs} (suc≢ x₁ ch₁ ch₂) with k ≟ length xs
Ch-to-ch {k = suc k} {xs = x ∷ xs} (suc≢ x₁ ch₁ ch₂) | yes refl = ⊥-elim (x₁ refl)
Ch-to-ch {k = suc k} {xs = x ∷ xs} (suc≢ x₁ ch₁ ch₂) | no  neq  = cong₂ node (cong (mapB (x ∷_)) (Ch-to-ch ch₁)) (Ch-to-ch ch₂) 
-- ch → Ch
ch-to-Ch : ∀ {n k} {xs : Vec A n} {k≤len : k ≤ n} {t : BTree (Vec A k) n k} → ch k xs k≤len ≡ t → Ch k xs t
ch-to-Ch                                   {t = tip0 .[]}                                    refl            = zero
ch-to-Ch {k = suc k} {xs = x₀ ∷ xs}        {t = tipN x}                                      eq   with k ≟ length xs
ch-to-Ch {k = suc k} {x₀ ∷ xs}     {_}     {tipN .(x₀ ∷ xs)}                                 refl | yes refl = suc≡
ch-to-Ch {k = suc k} {xs = x ∷ xs}         {t = node t u}                                    eq   with k ≟ length xs
ch-to-Ch {_} {_} {suc k} {x ∷ xs}  {_} {node t u} () | yes refl
ch-to-Ch {k = suc k} {x ∷ xs}      {k≤len} {node t u} refl | no  neq  = suc≢ {k = k} {x = x} {xs = xs} (λ x₁ → neq (suc-injective x₁)) (ch-to-Ch refl) (ch-to-Ch refl)

-- helper functtion
ch-inverse : ∀ {n k} {xs : Vec A n} {k≤len : k ≤ n} {t : BTree (Vec A k) n k} → {ch : Ch k xs t} → ch-to-Ch {k≤len = k≤len} (Ch-to-ch ch) ≡ ch
ch-inverse                                                       {ch = zero}                       = refl
ch-inverse {n = suc k} {xs = x ∷ xs}                             {ch = suc≡}            with k ≟ length xs
ch-inverse {n = suc k} {xs = x ∷ xs}                             {ch = suc≡}            | yes refl = refl
ch-inverse {n = suc k} {xs = x ∷ xs}                             {ch = suc≡}            | no  neq  = ⊥-elim (neq refl)
ch-inverse {k = suc k} {xs = x ∷ xs}                             {ch = suc≢ x₀ ch₁ ch₂} with k ≟ length xs
ch-inverse {k = suc k} {xs = x ∷ xs}                             {ch = suc≢ x₀ ch₁ ch₂} | yes refl = ⊥-elim (x₀ refl)
ch-inverse {k = suc k} {xs = x ∷ xs} {k≤len = s≤s k≤len} {t = t} {ch = suc≢ x₀ ch₁ ch₂} | no  neq  = {! (cong₂ node (cong (mapB (_∷_ x)) (Ch-to-ch ch₁)) (Ch-to-ch ch₂))  !}

Ch-inverse : ∀ {n k} {xs : Vec A n} {k≤len : k ≤ n} {t : BTree (Vec A k) n k} → {eq : ch k xs k≤len ≡ t} → Ch-to-ch (ch-to-Ch eq) ≡ eq 
Ch-inverse                           {t = tip0 .[]}        {eq = refl} = refl
Ch-inverse {n = suc k} {xs = x ∷ xs} {t = tipN (x' ∷ xs')} {eq = eq} = {!   !}
Ch-inverse {k = suc k} {xs = x ∷ xs} {t = node t u}        {eq = eq} = {!   !}
-- helper function

-- ch ⇔ Ch (Equivalence)
ch⇔Ch : ∀ {n k} {xs : Vec A n} {k≤len : k ≤ n} {t : BTree (Vec A k) n k} → (ch k xs k≤len ≡ t ⇔ Ch k xs t)
ch⇔Ch = mk⇔ ch-to-Ch Ch-to-ch
-- ch ↔ Ch (Inverse)
ch↔Ch :  ∀ {n k} {xs : Vec A n} {k≤len : k ≤ n} {t : BTree (Vec A k) n k} → (ch k xs k≤len ≡ t ↔ Ch k xs t)
ch↔Ch = mk↔ {to = ch-to-Ch} {from = Ch-to-ch} ((λ x → trans (cong ch-to-Ch x) ch-inverse) , (λ x → trans (cong Ch-to-ch x) Ch-inverse))

-- (2) Ch n xs t ∧ Ch n xs t' → t ≡ t'
tree-eq : ∀ {n : ℕ} {xs : Vec A m} {t t' : BTree (Vec A n) m n} → Ch n xs t → Ch n xs t' → t ≡ t'
tree-eq                 zero            zero              = refl
tree-eq                 suc≡            suc≡              = refl
tree-eq                 suc≡           (suc≢ x  ch' ch'') = ⊥-elim (x refl) 
tree-eq                (suc≢ x ch ch₁)  suc≡              = ⊥-elim (x refl)
tree-eq {xs = x₂ ∷ xs} (suc≢ x ch ch₁) (suc≢ x₁ ch' ch'') = cong₂ node (cong (mapB (x₂ ∷_)) (tree-eq ch ch')) (tree-eq ch₁ ch'')
-- ------------------------------

up : {k : ℕ} → {z≤k : 0 < k} → {k < n} → BTree A n k → BTree (Vec A (suc k)) n (suc k) 
up {k = suc k}       {0<k} {k<n} (tipN x)                              = ⊥-elim (n≮n (suc k) k<n)
up                   {0<k} {k<n} (node (tip0 x) (tipN y))              = tipN (x ∷ y ∷ [])
up {_} {_} {_}       {0<k} {k<n} (node (tip0 x) u@(node (tip0 x₀) x₁)) = node (mapB (λ q → x ∷ q ∷ []) u) (up {_} {_} {_} {0<k} {m≤n⇒m<1+n (bounded x₁)} u)
up {k = suc (suc k)} {0<k} {k<n} (node (tipN x) u)                     = ⊥-elim (n≮n (suc (suc k)) k<n)
up {_} {_} {_}       {0<k} {k<n} (node t@(node _ _) (tipN y))          = tipN ((unTip (up {_} {_} {_} {0<1+n} {(<-pred k<n)} t)) ∷ʳ y)
up {_} {_} {_}       {0<k} {k<n} (node t@(node _ _) u@(node _ u'))     = node (zipBW (_∷ʳ_) (up {_} {_} {_} {0<1+n} {(s<s⁻¹ k<n)} t) u) (up {_} {_} {_} {0<1+n} {(m≤n⇒m<1+n (bounded u'))} u)

-- upSpec : {k : ℕ} {xs : Vec A n} {t : BTree (Vec A k) n k} {t' : BTree (Vec A (suc k)) n (suc k)}
--        → Ch k xs t → Ch (suc k) xs t' → 2 ≤ suc k → (suc-k≤len : suc k ≤ n) → up t ≡ mapB subs t'
-- -- left : tip0 
-- upSpec zero ch' (s≤s ()) suc-k≤len
-- -- left : tipN → up case 1.
-- upSpec suc≡ ch' 2≤suc-k suc-k≤len = ⊥-elim (1+n≰n suc-k≤len)
-- -- left : node t u → def. of up
-- -- node tip0 tipN → up case 2.
-- upSpec {xs = x₀ ∷ x₁ ∷ []} (suc≢ x  zero              suc≡)                   suc≡              2≤suc-k suc-k≤len = refl
-- upSpec                     (suc≢ x  zero              suc≡)                  (suc≢ x₁ ch' ch'') 2≤suc-k suc-k≤len = ⊥-elim (x₁ refl)
-- -- node tip0 (node t u) → up case 3.
-- upSpec                     (suc≢ x  zero              ch@(suc≢ x₁ zero ch₃)) (suc≢ x₂ ch' ch'') 2≤suc-k suc-k≤len = cong₂ node {!   !}  (upSpec ch ch'' ≤-refl (m<1+n⇒m≤n (≤∧≢⇒< suc-k≤len x₂)))
-- -- node tipN (node t u) → up case 4.
-- upSpec                     (suc≢ x  suc≡             (suc≢ x₁ ch₂ ch₃))       ch'               2≤suc-k suc-k≤len = ⊥-elim (1+n≰n suc-k≤len)
-- -- node (node t u) tipN → up case 5.
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃)  suc≡)                   suc≡              2≤suc-k suc-k≤len = cong tipN {!   !}
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃)  suc≡)                  (suc≢ x₂ ch' ch'') 2≤suc-k suc-k≤len = ⊥-elim (x₂ refl)
-- -- node (node t u) (node t' u') → up case 6.
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃) (suc≢ x₂ ch₂ ch₄))       suc≡              2≤suc-k suc-k≤len = ⊥-elim (x₂ refl)
-- upSpec                     (suc≢ x (suc≢ x₁ ch₁ ch₃)  ch@(suc≢ x₂ ch₂ ch₄))  (suc≢ x₃ ch' ch'') 2≤suc-k suc-k≤len = cong₂ node {!   !} (upSpec ch ch'' (s≤s (s≤s z≤n)) (m<1+n⇒m≤n (≤∧≢⇒< suc-k≤len x₃)))
