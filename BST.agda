-- {-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}
{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Bool.Properties hiding (_≟_)
{-# REWRITE Data.Bool.Properties.∨-identityʳ #-}
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
  b b'               : Bool
  x                  : A
  xs ys zs           : Vec A n

data BTree : Set where
    nil  :                     BTree 
    node : ℕ → BTree → BTree → BTree

variable
    t t' t'' u u' : BTree

-- Search if a natural number is in a tree.
search : ℕ → BTree → Bool
search n  nil  = false
search n (node x t u) with n ≟ x
... | yes refl = true
... | no  _    = (search n t) ∨ (search n u)

data Search : ℕ → BTree → Bool → Set where
    nil :                                                  Search n  nil          false
    eq  : {x : ℕ} → n ≡ x                                → Search n (node x t u)  true
    neq : {x : ℕ} → n ≢ x → Search n t b → Search n u b' → Search n (node x t u) (b ∨ b')

-- Giving two identical trees, the result of "search" will be equivalent.
search-eq : ∀ {n t t' b b'} → t ≡ t' → Search n t b → Search n t' b' → b ≡ b'
search-eq refl  nil          nil            = refl
search-eq refl (eq x)       (eq x₁)         = refl
search-eq refl (eq refl)    (neq x₁ s' s'') = ⊥-elim (x₁ refl)
search-eq refl (neq x s s₁) (eq refl)       = ⊥-elim (x refl)
search-eq refl (neq x s s₁) (neq x₁ s' s'') = cong₂ (_∨_) (search-eq refl s s') (search-eq refl s₁ s'')

-- Delete a natural number from a tree if it is in the tree.
delete : ℕ → BTree → BTree
delete n nil   = nil
delete n bt@(node x t u) with (search n bt)
... | false    = bt
... | true with n ≟ x
delete n (node n nil nil)                       | true | yes refl = nil
delete n (node n nil u@(node x _ _))            | true | yes refl = u
delete n (node n t@(node x _ _) nil)            | true | yes refl = t
delete n (node n t@(node x _ _) u@(node _ _ _)) | true | yes refl = node x (delete x t) u
... | no  _ with (search n t)
... | true     = node x (delete n t) u
... | false    = node x t (delete n u)

data Delete : ℕ → BTree → BTree → Set where
    empty  :                                                          Delete n  nil                                  nil
    no-del :         Search n t false                               → Delete n  t                                    t
    eqn    : n ≡ x                                                  → Delete n (node n  nil           nil)           nil
    eqr    : n ≡ x                                                  → Delete n (node n  nil          (node m u u')) (node m u    u')
    eql    : n ≡ x                                                  → Delete n (node n (node m t t')  nil)          (node m t    t')
    eq2    : n ≡ x                    → Delete m (node m t t')  t'' → Delete n (node n (node m t t') (node k u u')) (node m t'' (node k u u'))
    neql   : n ≢ x → Search n t true  → Delete n  t             t'  → Delete n (node x  t             u)            (node x t'   u)
    neqr   : n ≢ x → Search n u true  → Delete n  u             u'  → Delete n (node x  t             u)            (node x t    u') 

-- Giving two natural number 'm' and 'n', with m ≢ n, the result of searching 'm' in the tree will remain the same after deleting 'n' from the tree.
-- Function version
delete-preserve : ∀ {m n} t → m ≢ n → search m t ≡ search m (delete n t)
delete-preserve {m} {n}  nil m≢n = refl -- relation ver. case 1
delete-preserve {m} {n} (node x t               u)               m≢n with m ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl with n ≟ m
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | yes refl = {!   !} -- ⊥-elim (m≢n refl) -- relation ver. case 2
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    with (search n t)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  with n ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | yes refl = ⊥-elim (m≢n refl)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | no  _    with (search n t)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | no  _    | true  with x ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | no  _    | true  | yes refl = refl
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | no  _    | true  | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | no  _    | false with x ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | no  _    | false | yes refl = refl
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | true  | no  _    | false | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false with (search n u)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true with n ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | yes refl = ⊥-elim (m≢n refl)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | no  _    with (search n t)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | no  _    | true with x ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | no  _    | true  | yes refl = refl
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | no  _    | true  | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | no  _    | false with x ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | no  _    | false | yes refl = refl
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | true  | no  _    | false | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | false with x ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | false | yes refl = refl
delete-preserve {m} {n} (node x t               u)               m≢n | yes refl | no  _    | false | false | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m} {n} (node x t               u)               m≢n | no  _    with n ≟ x
delete-preserve {m} {n} (node x t               u)               m≢n | no  _    | yes refl with x ≟ x
delete-preserve {m} {x} (node x nil             nil)             m≢n | no  _    | yes refl | yes refl = refl
delete-preserve {m} {x} (node x nil             u@(node _ _ _))  m≢n | no  _    | yes refl | yes refl = refl
delete-preserve {m} {x} (node x t@(node _ _ _)  nil)             m≢n | no  _    | yes refl | yes refl = refl
delete-preserve {m} {x} (node x t@(node _ _ _)  u@(node _ _ _))  m≢n | no  _    | yes refl | yes refl with (search m t)
delete-preserve {m} {x} (node x t@(node _ _ _)  u@(node _ _ _))  m≢n | no  _    | yes refl | yes refl | true  = {!   !}
delete-preserve {m} {x} (node x t@(node _ _ _)  u@(node _ _ _))  m≢n | no  _    | yes refl | yes refl | false with (search m u)
delete-preserve {m} {x} (node x t@(node _ _ _)  u@(node _ _ _))  m≢n | no  _    | yes refl | yes refl | false | true  = {!   !}
delete-preserve {m} {x} (node x t@(node _ _ _)  u@(node _ _ _))  m≢n | no  _    | yes refl | yes refl | false | false = {!   !}
delete-preserve {m} {n} (node x t               u)               m≢n | no  _    | yes refl | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m} {n} (node x nil             nil)             m≢n | no  m≢x  | no n≢x   with m ≟ x
delete-preserve {m} {n} (node x nil             nil)             m≢n | no  m≢x  | no n≢x   | yes refl = ⊥-elim (m≢x refl)
delete-preserve {m} {n} (node x nil             nil)             m≢n | no  m≢x  | no n≢x   | no  _    = refl
delete-preserve {m} {n} (node x nil             u@(node _ _ _))  m≢n | no  m≢x  | no n≢x   with (search m u)
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | true  with m ≟ x₁
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | true  | yes refl with (search n u)
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | true  | yes refl | true  with n ≟ x
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | true  | yes refl | true  | yes refl = ⊥-elim (n≢x refl)
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | true  | yes refl | true  | no  _    = {!   !}
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | true  | yes refl | false = {!   !}
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | true  | no  _    = {!   !}
delete-preserve {m} {n} (node x nil             u@(node x₁ _ _)) m≢n | no  m≢x  | no n≢x   | false = {!   !}
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   with (search m t)
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | true  with m ≟ x₁
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | true  | yes refl with (search n t)
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | true  | yes refl | true  with n ≟ x
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | true  | yes refl | true  | yes refl = ⊥-elim (n≢x refl)
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | true  | yes refl | true  | no  _    = {!   !}
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | true  | yes refl | false = {!   !}
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | true  | no  _    = {!   !}
delete-preserve {m} {n} (node x t@(node x₁ _ _) nil)             m≢n | no  m≢x  | no n≢x   | false = {!   !}
delete-preserve {m} {n} (node x t@(node _ _ _)  u@(node _ _ _))  m≢n | no  m≢x  | no n≢x   = {! cong₂ (_∨_) (delete-preserve t m≢x) (delete-preserve u n≢x)  !} -- Can't directly use recursive call, but relation ver. can.

-- Relation version
delete-preserve' : ∀ {m n t b b'} {t' : BTree} → m ≢ n → Search m t b → Delete n t t' → Search m t' b' → b ≡ b'
delete-preserve' m≢n  nil                                 d                nil            = refl
-- Same as Dec(m ≡ x) ≡ yes case in function ver. (function: 13 cases, relation: 10 cases)
delete-preserve' m≢n (eq  refl)                          (eqn    refl)     nil            = ⊥-elim (m≢n refl)
delete-preserve' m≢n (eq  x)                              d               (eq  x₁)        = refl
delete-preserve' m≢n (eq  refl)                          (no-del x₂)      (neq x₁ s' s'') = ⊥-elim (x₁ refl)
delete-preserve' m≢n (eq  refl)                          (eqr    refl)    (neq x₁ s' s'') = ⊥-elim (m≢n refl)
delete-preserve' m≢n (eq  refl)                          (eql    refl)    (neq x₁ s' s'') = ⊥-elim (m≢n refl)
delete-preserve' m≢n (eq  refl)                          (eq2    refl  d) (neq x₁ s' s'') = ⊥-elim (m≢n refl)
delete-preserve' m≢n (eq  refl)                          (neql   x₂ x₃ d) (neq x₁ s' s'') = ⊥-elim (x₁ refl)
delete-preserve' m≢n (eq  refl)                          (neqr   x₂ x₃ d) (neq x₁ s' s'') = ⊥-elim (x₁ refl)
-- Same as Dec(m ≡ x) ≡ no case in function ver. (function: 20 cases, relation: 18 cases)  *function ver. will have more cases
delete-preserve' m≢n (neq x  nil          nil)           (eqn    x₁)       nil            = refl
delete-preserve' m≢n (neq x  s            s₁)            (no-del x₂)      (eq  refl)      = ⊥-elim (x refl)
delete-preserve' m≢n (neq x  nil         (eq x₁))        (eqr    refl)    (eq  refl)      = refl
delete-preserve' m≢n (neq x  nil         (neq x₁ s₁ s₂)) (eqr    refl)    (eq  refl)      = ⊥-elim (x₁ refl)
delete-preserve' m≢n (neq x (eq x₁)       s₁)            (eql    x₂)      (eq  refl)      = refl
delete-preserve' m≢n (neq x (neq x₁ s s₂) s₁)            (eql    x₂)      (eq  refl)      = ⊥-elim (x₁ refl)
delete-preserve' m≢n (neq x (eq x₁)       s₁)            (eq2    x₂    d) (eq  refl)      = refl
delete-preserve' m≢n (neq x (neq x₁ s s₂) s₁)            (eq2    x₂    d) (eq  refl)      = ⊥-elim (x₁ refl)
delete-preserve' m≢n (neq x  s            s₁)            (neql   x₂ x₃ d) (eq  refl)      = ⊥-elim (x refl)
delete-preserve' m≢n (neq x  s            s₁)            (neqr   x₂ x₃ d) (eq  refl)      = ⊥-elim (x refl)
delete-preserve' m≢n (neq x  s            s₁)            (no-del x₂)      (neq x₁ s' s'') = cong₂ (_∨_) (search-eq refl s s') (search-eq refl s₁ s'')
delete-preserve' m≢n (neq x  nil         (eq refl))      (eqr    x₂)      (neq x₁ s' s'') = ⊥-elim (x₁ refl)
delete-preserve' m≢n (neq x  nil         (neq x₃ s₁ s₂)) (eqr    x₂)      (neq x₁ s' s'') = cong₂ (_∨_) (search-eq refl s₁ s') (search-eq refl s₂ s'')
delete-preserve' m≢n (neq x (eq refl)     nil)           (eql    x₂)      (neq x₁ s' s'') = ⊥-elim (x₁ refl)
delete-preserve' m≢n (neq x (neq x₃ s s₁) nil)           (eql    x₂)      (neq x₁ s' s'') = cong₂ (_∨_) (search-eq refl s s') (search-eq refl s₁ s'')
delete-preserve' m≢n (neq x  s            s₁)            (eq2    x₂    d) (neq x₁ s' s'') = cong₂ (_∨_) (delete-preserve' x₁ s d s') (search-eq refl s₁ s'')
delete-preserve' m≢n (neq x  s            s₁)            (neql   x₂ x₃ d) (neq x₁ s' s'') = cong₂ (_∨_) (delete-preserve' m≢n s d s') (search-eq refl s₁ s'')
delete-preserve' m≢n (neq x  s            s₁)            (neqr   x₂ x₃ d) (neq x₁ s' s'') = cong₂ (_∨_) (search-eq refl s s') (delete-preserve' m≢n s₁ d s'')