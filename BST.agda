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
delete n (node n nil u)                         | true | yes refl = u
delete n (node n t@(node x _ _) nil)            | true | yes refl = t
delete n (node n t@(node x _ _) u@(node _ _ _)) | true | yes refl = node x (delete x t) u
... | no  _ with (search n t)
... | true     = node x (delete n t) u
... | false    = node x t (delete n u)

-- mutual

--     data Delete : ℕ →­ BTree → BTree → Set where
--         nil  : bt ≡ nil        → r ≡ nil                             → Delete n bt r
--         ­node : bt ≡ node x t u → Search n bt b → Delete₀ n x t u b r → Delete n bt r

--     data Delete₀ : ℕ → ℕ → BTree → BTree → Bool → BTree → Set where
--         false : b ≡ false → r ≡ bt                            → Delete₀ n x t u b r 
--         true  : b ≡ true  → DecEq n x d → Delete₁ n x t u d r → Delete₀ n x t u b r

--     data Delete₁ : (n : ℕ) → (x : ℕ) → BTree → BTree → Dec (n ≡ x) → BTree → Set where
--         yes : d ≡ yes eq → Delete₂ n x t u eq r                   → Delete₁ n x t u d r
--         no  : d ≡ no neq → Search n t b → Delete₅ n x t u neq b r → Delete₁ n x t u d r

--     data Delete₂ : (n : ℕ) → (x : ℕ) → BTree → BTree → n ≡ x → BTree → Set where
--         refl : eq ≡ refl → Delete₃ n t u r → Delete₂ n n t u eq r

--     data Delete₃ : ℕ → BTree → BTree → BTree → Set where
--         nil  : t ≡ nil          → r ≡ u                 → Delete₃ n t u r
--         node : t ≡ node x t' u' → Delete₄ n x t' u' u r → Delete₃ n t u r

--     data Delete₄ : ℕ → ℕ → BTree → BTree → BTree → BTree → Set where
--         nil  : u ≡ nil → r ≡ t → Delete₄ n x t' u' u r
--         node : u ≡ node x' t'' u'' → Delete x (node x t' u') r' → r ≡ node x r' u → Delete₄ n x t' u' u r


data Delete : ℕ → BTree → BTree → Set where
    empty  :                                                          Delete n  nil                                  nil
    no-del :         Search n t false                               → Delete n  t                                    t
    eqr    : n ≡ x                                                  → Delete n (node n  nil          u)              u
    eql₀   : n ≡ x                                                  → Delete n (node n (node m t t')  nil)           (node m t t')
    eql    : n ≡ x                    → Delete m (node m t t')  t'' → Delete n (node n (node m t t')  (node k u u'))             (node m t'' (node k u u'))
    neql   : n ≢ x → Search n t true  → Delete n  t             t'  → Delete n (node x  t             u)            (node x t'   u)
    neqr   : n ≢ x → Search n t false  → Delete n  u             u'  → Delete n (node x  t             u)            (node x t    u') 
    
    
    -- eqn    : n ≡ x                                                  → Delete n (node n  nil           nil)           nil
    -- eqr    : n ≡ x                                                  → Delete n (node n  nil          (node m u u')) (node m u    u')
    -- eql    : n ≡ x                                                  → Delete n (node n t  nil)          t
    -- eq2    : n ≡ x                    → Delete m (node m t t')  t'' → Delete n (node n (node m t t') (node k u u')) (node m t'' (node k u u'))
    

-- Giving two natural number 'm' and 'n', with m ≢ n, the result of searching 'm' in the tree will remain the same after deleting 'n' from the tree.
-- Function version
delete-preserve : ∀ {m n} t → m ≢ n → search m t ≡ search m (delete n t)
delete-preserve {m}  {n}  nil                                       m≢n = refl
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n with m ≟ x
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | yes refl with (search n bt)
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | yes refl | true  with n ≟ x
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | yes refl | true  | yes refl = {!   !} 
delete-preserve {m}  {n}  bt@(node m t t')                          m≢n | yes refl | true  | no  _    with (search n t)
delete-preserve {m}  {n}  bt@(node m t t')                          m≢n | yes refl | true  | no  _    | true  with m ≟ m
delete-preserve {m}  {n}  bt@(node m t t')                          m≢n | yes refl | true  | no  _    | true  | yes refl = refl
delete-preserve {m}  {n}  bt@(node m t t')                          m≢n | yes refl | true  | no  _    | true  | no  m≢m  = ⊥-elim (m≢m refl)
delete-preserve {m}  {n}  bt@(node m t t')                          m≢n | yes refl | true  | no  _    | false with m ≟ m
delete-preserve {m}  {n}  bt@(node m t t')                          m≢n | yes refl | true  | no  _    | false | yes refl = refl
delete-preserve {m}  {n}  bt@(node m t t')                          m≢n | yes refl | true  | no  _    | false | no  m≢m  = ⊥-elim (m≢m refl)
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | yes refl | false with x ≟ x
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | yes refl | false | yes refl = refl
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | yes refl | false | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    with (search n bt)
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | true  with n ≟ x
delete-preserve {m}  {x} (node x nil t')                            m≢n | no  _    | true  | yes refl = refl
delete-preserve {m}  {x} (node x t@(node x₁ _ _) t')                m≢n | no  _    | true  | yes refl with m ≟ x₁
delete-preserve {m}  {x} (node x t@(node x₁ _ _) t')                m≢n | no  _    | true  | yes refl | yes refl with (search m t)
delete-preserve {x₁} {x} (node x (node x₁ _ _) t')                 m≢n | no  _    | true  | yes refl | yes refl | true with x₁ ≟ x₁
delete-preserve {x₁} {x} (node x (node x₁ _ _) t')                 m≢n | no  _    | true  | yes refl | yes refl | true  | yes refl = {!   !} -- neq case 4
delete-preserve {x₁} {x} (node x (node x₁ _ _) t')                 m≢n | no  _    | true  | yes refl | yes refl | true  | no  x≢x  = {!   !} -- neq case 5
delete-preserve {x₁} {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | yes refl | false with x₁ ≟ x₁ -- nil case (of relation) can't be reduced automatically
delete-preserve {x₁} {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | yes refl | false | yes refl = refl
delete-preserve {x₁} {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | yes refl | false | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {x₁} {x} (node x (node x₁ _ _) (node x₂ t' t''))    m≢n | no  _    | true  | yes refl | yes refl | false with x₁ ≟ x₁ 
delete-preserve {x₁} {x} (node x (node x₁ _ _) (node x₂ t' t''))    m≢n | no  _    | true  | yes refl | yes refl | false | yes refl = refl
delete-preserve {x₁} {x} (node x (node x₁ _ _) (node x₂ t' t''))    m≢n | no  _    | true  | yes refl | yes refl | false | no  x≢x  = ⊥-elim (x≢x refl)
delete-preserve {m}  {x} (node x t@(node x₁ _ _) t')                m≢n | no  _    | true  | yes refl | no  _    with (search m t)
delete-preserve {m}  {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | no  _    | true  with m ≟ x₁
delete-preserve {m}  {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | no  x≢x  | true  | yes refl = ⊥-elim (x≢x refl) -- neq case 6
delete-preserve {m}  {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | no  _    | true  | no  _    = refl -- neq case 7
delete-preserve {m}  {x} (node x (node x₁ _ _) (node x₂ t' t''))    m≢n | no  _    | true  | yes refl | no  _    | true  with m ≟ x₁
delete-preserve {m}  {x} (node x (node x₁ _ _) (node x₂ t' t''))    m≢n | no  _    | true  | yes refl | no  x≢x  | true  | yes refl = ⊥-elim (x≢x refl) -- neq case 6
delete-preserve {m}  {x} (node x t@(node x₁ _ _) u@(node x₂ t' u')) m≢n | no  _    | true  | yes refl | no  _    | true  | no  m≢x  = cong₂ (_∨_) {! delete-preserve t m≢n !} (refl {x = search m u}) -- neq case 7
delete-preserve {m}  {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | no  _    | false with m ≟ x₁ -- nil case (of relation) can't be reduced automatically₁
delete-preserve {m}  {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | no  x≢x  | false | yes refl = ⊥-elim (x≢x refl)
delete-preserve {m}  {x} (node x (node x₁ _ _) nil)                 m≢n | no  _    | true  | yes refl | no  _    | false | no  _    = refl
delete-preserve {m}  {x} (node x (node x₁ _ _) (node x₂ t' t''))    m≢n | no  _    | true  | yes refl | no  _    | false with m ≟ x₁
delete-preserve {m}  {x} (node x (node x₁ _ _) (node x₂ t' t''))    m≢n | no  _    | true  | yes refl | no  x≢x  | false | yes refl = ⊥-elim (x≢x refl)
delete-preserve {m}  {x} (node x t@(node x₁ _ _) u@(node x₂ t' u')) m≢n | no  _    | true  | yes refl | no  _    | false | no  _    = cong₂ (_∨_) {! delete-preserve t m≢n   !} (refl {x = search m u}) 
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | true  | no  _    with (search n t)
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | true  | no  _    | true  with m ≟ x
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  m≢x  | true  | no  _    | true  | yes refl = ⊥-elim (m≢x refl) -- neq case 8
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | true  | no  _    | true  | no  m≢x  = cong₂ (_∨_) (delete-preserve t m≢n) (refl {x = search m t'}) -- neq case 9
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | true  | no  _    | false with m ≟ x
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  m≢x  | true  | no  _    | false | yes refl = ⊥-elim (m≢x refl) -- neq case 10
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | true  | no  _    | false | no  m≢x  = cong₂ (_∨_) (refl {x = search m t}) (delete-preserve t' m≢n) -- neqe case 11
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | false with m ≟ x
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  m≢x  | false | yes refl = ⊥-elim (m≢x refl) -- neq case 1
delete-preserve {m}  {n}  bt@(node x t t')                          m≢n | no  _    | false | no  _    = refl -- neq case 2

-- Relation version
delete-preserve' : ∀ {m n t b b'} {t' : BTree} → m ≢ n → Search m t b → Delete n t t' → Search m t' b' → b ≡ b'
delete-preserve' m≢n  nil                      d               nil            = refl
-- Same as Dec(m ≡ x) ≡ yes case in function ver. (function: 7 cases, relation: 9 cases)
delete-preserve' m≢n (eq  refl)                (no-del x)     (eq  x₁)        = refl
delete-preserve' m≢n (eq  refl)                (no-del x)     (neq x₁ s' s'') = ⊥-elim (x₁ refl)
delete-preserve' m≢n (eq  refl)                (eqr x)         s'             = ⊥-elim (m≢n refl)
delete-preserve' m≢n (eq  refl)                (eql x d)       s'             = ⊥-elim (m≢n refl)
delete-preserve' m≢n (eq  refl)                (eql₀ d)       s'              = ⊥-elim (m≢n refl)
delete-preserve' m≢n (eq  refl)                (neql x x₁ d)  (eq  x₂)        = refl
delete-preserve' m≢n (eq  refl)                (neql x x₁ d)  (neq x₂ s' s'') = ⊥-elim (x₂ refl)
delete-preserve' m≢n (eq  refl)                (neqr x x₁ d)  (eq  refl)      = refl
delete-preserve' m≢n (eq  refl)                (neqr x x₁ d)  (neq x₂ s' s'') = ⊥-elim (x₂ refl)
-- Same as Dec(m ≡ x) ≡ no case in function ver. (function: 24 cases, relation: 13 cases)  *function ver. will have more cases
delete-preserve' m≢n (neq x  s             s₁)  (no-del x₁)        (eq  refl)      = ⊥-elim (x refl)
delete-preserve' m≢n (neq x  s             s₁)  (no-del x₁)        (neq x₂ s' s'') = cong₂ (_∨_) (search-eq refl s s') (search-eq refl s₁ s'')
delete-preserve' m≢n (neq x  nil           s₁)  (eqr    x₁)         s'             = search-eq refl s₁ s'
delete-preserve' m≢n (neq x (eq x₁) nil)        (eql₀         d)   (eq  refl)      = refl
delete-preserve' m≢n (neq x (neq x₁ s s₁)  nil) (eql₀         d)   (eq  refl)      = ⊥-elim (x₁ refl)
delete-preserve' m≢n (neq x s nil)              (eql₀         d) t@(neq x₁ s' s'') = search-eq refl s t 
delete-preserve' m≢n (neq x (eq  x₂)       s₁)  (eql    x₁    d)   (eq  refl)      = refl
delete-preserve' m≢n (neq x (neq x₂ s s₂)  s₁)  (eql    x₁    d)   (eq  refl)      = ⊥-elim (x₂ refl)
delete-preserve' m≢n (neq x (eq refl)      s₁)  (eql    x₁    d)   (neq x₂ s' s'') = ⊥-elim (x₂ refl)
delete-preserve' m≢n (neq x  s@(neq _ _ _) s₁)  (eql    x₁    d)   (neq x₂ s' s'') = cong₂ (_∨_) (delete-preserve' x₂ s d s') (search-eq refl s₁ s'')
delete-preserve' m≢n (neq x  s             s₁)  (neql   x₁ x₂ d)   (eq  refl)      = ⊥-elim (x refl)
delete-preserve' m≢n (neq x  s             s₁)  (neql   x₁ x₂ d)   (neq x₃ s' s'') = cong₂ (_∨_) (delete-preserve' m≢n s d s') (search-eq refl s₁ s'')
delete-preserve' m≢n (neq x  s             s₁)  (neqr   x₁ x₂ d)   (eq  refl)      = ⊥-elim (x refl)
delete-preserve' m≢n (neq x  s             s₁)  (neqr   x₁ x₂ d)   (neq x₃ s' s'') = cong₂ (_∨_) (search-eq refl s s') (delete-preserve' m≢n s₁ d s'')
