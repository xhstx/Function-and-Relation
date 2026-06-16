open import Data.Nat using (ℕ; zero; suc) renaming (_≤′_ to _≤_; ≤′-reflexive to base; ≤′-step to step)
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding (cong)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Empty

variable
    A B C : Set
    m n k : ℕ

module Part1 -- wk (Case analysis on indexed data) v.s. wk' (Case analysis on the indices first)
  where

  -- Version 1: wk (Case analysis on suc m ≤ n, which is the version where only the right-hand side increases)
  -- Using dot patterns to distinguish pattern matching performed by the programmer or forced by unification
  wk : (m n : ℕ) → suc m ≤ n → m ≤ n
  -- wk m n m<n = ?
  wk m .(suc m) (base refl)    = step (base refl)
  wk m .(suc n) (step {n} m<n) = step (wk m n m<n)

  -- Version 2: wk' (Case analysis on m and n first)
  wk' : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk'  zero    zero          m<n         = base refl
  wk'  zero   (suc .zero)    (base refl) = step (base refl)
  wk'  zero   (suc n)        (step m<n)  = step (wk' zero n m<n)
  wk' (suc m)  zero          (base ())
  wk' (suc m) (suc .(suc m)) (base refl) = step (base refl)
  wk' (suc m) (suc n)        (step m<n)  = step (wk' (suc m) n m<n)

  -- Transforming wk' to wk
  -- 1. Expand All Cases (With case analysis on suc m ≤ n)
  wk₁ : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk₁  zero    zero          (base _)    = base refl
  wk₁  zero   (suc .zero)    (base refl) = step (base refl)
  wk₁  zero   (suc n)        (step m<n)  = step (wk₁ zero n m<n)
  wk₁ (suc m)  zero          (base ())
  wk₁ (suc m) (suc .(suc m)) (base refl) = step (base refl)
  wk₁ (suc m) (suc n)        (step m<n)  = step (wk₁ (suc m) n m<n)

  -- 2. Reorder the Cases
  wk₂ : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk₂  zero    zero          (base _)    = base refl
  wk₂  zero   (suc .zero)    (base refl) = step (base refl)
  wk₂ (suc m)  zero          (base ())
  wk₂ (suc m) (suc .(suc m)) (base refl) = step (base refl)
  wk₂  zero   (suc n)        (step m<n)  = step (wk₂  zero   n m<n)
  wk₂ (suc m) (suc n)        (step m<n)  = step (wk₂ (suc m) n m<n)

  -- 3. Eliminate Redundant Case Analysis (for step; what about base?)
  wk₃ : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk₃  zero    zero          (base _)    = base refl
  -- wk₃  zero    zero          (base ())
  wk₃  zero   (suc .zero)    (base refl) = step (base refl)
  wk₃ (suc m)  zero          (base ())
  wk₃ (suc m) (suc .(suc m)) (base refl) = step (base refl)
  wk₃ m       (suc n)        (step m<n)  = step (wk₃ m n m<n)

module Part2 -- up (Case analysis on BTree) v.s. up' (Case analysis on _≤_ and k)
  where

  data BTree (A : Set) : (n k : ℕ) → Set where
    tip0 : A                               → BTree A  n       0
    tipN : A                               → BTree A (suc k) (suc k)
    node : BTree A n k → BTree A n (suc k) → BTree A (suc n) (suc k)

  variable
      t t' u u' : BTree A n k
      xs ys     : Vec A n

  z≤n : ∀ {n} → 0 ≤ n
  z≤n {zero}  = base refl
  z≤n {suc _} = step z≤n

  -- Properties of BTree
  bounded : BTree A n k → k ≤ n
  bounded (tip0 _)   = z≤n
  bounded (tipN _)   = base refl
  bounded (node t u) = step (bounded u)

  unbounded : BTree A k (suc k) → ⊥
  unbounded (node t u) = unbounded t

  -- Functions for BTree
  mapB : (A → B) → BTree A n k → BTree B n k
  mapB f (tip0 x)   = tip0 (f x)
  mapB f (tipN x)   = tipN (f x)
  mapB f (node t u) = node (mapB f t) (mapB f u)

  unTip : BTree A (suc n) (suc n) → A
  unTip (tipN x)   = x
  unTip (node t u) = ⊥-elim (unbounded u)

  zipBW : (A → B → C) → BTree A n k → BTree B n k → BTree C n k
  zipBW f (tip0 x)   (tip0 y)      = tip0 (f x y)
  zipBW f (tipN x)   (tipN y)     = tipN (f x y)
  zipBW f (tipN x)   (node t u)   = ⊥-elim (unbounded u)
  zipBW f (node t u) (tipN x)     = ⊥-elim (unbounded u)
  zipBW f (node t u) (node t' u') = node (zipBW f t t') (zipBW f u u')

  -- A version of the upgrade function derived by Shin (pattern matching on BTree)
  up : ∀ k → BTree A n (suc k) → 2 ≤ n → suc (suc k) ≤ n → BTree (Vec A (suc (suc k))) n (suc (suc k))
  up k (tipN x)                        l₁          l₂         = ⊥-elim (n≮n (suc k) (≤′⇒≤ l₂))
  up k (node (tip0 x)    (tipN y))     l₁          l₂         = tipN (x ∷ y ∷ []) -- Case 1
  up k (node (tip0 x)    (node u u'))  l₁          l₂         = node (mapB (λ q → x ∷ q ∷ []) (node u u')) (up zero (node u u') (s≤′s (bounded u')) (s≤′s (bounded u'))) -- Case 3.1
  up k (node (tipN x)     u)           l₁          l₂         = ⊥-elim (n≮n (suc k) (≤′⇒≤ l₂))
  up k (node (node t t') (tipN x))    (step l₁)    l₂         = tipN (unTip (up _ (node t t') l₁ (base refl)) ∷ʳ x) -- Case 2
  up k (node (node t t') (node u u')) (base refl)  l₂         = ⊥-elim (n≮0 (≤-pred (≤-pred (≤′⇒≤ l₂))))
  up k (node (node t t') (node u u')) (step l₁)   (base refl) = ⊥-elim (unbounded u')
  up k (node (node t t') (node u u')) (step l₁)   (step l₂)   = node (zipBW _∷ʳ_ (up _ (node t t') l₁ (≤⇒≤′ (<⇒≤ (≤′⇒≤ l₂)))) (node u u')) (up _ (node u u') l₁ l₂) -- Case 3.2

  -- A variant of the function that follows the case analysis structure of the derivation/proof
  -- Reordering the arguments to show the case analysis structure/order more clearly
  -- 2 ≤ n → suc (suc k) ≤ n → ∀ k → ...
  up' : 2 ≤ n → ∀ k → suc (suc k) ≤ n → BTree A n (suc k) → BTree (Vec A (suc (suc k))) n (suc (suc k))
  up' (base refl) k      (base refl) (node (tip0 x)    (tipN y))    = tipN (x ∷ y ∷ []) -- Case 1
  up' (base refl) k      (step l₂)    t                             with step (base ()) ← l₂
  up' (step l₁)   k      (base refl) (node (tip0 x)    (tipN y))    with step (base ()) ← l₁
  up' (step l₁) .(suc _) (base refl) (node (node t t') (tipN x))    = tipN (unTip (up' l₁ _ (base refl) (node t t')) ∷ʳ x) -- Case 2
  up' (step l₁) .(suc _) (base refl) (node (node t t') (node u u')) = ⊥-elim (unbounded u')
  up' (step l₁)   zero   (step l₂)   (tipN x)                       = ⊥-elim (n≮0 (≤′⇒≤ l₂))
  up' (step l₁)   zero   (step l₂)   (node (tip0 x)     u)          = node (mapB (λ q → x ∷ q ∷ []) u) (up' l₁ zero l₂ u) -- Case 3.1
  up' (step l₁)  (suc k) (step l₂)   (tipN x)                       = ⊥-elim (n≮n (suc (suc k)) (≤′⇒≤ (step l₂)))
  up' (step l₁)  (suc k) (step l₂)   (node t            u)          = node (zipBW _∷ʳ_ (up' l₁ k (≤⇒≤′ (≤-pred (≤′⇒≤ (step l₂)))) t) u) (up' l₁ (suc k) l₂ u) -- Case 3.2

  -- The whole story:
  -- upSpec : 2 ≤ n → ∀ k → suc (suc k) ≤ n → ∀ t → ch k xs ≡ t → up t ≡ mapB subs (ch (suc k) xs)
  -- upSpec : 2 ≤ n → ∀ k → suc (suc k) ≤ n → ∀ t → Ch k xs t   → ∃ (λ t' → t' ≡ mapB subs (ch (suc k) xs))
  -- retab' : 2 ≤ n → ∀ k → suc (suc k) ≤ n → BT ...            → BT ...

module Part3 -- Basic Analysis
  where

  -- Goguen, McBride, and McKinna [2006]. Eliminating dependent pattern matching.
  -- McBride [2002]. Elimination with a motive.

  -- Standard eliminator
  -- Mixing case analysis and recursion
  -- Assuming that the whole input is exactly the things to be eliminated
  elim-≤ : (P : (m n : ℕ) → m ≤ n → Set)
        → ({m n : ℕ} {m≡n : m ≡ n} → P m n (base m≡n))
        → ({m n : ℕ} {m≤n : m ≤ n} → P m n m≤n → P m (suc n) (step m≤n))
        → (m n : ℕ) (m≤n : m ≤ n) → P m n m≤n
  elim-≤ P pb ps m .m       (base refl) = pb
  elim-≤ P pb ps m .(suc _) (step m≤n)  = ps (elim-≤ P pb ps m _ m≤n)

  -- McBride [2004]. Epigram: Practical programming with dependent types.
  -- The plus example (Section 2)

  -- Case analysis only
  case-≤ : (P : ∀ m n → m ≤ n → Set)
        → ((m n : ℕ) (m≡n : m ≡ n) → P m n (base m≡n))
        → ((m n : ℕ) (m≤n : m ≤ n) → P m (suc n) (step m≤n))
        → (m n : ℕ) (m≤n : m ≤ n) → P m n m≤n
  case-≤ P pb ps m n m≤n = elim-≤ P (λ {m₀ n₀ m₀≡n₀} → pb m₀ n₀ m₀≡n₀) (λ {m₀ n₀ m₀≤n₀} _ → ps m₀ n₀ m₀≤n₀) m n m≤n

  -- Generalize to an arbitrary dependent function type
  -- t: Extract the data and its indices from the input
  -- Each case is the original function type augmented with constraints.
  -- Systematically derivable from the case operator
  -- Each case starts with a new quantification over δ; instantiate P to end with T δ and add constraints on the extracted data and indices.
  basic-case-≤ : (Δ : Set) (T : Δ → Set) (t : Δ → Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] (m ≤ n))
              → ((δ : Δ) (m n : ℕ) (m≡n : m ≡ n) → (m , n , base m≡n) ≡ t δ → T δ)
              → ((δ : Δ) (m n : ℕ) (m≤n : m ≤ n) → (m , suc n , step m≤n) ≡ t δ → T δ)
              → (δ : Δ) → T δ
  basic-case-≤ Δ T t m₁ m₂ δ = let (m , n , m≤n) = t δ in case-≤ (λ m n m≤n → (δ : Δ) → (m , n , m≤n) ≡ t δ → T δ) (λ m n m≡n δ → m₁ δ m n m≡n) (λ m n m≤n δ → m₂ δ m n m≤n) m n m≤n δ refl

  -- Recursion: The rec operator (strong induction)
  Below-≤ : (P : ∀ m n → m ≤ n → Set) → ∀ m n → m ≤ n → Set
  Below-≤ P m .m       (base refl) = ⊤
  Below-≤ P m .(suc _) (step m≤n)  = Below-≤ P m _ m≤n × P m _ m≤n

  below-≤ : (P : ∀ m n → m ≤ n → Set)
          → (p : ∀ m n → (m≤n : m ≤ n) → Below-≤ P m n m≤n → P m n m≤n)
          → ∀ m n → (m≤n : m ≤ n) → Below-≤ P m n m≤n
  below-≤ P p m .m       (base refl) = tt
  below-≤ P p m .(suc _) (step m≤n)  = let b = below-≤ P p m _ m≤n
                                      in (b , p m _ m≤n b)

  -- Below: Results of recursive calls on all structurally smaller data
  rec-≤ : (P : ∀ m n → m ≤ n → Set)
        → (∀ m n → (m≤n : m ≤ n) → Below-≤ P m n m≤n → P m n m≤n)
        → ∀ m n → (m≤n : m ≤ n) → P m n m≤n
  rec-≤ P p m n m≤n = p m n m≤n (below-≤ P p m n m≤n)

  -- Derived basic analysis
  basic-rec-≤ : (Δ : Set) (T : Δ → Set) (t : (δ : Δ) → Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] (m ≤ n))
              → ((δ : Δ) (m n : ℕ) (m≤n : m ≤ n) → (b : Below-≤ (λ m n m≤n → (δ : Δ) → (m , n , m≤n) ≡ t δ → T δ) m n m≤n) → (m , n , m≤n) ≡ t δ → T δ)
              → (δ : Δ) → T δ
  basic-rec-≤ Δ T t p δ = let (m , n , m≤n) = t δ in rec-≤ (λ m n m≤n → (δ : Δ) → (m , n , m≤n) ≡ t δ → T δ) (λ m n m≤n b δ → p δ m n m≤n b) m n m≤n δ refl

  -- ℕPair
  -- Non-standard eliminator
  elim-ℕPair : (P : ℕ × ℕ → Set)
            → P (zero , zero)
            → ({n : ℕ} → P (zero , n) → P (zero , suc n))
            → ({m : ℕ} → P (m , zero) → P (suc m , zero))
            → ({m n : ℕ} → P (m , n) → P (suc m , n) → P (m , suc n) → P (suc m , suc n))
            → ((m , n) : ℕ × ℕ) → P (m , n)
  elim-ℕPair p pz psₙ psₘ ps (zero  , zero)  = pz
  elim-ℕPair p pz psₙ psₘ ps (zero  , suc n) = psₙ (elim-ℕPair p pz psₙ psₘ ps (zero , n))
  elim-ℕPair p pz psₙ psₘ ps (suc m , zero ) = psₘ (elim-ℕPair p pz psₙ psₘ ps (m , zero))
  elim-ℕPair p pz psₙ psₘ ps (suc m , suc n) = ps (elim-ℕPair p pz psₙ psₘ ps (m , n)) (elim-ℕPair p pz psₙ psₘ ps (suc m , n)) (elim-ℕPair p pz psₙ psₘ ps (m , suc n))

  case-ℕPair : (P : ℕ × ℕ → Set)
            → P (zero , zero)
            → ((n : ℕ) → P (zero , suc n))
            → ((m : ℕ) → P (suc m , zero))
            → ((m n : ℕ) → P (suc m , suc n))
            → (m n : ℕ) → P (m , n)
  case-ℕPair P pz pn pm ps zero zero = pz
  case-ℕPair P pz pn pm ps zero (suc n) = pn n
  case-ℕPair P pz pn pm ps (suc m) zero = pm m
  case-ℕPair P pz pn pm ps (suc m) (suc n) = ps m n

  basic-case-ℕPair : (Δ : Set) (T : Δ → Set) (t : Δ → ℕ × ℕ)
                  → ((δ : Δ) → (zero , zero) ≡ t δ → T δ)
                  → ((δ : Δ) (n : ℕ) → (zero , suc n) ≡ t δ → T δ)
                  → ((δ : Δ) (m : ℕ) → (suc m , zero) ≡ t δ → T δ)
                  → ((δ : Δ) (m n : ℕ) → (suc m , suc n) ≡ t δ → T δ)
                  → (δ : Δ) → T δ
  basic-case-ℕPair Δ T t p₁ p₂ p₃ p₄ δ = let (m , n) = t δ in case-ℕPair (λ (m , n) → (δ : Δ) → (m , n) ≡ t δ → T δ) p₁ (λ n δ → p₂ δ n) (λ m δ → p₃ δ m) (λ m n δ → p₄ δ m n) m n δ refl

  Below-ℕPair : (P : ℕ × ℕ → Set) → ℕ → ℕ → Set
  Below-ℕPair P  zero    zero   = ⊤
  Below-ℕPair P  zero   (suc n) = Below-ℕPair P zero n × P (zero , n)
  Below-ℕPair P (suc m)  zero   = Below-ℕPair P m zero × P (m , zero)
  Below-ℕPair P (suc m) (suc n) = (Below-ℕPair P (suc m) n × P (suc m , n)) × (Below-ℕPair P m (suc n) × P (m , suc n)) × (Below-ℕPair P m n × P (m , n))

  below-ℕPair : (P : ℕ × ℕ → Set)
              → (p : (m n : ℕ) → Below-ℕPair P m n → P (m , n))
              → (m n : ℕ) → Below-ℕPair P m n
  below-ℕPair P p  zero    zero   = tt
  below-ℕPair P p  zero   (suc n) = let b = below-ℕPair P p zero n in (b , p zero n b)
  below-ℕPair P p (suc m)  zero   = let b = below-ℕPair P p m zero in (b , p m zero b)
  below-ℕPair P p (suc m) (suc n) = let bₙ = below-ℕPair P p (suc m) n
                                        bₘ = below-ℕPair P p m (suc n)
                                        b = below-ℕPair P p m n
                                    in ((bₙ , p (suc m) n bₙ) , (bₘ , p m (suc n) bₘ) , (b , p m n b))

  rec-ℕPair : (P : ℕ × ℕ → Set)
            → ((m n : ℕ) → Below-ℕPair P m n → P (m , n))
            → (m n : ℕ) → P (m , n)
  rec-ℕPair P p m n = p m n (below-ℕPair P p m n)

  basic-rec-ℕPair : (Δ : Set) (T : Δ → Set) (t : (δ : Δ) → ℕ × ℕ)
                  → ((δ : Δ) (m n : ℕ) → (b : Below-ℕPair (λ (m , n) → (δ : Δ) → (m , n) ≡ t δ → T δ) m n) → (m , n) ≡ t δ → T δ)
                  → (δ : Δ) → T δ
  basic-rec-ℕPair Δ T t p δ = let (m , n) = t δ in rec-ℕPair (λ (m , n) → (δ : Δ) → (m , n) ≡ t δ → T δ) (λ m n b δ → p δ m n b) m n δ refl

open Part3

module Part4 -- Translation to basic analysis operators (eliminating dependent pattern matching)
  where
    -- To use a basic analysis, pass in all the inputs, and get some new arguments:
    --   basic-rec:  recursive subresults
    --   basic-case: constraints
    -- All inputs should be passed in to allow specialization by unification (for example expanding the Below argument in a subsequent basic-case).
    -- Constraints can be solved right away or passed as inputs to the next level.

    -- Example:
    -- wk : (m n : ℕ) → suc m ≤ n → m ≤ n
    -- wk m .(suc m) (base refl)    = step (base refl)
    -- wk m .(suc n) (step {n} m<n) = step (wk m n m<n)

    wk : (m n : ℕ) → suc m ≤ n → m ≤ n
    wk m n m<n =
      let P : (m n : ℕ) → m ≤ n → Set
          P = λ Dm Dn Dm<n → ((m , n , m<n) : Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) → (Dm , Dn , Dm<n) ≡ (suc m , n , m<n) → m ≤ n
      in  basic-rec-≤ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) (λ (m , n , _) → m ≤ n) (λ (m , n , m<n) → (suc m , n , m<n))
            (λ {(m , n , m<n) .(suc m) .n .m<n b refl →
                basic-case-≤ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] Σ[ m<n ∈ suc m ≤ n ] Below-≤ P (suc m) n m<n) (λ (m , n , _) → m ≤ n) (λ (m , n , m<n , _) → (suc m , n , m<n))
                  (λ {(m , n     , base refl , b) .(suc m) .n .refl refl → step (base refl) })
                  (λ {(m , suc n , step m≤n  , b) .(suc m) .n .m≤n  refl → let (_ , b') = b in step (b' (m , n , m≤n) refl) })
                 (m , n , m<n , b) })
           (m , n , m<n)

module Part5 -- Laws/transformations
  where

  -- Redundant case analysis:
  {-    lhs ⇒ rhs
     =  lhs ⇐ case ... {
          lhs'  ⇒ rhs'
          lhs'' ⇒ rhs'' }
  -}

  -- Swapping of nested case analyses
  {-   case x {
          x0 ⇒ case y { y0 ⇒ ...
                        y1 ⇒ ... }
          x1 ⇒ case y { y0 ⇒ ...
                        y1 ⇒ ... } }
     = case y {
          y0 ⇒ case x { x0 ⇒ ...
                        x1 ⇒ ... }
          y1 ⇒ case x { x0 ⇒ ...
                        x1 ⇒ ... } }
  -}

  -- Key: What basic case operators do is only add constraints.
  -- To-do: datatype-generic theorems

  -- What about basic-rec?
  -- Reducing induction on (indexed) data to induction on (indices that work as a) termination measure

  -- Back to wk v.s. wk', does the redundant case analysis transformation actually apply in the ‘base’ case?

  -- Expand All Cases
  -- wk₁ : (m n : ℕ) → suc m ≤ n → m ≤ n
  -- wk₁  zero    zero          (base _)    = base refl
  -- wk₁  zero   (suc .zero)    (base refl) = step (base refl)
  -- wk₁  zero   (suc n)        (step m<n)  = step (wk₁ zero n m<n)
  -- wk₁ (suc m)  zero          (base ())
  -- wk₁ (suc m) (suc .(suc m)) (base refl) = step (base refl)
  -- wk₁ (suc m) (suc n)        (step m<n)  = step (wk₁ (suc m) n m<n)
  wk₁ : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk₁ m n m<n = let P = λ (Dm , Dn) → ((m , n , m<n) : Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) → (Dm , Dn) ≡ (suc m , n) → m ≤ n
                 in basic-rec-ℕPair (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) (λ (m , n , _) → m ≤ n) (λ (m , n , _) → (suc m , n))
                                    (λ {(m , n , m<n) .(suc m) .n b refl →
                                        basic-case-ℕPair (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] Σ[ m<n ∈ suc m ≤ n ] Below-ℕPair P (suc m) n) (λ (m , n , _) → m ≤ n) (λ (m , n , _) → (m , n))
                                                         (λ {(.zero , .zero , m<n , b) refl →
                                                             basic-case-≤ (suc zero ≤ zero × Below-ℕPair P (suc zero) zero) (λ _ → zero ≤ zero) (λ (m<n , _) → (suc zero , zero , m<n))
                                                                          (λ {(m<n , b) m₀ n₀ m₀≡n₀ refl → base refl})
                                                                          (λ {(m<n , b) m₀ n₀ m₀≤n₀ ()})
                                                             (m<n , b)})
                                                         (λ {(.zero , .(suc nₚ) , m<n , b) nₚ refl →
                                                             basic-case-≤ (Σ[ nₚ ∈ ℕ ] suc zero ≤ suc nₚ × Below-ℕPair P (suc zero) (suc nₚ)) (λ (nₚ , _) → zero ≤ suc nₚ) (λ (nₚ , m<n , _) → (suc zero , suc nₚ , m<n))
                                                                          (λ {(.zero , m<n , b) m₀ n₀ refl refl → step (base refl)})
                                                                          (λ {(nₚ , .(step m₀≤n₀) , b) m₀ n₀ m₀≤n₀ refl → let ((_ , b') , _) = b in step (b' (zero , nₚ , m₀≤n₀) refl)})
                                                             (nₚ , m<n , b)})
                                                         (λ {(.(suc mₚ) , .zero , m<n , b) mₚ refl →
                                                             basic-case-≤ (Σ[ mₚ ∈ ℕ ] suc (suc mₚ) ≤ zero × Below-ℕPair P (suc (suc mₚ)) zero) (λ (mₚ , _) → suc mₚ ≤ zero) (λ (mₚ , m<n , _) → (suc (suc mₚ) , zero , m<n))
                                                                          (λ {(mₚ , .(base _) , b) m₀ n₀ () refl})
                                                                          (λ {(mₚ , m<n , b) m₀ n₀ m₀≤n₀ ()})
                                                             (mₚ , m<n , b)})
                                                         (λ {(.(suc mₚ) , .(suc nₚ) , m<n , b) mₚ nₚ refl →
                                                             basic-case-≤ (Σ[ mₚ ∈ ℕ ] Σ[ nₚ ∈ ℕ ] suc (suc mₚ) ≤ suc nₚ × Below-ℕPair P (suc (suc mₚ)) (suc nₚ)) (λ (mₚ , nₚ , _) → suc mₚ ≤ suc nₚ) (λ (mₚ , nₚ , m<n , _) → (suc (suc mₚ) , suc nₚ , m<n))
                                                                          (λ {(mₚ , .(suc mₚ) , .(base refl) , b) m₀ n₀ refl refl → step (base refl)})
                                                                          (λ {(mₚ , nₚ , .(step m₀≤n₀) , b) m₀ n₀ m₀≤n₀ refl → let ((_ , b') , _) = b in step (b' (suc mₚ , nₚ , m₀≤n₀) refl)})
                                                             (mₚ , nₚ , m<n , b)})
                                        (m , n , m<n , b)})
                    (m , n , m<n)

  -- Delayed constraints
  wk₁．₄ : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk₁．₄ m n m<n = let P = λ (Dm , Dn) → ((m , n , m<n) : Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) → (Dm , Dn) ≡ (suc m , n) → m ≤ n
                  in basic-rec-ℕPair (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) (λ (m , n , _) → m ≤ n) (λ (m , n , _) → (suc m , n))
                                     (λ {(m , n , m<n) .(suc m) .n b refl →
                                         basic-case-ℕPair (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n × Below-ℕPair P (suc m) n) (λ (m , n , _) → m ≤ n) (λ (m , n , _) → (m , n))
                                                          (λ {(m , n , m<n , b) r →
                                                              basic-case-≤ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n × Below-ℕPair P (suc m) n × (zero , zero) ≡ (m , n)) (λ (m , n , _) → m ≤ n) (λ (m , n , m<n , _) → (suc m , n , m<n))
                                                                           (λ {(m , n , m<n , b , refl) m₀ n₀ m₀≡n₀ refl → base refl})
                                                                           (λ {(m , n , m<n , b , refl) m₀ n₀ m₀≤n₀ ()})
                                                              (m , n , m<n , b , r)})
                                                          (λ {(m , n , m<n , b) nₚ r →
                                                              basic-case-≤ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n × Below-ℕPair P (suc m) n × Σ[ nₚ ∈ ℕ ] (zero , suc nₚ) ≡ (m , n)) (λ (m , n , _) → m ≤ n) (λ (m , n , m<n , _) → (suc m , n , m<n))
                                                                           (λ {(m , n , m<n , b , nₚ , refl) m₀ n₀ refl  refl → step (base refl)})
                                                                           (λ {(m , n , m<n , b , nₚ , refl) m₀ n₀ m₀≤n₀ refl → let ((_ , b') , _) = b in step (b' (zero , nₚ , m₀≤n₀) refl)})
                                                              (m , n , m<n , b , nₚ , r)})
                                                          (λ {(m , n , m<n , b) mₚ r →
                                                              basic-case-≤ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n × Below-ℕPair P (suc m) n × Σ[ mₚ ∈ ℕ ] (suc mₚ , zero) ≡ (m , n)) (λ (m , n , _) → m ≤ n) (λ (m , n , m<n , _) → (suc m , n , m<n))
                                                                           (λ {(m , n , m<n , b , mₚ , refl) m₀ n₀ () refl})
                                                                           (λ {(m , n , m<n , b , mₚ , refl) m₀ n₀ m₀≤n₀ ()})
                                                              (m , n , m<n , b , mₚ , r)})
                                                          (λ {(m , n , m<n , b) mₚ nₚ r →
                                                              basic-case-≤ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n × Below-ℕPair P (suc m) n × Σ[ mₚ ∈ ℕ ] Σ[ nₚ ∈ ℕ ] (suc mₚ , suc nₚ) ≡ (m , n)) (λ (m , n , _) → m ≤ n) (λ (m , n , m<n , _) → (suc m , n , m<n))
                                                                           (λ {(m , n , m<n , b , mₚ , nₚ , refl) m₀ n₀ refl  refl → step (base refl)})
                                                                           (λ {(m , n , m<n , b , mₚ , nₚ , refl) m₀ n₀ m₀≤n₀ refl → let ((_ , b') , _) = b in step (b' (suc mₚ , nₚ , m₀≤n₀) refl)})
                                                              (m , n , m<n , b , mₚ , nₚ , r)})
                                         (m , n , m<n , b)})
                     (m , n , m<n)

  -- Swapping of nested case analyses
  -- (Now the methods of the first basic-case-ℕPair can be individually rewritten to the same one modulo substitution.)
  wk₁．₅ : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk₁．₅ m n m<n =
    let P = λ (Dm , Dn) → ((m , n , m<n) : Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) → (Dm , Dn) ≡ (suc m , n) → m ≤ n
    in basic-rec-ℕPair (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n) (λ (m , n , _) → m ≤ n) (λ (m , n , _) → (suc m , n))
         (λ { (m , n , m<n) .(suc m) .n b refl →
                basic-case-≤ (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] suc m ≤ n × Below-ℕPair P (suc m) n) (λ (m , n , _) → m ≤ n) (λ (m , n , m<n , _) → (suc m , n , m<n))
                  (λ { (m , n , m<n , b) m₀ n₀ m₀≡n₀ r' →
                         basic-case-ℕPair (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] Σ[ m<n ∈ suc m ≤ n ] Below-ℕPair P (suc m) n × Σ[ m₀ ∈ ℕ ] Σ[ n₀ ∈ ℕ ] Σ[ m₀≡n₀ ∈ m₀ ≡ n₀ ] (m₀ , n₀ , base m₀≡n₀) ≡ (suc m , n , m<n)) (λ (m , n , _) → m ≤ n) (λ (m , n , _) → (m , n))
                           (λ { (m , n , m<n , b , m₀ , n₀ , m₀≡n₀ , refl)       refl → base refl })
                          --  (λ { (m , n , m<n , b , m₀ , n₀ , refl , refl)       r → step (base refl) })
                           (λ { (m , n , m<n , b , m₀ , n₀ , refl  , refl)    nₚ refl → step (base refl) })
                          --  (λ { (m , n , m<n , b , m₀ , n₀ , refl , refl)    nₚ r → step (base refl) })
                           (λ { (m , n , m<n , b , m₀ , n₀ , ()    , refl) mₚ    refl })
                          --  (λ { (m , n , m<n , b , m₀ , n₀ , refl , refl) mₚ    r → step (base refl) })
                           (λ { (m , n , m<n , b , m₀ , n₀ , refl  , refl) mₚ nₚ refl → step (base refl) })
                          --  (λ { (m , n , m<n , b , m₀ , n₀ , refl , refl) mₚ nₚ r → step (base refl) })
                           (m , n , m<n , b , m₀ , n₀ , m₀≡n₀ , r') })
                  (λ { (m , n , m<n , b) m₀ n₀ m₀≤n₀ r' →
                         basic-case-ℕPair (Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] Σ[ m<n ∈ suc m ≤ n ] Below-ℕPair P (suc m) n × Σ[ m₀ ∈ ℕ ] Σ[ n₀ ∈ ℕ ] Σ[ m₀≤n₀ ∈ m₀ ≤ n₀ ] (m₀ , suc n₀ , step m₀≤n₀) ≡ (suc m , n , m<n)) (λ (m , n , _) → m ≤ n) (λ (m , n , _) → (m , n))
                           (λ { (m , n , m<n , b , m₀ , n₀ , m₀≤n₀ , ()  )       refl })
                           (λ { (m , n , m<n , b , m₀ , n₀ , m₀≤n₀ , refl)    nₚ refl → let ((_ , b') , _) = b in step (b' (zero   , nₚ , m₀≤n₀) refl) })
                           (λ { (m , n , m<n , b , m₀ , n₀ , m₀≤n₀ , ()  ) mₚ    refl })
                           (λ { (m , n , m<n , b , m₀ , n₀ , m₀≤n₀ , refl) mₚ nₚ refl → let ((_ , b') , _) = b in step (b' (suc mₚ , nₚ , m₀≤n₀) refl) })
                           (m , n , m<n , b , m₀ , n₀ , m₀≤n₀ , r')})
                  (m , n , m<n , b)})
         (m , n , m<n)

  -- Difficulty: the laws hold at the basic analysis level (in particular the ‘delayed constraints’ transformation), not the pattern matching level,
  --             and they are quite tedious.

module Part6 -- Fording to the rescue
  where

  -- 3. Eliminate Redundant Case Analysis (for step; what about base?)
  wk₃ : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk₃  zero    zero          (base _)    = base refl
  wk₃  zero   (suc .zero)    (base refl) = step (base refl)
  wk₃ (suc m)  zero          (base ())
  wk₃ (suc m) (suc .(suc m)) (base refl) = step (base refl)
  wk₃ m       (suc n)        (step m<n)  = step (wk₃ m n m<n)

  -- 4. Fording to allow unified goal types (with different constraints)
  wk₄ : (m n : ℕ) → suc m ≤ n → (m' n' : ℕ) → m' ≡ m → n' ≡ n → m ≤ n
  wk₄ m n (base _)     zero     zero           refl refl = base refl
  wk₄ m n (base refl)  zero    (suc .zero)     refl refl = step (base refl)
  wk₄ m n (base ())   (suc m')  zero           refl refl
  wk₄ m n (base refl) (suc m') (suc .(suc m')) refl refl = step (base refl)
  wk₄ m n (step m<n)  m'       (suc n')        refl refl = step (wk₄ _ _ m<n m' n' refl refl)

  -- 5. Rewrite equationally
  wk₅ : (m n : ℕ) → suc m ≤ n → (m' n' : ℕ) → m' ≡ m → n' ≡ n → m ≤ n
  wk₅ m n (base refl)  zero     zero    meq  neq  = step (base refl)
  wk₅ m n (base refl)  zero    (suc n') meq  neq  = step (base refl)
  wk₅ m n (base refl) (suc m')  zero    meq  neq  = step (base refl)
  wk₅ m n (base refl) (suc m') (suc n') meq  neq  = step (base refl)
  wk₅ m n (step m<n)  m'       (suc n') refl refl = step (wk₅ _ _ m<n m' n' refl refl)

  -- 6. Eliminate Redundant Case Analysis for base
  wk₆ : (m n : ℕ) → suc m ≤ n → (m' n' : ℕ) → m' ≡ m → n' ≡ n → m ≤ n
  wk₆ m n (base refl) m' n'       meq  neq  = step (base refl)
  wk₆ m n (step m<n)  m' (suc n') refl refl = step (wk₆ _ _ m<n m' n' refl refl)

  -- 7. Rewrite equationally (matching refl again)
  wk₇ : (m n : ℕ) → suc m ≤ n → (m' n' : ℕ) → m' ≡ m → n' ≡ n → m ≤ n
  wk₇ m n (base refl) m' n'       refl refl = step (base refl)
  wk₇ m n (step m<n)  m' (suc n') refl refl = step (wk₇ _ _ m<n m' n' refl refl)

  -- 8. Unfording
  wk : (m n : ℕ) → suc m ≤ n → m ≤ n
  wk m n       (base refl) = step (base refl)
  wk m (suc n) (step m<n)  = step (wk m n m<n)

  -- Requires K
  rewriteEqArg : {P : A → A → Set} {x y : A} (f : x ≡ y → P x y) → (eq eq' : x ≡ y) → f eq ≡ f eq'
  rewriteEqArg f refl refl = refl
