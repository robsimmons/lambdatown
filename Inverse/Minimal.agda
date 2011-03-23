open import Prelude 

module Inverse.Minimal where

infixr 5 _⊃_

data Base : Set where
   atm : String → Base
   typ : Base 

data Class : Set where
   con : (Q : Base) → Class
   _⊃_ : (A : Class) (B : Class) → Class
   _∧_ : (A B : Class) → Class

{- Contexts and inclusion in contexts -}

Ctx = List Class

open LIST.SET public
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub



module MINIMAL (sig : String → Maybe Class) where


   {- PART 1: LOGIC -}

   data Head (Γ : Ctx) : Class → Set where
      var : ∀{A} (x : A ∈ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   -- K : Skel Δ A C is the pattern judgment Δ ⊩ K : A > C
   data Skel : Ctx → Class → Class → Set where
      ⟨⟩ : ∀{A} → Skel [] A A
      ·_ : ∀{Δ₂ A B C}
         (K : Skel Δ₂ B C)
         → Skel (A :: Δ₂) (A ⊃ B) C
      π₁ : ∀{Δ A B C}
         (K : Skel Δ A C)
         → Skel Δ (A ∧ B) C
      π₂ : ∀{Δ A B C}
         (K : Skel Δ B C)
         → Skel Δ (A ∧ B) C
   
   infixr 21 _·_[_]
   mutual
      -- σ : Subst Γ Δ is the derivation Γ ⊢ σ : Δ
      data Subst (Γ : Ctx) : Ctx → Set where
         ⟨⟩ : Subst Γ []
         _,_ : ∀{A Δ}
            (N : Term Γ A) 
            (σ : Subst Γ Δ)
            → Subst Γ (A :: Δ) 

      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term (Γ : Ctx) : Class → Set where
         _·_[_] : ∀{A Q Δ}
            (h : Head Γ A)
            (K : Skel Δ A (con Q))
            (σ : Subst Γ Δ)
            → Term Γ (con Q)
         Λ : ∀{A B}
            (N : Term (A :: Γ) B)
            → Term Γ (A ⊃ B)
         _,_ : ∀{A B}
            (N₁ : Term Γ A)
            (N₂ : Term Γ B)
            → Term Γ (A ∧ B) 


   {- PART 2: METRIC (TOTALLY NAMELESS REPRESENTATION -}

   -- Totally nameless terms
   data trm : Set where
      con : (s : List trm) → trm
      Λ : (n : trm) → trm
      _,_ : (n₁ n₂ : trm) → trm

   -- Terms with the metric
   mutual
      data Subst' (Γ : Ctx) : List trm → Ctx → Set where
         ⟨⟩ : Subst' Γ [] []
         _,_ : ∀{A Δ n s}
            (N : Term' Γ n A) 
            (σ : Subst' Γ s Δ)
            → Subst' Γ (n :: s) (A :: Δ) 

      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term' (Γ : Ctx) : trm → Class → Set where
         _·_[_] : ∀{A Q Δ s}
            (h : Head Γ A)
            (K : Skel Δ A (con Q))
            (σ : Subst' Γ s Δ)
            → Term' Γ (con s) (con Q)
         Λ : ∀{A B n}
            (N : Term' (A :: Γ) n B)
            → Term' Γ (Λ n) (A ⊃ B)
         _,_ : ∀{A B n₁ n₂}
            (N₁ : Term' Γ n₁ A)
            (N₂ : Term' Γ n₂ B)
            → Term' Γ (n₁ , n₂) (A ∧ B) 
            
   -- Metric erasure
   mutual 
      m→ : ∀{Γ n A} → Term' Γ n A → Term Γ A
      m→ (h · K [ σ ]) = h · K [ mσ→ σ ]
      m→ (Λ N) = Λ (m→ N)
      m→ (N₁ , N₂) = m→ N₁ , m→ N₂ 

      mσ→ : ∀{Γ s Δ} → Subst' Γ s Δ → Subst Γ Δ
      mσ→ ⟨⟩ = ⟨⟩
      mσ→ (N , σ) = m→ N , mσ→ σ

   -- Metric calculation
   mutual
      mN : ∀{Γ A} → Term Γ A → trm
      mN (h · K [ σ ]) = con (mσ σ)
      mN (Λ N) = Λ (mN N)
      mN (N₁ , N₂) = mN N₁ , mN N₂

      mσ : ∀{Γ Δ} → Subst Γ Δ → List trm
      mσ ⟨⟩ = []
      mσ (N , σ) = mN N :: mσ σ

   -- Metric addition 
   mutual
      →m : ∀{Γ A} (N : Term Γ A) → Term' Γ (mN N) A
      →m (h · K [ σ ]) = h · K [ →mσ σ ]
      →m (Λ N) = Λ (→m N)
      →m (N₁ , N₂) = →m N₁ , →m N₂

      →mσ : ∀{Γ Δ} (σ : Subst Γ Δ) → Subst' Γ (mσ σ) Δ
      →mσ ⟨⟩ = ⟨⟩
      →mσ (N , σ) = →m N , →mσ σ


   {- PART 3: GENERALIZED WEAKENING (a.k.a. renaming, context renaming) -}

   mutual
      wk' : ∀{Γ Γ' A n} → Γ ⊆ Γ' → Term' Γ n A → Term' Γ' n A
      wk' θ (var x · K [ σ ]) = var (θ x) · K [ wkσ' θ σ ]
      wk' θ (con c · K [ σ ]) = con c · K [ wkσ' θ σ ]
      wk' θ (Λ N) = Λ (wk' (sub-cons-congr θ) N)
      wk' θ (N₁ , N₂) = wk' θ N₁ , wk' θ N₂

      wkσ' : ∀{Γ Γ' s Δ} → Γ ⊆ Γ' → Subst' Γ s Δ → Subst' Γ' s Δ
      wkσ' θ ⟨⟩ = ⟨⟩
      wkσ' θ (N , σ) = wk' θ N , wkσ' θ σ

   wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
   wk θ N = m→ (wk' θ (→m N))

   wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
   wkσ θ σ = mσ→ (wkσ' θ (→mσ σ))


   {- PART 4: SUBSTITUTION -}

   mutual
      subN : ∀{Γ A C n} 
         → Term Γ A 
         → Term' (A :: Γ) n C 
         → Term Γ C
      subN M (Λ N) = Λ (subN (wk sub-wken M) (wk' sub-exch N))
      subN M (N₁ , N₂) = subN M N₁ , subN M N₂
      subN M (var (S x) · K [ σ ]) = var x · K [ subσ M σ ]
      subN M (con c · K [ σ ]) = con c · K [ subσ M σ ]
      subN M (var Z · K [ σ ]) = M • K [ subσ M σ ]

      _•_[_] : ∀{Γ Δ A C}
         → Term Γ A 
         → Skel Δ A C
         → Subst Γ Δ
         → Term Γ C
      M • ⟨⟩ [ σ ] = M
      Λ M • (· K) [ N , σ ] = (subN N (→m M)) • K [ σ ] 
      (M₁ , M₂) • (π₁ K) [ σ ] = M₁ • K [ σ ]
      (M₁ , M₂) • (π₂ K) [ σ ] = M₂ • K [ σ ]

      subσ : ∀{Γ Δ A s} 
         → Term Γ A 
         → Subst' (A :: Γ) s Δ
         → Subst Γ Δ
      subσ M ⟨⟩ = ⟨⟩
      subσ M (N , σ) = subN M N , subσ M σ


   {- PART 5: ETA-EXPANSION -}

   -- Mostly amounts to dealing with the fact that we don't have proper zippers

   ·' : ∀{Γ A B C} → Skel Γ A (B ⊃ C) → Skel (Γ ++ [ B ]) A C
   ·' ⟨⟩ = · ⟨⟩
   ·' (· K) = · ·' K
   ·' (π₁ K) = π₁ (·' K)
   ·' (π₂ K) = π₂ (·' K)    

   π₁' : ∀{Γ A B C} → Skel Γ A (B ∧ C) → Skel Γ A B
   π₁' ⟨⟩ = π₁ ⟨⟩
   π₁' (· K) = · π₁' K
   π₁' (π₁ K) = π₁ (π₁' K)
   π₁' (π₂ K) = π₂ (π₁' K)

   π₂' : ∀{Γ A B C} → Skel Γ A (B ∧ C) → Skel Γ A C
   π₂' ⟨⟩ = π₂ ⟨⟩
   π₂' (· K) = · π₂' K
   π₂' (π₁ K) = π₁ (π₂' K)
   π₂' (π₂ K) = π₂ (π₂' K)

   _,'_ : ∀{Γ Δ A} → Term Γ A → Subst Γ Δ → Subst Γ (Δ ++ [ A ])
   N ,' ⟨⟩ = N , ⟨⟩
   N ,' (N' , σ) = N' , (N ,' σ)

   eta : ∀{Γ Δ A} (B : Class) 
      → Head Γ A 
      → Skel Δ A B
      → Subst Γ Δ
      → Term Γ B
   eta (con Q) h K σ = h · K [ σ ]
   eta (A ⊃ B) (con c) K σ = 
      Λ (eta B (con c) (·' K) (eta _ (var Z) ⟨⟩ ⟨⟩ ,' wkσ sub-wken σ) )
   eta (A ⊃ B) (var x) K σ = 
      Λ (eta B (var (sub-wken x)) (·' K) (eta _ (var Z) ⟨⟩ ⟨⟩ ,' wkσ sub-wken σ))
   eta (A ∧ B) h K σ = eta A h (π₁' K) σ , eta B h (π₂' K) σ

   η : ∀{Γ A} → Term (A :: Γ) A
   η = eta _ (var Z) ⟨⟩ ⟨⟩

   η' : ∀{Γ A} → A ∈ Γ → Term Γ A
   η' x = eta _ (var x) ⟨⟩ ⟨⟩ 

   {- PART 6: APPLYING AND COMPOSING SUBSTITUTIONS -} 

   σ→ : ∀{Γ Δ A} → A ∈ Δ → Subst Γ Δ → Term Γ A
   σ→ () ⟨⟩
   σ→ Z (N , σ) = N
   σ→ (S x) (N , σ) = σ→ x σ

   -- XXX add to stdlib
   _⟩⟩_ : Ctx → Ctx → Ctx  
   [] ⟩⟩ γ = γ
   (a :: δ) ⟩⟩ γ = δ ⟩⟩ (a :: γ)

   sub-⟩⟩-l : ∀{δ γ} → γ ⊆ (δ ⟩⟩ γ)
   sub-⟩⟩-l {[]} n = n
   sub-⟩⟩-l {x :: xs} n = sub-⟩⟩-l {xs} (S n)

   sub-⟩⟩-r : ∀{δ γ} → δ ⊆ (δ ⟩⟩ γ)
   sub-⟩⟩-r {[]} () 
   sub-⟩⟩-r {x :: xs} Z = sub-⟩⟩-l {xs} Z
   sub-⟩⟩-r {x :: xs} (S n) = sub-⟩⟩-r {xs} n

   split-revappend : ∀{x ys} (xs : Ctx)
      → x ∈ (xs ⟩⟩ ys)
      → (x ∈ xs) + (x ∈ ys)
   split-revappend [] n = Inr n
   split-revappend (x :: xs) n with split-revappend xs n
   ... | Inl n' = Inl (S n')
   ... | Inr Z = Inl Z
   ... | Inr (S n') = Inr n'

   sub-exch-ra : ∀{δ a γ} → (δ ⟩⟩ (a :: γ)) ⊆ (a :: δ ⟩⟩ γ)
   sub-exch-ra {δ} n with split-revappend δ n
   ... | Inl n' = S (sub-⟩⟩-r n')
   ... | Inr Z = Z
   ... | Inr (S n') = S (sub-⟩⟩-l {δ} n')

   sub-ra-exch : ∀{δ a γ} → (a :: δ ⟩⟩ γ) ⊆ (δ ⟩⟩ (a :: γ))
   sub-ra-exch {δ} Z = sub-⟩⟩-l {δ} Z
   sub-ra-exch {δ} (S n) = 
      case (split-revappend δ n) sub-⟩⟩-r (λ x → sub-⟩⟩-l {δ} (S x))

   mutual
      ssubN : ∀{Δ Γ n A} → Subst Γ Δ → Term' (Δ ⟩⟩ Γ) n A → Term Γ A
      ssubN τ (var x · K [ σ ]) = 
         case (split-revappend _ x) 
          (λ x' → σ→ x' τ • K [ ssubσ τ σ ]) 
          (λ x' → var x' · K [ ssubσ τ σ ])
      ssubN τ (con c · K [ σ ]) = con c · K [ ssubσ τ σ ]
      ssubN {Δ} τ (Λ N) = Λ (ssubN (wkσ sub-wken τ) (wk' (sub-ra-exch {Δ}) N))
      ssubN τ (N₁ , N₂) = (ssubN τ N₁) , (ssubN τ N₂)

      ssubσ : ∀{Δ Γ s Δ'} → Subst Γ Δ → Subst' (Δ ⟩⟩ Γ) s Δ' → Subst Γ Δ'
      ssubσ τ ⟨⟩ = ⟨⟩
      ssubσ τ (N , σ) = ssubN τ N , ssubσ τ σ

   {- PART 7 : LEFT RULES -}