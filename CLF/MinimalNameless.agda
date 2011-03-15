open import Prelude 

module CLF.MinimalNameless where

infixr 5 _⊃_

data Type : Set where
   con : (Q : String) → Type
   _⊃_ : (A : Type) (B : Type) → Type
   _∧_ : (A B : Type) → Type

{- Contexts and inclusion in contexts -}

Ctx = List Type

open LIST.SET public
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub



module MINIMAL (sig : String → Maybe Type) where


   {- PART 1: LOGIC -}

   data Head (Γ : Ctx) : Type → Set where
      var : ∀{A} (x : A ∈ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   -- K : Skel Δ A C is the pattern judgment Δ ⊩ K : A > C
   data Skel : Ctx → Type → Type → Set where
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
      data Term (Γ : Ctx) : Type → Set where
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
      data Term' (Γ : Ctx) : trm → Type → Set where
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
      subst : ∀{Γ A C n} 
         → Term Γ A 
         → Term' (A :: Γ) n C 
         → Term Γ C
      subst M (Λ N) = Λ (subst (wk sub-wken M) (wk' sub-exch N))
      subst M ( N₁ , N₂ ) = subst M N₁ , subst M N₂
      subst M (var (S x) · K [ σ ]) = var x · K [ substσ M σ ]
      subst M (con c · K [ σ ]) = con c · K [ substσ M σ ]
      subst M (var Z · K [ σ ]) = red M K (substσ M σ)

      red : ∀{Γ Δ A C}
         → Term Γ A 
         → Skel Δ A C
         → Subst Γ Δ
         → Term Γ C
      red M ⟨⟩ σ = M
      red (Λ M) (· K) (N , σ) = red (subst N (→m M)) K σ 
      red (M₁ , M₂) (π₁ K) σ = red M₁ K σ
      red (M₁ , M₂) (π₂ K) σ = red M₂ K σ

      substσ : ∀{Γ Δ A s} 
         → Term Γ A 
         → Subst' (A :: Γ) s Δ
         → Subst Γ Δ
      substσ M ⟨⟩ = ⟨⟩
      substσ M (N , σ) = subst M N , substσ M σ


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

   eta : ∀{Γ Δ A} (B : Type) 
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


   {- PART 6: APPLYING AND COMPOSING SUBSTITUTIONS -} 

   lookup : ∀{Γ Γ' A} → A ∈ Γ' → Subst Γ Γ' → Term Γ A
   lookup () ⟨⟩
   lookup Z (N , σ) = N
   lookup (S x) (N , σ) = lookup x σ

   mutual
      _[_]N : ∀{Γ Γ' A} → Term Γ' A → Subst Γ Γ' → Term Γ A
      con c · K [ σ' ] [ σ ]N = con c · K [ σ' [ σ ]σ ]
      var x · K [ σ' ] [ σ ]N = red (lookup x σ) K (σ' [ σ ]σ)
      Λ N [ σ ]N = Λ (N [ η , wkσ sub-wken σ ]N)
      (N₁ , N₂) [ σ ]N = (N₁ [ σ ]N) , (N₂ [ σ ]N)

      _[_]σ : ∀{Γ Γ' Δ} → Subst Γ' Δ → Subst Γ Γ' → Subst Γ Δ
      ⟨⟩ [ σ ]σ = ⟨⟩
      (N , σ') [ σ ]σ = (N [ σ ]N) , (σ' [ σ ]σ)
