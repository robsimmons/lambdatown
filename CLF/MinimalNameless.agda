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

{- Skeletons -}

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
   
{- Definition of logic -}

module MINIMAL (sig : String → Maybe Type) where

   -- Metric (totally nameless terms)
   data trm : Set where
      con : (s : List trm) → trm
      Λ : (n : trm) → trm
      _,_ : (n₁ n₂ : trm) → trm

   -- Logic
   data Head (Γ : Ctx) : Type → Set where
      var : ∀{A} (x : A ∈ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   -- Outside the metric
   infixr 21 _·_[_]
   mutual
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
            
   -- Inside the metric
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
            
   -- WEAKENING
   mutual
      wk' : ∀{Γ Γ' A n} → Γ ⊆ Γ' → Term' Γ n A → Term' Γ' n A
      wk' θ (var x · K [ σ ]) = var (θ x) · K [ wkσ' θ σ ]
      wk' θ (con c · K [ σ ]) = con c · K [ wkσ' θ σ ]
      wk' θ (Λ N) = Λ (wk' (sub-cons-congr θ) N)
      wk' θ (N₁ , N₂) = wk' θ N₁ , wk' θ N₂

      wkσ' : ∀{Γ Γ' s Δ} → Γ ⊆ Γ' → Subst' Γ s Δ → Subst' Γ' s Δ
      wkσ' θ ⟨⟩ = ⟨⟩
      wkσ' θ (N , σ) = wk' θ N , wkσ' θ σ

   -- IN AND OUT OF THE METRIC
   mutual
      mN : ∀{Γ A} → Term Γ A → trm
      mN (h · K [ σ ]) = con (mσ σ)
      mN (Λ N) = Λ (mN N)
      mN (N₁ , N₂) = mN N₁ , mN N₂

      mσ : ∀{Γ Δ} → Subst Γ Δ → List trm
      mσ ⟨⟩ = []
      mσ (N , σ) = mN N :: mσ σ

   mutual 
      m→ : ∀{Γ n A} → Term' Γ n A → Term Γ A
      m→ (h · K [ σ ]) = h · K [ mσ→ σ ]
      m→ (Λ N) = Λ (m→ N)
      m→ (N₁ , N₂) = m→ N₁ , m→ N₂ 

      mσ→ : ∀{Γ s Δ} → Subst' Γ s Δ → Subst Γ Δ
      mσ→ ⟨⟩ = ⟨⟩
      mσ→ (N , σ) = m→ N , mσ→ σ

   mutual
      →m : ∀{Γ A} (N : Term Γ A) → Term' Γ (mN N) A
      →m (h · K [ σ ]) = h · K [ →mσ σ ]
      →m (Λ N) = Λ (→m N)
      →m (N₁ , N₂) = →m N₁ , →m N₂

      →mσ : ∀{Γ Δ} (σ : Subst Γ Δ) → Subst' Γ (mσ σ) Δ
      →mσ ⟨⟩ = ⟨⟩
      →mσ (N , σ) = →m N , →mσ σ

   wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
   wk θ N = m→ (wk' θ (→m N))

   -- SUBSTITUTION
   mutual
      -- Type A stays the same
      -- Term N gets smaller
      subst : ∀{Γ A C n} 
         → Term Γ A 
         → Term' (A :: Γ) n C 
         → Term Γ C
      subst M (var Z · K [ σ ]) = hred M K (substσ M σ)
      subst M (var (S x) · K [ σ ]) = var x · K [ substσ M σ ]
      subst M (con c · K [ σ ]) = con c · K [ substσ M σ ]
      subst M (Λ N) = Λ (subst (wk sub-wken M) (wk' sub-exch N))
      subst M ( N₁ , N₂ ) = subst M N₁ , subst M N₂

      -- Type A stays the same
      -- Substitution σ gets smaller
      substσ : ∀{Γ Δ A s} 
         → Term Γ A 
         → Subst' (A :: Γ) s Δ
         → Subst Γ Δ
      substσ M ⟨⟩ = ⟨⟩
      substσ M (N , σ) = subst M N , substσ M σ

      hred : ∀{Γ Δ A C}
         → Term Γ A 
         → Skel Δ A C
         → Subst Γ Δ
         → Term Γ C
      hred M ⟨⟩ σ = M
      hred (Λ M) (· K) (N , σ) = hred (subst N (→m M)) K σ 
      hred (M₁ , M₂) (π₁ K) σ = hred M₁ K σ
      hred (M₁ , M₂) (π₂ K) σ = hred M₂ K σ

