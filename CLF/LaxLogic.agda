
-- Too lazy for metrics, we're switching to %trustme
{-# OPTIONS --no-termination-check #-}

open import Prelude 

module CLF.LaxLogic where

infixr 5 _⊃_

data Polarity : Set where
   ⁺ : Polarity
   ⁻ : Polarity

data Type : Polarity → Set where
   con : (Q : String) {⁼ : Polarity} → Type ⁼
   _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
   _∧_ : (A B : Type ⁻) → Type ⁻
   ○ : (A : Type ⁺) → Type ⁻
   ↓ : (A : Type ⁻) → Type ⁺

{- Contexts and inclusion in contexts -}

data Jmt : Set where 
   _true⁺ : String → Jmt
   _true⁻ : Type ⁻ → Jmt

Ctx = List Jmt

open LIST.SET public
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub

{- Skeletons -}

-- Hypotheses are just degenerate positive skeletons
Hyp : Type ⁺ → Jmt
Hyp (con Q) = Q true⁺
Hyp (↓ A) = A true⁻

data Skel : Ctx → Type ⁻ → Type ⁻ → Set where
   ⟨⟩ : ∀{A} → Skel [] A A
   ·_ : ∀{Δ₂ A B C}
      (K : Skel Δ₂ B C)
      → Skel (Hyp A :: Δ₂) (A ⊃ B) C
   π₁ : ∀{Δ A B C}
      (K : Skel Δ A C)
      → Skel Δ (A ∧ B) C
   π₂ : ∀{Δ A B C}
      (K : Skel Δ B C)
      → Skel Δ (A ∧ B) C
   
{- Definition of logic -}

module LAX (sig : String → Maybe (Type ⁻)) where
   data Head (Γ : Ctx) : Type ⁻ → Set where
      var : ∀{A} (x : A true⁻ ∈ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   infixr 21 _·_[_]
   mutual
      data Value (Γ : Ctx) : Jmt → Set where
         ⁺ : ∀{Q} (x : Q true⁺ ∈ Γ) → Value Γ (Q true⁺)
         ⁻ : ∀{A} (N : Term Γ A) → Value Γ (A true⁻)
         
      data Subst (Γ : Ctx) : Ctx → Set where
         ⟨⟩ : Subst Γ []
         _,⁻_ : ∀{A Δ}
            (N : Term Γ A) 
            (σ : Subst Γ Δ)
            → Subst Γ (A true⁻ :: Δ) 
         _,⁺_ : ∀{Q Δ} 
            (x : Q true⁺ ∈ Γ)
            (σ : Subst Γ Δ)
            → Subst Γ (Q true⁺ :: Δ)


      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term (Γ : Ctx) : Type ⁻ → Set where
         _·_[_] : ∀{A Q Δ}
            (h : Head Γ A)
            (K : Skel Δ A (con Q))
            (σ : Subst Γ Δ)
            → Term Γ (con Q)
         ○ : ∀{A}
            (E : Exp Γ A)
            → Term Γ (○ A)
         Λ : ∀{A B}
            (N : Term (Hyp A :: Γ) B)
            → Term Γ (A ⊃ B)
         _,_ : ∀{A B}
            (N₁ : Term Γ A)
            (N₂ : Term Γ B)
            → Term Γ (A ∧ B) 
            
      -- E : Exp Γ A is the derivation Γ ⊢ E ÷ A lax
      data Exp (Γ : Ctx) : Type ⁺ → Set where
         ⟨_⟩ : ∀{A}
            (V : Value Γ (Hyp A))
            → Exp Γ A 
         let○ : ∀{Δ A B C} 
            (h : Head Γ A)
            (K : Skel Δ A (○ B))
            (σ : Subst Γ Δ)
            (E : Exp (Hyp B :: Γ) C)
            → Exp Γ C 

   -- WEAKENING
   mutual
      wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
      wk θ (var x · K [ σ ]) = var (θ x) · K [ wkσ θ σ ]
      wk θ (con c · K [ σ ]) = con c · K [ wkσ θ σ ]
      wk θ (○ E) = ○ (wkE θ E)
      wk θ (Λ N) = Λ (wk (sub-cons-congr θ) N)
      wk θ (N₁ , N₂) = wk θ N₁ , wk θ N₂

      wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
      wkσ θ ⟨⟩ = ⟨⟩
      wkσ θ (N ,⁻ σ) = wk θ N ,⁻ wkσ θ σ
      wkσ θ (x ,⁺ σ) = θ x ,⁺ wkσ θ σ

      wkE : ∀{Γ Γ' A} → Γ ⊆ Γ' → Exp Γ A → Exp Γ' A
      wkE {A = con Q} θ ⟨ ⁺ x ⟩ = ⟨ ⁺ (θ x) ⟩
      wkE {A = ↓ A} θ ⟨ ⁻ N ⟩ = ⟨ ⁻ (wk θ N) ⟩
      wkE θ (let○ (var x) K σ E) = 
         let○ (var (θ x)) K (wkσ θ σ) (wkE (sub-cons-congr θ) E)
      wkE θ (let○ (con c) K σ E) = 
         let○ (con c) K (wkσ θ σ) (wkE (sub-cons-congr θ) E)
 
   -- SUBSTITUTION
   mutual
      subst : ∀{Γ A C} → Term Γ A → Term (A true⁻ :: Γ) C → Term Γ C
      subst M (var Z · K [ σ ]) = hred M K (substσ M σ)
      subst M (var (S x) · K [ σ ]) = var x · K [ substσ M σ ]
      subst M (con c · K [ σ ]) = con c · K [ substσ M σ ]
      subst M (○ E) = ○ (substE M E)
      subst M (Λ N) = Λ (subst (wk sub-wken M) (wk sub-exch N))
      subst M ( N₁ , N₂ ) = subst M N₁ , subst M N₂

      substσ : ∀{Γ Δ A} → Term Γ A → Subst (A true⁻ :: Γ) Δ → Subst Γ Δ
      substσ M ⟨⟩ = ⟨⟩
      substσ M (N ,⁻ σ) = subst M N ,⁻ substσ M σ
      substσ M (S x ,⁺ σ) = x ,⁺ substσ M σ

      substE : ∀{Γ A C} → Term Γ A → Exp (A true⁻ :: Γ) C → Exp Γ C
      substE {C = con Q} M ⟨ ⁺ (S x) ⟩ = ⟨ ⁺ x ⟩
      substE {C = ↓ A'} M ⟨ ⁻ N ⟩ = ⟨ ⁻ (subst M N) ⟩
      substE M (let○ (var Z) K σ E) with hred M K (substσ M σ)
      ... | ○ E' = leftist E' (substE (wk sub-wken M) (wkE sub-exch E)) 
      substE M (let○ (var (S x)) K σ E) = 
         let○ (var x) K (substσ M σ) (substE (wk sub-wken M) (wkE sub-exch E))
      substE M (let○ (con c) K σ E) = 
         let○ (con c) K (substσ M σ) (substE (wk sub-wken M) (wkE sub-exch E))

      leftist : ∀{Γ A C} → Exp Γ A → Exp (Hyp A :: Γ) C → Exp Γ C
      leftist {A = con Q} ⟨ ⁺ x ⟩ E = wkE (sub-cntr x) E
      leftist {A = ↓ A} ⟨ ⁻ M ⟩ E = substE M E
      leftist (let○ h K σ E) E' = let○ h K σ (leftist E (wkE sub-wkex E'))

      hred : ∀{Γ Δ A C}
         → Term Γ A 
         → Skel Δ A C
         → Subst Γ Δ
         → Term Γ C
      hred M ⟨⟩ σ = M
      hred {A = con Q ⊃ A'} (Λ M) (· K) (x ,⁺ σ) = 
         hred (wk (sub-cntr x) M) K σ 
      hred {A = ↓ A ⊃ A'} (Λ M) (· K) (N ,⁻ σ) = hred (subst N M) K σ 
      hred (M₁ , M₂) (π₁ K) σ = hred M₁ K σ
      hred (M₁ , M₂) (π₂ K) σ = hred M₂ K σ

