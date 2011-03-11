open import Prelude 

module CLF.LaxLogic where

infixr 5 _⊃_
infixr 4 _∧_

data Polarity : Set where
   ⁺ : Polarity
   ⁻ : Polarity

data Type : Polarity → Set where
   con : (Q : String) (⁼ : Polarity) → Type ⁼
   _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
   _∧_ : ∀{⁼} (A B : Type ⁼) → Type ⁼
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

-- This definition only works because skeletons are determinstic
Pat⁺ : Type ⁺ → Ctx → Ctx
Pat⁺ (con Q .⁺) Δ = Q true⁺ :: Δ
Pat⁺ (A ∧ B) Δ = Pat⁺ A (Pat⁺ B Δ)
Pat⁺ (↓ A) Δ = A true⁻ :: Δ

{- (con Q .⁺) = [ Q true⁺ ]
Pat⁺ (A ∧ B) = Pat⁺ A ++ Pat⁺ B
Pat⁺ (↓ A) = [ A true⁻ ] -}

{-
data Skel⁺ : Ctx → Type ⁺ → Set where
   ⟨⟩ : ∀{Q} → Skel⁺ (Q true⁺) (con Q ⁺)
   ↓ : ∀{A} → Skel⁺ (A true⁻) (↓ A)
   ⟨_,_⟩ : ∀{Δ₁ Δ₂ A B}
      (sk₁ : Skel⁺ Δ₁ A) 
      (sk₂ : Skel⁺ Δ₂ B)
      → Skel⁺ (Δ₁ , Δ₂) (A ∧ B)
-}

data Skel⁻ : Ctx → Type ⁻ → Type ⁻ → Set where
   ⟨⟩ : ∀{A} → Skel⁻ [] A A
   ·_ : ∀{Δ₂ A B C}
      (K : Skel⁻ Δ₂ B C)
      → Skel⁻ (Pat⁺ A Δ₂) (A ⊃ B) C
   π₁ : ∀{Δ A B C}
      (K : Skel⁻ Δ A C)
      → Skel⁻ Δ (A ∧ B) C
   π₂ : ∀{Δ A B C}
      (K : Skel⁻ Δ B C)
      → Skel⁻ Δ (A ∧ B) C
   
{- Definition of logic -}

module LAX (sig : String → Maybe (Type ⁻)) where
   data Head (Γ : Ctx) : Type ⁻ → Set where
      var : ∀{A} (x : A true⁻ ∈ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   infixr 21 _·_[_]
   mutual
      data Subst (Γ : Ctx) : Ctx → Set where
         [] : Subst Γ []
         _,⁺_ : ∀{Q Δ} 
            (x : Q true⁺ ∈ Γ) 
            (σ : Subst Γ Δ)
            → Subst Γ (Q true⁺ :: Δ)
         _,⁻_ : ∀{A Δ} 
            (N : Term Γ A)
            (σ : Subst Γ Δ)
            → Subst Γ (A true⁻ :: Δ)
         
      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term (Γ : Ctx) : Type ⁻ → Set where
         _·_[_] : ∀{A Q Δ}
            (h : Head Γ A)
            (K : Skel⁻ Δ A (con Q ⁻))
            (σ : Subst Γ Δ)
            → Term Γ (con Q ⁻)
         ○ : ∀{A}
            (E : Exp Γ A)
            → Term Γ (○ A)
         Λ : ∀{A B}
            (N : Term (Pat⁺ A Γ) B)
            → Term Γ (A ⊃ B)
         _,_ : ∀{A B}
            (N₁ : Term Γ A)
            (N₂ : Term Γ B)
            → Term Γ (A ∧ B) 
            
      -- E : Exp Γ A is the derivation Γ ⊢ E ÷ A lax
      data Exp (Γ : Ctx) : Type ⁺ → Set where
         ⟨_⟩ : ∀{A}
            (σ : Subst Γ (Pat⁺ A []))
            → Exp Γ A 
         let○ : ∀{Δ A B C} 
            (h : Head Γ A)
            (K : Skel⁻ Δ A (○ B))
            (σ : Subst Γ Δ)
            (E : Exp (Pat⁺ B Γ) C)
            → Exp Γ C 
 
   -- SUBSTITUTION
   mutual
      subst⁻ : ∀{Γ A C} → Term Γ A → Term (A true⁻ :: Γ) C → Term Γ C
      subst⁻ M (var Z · K [ σ ]) = {!!}
      subst⁻ M (var (S x) · K [ σ ]) = var x · K [ substσ M σ ]
      subst⁻ M (con c · K [ σ ]) = con c · K [ substσ M σ ]
      subst⁻ M (○ E) = {!!}
      subst⁻ M (Λ N) = {!!}
      subst⁻ M ( N₁ , N₂ ) = {!!}

      subst⁺ : ∀{Γ A C} → Term Γ A

      substσ : ∀{Γ Δ A} → Term Γ A → Subst (A true⁻ :: Γ) Δ → Subst Γ Δ
      substσ M [] = []
      substσ M (S x ,⁺ σ') = x ,⁺ substσ M σ'
      substσ M (N ,⁻ σ') = subst⁻ M N ,⁻ substσ M σ'

      hred : ∀{Γ Δ A C}
         → Term Γ A 
         → Skel⁻ Δ A C
         → Subst Γ Δ
         → Term Γ C
      hred M ⟨⟩ σ = M
      hred (Λ M) (· K) σ = {!!} -- hred {!!} K {!σ!}
      hred (M₁ , M₂) (π₁ K) σ = hred M₁ K σ
      hred (M₁ , M₂) (π₂ K) σ = hred M₂ K σ

      hred⁺ : ∀{Γ Δ B C}
         → (A : Type ⁺)
         → Term (Pat⁺ A Γ) B
         → Skel⁻ Δ B C
         → Subst Γ (Pat⁺ A Δ)
         → Term Γ C
      hred⁺ (con Q .⁺) M K σ = {!!}
      hred⁺ (A ∧ B) M K σ = {!hred⁺ A M K!}
      hred⁺ (↓ A) M K σ = {!!}

{- ε N = {! -- weaken --!}
      substσ ⟨ x ⟩⁺ N = {! !}
      substσ ⟨ M ⟩⁻ N = subst M N
      substσ (σ₁ , σ₂) N = {!substσ σ₁ N!} -}