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

data Ctx : Set where
   ε : Ctx
   _true⁺ : (Q : String) → Ctx
   _true⁻ : (A : Type ⁻) → Ctx
   _,_ : Ctx → Ctx → Ctx

data _∈⁺_ (Q : String) : Ctx → Set where
   ⟨⟩ : Q ∈⁺ Q true⁺
   l : ∀{Γ₁ Γ₂} (x : Q ∈⁺ Γ₁) → Q ∈⁺ (Γ₁ , Γ₂)
   r : ∀{Γ₁ Γ₂} (x : Q ∈⁺ Γ₂) → Q ∈⁺ (Γ₁ , Γ₂)

data _∈⁻_ (A : Type ⁻) : Ctx → Set where
   ⟨⟩ : A ∈⁻ A true⁻
   l : ∀{Γ₁ Γ₂} (x : A ∈⁻ Γ₁) → A ∈⁻ (Γ₁ , Γ₂)
   r : ∀{Γ₁ Γ₂} (x : A ∈⁻ Γ₂) → A ∈⁻ (Γ₁ , Γ₂)

_⊆_ : Ctx → Ctx → Set
Δ ⊆ Γ = (∀{Q} → Q ∈⁺ Δ → Q ∈⁺ Γ) × (∀{A} → A ∈⁻ Δ → A ∈⁻ Γ)

{- Skeletons -}

-- This definition only works because skeletons aren't 
Pat⁺ : Type ⁺ → Ctx
Pat⁺ (con Q .⁺) = Q true⁺
Pat⁺ (A ∧ B) = Pat⁺ A , Pat⁺ B
Pat⁺ (↓ A) = A true⁻

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
   ⟨⟩ : ∀{A} → Skel⁻ ε A A
   _·_ : ∀{Δ₂ A B C}
      (sk₂ : Skel⁻ Δ₂ B C)
      → Skel⁻ (Pat⁺ A , Δ₂) (A ⊃ B) C
   π₁ : ∀{Δ A B C}
      (sk : Skel⁻ Δ A C)
      → Skel⁻ Δ (A ∧ B) C
   π₂ : ∀{Δ A B C}
      (sk : Skel⁻ Δ B C)
      → Skel⁻ Δ (A ∧ B) C
   
{- Definition of logic -}

module LAX (sig : String → Maybe (Type ⁻)) where
   data Head (Γ : Ctx) : Type ⁻ → Set where
      var : ∀{A} (x : A ∈⁻ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   infixr 21 _·_[_]
   mutual
      data Subst (Γ : Ctx) : Ctx → Set where
         ε : Subst Γ ε
         ⟨_⟩⁺ : ∀{Q} (x : Q ∈⁺ Γ) → Subst Γ (Q true⁺)
         ⟨_⟩⁻ : ∀{A} (N : Term Γ A) → Subst Γ (A true⁻)
         _,_ : ∀{Δ₁ Δ₂}
            (σ₁ : Subst Γ Δ₁) 
            (σ₂ : Subst Γ Δ₂) 
            → Subst Γ (Δ₁ , Δ₂) 
         
      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term (Γ : Ctx) : Type ⁻ → Set where
         _·_[_] : ∀{A Q Δ}
            (h : Head Γ A)
            (K : Skel⁻ Γ A (con Q ⁻))
            (σ : Subst Γ Δ)
            → Term Γ (con Q ⁻)
         ○ : ∀{A}
            (E : Exp Γ A)
            → Term Γ (○ A)
         Λ : ∀{A B}
            (N : Term (Γ , Pat⁺ A) B)
            → Term Γ (A ⊃ B)
         _,_ : ∀{A B}
            (N₁ : Term Γ A)
            (N₂ : Term Γ B)
            → Term Γ (A ∧ B) 
            
      -- E : Exp Γ A is the derivation Γ ⊢ E ÷ A lax
      data Exp (Γ : Ctx) : Type ⁺ → Set where
         ⟨_⟩ : ∀{A}
            (σ : Subst Γ (Pat⁺ A))
            → Exp Γ A
         let○ : ∀{Δ A B C} 
            (h : Head Γ A)
            (K : Skel⁻ Δ A (○ B))
            (σ : Subst Γ Δ)
            (E : Exp (Γ , Pat⁺ B) C)
            → Exp Γ C
 
   -- SUBSTITUTION
   mutual
      subst : ∀{Γ A C} → Term Γ A → Term (Γ , A true⁻) C → Term Γ C
      subst M (h · K [ σ ]) = {!!}
      subst M (○ E) = {!!}
      subst M (Λ N) = {!!}
      subst M ( N₁ , N₂ ) = {!!}

      substσ : ∀{Γ Δ C} → Subst Γ Δ → Term (Γ , Δ) C → Term Γ C
      substσ ε N = {! -- weaken --!}
      substσ ⟨ x ⟩⁺ N = {! !}
      substσ ⟨ M ⟩⁻ N = subst {!M!} {!!}
      substσ (σ₁ , σ₂) N = {!!}