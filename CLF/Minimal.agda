open import Prelude 

module CLF.Minimal where

infixr 5 _⊃_

data Type : Set where
   con : (Q : String) → Type
   _⊃_ : (A : Type) (B : Type) → Type
   _∧_ : (A B : Type) → Type

{- Contexts and inclusion in contexts -}

Ctx = List Type

open LIST.SET public hiding (refl)
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub

{- Skeletons -}

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
   

module MINIMAL (sig : String → Maybe Type) where


   {- PART 1: LOGIC -}

   data Head (Γ : Ctx) : Type → Set where
      var : ∀{A} (x : A ∈ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   infixr 21 _·_[_]
   mutual
      -- σ : Subst Γ Δ is the derivation Γ ⊢ σ : Δ
      data Subst (Γ : Ctx) : Ctx → Set where
         ⟨⟩ : Subst Γ []
         _,_ : ∀{A Δ}
            (N : Term Γ A) 
            (σ : Subst Γ Δ)
            → Subst Γ (A :: Δ) 

      -- R : Neutral Γ A is the neutral derivation Γ ⊢ R : A true
      -- In normal derivations, neutral terms only exist at base type
      data Neutral (Γ : Ctx) : Type → Set where
         _·_[_] : ∀{A C Δ}
            (h : Head Γ A)
            (K : Skel Δ A C)
            (σ : Subst Γ Δ)
            → Neutral Γ C

      -- N : Term Γ A is the derivation, in right inversion, of Γ ⊢ N : A true
      data Term (Γ : Ctx) : Type → Set where
         ·_ : ∀{Q}
            (h : Neutral Γ (con Q))
            → Term Γ (con Q)
         Λ : ∀{A B}
            (N : Term (A :: Γ) B)
            → Term Γ (A ⊃ B)
         _,_ : ∀{A B}
            (N₁ : Term Γ A)
            (N₂ : Term Γ B)
            → Term Γ (A ∧ B) 


   {- PART 2: GENERALIZED WEAKENING (a.k.a. renaming, context renaming) -}

   mutual
      wkN : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
      wkN θ (· R) = · wkR θ R
      wkN θ (Λ N) = Λ (wkN (sub-cons-congr θ) N)
      wkN θ (N₁ , N₂) = wkN θ N₁ , wkN θ N₂

      wkh : ∀{Γ Γ' A} → Γ ⊆ Γ' → Head Γ A → Head Γ' A
      wkh θ (var x) = var (θ x)
      wkh θ (con c) = con c

      wkR : ∀{Γ Γ' A} → Γ ⊆ Γ' → Neutral Γ A → Neutral Γ' A
      wkR θ (h · K [ σ ]) = wkh θ h · K [ wkσ θ σ ]

      wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
      wkσ θ ⟨⟩ = ⟨⟩
      wkσ θ (N , σ) = wkN θ N , wkσ θ σ


   {- PART 3: SUBSTITUTION -}

   -- Is a variable pointing to the part of the context being substituted for?
   Γ? : ∀{Γ A B} (Γ' : Ctx)
      → B ∈ Γ' ++ A :: Γ 
      → (A ≡ B) + (B ∈ Γ' ++ Γ)
   Γ? [] Z = Inl refl
   Γ? [] (S x) = Inr x
   Γ? (B :: Γ') Z = Inr Z
   Γ? (_ :: Γ') (S x) with Γ? Γ' x 
   ... | Inl Refl = Inl refl
   ... | Inr y = Inr (S y) 

   mutual
      sbN : ∀{Γ A C} (Γ' : Ctx) 
         → Term Γ A 
         → Term (Γ' ++ A :: Γ) C 
         → Term (Γ' ++ Γ) C
      sbN Γ' M (· R) = sbR Γ' M R 
      sbN Γ' M (Λ N) = Λ (sbN (_ :: Γ') M N)
      sbN Γ' M (N₁ , N₂) = sbN Γ' M N₁ , sbN Γ' M N₂

      sbR : ∀{Γ A Q} (Γ' : Ctx)
         → Term Γ A 
         → Neutral (Γ' ++ A :: Γ) (con Q) 
         → Term (Γ' ++ Γ) (con Q)
      sbR Γ' M (var x · K [ σ ]) with Γ? Γ' x
      ... | Inl Refl = wkN (sub-appendl _ Γ') M • K [ sbσ Γ' M σ ]
      ... | Inr y = · var y · K [ sbσ Γ' M σ ]
      sbR Γ' M (con c · K [ σ ]) = · con c · K [ sbσ Γ' M σ ]

      sbσ : ∀{Γ A Δ} (Γ' : Ctx)
         → Term Γ A 
         → Subst (Γ' ++ A :: Γ) Δ 
         → Subst (Γ' ++ Γ) Δ
      sbσ Γ' M ⟨⟩ = ⟨⟩
      sbσ Γ' M (N , σ) = sbN Γ' M N , sbσ Γ' M σ

      _•_[_] : ∀{Γ Δ A C} → Term Γ A → Skel Δ A C → Subst Γ Δ → Term Γ C
      M • ⟨⟩ [ ⟨⟩ ] = M
      Λ M • · K [ N , σ ] = sbN [] N M • K [ σ ]
      (M₁ , M₂) • π₁ K [ σ ] = M₁ • K [ σ ]
      (M₁ , M₂) • π₂ K [ σ ] = M₂ • K [ σ ]

   subN : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
   subN = sbN []

   subR : ∀{Γ A Q} → Term Γ A → Neutral (A :: Γ) (con Q) → Term Γ (con Q)
   subR = sbR []

   subσ : ∀{Γ A Δ} → Term Γ A → Subst (A :: Γ) Δ → Subst Γ Δ
   subσ = sbσ []


   {- PART 4: ETA-EXPANSION -}

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

   eta : ∀{B Γ Δ A}
      → Head Γ A
      → Skel Δ A B
      → Subst Γ Δ
      → Term Γ B
   eta {con Q} h K σ = · h · K [ σ ]
   eta {A ⊃ B} h K σ = 
      Λ (eta (wkh sub-wken h) (·' K) (eta (var Z) ⟨⟩ ⟨⟩ ,' wkσ sub-wken σ))
   eta {A ∧ B} h K σ = eta h (π₁' K) σ , eta h (π₂' K) σ 

   η : ∀{Γ A} → Neutral Γ A → Term Γ A
   η (h · K [ σ ]) = eta h K σ

