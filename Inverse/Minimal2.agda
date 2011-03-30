-- This prevents us from needng to define hereditary substitution twice over
{-# OPTIONS --no-termination-check #-}

open import Prelude 

module Inverse.Minimal2 where

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

-- open import Lib.List.In

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

      -- R : Neutral Γ A is a partial derivation used in substitutions
      data Neutral (Γ : Ctx) : Class → Set where
         _·_[_] : ∀{A C Δ}
            (h : Head Γ A)
            (K : Skel Δ A C)
            (σ : Subst Γ Δ)
            → Neutral Γ C

      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term (Γ : Ctx) : Class → Set where
         ·_ : ∀{Q}
            (R : Neutral Γ (con Q))
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

      wkR : ∀{Γ Γ' A} → Γ ⊆ Γ' → Neutral Γ A → Neutral Γ' A
      wkR θ (var x · K [ σ ]) = var (θ x) · K [ wkσ θ σ ]
      wkR θ (con c · K [ σ ]) = con c · K [ wkσ θ σ ]

      wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
      wkσ θ ⟨⟩ = ⟨⟩
      wkσ θ (N , σ) = wkN θ N , wkσ θ σ


   {- PART 3: SUBSTITUTION -}

   -- Reversal-append
   _⟩⟩_ : Ctx → Ctx → Ctx  
   [] ⟩⟩ γ = γ
   (a :: δ) ⟩⟩ γ = δ ⟩⟩ (a :: γ)

   -- Pull a term out of a substitution
   σ→ : ∀{Γ Δ A} → A ∈ Δ → Subst Γ Δ → Term Γ A
   σ→ () ⟨⟩
   σ→ Z (N , σ) = N
   σ→ (S x) (N , σ) = σ→ x σ

   -- Check to see where a variable lives in the context
   Γ? : ∀{Γ Δ B} (Γ' : Ctx)
      → Subst Γ Δ 
      → B ∈ Γ' ++ Δ ⟩⟩ Γ 
      → (B ∈ Δ) + (B ∈ Γ' ++ Γ)
   Γ? [] ⟨⟩ x = Inr x
   Γ? [] (M , σ) x with Γ? [] (wkσ sub-wken σ) x
   ... | Inl y = Inl (S y) 
   ... | Inr Z = Inl Z
   ... | Inr (S y) = Inr y
   Γ? (B :: Γ') σ Z = Inr Z
   Γ? (_ :: Γ') σ (S x) with Γ? Γ' σ x 
   ... | Inl y = Inl y
   ... | Inr y = Inr (S y) 


   -- Simultaneous substitution
   mutual
      sbN : ∀{Δ Γ A} (Γ' : Ctx) 
         → Subst Γ Δ 
         → Term (Γ' ++ Δ ⟩⟩ Γ) A 
         → Term (Γ' ++ Γ) A
      sbN Γ' τ (· R) = sbR Γ' τ R
      sbN Γ' τ (Λ N) = Λ (sbN (_ :: Γ') τ N)
      sbN Γ' τ (N₁ , N₂) = sbN Γ' τ N₁ , sbN Γ' τ N₂

      sbR : ∀{Δ Γ Q} (Γ' : Ctx)
         → Subst Γ Δ
         → Neutral (Γ' ++ Δ ⟩⟩ Γ) (con Q) 
         → Term (Γ' ++ Γ) (con Q)
      sbR Γ' τ (var x · K [ σ ]) with Γ? Γ' τ x
      ... | Inl y = wkN (sub-appendl _ Γ') (σ→ y τ) • K [ sbσ Γ' τ σ ]
      ... | Inr y = · var y · K [ sbσ Γ' τ σ ]
      sbR Γ' τ (con c · K [ σ ]) = · con c · K [ sbσ Γ' τ σ ]

      sbσ : ∀{Δ Γ Δ'} (Γ' : Ctx) 
         → Subst Γ Δ
         → Subst (Γ' ++ (Δ ⟩⟩ Γ)) Δ' 
         → Subst (Γ' ++ Γ) Δ'
      sbσ Γ' τ ⟨⟩ = ⟨⟩
      sbσ Γ' τ (N , σ) = sbN Γ' τ N , sbσ Γ' τ σ

      _•_[_] : ∀{Γ Δ A C} → Term Γ A → Skel Δ A C → Subst Γ Δ → Term Γ C
      M • ⟨⟩ [ ⟨⟩ ] = M
      Λ M • · K [ N , σ ] = sbN [] (N , ⟨⟩) M • K [ σ ]
      (M₁ , M₂) • π₁ K [ σ ] = M₁ • K [ σ ]
      (M₁ , M₂) • π₂ K [ σ ] = M₂ • K [ σ ]


   subN : ∀{Γ Δ C} → Subst Γ Δ → Term (Δ ⟩⟩ Γ) C → Term Γ C
   subN = sbN []

   subR : ∀{Γ Δ Q} → Subst Γ Δ → Neutral (Δ ⟩⟩ Γ) (con Q) → Term Γ (con Q)
   subR = sbR []

   subσ : ∀{Γ Δ Δ'} → Subst Γ Δ → Subst (Δ ⟩⟩ Γ) Δ' → Subst Γ Δ'
   subσ = sbσ []


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
   eta (con Q) h K σ = · h · K [ σ ]
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

   -- XXX add to stdlib

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

   sub-ra-congr : ∀{δ γ γ'} → γ ⊆ γ' → (δ ⟩⟩ γ) ⊆ (δ ⟩⟩ γ')
   sub-ra-congr {[]} θ = θ
   sub-ra-congr {x :: xs} θ = sub-ra-congr {xs} (sub-cons-congr θ) 

   -- The critical thing about Γs? is that it has a %reduces property,
   -- namely that B is "smaller" than Δ in the left branch. 
   -- Because Agda can't check this, this formulation won't termination check. 
   Γs? : ∀{Γ Δ B} (Γ' : Ctx)
      → Subst Γ Δ 
      → B ∈ Γ' ++ Δ ⟩⟩ Γ 
      → (B ∈ Δ) + (B ∈ Γ' ++ Γ)
   Γs? [] ⟨⟩ x = Inr x
   Γs? [] (M , σ) x with Γs? [] (wkσ sub-wken σ) x
   ... | Inl y = Inl (S y) 
   ... | Inr Z = Inl Z
   ... | Inr (S y) = Inr y
   Γs? (B :: Γ') σ Z = Inr Z
   Γs? (_ :: Γ') σ (S x) with Γs? Γ' σ x 
   ... | Inl y = Inl y
   ... | Inr y = Inr (S y) 


{-


   {- PART 7 : LEFT RULES -}

   sub-wken2 : ∀{Γ} {A B C x : Class} → x ∈ B :: A :: Γ → x ∈ B :: A :: C :: Γ
   sub-wken2 Z = Z
   sub-wken2 (S Z) = S Z
   sub-wken2 (S (S n)) = S (S (S n))

   sub-wken1 : ∀{Γ} {A B x : Class} → x ∈ A :: Γ → x ∈ A :: B :: Γ
   sub-wken1 Z = Z
   sub-wken1 (S n) = S (S n)

   sub-wkra : ∀{Δ Γ} {A B C x : Class}  
     → x ∈ C :: Δ ⟩⟩ (A :: B :: Γ) 
     → x ∈ Δ ⟩⟩ (A :: B :: C :: Γ)
   sub-wkra {Δ} Z = sub-⟩⟩-l {Δ} (S (S Z))
   sub-wkra {Δ} (S n) = sub-ra-congr {Δ} sub-wken2 n


   ∧L₁ : ∀{Δ Γ A B C}
      → Term (Δ ⟩⟩ (A :: Γ)) C
      → Term (Δ ⟩⟩ ((A ∧ B) :: Γ)) C
   ∧L₁ {Δ} D = 
     subN
       (eta _ (var (sub-⟩⟩-l {Δ} Z)) (π₁ ⟨⟩) ⟨⟩)
       (→m (wk (sub-exch-ra {Δ}) (wk (sub-ra-congr {Δ} sub-wken1) D)))

   ∧L : ∀{Δ Γ A B C}
     → Term (Δ ⟩⟩ (B :: A ::  Γ)) C
     → Term (Δ ⟩⟩ ((A ∧ B) :: Γ)) C
   ∧L {Δ} {Γ} {A} {B} D =
      subN (eta _ (var (sub-⟩⟩-l {Δ} Z)) (π₂ ⟨⟩) ⟨⟩) 
           (→m (wk (sub-exch-ra {Δ}) (∧L₁ {B :: Δ} {Γ} {A} {B} D)))

   ∧Lσ : ∀{Δ Γ A B Δ'} 
      → Subst (Δ ⟩⟩ (B :: A :: Γ)) Δ'
      → Subst (Δ ⟩⟩ ((A ∧ B) :: Γ)) Δ'
   ∧Lσ ⟨⟩ = ⟨⟩
   ∧Lσ {Δ} (N , σ) = ∧L {Δ} N , ∧Lσ {Δ} σ


   ∧L₁σ : ∀{Δ Γ A B Δ'} 
      → Subst (Δ ⟩⟩ (A :: Γ)) Δ'
      → Subst (Δ ⟩⟩ ((A ∧ B) :: Γ)) Δ'
   ∧L₁σ ⟨⟩ = ⟨⟩
   ∧L₁σ {Δ} (N , σ) = ∧L₁ {Δ} N , ∧L₁σ {Δ} σ


   ⊃L : ∀{Δ Γ A B C} 
      → Term (Δ ⟩⟩ (B :: A :: Γ)) C 
      → Term (Δ ⟩⟩ (A :: (A ⊃ B) :: Γ)) C
   ⊃L {Δ} D = 
      subN
       (eta _ (var (sub-⟩⟩-l {Δ} (S Z))) (· ⟨⟩) (η' (sub-⟩⟩-l {Δ} Z) , ⟨⟩))
       (→m (wk (sub-exch-ra {Δ}) (wk (sub-ra-congr {Δ} sub-wken2) D)))

   ⊃Lσ : ∀{Δ Γ A B Δ'} 
      → Subst (Δ ⟩⟩ (B :: A :: Γ)) Δ'
      → Subst (Δ ⟩⟩ (A :: (A ⊃ B) :: Γ)) Δ'
   ⊃Lσ ⟨⟩ = ⟨⟩
   ⊃Lσ {Δ} (N , σ) = ⊃L {Δ} N , ⊃Lσ {Δ} σ
-}