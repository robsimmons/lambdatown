-- Too lazy for metrics, we're switching to %trustme
{-# OPTIONS --no-termination-check #-}

open import Prelude 

module CLF.Proclax where

infixr 5 _⊃_

data Type : Set where
   con : (Q : String) → Type
   _⊃_ : (A : Type) (B : Type) → Type
   _∧_ : (A B : Type) → Type
   ○ : (A : Type) → Type

Ctx = List Type

open LIST.SET public
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub



module LAX (sig : String → Maybe Type) where


   {- PART 1: LOGIC -}

   data Head (Γ : Ctx) : Type → Set where
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})
      var : ∀{A} (x : A ∈ Γ)
         → Head Γ A

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
         let○ : ∀{Γ₂ A}
            (E : Exp Γ Γ₂)
            (N : Term Γ₂ A)
            → Term Γ (○ A)
            
      -- E : Exp Γ Γ' is the derivation Γ ↝ Γ'
      data Exp (Γ₁ : Ctx) : Ctx → Set where
         ⟨⟩ : Exp Γ₁ Γ₁
         _·_[_],_ : ∀{Δ A B Γ₂} 
            (h : Head Γ₁ A)
            (K : Skel Δ A (○ B))
            (σ : Subst Γ₁ Δ)
            (E : Exp (B :: Γ₁) Γ₂)
            → Exp Γ₁ Γ₂


   {- PART 2: GENERALIZED WEAKENING (a.k.a. renaming, context renaming) -}

   -- The action of an expression on renamings
   expΓ : ∀{Γ₁ Γ₂} (Γ₁' : Ctx) → Exp Γ₁ Γ₂ → Ctx
   expΓ Γ₁' ⟨⟩ = Γ₁'
   expΓ Γ₁' (_·_[_],_ {B = B} _ _ _ E) = expΓ (B :: Γ₁') E

   expθ : ∀{Γ₁ Γ₁' Γ₂} (θ : Γ₁ ⊆ Γ₁') (E : Exp Γ₁ Γ₂) → Γ₂ ⊆ (expΓ Γ₁' E)
   expθ θ ⟨⟩ = θ
   expθ θ (h · K [ σ ], E) = expθ (sub-cons-congr θ) E

   wkh : ∀{Γ Γ' A} → Γ ⊆ Γ' → Head Γ A → Head Γ' A
   wkh θ (con c) = con c
   wkh θ (var x) = var (θ x)

   mutual
      wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
      wk θ (var x · K [ σ ]) = var (θ x) · K [ wkσ θ σ ]
      wk θ (con c · K [ σ ]) = con c · K [ wkσ θ σ ]
      wk θ (Λ N) = Λ (wk (sub-cons-congr θ) N)
      wk θ (N₁ , N₂) = wk θ N₁ , wk θ N₂
      wk θ (let○ E N) = let○ (wkE θ E) (wk (expθ θ E) N)

      wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
      wkσ θ ⟨⟩ = ⟨⟩
      wkσ θ (N , σ) = wk θ N , wkσ θ σ

      wkE : ∀{Γ₁ Γ₁' Γ₂}
         (θ : Γ₁ ⊆ Γ₁')
         (E : Exp Γ₁ Γ₂)
         → Exp Γ₁' (expΓ Γ₁' E) 
      wkE θ ⟨⟩ = ⟨⟩
      wkE θ (h · K [ σ ], E) =
         wkh θ h · K [ wkσ θ σ ], wkE (sub-cons-congr θ) E


   {- PART 4: SUBSTITUTION -}

   mutual
      subst : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
      subst M (Λ N) = Λ (subst (wk sub-wken M) (wk sub-exch N))
      subst M (N₁ , N₂) = subst M N₁ , subst M N₂
      subst M (let○ E N) = {!!} -- ○ (substE M E)
      subst M (con c · K [ σ ]) = con c · K [ substσ M σ ]
      subst M (var (S x) · K [ σ ]) = var x · K [ substσ M σ ]
      subst M (var Z · K [ σ ]) = red⁻ M K (substσ M σ)

      red⁻ : ∀{Γ Δ A C} → Term Γ A → Skel Δ A C → Subst Γ Δ → Term Γ C
      red⁻ M ⟨⟩ σ = M
      red⁻ (Λ M) (· K) (N , σ) = red⁻ (subst N M) K σ
      red⁻ (M₁ , M₂) (π₁ K) σ = red⁻ M₁ K σ
      red⁻ (M₁ , M₂) (π₂ K) σ = red⁻ M₂ K σ

      substσ : ∀{Γ Δ A} → Term Γ A → Subst (A :: Γ) Δ → Subst Γ Δ
      substσ M ⟨⟩ = ⟨⟩
      substσ M (N , σ) = subst M N , substσ M σ

      substE : ∀{Γ A C} → Term Γ A → Exp (A :: Γ) C → Exp Γ C
      substE M E = {!!}
{-
      substE M ⟨ N ⟩ = ⟨ subst M N ⟩
      substE M (let○ (con c) K σ E) = 
         let○ (con c) K (substσ M σ) (substE (wk sub-wken M) {! wkE sub-exch E !})
      substE M (let○ (var (S x)) K σ E) = 
         let○ (var x) K (substσ M σ) (substE (wk sub-wken M) {! wkE sub-exch E))
      substE M (let○ (var Z) K σ E) = 
         red⁺ M K (substσ M σ) (substE (wk sub-wken M) (wkE sub-exch E)) -}

      red⁺ : ∀{Γ Δ A B C} 
         → Term Γ A 
         → Skel Δ A (○ B) 
         → Subst Γ Δ 
         → Exp (B :: Γ) C
         → Exp Γ C
      red⁺ (h · K [ σ' ]) () σ E 
      red⁺ (Λ M) (· K) (N , σ) E = red⁺ (subst N M) K σ E
      red⁺ (M₁ , M₂) (π₁ K) σ E = red⁺ M₁ K σ E
      red⁺ (M₁ , M₂) (π₂ K) σ E = red⁺ M₂ K σ E
      red⁺ (let○ E' M) ⟨⟩ σ E = {!!} -- leftist E' E
{-       where
         leftist : ∀{Γ B C} → Exp Γ B → Exp (B :: Γ) C → Exp Γ C
         leftist ⟨ M ⟩ E' = substE M E'
         leftist (let○ h K σ E) E' = let○ h K σ (leftist E (wkE sub-wkex E')) -}

 

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
   eta A h K σ = {!!} 
   -- eta (○ A) h K σ = ○ (let○ h K σ ⟨ eta _ (var Z) ⟨⟩ ⟨⟩ ⟩)

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
      var x · K [ σ' ] [ σ ]N = red⁻ (lookup x σ) K (σ' [ σ ]σ)
      Λ N [ σ ]N = Λ (N [ η , wkσ sub-wken σ ]N)
      (N₁ , N₂) [ σ ]N = (N₁ [ σ ]N) , (N₂ [ σ ]N)
      let○ E N [ σ ]N = {!!} -- ○ (E [ σ ]E)

      _[_]σ : ∀{Γ Γ' Δ} → Subst Γ' Δ → Subst Γ Γ' → Subst Γ Δ
      ⟨⟩ [ σ ]σ = ⟨⟩
      (N , σ') [ σ ]σ = (N [ σ ]N) , (σ' [ σ ]σ)

      _[_]E : ∀{Γ Γ' A} → Exp Γ' A → Subst Γ Γ' → Exp Γ A
      ⟨⟩ [ σ' ]E = {!!}
      (h · K [ σ' ], E) [ σ ]E = {!!}
{-
      ⟨ N ⟩ [ σ ]E = ⟨ N [ σ ]N ⟩
      let○ (con c) K σ' E [ σ ]E = 
         let○ (con c) K (σ' [ σ ]σ) (E [ η , wkσ sub-wken σ ]E)
      let○ (var x) K σ' E [ σ ]E = 
         red⁺ (lookup x σ) K (σ' [ σ ]σ) (E [ η , wkσ sub-wken σ ]E) -}

