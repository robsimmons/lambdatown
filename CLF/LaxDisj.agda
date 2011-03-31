open import Prelude 

module CLF.LaxDisj where

infixr 5 _⊃_

data Polarity : Set where
   ⁺ : Polarity
   ⁻ : Polarity

data Type : Polarity → Set where
   con : (Q : String) → Type ⁻
   _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
   _∧_ : {⁼ : Polarity} (A B : Type ⁼) → Type ⁼
   _∨_ : (A B : Type ⁺) → Type ⁺
   ○ : (A : Type ⁺) → Type ⁻
   ↓ : (A : Type ⁻) → Type ⁺

{- Contexts and inclusion in contexts -}

Ctx = List (Type ⁻)

data Pat : Set where
   _⊗_ : (Δ₁ Δ₂ : Pat) → Pat
   ⟨_⟩ : (A : Type ⁺) → Pat 
   ⟨⟩ : Pat  

data _∈p_ : Type ⁺ → Pat → Set where 
   ⟨⟩ : ∀{A} → A ∈p ⟨ A ⟩
   ⟨_ : ∀{A Δ Δ'} (x : A ∈p Δ) → A ∈p (Δ ⊗ Δ')
   ⟩_ : ∀{A Δ Δ'} (x : A ∈p Δ) → A ∈p (Δ' ⊗ Δ)

open LIST.SET public hiding (refl)
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub

sub++ : ∀{Γ} (Γ' : Ctx) → Γ ⊆ (Γ' ++ Γ)
sub++ Γ' = sub-appendl _ Γ'

{- Skeletons -}

-- K⁺ : Skel⁺ C A is just a (degenerate) positive skeleton Δ ⊩ A
data Skel⁺ : Pat → Type ⁺ → Set where
   ⟨⟩ : ∀{A} → Skel⁺ (⟨ A ⟩) A
   inl : ∀{A B Δ} 
      (K : Skel⁺ Δ A) 
      → Skel⁺ Δ (A ∨ B)
   inr : ∀{A B Δ} 
      (K : Skel⁺ Δ B)
      → Skel⁺ Δ (A ∨ B)

-- K : Skel Δ A C is the pattern judgment Δ ⊩ K : A > C
data Skel⁻ : Pat → Type ⁻ → Type ⁻ → Set where
   ⟨⟩ : ∀{A} → Skel⁻ ⟨⟩ A A
   ap : ∀{Δ₁ Δ₂ A B C} 
      (K⁺ : Skel⁺ Δ₁ A)
      (K⁻ : Skel⁻ Δ₂ B C)
      → Skel⁻ (Δ₁ ⊗ Δ₂) (A ⊃ B) C
   π₁ : ∀{Δ A B C}
      (K : Skel⁻ Δ A C)
      → Skel⁻ Δ (A ∧ B) C
   π₂ : ∀{Δ A B C}
      (K : Skel⁻ Δ B C)
      → Skel⁻ Δ (A ∧ B) C

ηPat : Pat → Set
ηPat (Δ ⊗ Δ') = ηPat Δ × ηPat Δ'
ηPat ⟨ A ∧ B ⟩ = Void
ηPat ⟨ (A ∨ B) ⟩ = Void
ηPat ⟨ ↓ A ⟩ = Unit
ηPat ⟨⟩ = Unit

{- [] = Unit
ηPat (con Q :: Δ) = ηPat Δ
ηPat (↓ A :: Δ) = ηPat Δ
ηPat (A ∨ B :: Δ) = Void -}

module LAX (sig : String → Maybe (Type ⁻)) where

   {- PART 1: LOGIC -}

   data Head (Γ : Ctx) : Type ⁻ → Set where
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})
      var : ∀{A} (x : A ∈ Γ)
         → Head Γ A

   infixr 21 _·_[_]
   mutual
      data Value (Γ : Ctx) : Type ⁺ → Set where
         _[_]v : ∀{Δ A} 
            (K : Skel⁺ Δ A)
            (σ : Subst Γ Δ)
            → Value Γ A

      -- σ : Subst Γ Δ is the derivation Γ ⊢ σ : Δ
      data Subst (Γ : Ctx) : Pat → Set where
         ⟨⟩ : Subst Γ ⟨⟩
         ⟨_⟩ : ∀{A}
            (N : Term Γ A) 
            → Subst Γ ⟨ ↓ A ⟩
         _,_ : ∀{Δ₁ Δ₂}
            (σ₁ : Subst Γ Δ₁)
            (σ₂ : Subst Γ Δ₂)
            → Subst Γ (Δ₁ ⊗ Δ₂) 
           
      -- R : Neutral Γ A is the neutral derivation Γ ⊢ R : A true
      -- In normal derivations, neutral terms only exist at base type
      data Neutral (Γ : Ctx) : Type ⁻ → Set where
         _·_[_] : ∀{A C Δ}
            (h : Head Γ A)
            (K : Skel⁻ Δ A C)
            (σ : Subst Γ Δ)
            → Neutral Γ C

      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term (Γ : Ctx) : Type ⁻ → Set where
         ·_ : ∀{Q}
            (R : Neutral Γ (con Q))
            → Term Γ (con Q)
         ○ : ∀{A}
            (E : Exp Γ A)
            → Term Γ (○ A)
         Λ : ∀{A B}
            (N : InvTerm Γ A B)
            → Term Γ (A ⊃ B)
         _,_ : ∀{A B}
            (N₁ : Term Γ A)
            (N₂ : Term Γ B)
            → Term Γ (A ∧ B) 
            
      -- N : InvTerm Γ A C is the derivation Γ; A ⊢ N : C true
      data InvTerm (Γ : Ctx) : Type ⁺ → Type ⁻ → Set where
         ·_ : ∀{A C}
            (N : Term (A :: Γ) C)
            → InvTerm Γ (↓ A) C
         _∣_ : ∀{A B C}
            (N₁ : InvTerm Γ A C)
            (N₂ : InvTerm Γ B C)
            → InvTerm Γ (A ∨ B) C

      -- E : Exp Γ A is the derivation Γ ⊢ E ÷ A lax
      data Exp (Γ : Ctx) : Type ⁺ → Set where
         ·_ : ∀{A}
            (V : Value Γ A)
            → Exp Γ A 
         let○ : ∀{A C} 
            (R : Neutral Γ (○ A))
            (E : InvExp Γ A C)
            → Exp Γ C

            
      -- E : InvExp Γ A C is the derivation Γ; A ⊢ N ÷ C lax
      data InvExp (Γ : Ctx) : Type ⁺ → Type ⁺ → Set where
         ·_ : ∀{A C}
            (E : Exp (A :: Γ) C)
            → InvExp Γ (↓ A) C
         _∣_ : ∀{A B C}
            (E₁ : InvExp Γ A C)
            (E₂ : InvExp Γ B C)
            → InvExp Γ (A ∨ B) C

   {- PART 2: GENERALIZED WEAKENING (a.k.a. renaming, context renaming) -}

   mutual
      wkN : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
      wkN θ (· R) = · wkR θ R
      wkN θ (Λ N) = Λ (wkIN θ N)
      wkN θ (N₁ , N₂) = wkN θ N₁ , wkN θ N₂
      wkN θ (○ E) = ○ (wkE θ E)

      wkIN : ∀{Γ Γ' A C} → Γ ⊆ Γ' → InvTerm Γ A C → InvTerm Γ' A C
      wkIN θ (· N) = · (wkN (sub-cons-congr θ) N)
      wkIN θ (N₁ ∣ N₂) = wkIN θ N₁ ∣ wkIN θ N₂

      wkh : ∀{Γ Γ' A} → Γ ⊆ Γ' → Head Γ A → Head Γ' A
      wkh θ (var x) = var (θ x)
      wkh θ (con c) = con c

      wkR : ∀{Γ Γ' A} → Γ ⊆ Γ' → Neutral Γ A → Neutral Γ' A
      wkR θ (h · K [ σ ]) = wkh θ h · K [ wkσ θ σ ] 

      wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
      wkσ θ ⟨⟩ = ⟨⟩
      wkσ θ ⟨ N ⟩ = ⟨ wkN θ N ⟩
      wkσ θ (σ₁ , σ₂) = wkσ θ σ₁ , wkσ θ σ₂

      wkV : ∀{Γ Γ' J} → Γ ⊆ Γ' → Value Γ J → Value Γ' J
      wkV θ (K [ σ ]v) = K [ wkσ θ σ ]v

      wkE : ∀{Γ Γ' A} → Γ ⊆ Γ' → Exp Γ A → Exp Γ' A
      wkE θ (· V) = · wkV θ V
      wkE θ (let○ R E) = let○ (wkR θ R) (wkIE θ E)

      wkIE : ∀{Γ Γ' A C} → Γ ⊆ Γ' → InvExp Γ A C → InvExp Γ' A C
      wkIE θ (· E) = · wkE (sub-cons-congr θ) E
      wkIE θ (E₁ ∣ E₂) = wkIE θ E₁ ∣ wkIE θ E₂ 

   {- PART 3: SUBSTITUTION -}

   -- Chucking a fully eta-expanded pattern into the context
   _⟫_⟫_ : (Δ : Pat) (Γ : Ctx) → ηPat Δ → Ctx
   (Δ₁ ⊗ Δ₂) ⟫ Γ ⟫ (p₁ , p₂) = Δ₂ ⟫ Δ₁ ⟫ Γ ⟫ p₁ ⟫ p₂
   ⟨ A ∧ B ⟩ ⟫ Γ ⟫ ()
   ⟨ A ∨ B ⟩ ⟫ Γ ⟫ ()
   ⟨ ↓ A ⟩ ⟫ Γ ⟫ <> = A :: Γ
   ⟨⟩ ⟫ Γ ⟫ <> = Γ 

   -- Is a variable pointing to the part of the context being substituted for?
   Γ? : ∀{Γ B} (Γ' : Ctx) (Δ : Pat) (p : ηPat Δ)
      → B ∈ Γ' ++ Δ ⟫ Γ ⟫ p 
      → (↓ B ∈p Δ) + (B ∈ Γ' ++ Γ)
   Γ? [] (Δ₁ ⊗ Δ₂) (p₁ , p₂) x with Γ? [] Δ₂ p₂ x
   ... | Inl y = Inl (⟩ y)
   ... | Inr y with Γ? [] Δ₁ p₁ y
   ... | Inl z = Inl (⟨ z)
   ... | Inr z = Inr z
   Γ? [] ⟨ A ∧ B' ⟩ () x
   Γ? [] ⟨ A ∨ B' ⟩ () x
   Γ? [] ⟨ ↓ A ⟩ p Z = Inl ⟨⟩
   Γ? [] ⟨ ↓ A ⟩ p (S x) = Inr x
   Γ? [] ⟨⟩ p x = Inr x
   Γ? (A :: Γ') Δ p Z = Inr Z
   Γ? (A :: Γ') Δ p (S x) with Γ? Γ' Δ p x 
   ... | Inl y = Inl y
   ... | Inr y = Inr (S y)

{-
{-
   [] ⟫ Γ ⟫ p = Γ
   (con Q :: Δ) ⟫ Γ ⟫ p = Δ ⟫ Q true⁺ :: Γ ⟫ p
   (↓ A :: Δ) ⟫ Γ ⟫ p = Δ ⟫ A true⁻ :: Γ ⟫ p
   (A ∨ B :: Δ) ⟫ Γ ⟫ () -}
   

   Γ? [] Δ p c = {!!}
   Γ? (J :: Γ') Δ p Z = {!!}
   Γ? (J :: Γ') Δ p (S x) with Γ? Γ' Δ p x 
   ... | Inl <> = {!!}
   ... | Inr y = Inr (S y)
{-
   Γ? [] () x = Inr x
   Γ? [] p x with Γ? [] ? {!x!}
   ... | Inl <> = {!!}
   ... | Inr y = {!!}
   Γ? [] p x' = {!x'!}
   Γ? (x :: xs) τ x' = {!!}
-}
{-
   Γ? [] τ Z = Inl refl
   Γ? [] τ (S x) = Inr x
   Γ? (B :: Γ') Z = Inr Z
   Γ? (_ :: Γ') (S x) with Γ? Γ' x 
   ... | Inl Refl = Inl refl
   ... | Inr y = Inr (S y) 
-}
 

{-
   wkW : ∀ {Γ A} (Γ' : Ctx) → Value Γ (↓ A) → Term (Γ' ++ Γ) A
   wkW Γ' (⁻ N) = wkN (sub++ Γ') N
-}

   mutual
      sbN : ∀{Γ Δ C} (Γ' : Ctx) (τ : Subst Γ Δ)
         → Term (Γ' ++ Δ ⟫ Γ ⟫ {!!}) C 
         → Term (Γ' ++ Γ) C
      sbN Γ' τ (· con c · K [ σ ]) = · con c · K [ {!!} ]
      sbN Γ' τ (· var x · K [ σ ]) = {!!} -- red?⁻   
{-
with sbσ Γ' τ ? | Γ? Γ' x 
      ... | σ' | Inl Refl = ? -- red⁻ (wkW Γ' W) K σ'
      ... | σ' | Inr y = · var y · K [ sbσ Γ' τ σ ] -}
      sbN Γ' τ (○ E) = ○ {!!} -- (sbE Γ' W E)
      sbN Γ' τ (Λ N) = Λ {!!} -- (sbN (_ :: Γ') τ N)
      sbN Γ' τ (N₁ , N₂) = sbN Γ' τ N₁ , sbN Γ' τ N₂


{-
      red⁻ : ∀{A Γ Δ C} 
         → Term Γ A 
         → Skel⁻ Δ A C 
         → Subst Γ Δ 
         → Term Γ C
      red⁻ M ⟨⟩ ⟨⟩ = M
      red⁻ (Λ M) (· K) (V , σ) = red⁻ (sbN [] V M) K σ
      red⁻ (M₁ , M₂) (π₁ K) σ = red⁻ M₁ K σ
      red⁻ (M₁ , M₂) (π₂ K) σ = red⁻ M₂ K σ
-}

      sbσ : ∀{J Γ Δ} (Γ' : Ctx) (τ : Subst Γ Δ)
         → Subst (Γ' ++ Δ ⟫ Γ ⟫ {!!}) Δ
         → Subst (Γ' ++ Γ) Δ
      sbσ Γ' W σ = {!!}

{- = ⟨⟩
      sbσ Γ' W (x ,⁺ σ) = {!!} -- sbV Γ' W V , sbσ Γ' W σ
      sbσ Γ' W (N ,⁻ σ) = {!!} -- sbV Γ' W V , sbσ Γ' W σ -}

{-
      sbV : ∀{J Γ J'} (Γ' : Ctx)
         → Value Γ J
         → Value (Γ' ++ J :: Γ) J'
         → Value (Γ' ++ Γ) J'
      sbV Γ' W (⁺ x) with Γ? Γ' x
      ... | Inl Refl = wkV (sub++ Γ') W
      ... | Inr y = ⁺ y      
      sbV Γ' W (⁻ N) = ⁻ (sbN Γ' W N)

      sbE : ∀{Γ A C} (Γ' : Ctx)
         → Value Γ A 
         → Exp (Γ' ++ A :: Γ) C
         → Exp (Γ' ++ Γ) C
      sbE Γ' W ⟨ V ⟩ = ⟨ sbV Γ' W V ⟩
      sbE Γ' W (let○ (con c · K [ σ ]) E) = 
         let○ (con c · K [ sbσ Γ' W σ ]) (sbE (_ :: Γ') W E)
      sbE Γ' W (let○ (var x · K [ σ ]) E) with Γ? Γ' x
      ... | Inl Refl =  wkW Γ' W •⁺ K [ sbσ Γ' W σ ] sbE (_ :: Γ') W E
      ... | Inr y = let○ (var y · K [ sbσ Γ' W σ ]) (sbE (_ :: Γ') W E)

      _•⁺_[_]_ : ∀{Γ Δ A B C} 
         → Term Γ A 
         → Skel⁻ Δ A (○ B)
         → Subst Γ Δ 
         → Exp (B :: Γ) C
         → Exp Γ C
      · _ •⁺ () [ _ ] _
      ○ E •⁺ ⟨⟩ [ ⟨⟩ ] E' = leftist [] E E'
      Λ M •⁺ · K [ N , σ ] E = sbN [] N M •⁺ K [ σ ] E
      (M₁ , M₂) •⁺ π₁ K [ σ ] E = M₁ •⁺ K [ σ ] E
      (M₁ , M₂) •⁺ π₂ K [ σ ] E = M₂ •⁺ K [ σ ] E

      leftist : ∀{Γ B C} (Γ' : Ctx) 
         → Exp (Γ' ++ Γ) B
         → Exp (B :: Γ) C 
         → Exp (Γ' ++ Γ) C
      leftist Γ' ⟨ V ⟩ E' = sbE [] V (wkE (sub-cons-congr (sub++ Γ')) E')
      leftist Γ' (let○ R E) E' = let○ R (leftist (_ :: Γ') E E')
-}

x : Set
x = {!!}

{-

   mutual
      sbN : ∀{Γ A C} (Γ' : Ctx) 
         → Term Γ A 
         → Term (Γ' ++ A :: Γ) C 
         → Term (Γ' ++ Γ) C
      sbN Γ' M (· con c · K [ σ ]) = · con c · K [ sbσ Γ' M σ ]
      sbN Γ' M (· var x · K [ σ ]) with Γ? Γ' x
      ... | Inl Refl = wkN (sub-appendl _ Γ') M •⁻ K [ sbσ Γ' M σ ]
      ... | Inr y = · var y · K [ sbσ Γ' M σ ] 
      sbN Γ' M (Λ N) = Λ (sbN (_ :: Γ') M N)
      sbN Γ' M (N₁ , N₂) = sbN Γ' M N₁ , sbN Γ' M N₂
      sbN Γ' M (○ E) = ○ (sbE Γ' M E)

      _•⁻_[_] : ∀{Γ Δ A C} 
         → Term Γ A 
         → Skel Δ A C 
         → Subst Γ Δ 
         → Term Γ C
      M •⁻ ⟨⟩ [ ⟨⟩ ] = M
      Λ M •⁻ · K [ N , σ ] = sbN [] N M •⁻ K [ σ ]
      (M₁ , M₂) •⁻ π₁ K [ σ ] = M₁ •⁻ K [ σ ]
      (M₁ , M₂) •⁻ π₂ K [ σ ] = M₂ •⁻ K [ σ ]

      sbσ : ∀{Γ A Δ} (Γ' : Ctx)
         → Term Γ A 
         → Subst (Γ' ++ A :: Γ) Δ 
         → Subst (Γ' ++ Γ) Δ
      sbσ Γ' M ⟨⟩ = ⟨⟩
      sbσ Γ' M (N , σ) = sbN Γ' M N , sbσ Γ' M σ

      sbE : ∀{Γ A C} (Γ' : Ctx)
         → Term Γ A 
         → Exp (Γ' ++ A :: Γ) C
         → Exp (Γ' ++ Γ) C
      sbE Γ' M ⟨ N ⟩ = ⟨ sbN Γ' M N ⟩
      sbE Γ' M (let○ (con c · K [ σ ]) E) = 
         let○ (con c · K [ sbσ Γ' M σ ]) (sbE (_ :: Γ') M E)
      sbE Γ' M (let○ (var x · K [ σ ]) E) with Γ? Γ' x
      ... | Inl Refl = wkN (sub++ Γ') M •⁺ K [ sbσ Γ' M σ ] sbE (_ :: Γ') M E
      ... | Inr y = let○ (var y · K [ sbσ Γ' M σ ]) (sbE (_ :: Γ') M E)

      _•⁺_[_]_ : ∀{Γ Δ A B C} 
         → Term Γ A 
         → Skel Δ A (○ B)
         → Subst Γ Δ 
         → Exp (B :: Γ) C
         → Exp Γ C
      · _ •⁺ () [ _ ] _
      ○ E •⁺ ⟨⟩ [ ⟨⟩ ] E' = leftist [] E E'
      Λ M •⁺ · K [ N , σ ] E = sbN [] N M •⁺ K [ σ ] E
      (M₁ , M₂) •⁺ π₁ K [ σ ] E = M₁ •⁺ K [ σ ] E
      (M₁ , M₂) •⁺ π₂ K [ σ ] E = M₂ •⁺ K [ σ ] E

      leftist : ∀{Γ B C} (Γ' : Ctx) 
         → Exp (Γ' ++ Γ) B
         → Exp (B :: Γ) C 
         → Exp (Γ' ++ Γ) C
      leftist Γ' ⟨ M ⟩ E' = sbE [] M (wkE (sub-cons-congr (sub++ Γ')) E')
      leftist Γ' (let○ R E) E' = let○ R (leftist (_ :: Γ') E E')

   subN : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
   subN = sbN []

   subσ : ∀{Γ A Δ} → Term Γ A → Subst (A :: Γ) Δ → Subst Γ Δ
   subσ = sbσ []

{-
   mutual
      subst : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
      subst M (Λ N) = Λ (subst (wk sub-wken M) (wk sub-exch N))
      subst M (N₁ , N₂) = subst M N₁ , subst M N₂
      subst M (○ E) = ○ (substE M E)
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
      substE M ⟨ N ⟩ = ⟨ subst M N ⟩
      substE M (let○ (con c) K σ E) = 
         let○ (con c) K (substσ M σ) (substE (wk sub-wken M) (wkE sub-exch E))
      substE M (let○ (var (S x)) K σ E) = 
         let○ (var x) K (substσ M σ) (substE (wk sub-wken M) (wkE sub-exch E))
      substE M (let○ (var Z) K σ E) = 
         red⁺ M K (substσ M σ) (substE (wk sub-wken M) (wkE sub-exch E))

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
      red⁺ (○ E') ⟨⟩ σ E = leftist E' E
       where
         leftist : ∀{Γ B C} → Exp Γ B → Exp (B :: Γ) C → Exp Γ C
         leftist ⟨ M ⟩ E' = substE M E'
         leftist (let○ h K σ E) E' = let○ h K σ (leftist E (wkE sub-wkex E'))

 

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
   eta (○ A) h K σ = ○ (let○ h K σ ⟨ eta _ (var Z) ⟨⟩ ⟨⟩ ⟩)

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
      ○ E [ σ ]N = ○ (E [ σ ]E)

      _[_]σ : ∀{Γ Γ' Δ} → Subst Γ' Δ → Subst Γ Γ' → Subst Γ Δ
      ⟨⟩ [ σ ]σ = ⟨⟩
      (N , σ') [ σ ]σ = (N [ σ ]N) , (σ' [ σ ]σ)

      _[_]E : ∀{Γ Γ' A} → Exp Γ' A → Subst Γ Γ' → Exp Γ A
      ⟨ N ⟩ [ σ ]E = ⟨ N [ σ ]N ⟩
      let○ (con c) K σ' E [ σ ]E = 
         let○ (con c) K (σ' [ σ ]σ) (E [ η , wkσ sub-wken σ ]E)
      let○ (var x) K σ' E [ σ ]E = 
         red⁺ (lookup x σ) K (σ' [ σ ]σ) (E [ η , wkσ sub-wken σ ]E) 

-}
-}
-}