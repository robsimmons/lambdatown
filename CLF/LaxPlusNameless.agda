open import Prelude 

module CLF.LaxPlusNameless where

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

   -- Metric (totally nameless terms)
   mutual
      val = Maybe trm

      sub = List val

      data trm : Set where
         con : (s : sub) → trm
         ○ : (e : exp) → trm
         Λ : (n : trm) → trm
         _,_ : (n₁ n₂ : trm) → trm
  
      data exp : Set where
         ⟨_⟩ : (v : val) → exp
         let○ : (s : sub) (e : exp) → exp

   -- Logic
   data Head (Γ : Ctx) : Type ⁻ → Set where
      var : ∀{A} (x : A true⁻ ∈ Γ)
         → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   -- Outside the metric
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

   -- Inside the metric
   mutual
      data Value' (Γ : Ctx) : val → Jmt → Set where
         ⁺ : ∀{Q} (x : Q true⁺ ∈ Γ) → Value' Γ Nothing (Q true⁺)
         ⁻ : ∀{A n} (N : Term' Γ n A) → Value' Γ (Just n) (A true⁻)
         
      data Subst' (Γ : Ctx) : sub → Ctx → Set where
         ⟨⟩ : Subst' Γ [] []
         _,⁻_ : ∀{A Δ n s}
            (N : Term' Γ n A) 
            (σ : Subst' Γ s Δ)
            → Subst' Γ (Just n :: s) (A true⁻ :: Δ) 
         _,⁺_ : ∀{Q Δ s} 
            (x : Q true⁺ ∈ Γ)
            (σ : Subst' Γ s Δ)
            → Subst' Γ (Nothing :: s) (Q true⁺ :: Δ)

      -- N : Term Γ A is the derivation Γ ⊢ N : A true
      data Term' (Γ : Ctx) : trm → Type ⁻ → Set where
         _·_[_] : ∀{A Q Δ s}
            (h : Head Γ A)
            (K : Skel Δ A (con Q))
            (σ : Subst' Γ s Δ)
            → Term' Γ (con s) (con Q)
         ○ : ∀{A e}
            (E : Exp' Γ e A)
            → Term' Γ (○ e) (○ A)
         Λ : ∀{A B n}
            (N : Term' (Hyp A :: Γ) n B)
            → Term' Γ (Λ n) (A ⊃ B)
         _,_ : ∀{A B n₁ n₂}
            (N₁ : Term' Γ n₁ A)
            (N₂ : Term' Γ n₂ B)
            → Term' Γ (n₁ , n₂) (A ∧ B) 
            
      -- E : Exp Γ A is the derivation Γ ⊢ E ÷ A lax
      data Exp' (Γ : Ctx) : exp → Type ⁺ → Set where
         ⟨_⟩ : ∀{A v}
            (V : Value' Γ v (Hyp A))
            → Exp' Γ (⟨ v ⟩) A 
         let○ : ∀{Δ A B C s e} 
            (h : Head Γ A)
            (K : Skel Δ A (○ B))
            (σ : Subst' Γ s Δ)
            (E : Exp' (Hyp B :: Γ) e C)
            → Exp' Γ (let○ s e) C 

   -- WEAKENING
   mutual
      wk' : ∀{Γ Γ' A n} → Γ ⊆ Γ' → Term' Γ n A → Term' Γ' n A
      wk' θ (var x · K [ σ ]) = var (θ x) · K [ wkσ' θ σ ]
      wk' θ (con c · K [ σ ]) = con c · K [ wkσ' θ σ ]
      wk' θ (○ E) = ○ (wkE' θ E)
      wk' θ (Λ N) = Λ (wk' (sub-cons-congr θ) N)
      wk' θ (N₁ , N₂) = wk' θ N₁ , wk' θ N₂

      wkσ' : ∀{Γ Γ' s Δ} → Γ ⊆ Γ' → Subst' Γ s Δ → Subst' Γ' s Δ
      wkσ' θ ⟨⟩ = ⟨⟩
      wkσ' θ (N ,⁻ σ) = wk' θ N ,⁻ wkσ' θ σ
      wkσ' θ (x ,⁺ σ) = θ x ,⁺ wkσ' θ σ

      wkE' : ∀{Γ Γ' A e} → Γ ⊆ Γ' → Exp' Γ e A → Exp' Γ' e A
      wkE' {A = con Q} θ ⟨ ⁺ x ⟩ = ⟨ ⁺ (θ x) ⟩
      wkE' {A = ↓ A} θ ⟨ ⁻ N ⟩ = ⟨ ⁻ (wk' θ N) ⟩
      wkE' θ (let○ (var x) K σ E) = 
         let○ (var (θ x)) K (wkσ' θ σ) (wkE' (sub-cons-congr θ) E)
      wkE' θ (let○ (con c) K σ E) = 
         let○ (con c) K (wkσ' θ σ) (wkE' (sub-cons-congr θ) E)
 
   -- IN AND OUT OF THE METRIC
   mutual
      mN : ∀{Γ A} → Term Γ A → trm
      mN (h · K [ σ ]) = con (mσ σ)
      mN (○ E) = ○ (mE E)
      mN (Λ N) = Λ (mN N)
      mN (N₁ , N₂) = mN N₁ , mN N₂

      mV : ∀{Γ A} → Value Γ A → val
      mV (⁺ x) = Nothing
      mV (⁻ N) = Just (mN N)

      mσ : ∀{Γ Δ} → Subst Γ Δ → sub
      mσ ⟨⟩ = []
      mσ (N ,⁻ σ) = Just (mN N) :: mσ σ
      mσ (x ,⁺ σ) = Nothing :: mσ σ

      mE : ∀{Γ A} → Exp Γ A → exp
      mE ⟨ V ⟩ = ⟨ mV V ⟩
      mE (let○ h K σ E) = let○ (mσ σ) (mE E)

   mutual 
      m→ : ∀{Γ n A} → Term' Γ n A → Term Γ A
      m→ (h · K [ σ ]) = h · K [ mσ→ σ ]
      m→ (○ E) = ○ (mE→ E)
      m→ (Λ N) = Λ (m→ N)
      m→ (N₁ , N₂) = m→ N₁ , m→ N₂ 

      mσ→ : ∀{Γ s Δ} → Subst' Γ s Δ → Subst Γ Δ
      mσ→ ⟨⟩ = ⟨⟩
      mσ→ (N ,⁻ σ) = m→ N ,⁻ mσ→ σ
      mσ→ (x ,⁺ σ) = x ,⁺ mσ→ σ

      mE→ : ∀{Γ e A} → Exp' Γ e A → Exp Γ A
      mE→ {A = con Q} ⟨ ⁺ x ⟩ = ⟨ ⁺ x ⟩
      mE→ {A = ↓ A} ⟨ ⁻ N ⟩ = ⟨ ⁻ (m→ N) ⟩
      mE→ (let○ h K σ E) = let○ h K (mσ→ σ) (mE→ E)

   mutual
      →m : ∀{Γ A} (N : Term Γ A) → Term' Γ (mN N) A
      →m (h · K [ σ ]) = {!!}
      →m (○ E) = {!!}
      →m (Λ N) = {!!}
      →m (N₁ , N₂) = {!!}

      →mV : ∀{Γ A} (V : Value Γ A) → Value' Γ (mV V) A
      →mV (⁺ x) = ⁺ x
      →mV (⁻ N) = ⁻ (→m N)

      →mσ : ∀{Γ Δ} (σ : Subst Γ Δ) → Subst' Γ (mσ σ) Δ
      →mσ ⟨⟩ = ⟨⟩
      →mσ (N ,⁻ σ) = →m N ,⁻ →mσ σ
      →mσ (x ,⁺ σ) = x ,⁺ →mσ σ

      →mE : ∀{Γ A} (E : Exp Γ A) → Exp' Γ (mE E) A
      →mE ⟨ V ⟩ = ⟨ →mV V ⟩
      →mE (let○ h K σ E) = let○ h K (→mσ σ) (→mE E)

   wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
   wk θ N = m→ (wk' θ (→m N))

   wkE : ∀{Γ Γ' A} → Γ ⊆ Γ' → Exp Γ A → Exp Γ' A
   wkE θ E = mE→ (wkE' θ (→mE E))

   -- SUBSTITUTION
   mutual
      -- Type A stays the same
      -- Term N gets smaller
      subst : ∀{Γ A C n} 
         → Term Γ A 
         → Term' (A true⁻ :: Γ) n C 
         → Term Γ C
      subst M (var Z · K [ σ ]) = hred M K (substσ M σ)
      subst M (var (S x) · K [ σ ]) = var x · K [ substσ M σ ]
      subst M (con c · K [ σ ]) = con c · K [ substσ M σ ]
      subst M (○ E) = ○ (substE M E)
      subst M (Λ N) = Λ (subst (wk sub-wken M) (wk' sub-exch N))
      subst M ( N₁ , N₂ ) = subst M N₁ , subst M N₂

      -- Type A stays the same
      -- Substitution σ gets smaller
      substσ : ∀{Γ Δ A s} 
         → Term Γ A 
         → Subst' (A true⁻ :: Γ) s Δ
         → Subst Γ Δ
      substσ M ⟨⟩ = ⟨⟩
      substσ M (N ,⁻ σ) = subst M N ,⁻ substσ M σ
      substσ M (S x ,⁺ σ) = x ,⁺ substσ M σ

      -- Type A stays the same 
      -- Expression E gets smaller
      substE : ∀{Γ A C e} → Term Γ A → Exp' (A true⁻ :: Γ) e C → Exp Γ C
      substE {C = con Q} M ⟨ ⁺ (S x) ⟩ = ⟨ ⁺ x ⟩
      substE {C = ↓ A'} M ⟨ ⁻ N ⟩ = ⟨ ⁻ (subst M N) ⟩
      substE M (let○ (var Z) K σ E) with hred M K (substσ M σ)
      ... | ○ E' = leftist E' (substE (wk sub-wken M) (wkE' sub-exch E))
       where
         leftist : ∀{Γ A C} → Exp Γ A → Exp (Hyp A :: Γ) C → Exp Γ C
         leftist {A = con Q} ⟨ ⁺ x ⟩ E' = wkE (sub-cntr x) E'
         leftist {A = ↓ A} ⟨ ⁻ M ⟩ E' = substE M (→mE E')
         leftist (let○ h K σ E) E' = let○ h K σ (leftist E (wkE sub-wkex E'))
      substE M (let○ (var (S x)) K σ E) = 
         let○ (var x) K (substσ M σ) (substE (wk sub-wken M) (wkE' sub-exch E))
      substE M (let○ (con c) K σ E) = 
         let○ (con c) K (substσ M σ) (substE (wk sub-wken M) (wkE' sub-exch E))

      -- Type A gets smaller
      hred : ∀{Γ Δ A C}
         → Term Γ A 
         → Skel Δ A C
         → Subst Γ Δ
         → Term Γ C
      hred M ⟨⟩ σ = M
      hred {A = con Q ⊃ A'} (Λ M) (· K) (x ,⁺ σ) = 
         hred (wk (sub-cntr x) M) K σ 
      hred {A = ↓ A ⊃ A'} (Λ M) (· K) (N ,⁻ σ) = hred (subst N (→m M)) K σ 
      hred (M₁ , M₂) (π₁ K) σ = hred M₁ K σ
      hred (M₁ , M₂) (π₂ K) σ = hred M₂ K σ

