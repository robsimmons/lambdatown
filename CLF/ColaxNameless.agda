-- Robert J. Simmons
-- Note, this doesn't work, see COUNTEREXAMPLE at the bottom

open import Prelude 

module CLF.ColaxNameless where

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



module COLAX (sig : String → Maybe Type) where


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
         ○ : ∀{A}
            (E : Lazy (Exp Γ A))
            → Term Γ (○ A)
            
      -- E : Exp Γ A is the derivation Γ ⊢ E ÷ A lax
      data Exp (Γ : Ctx) : Type → Set where
         ⟨_⟩ : ∀{A}
            (N : Term Γ A)
            → Exp Γ A 
         let○ : ∀{Δ A B C} 
            (h : Head Γ A)
            (K : Skel Δ A (○ B))
            (σ : Subst Γ Δ)
            (E : Lazy (Exp (B :: Γ) C))
            → Exp Γ C 


   {- PART 2: METRIC (TOTALLY NAMELESS REPRESENTATION) -}

   -- Totally nameless terms
   mutual
      sub = List trm

      data trm : Set where
         con : (s : sub) → trm
         ○ : (e : Lazy exp) → trm
         Λ : (n : trm) → trm
         _,_ : (n₁ n₂ : trm) → trm
  
      data exp : Set where
         ⟨_⟩ : (v : trm) → exp
         let○ : (s : sub) (e : Lazy exp) → exp

   -- Terms with the metric
   mutual
      data Subst' (Γ : Ctx) : sub → Ctx → Set where
         ⟨⟩ : Subst' Γ [] []
         _,_ : ∀{A Δ n s}
            (N : Term' Γ n A) 
            (σ : Subst' Γ s Δ)
            → Subst' Γ (n :: s) (A :: Δ) 

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
         ○ : ∀{A e}
            (E : Lazy (Exp' Γ (force e) A))
            → Term' Γ (○ e) (○ A)
            
      data Exp' (Γ : Ctx) : exp → Type → Set where
         ⟨_⟩ : ∀{A n}
            (N : Term' Γ n A)
            → Exp' Γ (⟨ n ⟩) A 
         let○ : ∀{Δ A B C s e} 
            (h : Head Γ A)
            (K : Skel Δ A (○ B))
            (σ : Subst' Γ s Δ)
            (E : Lazy (Exp' (B :: Γ) (force e) C))
            → Exp' Γ (let○ s e) C 

   -- Metric erasure
   mutual 
      m→ : ∀{Γ n A} → Term' Γ n A → Term Γ A
      m→ (h · K [ σ ]) = h · K [ mσ→ σ ]
      m→ (Λ N) = Λ (m→ N)
      m→ (N₁ , N₂) = m→ N₁ , m→ N₂ 
      m→ (○ E) = ○ (thunk (mE→ (force E)))

      mσ→ : ∀{Γ s Δ} → Subst' Γ s Δ → Subst Γ Δ
      mσ→ ⟨⟩ = ⟨⟩
      mσ→ (N , σ) = m→ N , mσ→ σ

      mE→ : ∀{Γ e A} → Exp' Γ e A → Exp Γ A
      mE→ ⟨ N ⟩ = ⟨ m→ N ⟩
      mE→ (let○ h K σ E) = let○ h K (mσ→ σ) (thunk (mE→ (force E)))

   -- Metric calculation
   mutual
      mN : ∀{Γ A} → Term Γ A → trm
      mN (h · K [ σ ]) = con (mσ σ)
      mN (Λ N) = Λ (mN N)
      mN (N₁ , N₂) = mN N₁ , mN N₂
      mN (○ E) = ○ (thunk (mE (force E))) -- (mE (force E))

      mσ : ∀{Γ Δ} → Subst Γ Δ → sub
      mσ ⟨⟩ = []
      mσ (N , σ) = mN N :: mσ σ

      mE : ∀{Γ A} → Exp Γ A → exp
      mE ⟨ N ⟩ = ⟨ mN N ⟩ -- susp ⟨ mN N ⟩
      mE (let○ h K σ E) = let○ (mσ σ) (thunk (mE (force E)))

   -- Metric addition
   mutual
      →m : ∀{Γ A} (N : Term Γ A) → Term' Γ (mN N) A
      →m (h · K [ σ ]) = h · K [ →mσ σ ]
      →m (Λ N) = Λ (→m N)
      →m (N₁ , N₂) = →m N₁ , →m N₂
      →m (○ E) = ○ (thunk (→mE (force E)))

      →mσ : ∀{Γ Δ} (σ : Subst Γ Δ) → Subst' Γ (mσ σ) Δ
      →mσ ⟨⟩ = ⟨⟩
      →mσ (N , σ) = →m N , →mσ σ

      →mE : ∀{Γ A} (E : Exp Γ A) → Exp' Γ (mE E) A
      →mE ⟨ N ⟩ = ⟨ →m N ⟩ 
      →mE (let○ h K σ E) = let○ h K (→mσ σ) (thunk (→mE (force E)))


   {- PART 3: GENERALIZED WEAKENING (a.k.a. renaming, context renaming) -}

   wkh : ∀{Γ Γ' A} → Γ ⊆ Γ' → Head Γ A → Head Γ' A
   wkh θ (con c) = con c
   wkh θ (var x) = var (θ x)

   mutual
      wk' : ∀{Γ Γ' A n} → Γ ⊆ Γ' → Term' Γ n A → Term' Γ' n A
      wk' θ (h · K [ σ ]) = wkh θ h · K [ wkσ' θ σ ]
      wk' θ (Λ N) = Λ (wk' (sub-cons-congr θ) N)
      wk' θ (N₁ , N₂) = wk' θ N₁ , wk' θ N₂
      wk' θ (○ E) = ○ (thunk (wkE' θ (force E))) -- (wkE' θ ?)

      wkσ' : ∀{Γ Γ' s Δ} → Γ ⊆ Γ' → Subst' Γ s Δ → Subst' Γ' s Δ
      wkσ' θ ⟨⟩ = ⟨⟩
      wkσ' θ (N , σ) = wk' θ N , wkσ' θ σ

      wkE' : ∀{Γ Γ' A e} → Γ ⊆ Γ' → Exp' Γ e A → Exp' Γ' e A
      wkE' θ ⟨ N ⟩ = ⟨ wk' θ N ⟩
      wkE' θ (let○ h K σ E) = 
         let○ (wkh θ h) K (wkσ' θ σ)
          (thunk (wkE' (sub-cons-congr θ) (force E)))
 
   wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Term Γ A → Term Γ' A
   wk θ N = m→ (wk' θ (→m N))

   wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
   wkσ θ σ = mσ→ (wkσ' θ (→mσ σ))

   wkE : ∀{Γ Γ' A} → Γ ⊆ Γ' → Exp Γ A → Exp Γ' A
   wkE θ E = mE→ (wkE' θ (→mE E))


   {- PART 4: SUBSTITUTION -}

   mutual
      subst : ∀{Γ A C n} → Term Γ A → Term' (A :: Γ) n C → Term Γ C
      subst M (Λ N) = Λ (subst (wk sub-wken M) (wk' sub-exch N))
      subst M (N₁ , N₂) = subst M N₁ , subst M N₂
      subst M (○ E) = ○ (thunk (substE M (force E)))
      subst M (con c · K [ σ ]) = con c · K [ substσ M σ ]
      subst M (var (S x) · K [ σ ]) = var x · K [ substσ M σ ]
      subst M (var Z · K [ σ ]) = red⁻ M K (substσ M σ)

      red⁻ : ∀{Γ Δ A C} → Term Γ A → Skel Δ A C → Subst Γ Δ → Term Γ C
      red⁻ M ⟨⟩ σ = M
      red⁻ (Λ M) (· K) (N , σ) = red⁻ (subst N (→m M)) K σ
      red⁻ (M₁ , M₂) (π₁ K) σ = red⁻ M₁ K σ
      red⁻ (M₁ , M₂) (π₂ K) σ = red⁻ M₂ K σ

      substσ : ∀{Γ Δ A s} → Term Γ A → Subst' (A :: Γ) s Δ → Subst Γ Δ
      substσ M ⟨⟩ = ⟨⟩
      substσ M (N , σ) = subst M N , substσ M σ

      substE : ∀{Γ A C e} → Term Γ A → Exp' (A :: Γ) e C → Exp Γ C
      substE M ⟨ N ⟩ = ⟨ subst M N ⟩
      substE {e = let○ s e} M (let○ (con c) K σ E) = 
         let○ (con c) K (substσ M σ)
          (thunk (substE (wk sub-wken M) (wkE' sub-exch (force E))))
      substE M (let○ (var (S x)) K σ E) = 
         let○ (var x) K (substσ M σ)
          (thunk (substE (wk sub-wken M) (wkE' sub-exch (force E))))
      substE M (let○ (var Z) K σ E) = 
         red⁺ M K (substσ M σ)
          (substE (wk sub-wken M) (wkE' sub-exch (force E)))

      red⁺ : ∀{Γ Δ A B C} 
         → Term Γ A 
         → Skel Δ A (○ B) 
         → Subst Γ Δ 
         → Exp (B :: Γ) C
         → Exp Γ C
      red⁺ (h · K [ σ' ]) () σ E 
      red⁺ (Λ M) (· K) (N , σ) E = red⁺ (subst N (→m M)) K σ E
      red⁺ (M₁ , M₂) (π₁ K) σ E = red⁺ M₁ K σ E
      red⁺ (M₁ , M₂) (π₂ K) σ E = red⁺ M₂ K σ E
      red⁺ (○ E') ⟨⟩ σ E = leftist (force E') E
       where
         leftist : ∀{Γ B C} → Exp Γ B → Exp (B :: Γ) C → Exp Γ C
         leftist ⟨ M ⟩ E' = substE M (→mE E')
         leftist (let○ h K σ E) E' = 
            let○ h K σ (thunk (leftist (force E) (wkE sub-wkex E')))

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
   eta (○ A) h K σ = ○ (thunk (let○ h K σ (thunk ⟨ eta _ (var Z) ⟨⟩ ⟨⟩ ⟩)))

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
      ○ E [ σ ]N = ○ (thunk (force E [ σ ]E))

      _[_]σ : ∀{Γ Γ' Δ} → Subst Γ' Δ → Subst Γ Γ' → Subst Γ Δ
      ⟨⟩ [ σ ]σ = ⟨⟩
      (N , σ') [ σ ]σ = (N [ σ ]N) , (σ' [ σ ]σ)

      _[_]E : ∀{Γ Γ' A} → Exp Γ' A → Subst Γ Γ' → Exp Γ A
      ⟨ N ⟩ [ σ ]E = ⟨ N [ σ ]N ⟩
      let○ (con c) K σ' E [ σ ]E = 
         let○ (con c) K (σ' [ σ ]σ) (thunk (force E [ η , wkσ sub-wken σ ]E))
      let○ (var x) K σ' E [ σ ]E = 
         red⁺ (lookup x σ) K (σ' [ σ ]σ) (force E [ η , wkσ sub-wken σ ]E)


{- Why this doesn't work -}
module COUNTEREXAMPLE where

   open COLAX (λ x → Nothing) public 

   -- term1 : · ⊢ Q ⊃ { Q }
   term1 : Term [] (con "q" ⊃ ○ (con "q"))
   term1 = Λ (○ (thunk ⟨ (var Z) · ⟨⟩ [ ⟨⟩ ] ⟩)) 

   -- term2 : Q ⊃ { Q } ⊢ Q ⊃ { P }
   term2 : Term [ con "q" ⊃ ○ (con "q") ] (con "q" ⊃ ○ (con "p"))
   term2 = Λ (○ (infexp (S Z) Z))
    where
      infexp : ∀{Γ}
         → (con "q" ⊃ ○ (con "q")) ∈ Γ 
         → con "q" ∈ Γ 
         → Lazy (Exp Γ (con "p"))
      infexp f x = thunk (let○ (var f) (· ⟨⟩) (var x · ⟨⟩ [ ⟨⟩ ] , ⟨⟩) 
                      (infexp (S f) (S x)))

   -- the trap: use cut elimination to produce non-productive term
   oh_crap : Void
   oh_crap = notterm3 term3
    where
      term3 : Term [] (con "q" ⊃ ○ (con "p"))
      term3 = subst term1 (→m term2)

      lem1 : Exp [ con "q" ] (con "p") → Void
      lem1 ⟨ con c {()} · K [ σ ] ⟩ 
      lem1 ⟨ var Z · () [ σ ] ⟩
      lem1 ⟨ var (S ()) · K [ σ ] ⟩
      lem1 (let○ (con c {()}) K σ E')
      lem1 (let○ (var Z) () σ E') 
      lem1 (let○ (var (S ())) K σ E')

      notterm3 : Term [] (con "q" ⊃ ○ (con "p")) → Void
      notterm3 (Λ (○ E)) = lem1 (force E) 
