-- STLC with pairs experimentation
-- Rob Simmons, Salil Joshi, Frank Pfenning

-- Too lazy for metrics, we're switching to %trustme
{-# OPTIONS --no-termination-check #-}

open import Prelude
open import Types
open import UserLanguage
open import RaisedLanguage 

module LoweredLanguage (sig : Sig) where
   data Head (Δ : LCtx) (Γ : Ctx) : Type → Set where
      var : ∀{A} (n : A ∈ Γ) 
         → Head Δ Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Δ Γ (valOf (sig c) {ch})

   -- sk : Skel Γ A C is the pattern judgment Γ ⊩ A > C
   data Skel : Ctx → Type → Type → Set where
      ⟨⟩ : ∀{A} → Skel [] A A
      ·_ : ∀{A B Γ C}
         (sk : Skel Γ B C)
         → Skel (A :: Γ) (A ⊃ B) C
      π₁ : ∀{A B Γ C}
         (sk : Skel Γ A C)
         → Skel Γ (A ∧ B) C
      π₂ : ∀{A B Γ C}
         (sk : Skel Γ B C)
         → Skel Γ (A ∧ B) C

   infixr 21 _·_[_]
   mutual
      -- σ : Subst Γ' Γ is the typing derivation Γ' ⊢ σ : Γ
      data Subst (Δ : LCtx) : Ctx → Ctx → Set where
         [] : ∀{Γ} → Subst Δ Γ []
         _,_ : ∀{Γ Γ' A} 
            (n : Term Δ Γ' A) 
            (σ : Subst Δ Γ' Γ)
            → Subst Δ Γ' (A :: Γ)
 
      -- n : Term Γ A is the typing derivation Γ ⊢ n : A
      data Term (Δ : LCtx) (Γ : Ctx) : Type → Set where
         _·_[_] : ∀{A Q ΓP}
            (x : Head Δ Γ A)
            (sk : Skel ΓP A (con Q))
            (σ : Subst Δ Γ ΓP)
            → Term Δ Γ (con Q)
         mvar : ∀{Γ' Q}
            (x : (Γ' , Q) ∈ Δ)
            (σ : Subst Δ Γ Γ')
            → Term Δ Γ (con Q)
         Λ : ∀{A B}
            (n : Term Δ (A :: Γ) B)
            → Term Δ Γ (A ⊃ B)
         ⟨_,_⟩ : ∀{A B}
            (n₁ : Term Δ Γ A)
            (n₂ : Term Δ Γ B)
            → Term Δ Γ (A ∧ B)
         
   -- WEAKENING
   mutual 
      wk : ∀{Δ Γ Γ' A} → Γ ⊆ Γ' → Term Δ Γ A → Term Δ Γ' A
      wk θ (x · sk [ σ ]) = wkH θ x · sk [ wkS θ σ ]
      wk θ (mvar x σ) = mvar x (wkS θ σ)
      wk θ (Λ n) = Λ (wk (sub-cons-congr θ) n)
      wk θ ⟨ n₁ , n₂ ⟩ = ⟨ wk θ n₁ , wk θ n₂ ⟩

      wkH : ∀{Δ Γ Γ' A} → Γ ⊆ Γ' → Head Δ Γ A → Head Δ Γ' A
      wkH θ (var x) = var (θ x)
      wkH θ (con c) = con c

      wkS : ∀{Δ Γ Γ' ΓP} → Γ ⊆ Γ' → Subst Δ Γ ΓP → Subst Δ Γ' ΓP
      wkS θ [] = []
      wkS θ (n , σ) = wk θ n , wkS θ σ

   -- SUBSTITUTION
   mutual 
      subst : ∀{Δ Γ A C} → Term Δ Γ A → Term Δ (A :: Γ) C → Term Δ Γ C
      subst n (var Z · sk [ σ ]) = hred n sk (substS n σ)
      subst n (var (S x) · sk [ σ ]) = var x · sk [ substS n σ ]
      subst n (con c · sk [ σ ]) = con c · sk [ substS n σ ]
      subst n (mvar x σ) = mvar x (substS n σ)
      subst n (Λ n') = Λ (subst (wk sub-wken n) (wk sub-exch n'))
      subst n ⟨ n₁ , n₂ ⟩ = ⟨ subst n n₁ , subst n n₂ ⟩

      substS : ∀{Δ Γ Γ' A} → Term Δ Γ A → Subst Δ (A :: Γ) Γ' → Subst Δ Γ Γ'
      substS n [] = []
      substS n (n' , σ) = subst n n' , substS n σ

      hred : ∀{Δ Γ ΓP A C} 
         → Term Δ Γ A 
         → Skel ΓP A C
         → Subst Δ Γ ΓP
         → Term Δ Γ C
      hred n ⟨⟩ [] = n
      hred (Λ n) (· sk) ( m , σ ) = hred (subst m n) sk σ
      hred (⟨ n₁ , n₂ ⟩) (π₁ sk) ( σ ) = hred n₁ sk σ 
      hred (⟨ n₁ , n₂ ⟩) (π₂ sk) ( σ ) = hred n₂ sk σ 

   -- In RaisedLanguage, these were treated together as the single "fuse"
   -- The difference between spines and skeletons, however, is that a skeleton's
   -- type includes the type of all of it's elements, so we have to use 
   -- list append and it's easier to do the separately.
   ·' : ∀{Γ A B C} → Skel Γ A (B ⊃ C) → Skel (Γ ++ [ B ]) A C 
   ·' ⟨⟩ = · ⟨⟩
   ·' (· sk) = · ·' sk
   ·' (π₁ sk) = π₁ (·' sk)
   ·' (π₂ sk) = π₂ (·' sk)

   π₁' : ∀{Γ A B C} → Skel Γ A (B ∧ C) → Skel Γ A B
   π₁' ⟨⟩ = π₁ ⟨⟩
   π₁' (· sk) = · π₁' sk
   π₁' (π₁ sk) = π₁ (π₁' sk)
   π₁' (π₂ sk) = π₂ (π₁' sk)

   π₂' : ∀{Γ A B C} → Skel Γ A (B ∧ C) → Skel Γ A C
   π₂' ⟨⟩ = π₂ ⟨⟩
   π₂' (· sk) = · π₂' sk
   π₂' (π₁ sk) = π₁ (π₂' sk)
   π₂' (π₂ sk) = π₂ (π₂' sk)

   eta : ∀{Δ Γ ΓP A} (B : Type)
      → Head Δ Γ A 
      → Skel ΓP A B
      → Subst Δ Γ ΓP 
      → Term Δ Γ B
   eta (con Q) h sk σ = h · sk [ σ ]
   eta (A ⊃ B) h sk σ = Λ (eta B (wkH sub-wken h) (·' sk) (wkη σ))
    where 
      wkη : ∀{Δ Γ ΓP A} → Subst Δ Γ ΓP → Subst Δ (A :: Γ) (ΓP ++ A :: [])
      wkη [] = eta _ (var Z) ⟨⟩ [] , []
      wkη (n , σ) = wk sub-wken n , wkη σ
   eta (A ∧ B) h sk σ = ⟨ eta A h (π₁' sk) σ , eta B h (π₂' sk) σ ⟩

   η : ∀{Δ Γ A} → A ∈ Γ → Term Δ Γ A
   η x = eta _ (var x) ⟨⟩ []

   lookup : ∀{Δ A Γ Γ'} → A ∈ Γ' → Subst Δ Γ Γ' → Term Δ Γ A
   lookup () []
   lookup Z (n , σ) = n
   lookup (S x) (n , σ) = lookup x σ

   pull : ∀{Δ Γ ΓP A C}
      → Term Δ Γ A
      → Skel ΓP A C
      → Term Δ (ΓP ++ Γ) C × Subst Δ (ΓP ++ Γ) ΓP
   pull n ⟨⟩ = n , [] 
   pull {_} {Γ} {A :: ΓP} (Λ n) (· sk) = term , subs
    where 
      wk1 : ∀{A} (Γ Γ' : Ctx) → (Γ ++ A :: Γ') ⊆ (A :: Γ ++ Γ')
      wk1 [] Γ x = x
      wk1 (B :: Γ) Γ' Z = S Z 
      wk1 (B :: Γ) Γ' (S x) = sub-wkex (wk1 Γ Γ' x)
      term = wk (wk1 ΓP Γ) (fst (pull n sk))
      subs = η Z , wkS (wk1 ΓP Γ) (snd (pull n sk))
   pull ⟨ n₁ , n₂ ⟩ (π₁ sk) = pull n₁ sk
   pull ⟨ n₁ , n₂ ⟩ (π₂ sk) = pull n₂ sk

   mutual
      _○_ : ∀{Δ Γ₁ Γ₂ Γ₃} → Subst Δ Γ₁ Γ₂ → Subst Δ Γ₂ Γ₃ → Subst Δ Γ₁ Γ₃
      σ ○ [] = []
      σ ○ (n , τ) = (n ⟦ σ ⟧) , (σ ○ τ)

      _⟦_⟧ : ∀{Δ Γ Γ' A}
         → Term Δ Γ' A
         → Subst Δ Γ Γ'
         → Term Δ Γ A
      mvar u σ ⟦ σ' ⟧ = mvar u (σ' ○ σ)
      var x · sk [ σ ] ⟦ σ' ⟧ = hred (lookup x σ') sk (σ' ○ σ)
       where
         pulled-term = pull (lookup x σ') sk
         n = fst pulled-term
         τ = snd pulled-term
      con c · sk [ σ ] ⟦ σ' ⟧ = con c · sk [ σ' ○ σ ]
      Λ n ⟦ σ ⟧ = Λ (n ⟦ η Z , wkS sub-wken σ ⟧)
      ⟨ n₁ , n₂ ⟩ ⟦ σ ⟧ = ⟨ n₁ ⟦ σ ⟧ , n₂ ⟦ σ ⟧ ⟩ 

   -- This will just be annoying, since involves strengthening
   seek : ∀{Γ Δ A B C}
      → Term [] Γ B
      → A ∈ Γ
      → Skel Δ A C
      → List (∃ λ Ψ → Skel Ψ B C × Subst [] Ψ Δ)
   seek n x sk = {!!}

   mutual 
      _○⁻¹_ : ∀{Γ₁ Γ₂ Γ₃} 
         → Subst [] Γ₁ Γ₂ 
         → Subst [] Γ₁ Γ₃ 
         → List (Subst [] Γ₂ Γ₃)
      σ ○⁻¹ [] = [ [] ]
      σ ○⁻¹ (n , τ) = LIST.cross _,_ (n ⟦ σ ⟧⁻¹) (σ ○⁻¹ τ)

      _⟦_⟧⁻¹ : ∀{Γ Γ' A}
         → Term [] Γ A
         → Subst [] Γ Γ'
         → List (Term [] Γ' A)
      mvar () σ ⟦ σ' ⟧⁻¹
      var n · sk [ σ ] ⟦ σ' ⟧⁻¹ = {!LIST.map ? ?!}
      con c · sk [ σ ] ⟦ σ' ⟧⁻¹ = LIST.map (_·_[_] (con c) sk) (σ' ○⁻¹ σ)
      Λ n ⟦ σ ⟧⁻¹ = LIST.map Λ (n ⟦ η Z , wkS sub-wken σ ⟧⁻¹)
      ⟨ n₁ , n₂ ⟩ ⟦ σ ⟧⁻¹ = LIST.cross ⟨_,_⟩ (n₁ ⟦ σ ⟧⁻¹) (n₂ ⟦ σ ⟧⁻¹)

{-
   mvar () σ ⟦ σ' ⟧⁻¹
   x · sk [ σ ] ⟦ σ' ⟧⁻¹ = {!!}
   Λ n ⟦ σ ⟧⁻¹ with n ⟦ wkS sub-wken σ ⟧⁻¹ 
   ... | qs = LIST.concat {!!} qs
   ⟨ n₁ , n₂ ⟩ ⟦ σ ⟧⁻¹ = {!!}
-}

   -- hred⁻¹ : ∀{Γ A} → Term [] Γ A → Subst [] Γ Γ' → 

   -- TRANSLATION FROM RAISED LANGUAGE
   open RAISED sig renaming 
      (Term to ExTerm 
      ; Head to ExHead 
      ; Spine to ExSpine
      ; _·_ to _··_)
   raiseA : Type → List (List Type × String)
   raiseA (con Q) = [ ([] , Q) ]
   raiseA (A ⊃ B) = LIST.map (λ C → (A :: fst C) , snd C) (raiseA B)
   raiseA (A ∧ B) = raiseA A ++ raiseA B

   raiseΔ : Ctx → LCtx
   raiseΔ = LIST.concat raiseA 

   raiseu : ∀{Δ Γ A C} → A ∈ Δ → Skel Γ A (con C) → (Γ , C) ∈ (raiseΔ Δ)
   raiseu x sk = LIST.in-concat raiseA x (raise sk)
    where
      raise : ∀{Γ A C} → Skel Γ A (con C) → (Γ , C) ∈ raiseA A
      raise ⟨⟩ = Z
      raise (· sk') = LIST.in-map _ (raise sk')
      raise (π₁ sk') = LIST.in-append (raise sk') _
      raise (π₂ {A = A} sk') = LIST.append-in (raiseA A) (raise sk')

   mutual
      raise : ∀{Δ Γ A} → ExTerm Δ Γ A → Term (raiseΔ Δ) Γ A
      raise (h ·· sp) with h | raiseS sp
      ... | var x | (_ , (sk , σ)) = var x · sk [ σ ]
      ... | con c {prf} | (_ , (sk , σ)) = con c {prf} · sk [ σ ]
      ... | mvar x | (_ , (sk , σ)) = mvar (raiseu x sk) σ
      raise (Λ n) = Λ (raise n)
      raise (⟨ n₁ , n₂ ⟩) = ⟨ raise n₁ , raise n₂ ⟩

      raiseS : ∀{Γ Δ A C} 
         → ExSpine Δ Γ A C 
         → ∃ λ ΓP → Skel ΓP A C × Subst (raiseΔ Δ) Γ ΓP
      raiseS ⟨⟩ = [] , (⟨⟩ , [])
      raiseS (n ·· sp) with raiseS sp
      ... | (Γ , (sk , σ)) = (_ :: Γ) , (· sk , (raise n , σ))
      raiseS (π₁ sp) with raiseS sp
      ... | (Γ , (sk , σ)) = Γ , (π₁ sk , σ)
      raiseS (π₂ sp) with raiseS sp
      ... | (Γ , (sk , σ)) = Γ , (π₂ sk , σ)


   -- postulate raise : ∀{Δ Γ A} → ExTerm Δ Γ A → Term (raiseΔ Δ) Γ A
{-
   mutual 
      skel : ∀{Δ Γ x}
-}