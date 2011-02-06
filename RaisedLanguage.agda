-- STLC with pairs experimentation
-- Rob Simmons, Salil Joshi, Frank Pfenning

-- Too lazy for metrics, we're switching to %trustme
{-# OPTIONS --no-termination-check #-}

open import Prelude
open import Types
open import UserLanguage

module RaisedLanguage where

module RAISED (sig : Sig) where
   data Head (Δ Γ : Ctx) : Type → Set where
      var : ∀{A} (n : A ∈ Γ) → Head Δ Γ A
      mvar : ∀{A} (n : A ∈ Δ) → Head Δ Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Δ Γ (valOf (sig c) {ch})

   infixr 20 _·_
   mutual
      data Term (Δ Γ : Ctx) : Type → Set where
         _·_ : ∀{A Q}
            (x : Head Δ Γ A)
            (sp : Spine Δ Γ A (con Q))
            → Term Δ Γ (con Q)
         Λ : ∀{A B}
            (n : Term Δ (A :: Γ) B)
            → Term Δ Γ (A ⊃ B)
         ⟨_,_⟩ : ∀{A B}
            (n₁ : Term Δ Γ A)
            (n₂ : Term Δ Γ B)
            → Term Δ Γ (A ∧ B)
         
      data Spine (Δ Γ : Ctx) : Type → Type → Set where
         ⟨⟩ : ∀{A} → Spine Δ Γ A A
         _·_ : ∀{A B C} 
            (n : Term Δ Γ A)
            (sp : Spine Δ Γ B C)
            → Spine Δ Γ (A ⊃ B) C         
         π₁ : ∀{A B C}
            (sp : Spine Δ Γ A C)
            → Spine Δ Γ (A ∧ B) C
         π₂ : ∀{A B C}
            (sp : Spine Δ Γ B C)
            → Spine Δ Γ (A ∧ B) C

   mutual 
      wk : ∀{Δ Γ Γ' A} → Γ ⊆ Γ' → Term Δ Γ A → Term Δ Γ' A
      wk θ (h · sp) = wkH θ h · wkS θ sp
      wk θ (Λ n) = Λ (wk (LIST.SET.sub-cons-congr θ) n)
      wk θ ⟨ n₁ , n₂ ⟩ = ⟨ wk θ n₁ , wk θ n₂ ⟩

      wkH : ∀{Δ Γ Γ' A} → Γ ⊆ Γ' → Head Δ Γ A → Head Δ Γ' A
      wkH θ (var n) = var (θ n)
      wkH θ (mvar n) = mvar n
      wkH θ (con c) = con c

      wkS : ∀{Δ Γ Γ' A C} → Γ ⊆ Γ' → Spine Δ Γ A C → Spine Δ Γ' A C
      wkS θ ⟨⟩ = ⟨⟩
      wkS θ (n · sp) = wk θ n · wkS θ sp
      wkS θ (π₁ sp) = π₁ (wkS θ sp)
      wkS θ (π₂ sp) = π₂ (wkS θ sp)
   
   mutual 
      subst : ∀{Δ Γ A C} → Term Δ Γ A → Term Δ (A :: Γ) C → Term Δ Γ C
      subst n1 (var Z · sp) = hred n1 (substS n1 sp)
      subst n1 (var (S n) · sp) = var n · substS n1 sp
      subst n1 (mvar n · sp) = mvar n · substS n1 sp
      subst n1 (con c · sp) = con c · substS n1 sp
      subst n1 (Λ n) = Λ (subst (wk sub-wken n1) (wk sub-exch n))
      subst n1 ⟨ n₁ , n₂ ⟩ = ⟨ subst n1 n₁ , subst n1 n₂ ⟩

      substS : ∀{Δ Γ A B C} → Term Δ Γ A → Spine Δ (A :: Γ) B C → Spine Δ Γ B C
      substS n1 ⟨⟩ = ⟨⟩
      substS n1 (n · sp) = subst n1 n · substS n1 sp
      substS n1 (π₁ sp) = π₁ (substS n1 sp)
      substS n1 (π₂ sp) = π₂ (substS n1 sp)

      hred : ∀{Δ Γ A C} → Term Δ Γ A → Spine Δ Γ A C → Term Δ Γ C
      hred n ⟨⟩ = n
      hred (Λ n) (n' · sp) = hred (subst n' n) sp
      hred ⟨ n₁ , n₂ ⟩ (π₁ sp) = hred n₁ sp
      hred ⟨ n₁ , n₂ ⟩ (π₂ sp) = hred n₂ sp

   fuse : ∀{Δ Γ A B C} → Spine Δ Γ A B → Spine Δ Γ B C → Spine Δ Γ A C
   fuse ⟨⟩ sp2 = sp2
   fuse (n · sp) sp2 = n · fuse sp sp2
   fuse (π₁ sp) sp2 = π₁ (fuse sp sp2)
   fuse (π₂ sp) sp2 = π₂ (fuse sp sp2)

   eta : ∀{Δ Γ A} (B : Type) → Head Δ Γ A → Spine Δ Γ A B → Term Δ Γ B
   eta (con y) h sp = h · sp
   eta (A ⊃ B) h sp = 
      Λ (eta B (wkH sub-wken h) (fuse (wkS sub-wken sp) (eta A (var Z) ⟨⟩ · ⟨⟩)))
   eta (A ∧ B) h sp = ⟨ eta A h (fuse sp (π₁ ⟨⟩)) , eta B h (fuse sp (π₂ ⟨⟩)) ⟩

   SSubst : Ctx → Ctx → Set 
   SSubst Δ Δ' = LIST.All (Term Δ' []) Δ

   postulate ssubst : ∀{Δ Δ' Γ A} → SSubst Δ Δ' → Term Δ Γ A → Term Δ' Γ A

   open USER sig renaming (Term to ExTerm ; SSubst to ExSSubst)
   canonize : ∀{Δ Γ A} → ExTerm Δ Γ A → Term Δ Γ A
   canonize (var x) = eta _ (var x) ⟨⟩
   canonize (mvar x) = eta _ (mvar x) ⟨⟩
   canonize (con c {prf}) = eta _ (con c {prf}) ⟨⟩
   canonize (n₁ · n₂) = hred (canonize n₁) (canonize n₂ · ⟨⟩)
   canonize (Λ n) = Λ (canonize n)

