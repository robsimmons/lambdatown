-- STLC with pairs experimentation
-- Rob Simmons, Salil Joshi, Frank Pfenning

-- Broken; terms have to be defined simultaneously with substitution

open import Prelude
open import Types
open import UserLanguage

module ExternalLanguage where

module EXTERNAL (sig : String → Maybe Type) where
   infixl 5 _·_
   data Term (Δ : MCtx) : (Ctx × Type) → Set where
      var : ∀{Γ A} (x : A ∈ Γ) → Term Δ (Γ , A)
      mvar : ∀{mty} (x : mty ∈ Δ) → Term Δ mty
      con : ∀{Γ} (c : String) {ch : Check (isSome (sig c))}
         → Term Δ (Γ , valOf (sig c) {ch})
      _·_ : ∀{Γ A B} 
         (n₁ : Term Δ (Γ , A ⊃ B)) 
         (n₂ : Term Δ (Γ , A)) 
         → Term Δ (Γ , B)
      Λ : ∀{Γ A B} 
         (n : Term Δ (A :: Γ , B)) 
         → Term Δ (Γ , A ⊃ B)

   open USER sig hiding (SSubst) renaming (Term to ExTerm)
   parse : ∀{Δ Γ A} → ExTerm Δ Γ A → Term (LIST.map (_,_ []) Δ) (Γ , A)
   parse (var x) = var x
   parse (mvar x) = mvar {!LIST.inmap (_,_ []) x!}
   parse (con c {prf}) = con c {prf}
   parse (n₁ · n₂) = parse n₁ · parse n₂
   parse (Λ n) = Λ (parse n)
 
   -- Variable substitution
   

   -- Simultaneous (modal) substitution
   SSubst : MCtx → MCtx → Set 
   SSubst Δ Δ' = LIST.All (λ mty → Term Δ' mty) Δ

   -- postulate ssubst : ∀{Δ Δ' Γ A} → SSubst Δ Δ' → Term Δ Γ A → Term Δ' Γ A

   