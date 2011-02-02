-- STLC with pairs experimentation
-- Rob Simmons, Salil Joshi, Frank Pfenning

open import Prelude
open import Types

module UserLanguage where

module USER (sig : String → Maybe Type) where
   infixl 5 _·_
   data Term (Δ : Ctx) (Γ : Ctx) : Type → Set where
      var : ∀{A} (x : A ∈ Γ) → Term Δ Γ A
      mvar : ∀{A} (x : A ∈ Δ) → Term Δ Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Term Δ Γ (valOf (sig c) {ch})
      _·_ : ∀{A B} (n₁ : Term Δ Γ (A ⊃ B)) (n₂ : Term Δ Γ A) → Term Δ Γ B
      Λ : ∀{A B} (n : Term Δ (A :: Γ) B) → Term Δ Γ (A ⊃ B)

   -- Simultaneous (modal) substitution
   SSubst : Ctx → Ctx → Set 
   SSubst Δ Δ' = LIST.All (Term Δ' []) Δ

   postulate ssubst : ∀{Δ Δ' Γ A} → SSubst Δ Δ' → Term Δ Γ A → Term Δ' Γ A
