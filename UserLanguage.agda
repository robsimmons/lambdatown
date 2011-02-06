-- STLC with pairs experimentation
-- Rob Simmons, Salil Joshi, Frank Pfenning

open import Prelude
open import Types

module UserLanguage where

module USER (sig : Sig) where
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

module USER-EX where
   sig : Sig
   sig "lam" = Just ((con "exp" ⊃ con "exp") ⊃ con "exp")
   sig "app" = Just (con "exp" ⊃ con "exp" ⊃ con "exp")
   sig "z" = Just (con "exp")
   sig "s" = Just (con "exp" ⊃ con "exp")
   sig _ = Nothing

   open USER sig 
   
   -- Combinators
   combI : Term [] [] (con "exp")
   combI = con "lam" · Λ (var Z)
   combK : Term [] [] (con "exp")
   combK = con "lam" · Λ (con "lam" · Λ (var (S Z)))
   combS : Term [] [] (con "exp")
   combS = 
      con "lam" · Λ (con "lam" · Λ (con "lam" · Λ 
       (con "app" · 
         (con "app" · var (S (S Z)) · var Z) · 
         (con "app" · var (S Z) · var Z))))

   -- Unification problem that requires pruning
   -- F ← λx. λy. F' x
   -- E ← s (F' x) 
   Δ₁ = (con "exp" ⊃ con "exp") :: (con "exp" ⊃ con "exp" ⊃ con "exp") :: []
   Γ₁ = con "exp" :: con "exp" :: (con "exp" ∧ con "exp") :: []
   prune1 : Term Δ₁ Γ₁ (con "exp") -- E x
   prune1 = mvar Z · var Z
   prune2 : Term Δ₁ Γ₁ (con "exp") -- s (F x y)
   prune2 = con "s" · (mvar (S Z) · var Z · var (S Z))

   


