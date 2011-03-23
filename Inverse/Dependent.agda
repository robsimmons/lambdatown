open import Prelude hiding (Σ)
open import Inverse.Minimal

module Inverse.Dependent where

open LIST.SET public

module TYPES (sig : String → Maybe Class) where
   
   open MINIMAL sig

   data Type (γ : Ctx) : Class → Set where
      _·_[_] : ∀{δ} (c : String) {ch : Check (isSome (sig c))}
         (K : Skel δ (valOf (sig c) {ch}) (con typ))
         (σ : Subst γ δ)
         → Type γ (con (atm c))
      Π : ∀{a b}
         (A : Type γ a)
         (B : Type (a :: γ) b) 
         → Type γ (a ⊃ b)  
      Σ : ∀{a b}
         (A : Type γ a)
         (B : Type (a :: γ) b)
         → Type γ (a ∧ b)

   data Kind (γ : Ctx) : Class → Set where
      typ : Kind γ (con typ)
      Π : ∀{a b}
         (A : Type γ a)
         (B : Kind (a :: γ) b)
         → Kind γ (a ⊃ b)

   data DCtx : Ctx → Set where
      ⟨⟩ : DCtx []
      _,_ : ∀{γ a}
         (Γ : DCtx γ) 
         (A : Type γ a) 
         → DCtx (a :: γ)

   data PCtx (γ : Ctx) : Ctx → Set where
      ⟨⟩ : PCtx γ []
      _,_ : ∀{a δ}
          (A : Type γ a)
          (Δ : PCtx (a :: γ) δ)
          → PCtx γ (a :: δ)

   _//_ : ∀{γ δ} → DCtx γ → PCtx γ δ → DCtx (δ ⟩⟩ γ)
   Γ // ⟨⟩ = Γ
   Γ // (A , Δ) = (Γ , A) // Δ

   data SigItem (c : String) : Set where
      con : {ch : Check (isSome (sig c))} 
         (A : Type [] (valOf (sig c) {ch}))
         → SigItem c
      atm : {ch : Check (isSome (sig c))} 
         (K : Kind [] (valOf (sig c) {ch}))
         → SigItem c

   wkA : ∀{γ γ' a} → γ ⊆ γ' → Type γ a → Type γ' a
   wkA θ (c · K [ σ ]) = c · K [ wkσ θ σ ]
   wkA θ (Π A B) = Π (wkA θ A) (wkA (sub-cons-congr θ) B)
   wkA θ (Σ A B) = Σ (wkA θ A) (wkA (sub-cons-congr θ) B)

   wkΔ : ∀{γ γ' δ} → γ ⊆ γ' → PCtx γ δ → PCtx γ' δ
   wkΔ θ ⟨⟩ = ⟨⟩
   wkΔ θ (A , Δ) = wkA θ A , wkΔ (sub-cons-congr θ) Δ

   lookΓ : ∀{γ a} → DCtx γ → a ∈ γ → Type γ a
   lookΓ ⟨⟩ ()
   lookΓ (Γ , A) Z = wkA sub-wken A
   lookΓ (Γ , A) (S x) = wkA sub-wken (lookΓ Γ x)

   subA : ∀{γ a c} → Term γ a → Type (a :: γ) c → Type γ c
   subA M (c · K [ σ ]) = c · K [ subσ M (→mσ σ) ]
   subA M (Π A B) = Π (subA M A) (subA (wk sub-wken M) (wkA sub-exch B))
   subA M (Σ A B) = Σ (subA M A) (subA (wk sub-wken M) (wkA sub-exch B))

   subΔ : ∀{γ a δ} → Term γ a → PCtx (a :: γ) δ → PCtx γ δ
   subΔ M ⟨⟩ = ⟨⟩
   subΔ M (A , Δ) = subA M A , subΔ (wk sub-wken M) (wkΔ sub-exch Δ)

   ssubA : ∀{δ γ a} → Subst γ δ → Type (δ ⟩⟩ γ) a → Type γ a
   ssubA τ (c · K [ σ' ])  = {!!}
   ssubA {δ} τ (Π A B) = 
      Π (ssubA τ A) (ssubA (wkσ sub-wken τ) (wkA (sub-ra-exch {δ}) B))
   ssubA {δ} τ (Σ A B) = 
      Σ (ssubA τ A) (ssubA (wkσ sub-wken τ) (wkA (sub-ra-exch {δ}) B))

module DEPENDENT 
  (sig : String → Maybe Class
   ; Sig : (c : String) → Maybe (TYPES.SigItem sig c)) where

   open MINIMAL sig
   open TYPES sig

   mutual 
      data _⊢_∶_∶ctx {γ : _} (Γ : DCtx γ) : ∀{δ}
            → Subst γ δ
            → PCtx γ δ → Set where
         ⟨⟩ : Γ ⊢ ⟨⟩ ∶ ⟨⟩ ∶ctx
         _,_ : ∀{a δ}
            {N : Term γ a}
            {A : Type γ a}
            {σ : Subst γ δ}
            {Δ : PCtx (a :: γ) δ}
            → Γ ⊢ N ∶ A ∶type
            → Γ ⊢ σ ∶ subΔ N Δ ∶ctx
            → Γ ⊢ N , σ ∶ A , Δ ∶ctx

      data _⊢_∶_∶type {γ : _} (Γ : DCtx γ) : ∀{a} 
            → Term γ a
            → Type γ a → Set where
         var : ∀{δ a c q}
            {Δ : PCtx (a :: γ) δ}
            {x : a ∈ γ}
            {K : Skel δ a (con (atm q))}
            {ch : Check (isSome (Sig c))}
            {C : Type (δ ⟩⟩ (a :: γ)) (con (atm q))}
            {σ : Subst γ δ}
            -- → Γ / Δ ⊩ K ∶ (lookΓ Γ x) > A
            → Γ / lookΓ Γ x / Δ ⊩ K ∶ C
            → Γ ⊢ σ ∶ subΔ (η' x) Δ ∶ctx
            → Γ ⊢ var x · K [ σ ] ∶ ssubA (η' x , σ) C ∶type
         Λ : ∀{a b}
            {A : Type γ a}
            {B : Type (a :: γ) b}
            {N : Term (a :: γ) b}
            → (Γ , A) ⊢ N ∶ B ∶type 
            → Γ ⊢ Λ N ∶ Π A B ∶type 
         _,_ : ∀{a b} 
            {A : Type γ a}
            {B : Type (a :: γ) b} 
            {N₁ : Term γ a}
            {N₂ : Term γ b}
            → Γ ⊢ N₁ ∶ A ∶type
            → Γ ⊢ N₂ ∶ subA N₁ B ∶type
            → Γ ⊢ N₁ , N₂ ∶ Σ A B ∶type

      data _/_/_⊩_∶_ {γ : _} (Γ : DCtx γ) : ∀{δ a c}
            → Type γ a
            → PCtx (a :: γ) δ 
            → Skel δ a c
            → Type (δ ⟩⟩ (a :: γ)) c → Set where 
         ⟨⟩ : ∀{a} 
            {A : Type γ a} 
            → Γ / A / ⟨⟩ ⊩ ⟨⟩ ∶ wkA sub-wken A
         ·_ : ∀{a δ b c} 
            {A : Type γ a}
            {Δ : PCtx (b :: a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type (δ ⟩⟩ (b :: a :: γ)) c}
            → (Γ , A) / B / Δ ⊩ K ∶ C
            → Γ / Π A B / wkA sub-wken A , {! ⊃LΔ Δ!} ⊩ (· K) ∶ {! ⊃LA C!}
         π₁ : ∀{a δ b c}
            {A : Type γ a}
            {Δ : PCtx (a :: γ) δ}
            {K : Skel δ a c}
            {B : Type (a :: γ) b}
            {C : Type (δ ⟩⟩ (a :: γ)) c}
            → Γ / A / Δ ⊩ K ∶ C
            → Γ / Σ A B / {! ∧L₁Δ Δ!} ⊩ (π₁ K) ∶ {! ∧L₁A C!}
         π₂ : ∀{a δ b c}
            {A : Type γ a}
            {Δ : PCtx (b :: a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type (δ ⟩⟩ (b :: a :: γ)) c}
            → (Γ , A) / B / Δ ⊩ K ∶ C 
            → Γ / Σ A B / {! ∧LΔ Δ!} ⊩ (π₂ K) ∶ {! ∧LA C!} 

   mutual 
      red-ok : ∀{γ a δ c}
         {Γ : DCtx γ}
         {N : Term γ a}
         {A : Type γ a}
         {Δ : PCtx (a :: γ) δ}
         {K : Skel δ a c}
         {C : Type (δ ⟩⟩ (a :: γ)) c}
         {σ : Subst γ δ}
         → Γ ⊢ N ∶ A ∶type
         → Γ / A / Δ ⊩ K ∶ C
         → Γ ⊢ σ ∶ subΔ N Δ ∶ctx
         → Γ ⊢ N • K [ σ ] ∶ ssubA (N , σ) C ∶type 
      red-ok DM ⟨⟩ ⟨⟩ = {! !} -- weakening, substituting does nothing
      red-ok (Λ DM) (· DK) (DN , Dσ) = {!!}
      red-ok (DM₁ , DM₂) (π₁ DK) Dσ = red-ok DM₁ DK {!Dσ!}
      red-ok (DM₁ , DM₂) (π₂ DK) Dσ = red-ok DM₂ {!!} {!!} 

{-
      data _/_⊩_∶_>_ {γ : _} : ∀{δ a c} 
            → DCtx γ 
            → PCtx γ δ 
            → Skel δ a c 
            → Type γ a 
            → Type (a :: (δ ⟩⟨⟩ γ)) c → Set where
         ·_ : ∀{a δ b c} 
            {Γ : DCtx γ}
            {A : Type γ a}
            {Δ : PCtx (a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type (b :: δ ⟩⟨⟩ (a :: γ)) c}
            → (Γ , A) / Δ ⊩ K ∶ B > C
            → Γ / (A , Δ) ⊩ (· K) ∶ Π A B > {! ⊃L η C!}
         π₁ : ∀{a δ b c}
            {Γ : DCtx γ}
            {A : Type γ a}
            {Δ : PCtx γ δ}
            {K : Skel δ a c}
            {B : Type (a :: γ) b}
            {C : Type (a :: δ ⟩⟨⟩ γ) c}
            → Γ / Δ ⊩ K ∶ A > C
            → Γ / Δ ⊩ (π₁ K) ∶ Σ A B > {! ∧L₁ C!}
         π₂ : ∀{a δ b c}
            {Γ : DCtx γ}
            {A : Type γ a}
            {Δ : PCtx (a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type (b :: δ ⟩⟨⟩ (a :: γ)) c}
            → (Γ , A) / Δ ⊩ K ∶ B > C 
            → Γ / {! Δ!} ⊩ (π₂ K) ∶ Σ A B > {! ∧L C!} -- interesting, pos rule
-}

