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

   -- XXX add to stdlib
   _⟩⟨⟩_ : Ctx → Ctx → Ctx  
   [] ⟩⟨⟩ γ = γ
   (a :: δ) ⟩⟨⟩ γ = δ ⟩⟨⟩ (a :: γ)

   sub-⟩⟨⟩ : ∀{δ γ} → γ ⊆ (δ ⟩⟨⟩ γ)
   sub-⟩⟨⟩ x = {!!}

   sub-exch-ra : ∀{δ a γ} → (δ ⟩⟨⟩ (a :: γ)) ⊆ (a :: δ ⟩⟨⟩ γ)
   sub-exch-ra x = {!!}

   sub-ra-exch : ∀{δ a γ} → (a :: δ ⟩⟨⟩ γ) ⊆ (δ ⟩⟨⟩ (a :: γ))
   sub-ra-exch x = {!!}

   _//_ : ∀{γ δ} → DCtx γ → PCtx γ δ → DCtx (δ ⟩⟨⟩ γ)
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
   wkA = {!!}

   wkΔ : ∀{γ γ' δ} → γ ⊆ γ' → PCtx γ δ → PCtx γ' δ
   wkΔ = {!!}

   lookΓ : ∀{γ a} → DCtx γ → a ∈ γ → Type γ a
   lookΓ ⟨⟩ ()
   lookΓ (Γ , A) Z = wkA sub-wken A
   lookΓ (Γ , A) (S x) = wkA sub-wken (lookΓ Γ x)

   substA : ∀{γ a c} → Term γ a → Type (a :: γ) c → Type γ c
   substA M (c · K [ σ ]) = c · K [ substσ M (→mσ σ) ]
   substA M (Π A B) = Π (substA M A) (substA (wk sub-wken M) (wkA sub-exch B))
   substA M (Σ A B) = Σ (substA M A) (substA (wk sub-wken M) (wkA sub-exch B))

   substΔ : ∀{γ a δ} → Term γ a → PCtx (a :: γ) δ → PCtx γ δ
   substΔ N ⟨⟩ = ⟨⟩
   substΔ N (A , Δ) = substA N A , substΔ (wk sub-wken N) (wkΔ sub-exch Δ)

   subA : ∀{δ γ a} → Type (δ ⟩⟨⟩ γ) a → Subst γ δ → Type γ a
   subA (c · K [ σ' ]) σ  = {!!}
   subA {δ} (Π A B) σ = 
      Π (subA A σ) (subA (wkA (sub-ra-exch {δ}) B) (wkσ sub-wken σ))
   subA {δ} (Σ A B) σ = 
      Σ (subA A σ) (subA (wkA (sub-ra-exch {δ}) B) (wkσ sub-wken σ))

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
            → Γ ⊢ σ ∶ substΔ N Δ ∶ctx
            → Γ ⊢ N , σ ∶ A , Δ ∶ctx

      data _⊢_∶_∶type {γ : _} (Γ : DCtx γ) : ∀{a} 
            → Term γ a
            → Type γ a → Set where
         var : ∀{δ a c q}
            {Δ : PCtx (a :: γ) δ}
            {x : a ∈ γ}
            {K : Skel δ a (con (atm q))}
            {ch : Check (isSome (Sig c))}
            {C : Type (δ ⟩⟨⟩ (a :: γ)) (con (atm q))}
            {σ : Subst γ δ}
            -- → Γ / Δ ⊩ K ∶ (lookΓ Γ x) > A
            → Γ / lookΓ Γ x / Δ ⊩ K ∶ C
            → Γ ⊢ σ ∶ substΔ (η' x) Δ ∶ctx
            → Γ ⊢ var x · K [ σ ] ∶ subA C (η' x , σ) ∶type
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
            → Γ ⊢ N₂ ∶ substA N₁ B ∶type
            → Γ ⊢ N₁ , N₂ ∶ Σ A B ∶type

      data _/_/_⊩_∶_ {γ : _} (Γ : DCtx γ) : ∀{δ a c}
            → Type γ a
            → PCtx (a :: γ) δ 
            → Skel δ a c
            → Type (δ ⟩⟨⟩ (a :: γ)) c → Set where 
         ⟨⟩ : ∀{a} 
            {A : Type γ a} 
            → Γ / A / ⟨⟩ ⊩ ⟨⟩ ∶ wkA sub-wken A
         ·_ : ∀{a δ b c} 
            {A : Type γ a}
            {Δ : PCtx (b :: a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type (δ ⟩⟨⟩ (b :: a :: γ)) c}
            → (Γ , A) / B / Δ ⊩ K ∶ C
            → Γ / Π A B / wkA sub-wken A , {! ⊃LΔ Δ!} ⊩ (· K) ∶ {! ⊃LA C!}
         π₁ : ∀{a δ b c}
            {A : Type γ a}
            {Δ : PCtx (a :: γ) δ}
            {K : Skel δ a c}
            {B : Type (a :: γ) b}
            {C : Type (δ ⟩⟨⟩ (a :: γ)) c}
            → Γ / A / Δ ⊩ K ∶ C
            → Γ / Σ A B / {! ∧L₁Δ Δ!} ⊩ (π₁ K) ∶ {! ∧L₁A C!}
         π₂ : ∀{a δ b c}
            {A : Type γ a}
            {Δ : PCtx (b :: a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type (δ ⟩⟨⟩ (b :: a :: γ)) c}
            → (Γ , A) / B / Δ ⊩ K ∶ C 
            → Γ / Σ A B / {! ∧LΔ Δ!} ⊩ (π₂ K) ∶ {! ∧LA C!} 

   mutual 
      red-ok : ∀{γ a δ c}
         {Γ : DCtx γ}
         {N : Term γ a}
         {A : Type γ a}
         {Δ : PCtx (a :: γ) δ}
         {K : Skel δ a c}
         {C : Type (δ ⟩⟨⟩ (a :: γ)) c}
         {σ : Subst γ δ}
         → Γ ⊢ N ∶ A ∶type
         → Γ / A / Δ ⊩ K ∶ C
         → Γ ⊢ σ ∶ substΔ N Δ ∶ctx
         → Γ ⊢ red N K σ ∶ subA C (N , σ) ∶type 
      red-ok DM ⟨⟩ ⟨⟩ = {! !} -- weakening, substituting does nothing
      red-ok (Λ DM) (· DK) (DN , Dσ) = {!!}
      red-ok (DM₁ , DM₂) (π₁ DK) Dσ = red-ok DM₁ DK {!Dσ!}
      red-ok (DM₁ , DM₂) (π₂ DK) Dσ = red-ok DM₂ {! -- DK --!} {!!} 

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

