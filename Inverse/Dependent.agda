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
   revappend : Ctx → Ctx → Ctx  
   revappend [] γ = γ
   revappend (a :: δ) γ = revappend δ (a :: γ)

   _//_ : ∀{γ δ} → DCtx γ → PCtx γ δ → DCtx (revappend δ γ)
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
   substΔ N (A , Δ) = substA N A , wkΔ {! sub-exch!} {!!}

module DEPENDENT 
  (sig : String → Maybe Class
   ; Sig : (c : String) → Maybe (TYPES.SigItem sig c)) where

   open MINIMAL sig
   open TYPES sig

   mutual 
      data _⊢_∶_∶subst {γ : _} (Γ : DCtx γ) : ∀{δ}
            → Subst γ δ
            → PCtx γ δ → Set where
         ⟨⟩ : Γ ⊢ ⟨⟩ ∶ ⟨⟩ ∶subst
         _,_ : ∀{a δ}
            {N : Term γ a}
            {A : Type γ a}
            {σ : Subst γ δ}
            {Δ : PCtx (a :: γ) δ}
            → Γ ⊢ N ∶ A ∶type
            → Γ ⊢ σ ∶ {!substΔ N Δ!} ∶subst
            → Γ ⊢ N , σ ∶ A , Δ ∶subst

      data _⊢_∶_∶type {γ : _} (Γ : DCtx γ) : ∀{a} 
            → Term γ a
            → Type γ a → Set where
         var : ∀{δ a c q}
            {Δ : PCtx γ δ}
            {x : a ∈ γ}
            {K : Skel δ a (con (atm q))}
            {ch : Check (isSome (Sig c))}
            {σ : Subst γ δ}
            → Γ / Δ ⊩ K ∶ (lookΓ Γ x) > {!!}
            → Γ ⊢ var x · K [ σ ] ∶ {!!} ∶type 
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

      data _/_⊩_∶_>_ {γ : _} : ∀{δ a c} 
            → DCtx γ 
            → PCtx γ δ 
            → Skel δ a c 
            → Type γ a 
            → Type (a :: (revappend δ γ)) c → Set where
         ⟨⟩ : ∀{a} 
            {Γ : DCtx γ}
            {A : Type γ a} 
            → Γ / ⟨⟩ ⊩ ⟨⟩ ∶ A > wkA sub-wken A
         ·_ : ∀{a δ b c} 
            {Γ : DCtx γ}
            {A : Type γ a}
            {Δ : PCtx (a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type (a :: (revappend δ γ)) c}
            → (Γ , A) / Δ ⊩ K ∶ B > {!C!}
            → Γ / (A , Δ) ⊩ (· K) ∶ Π A B > {!!}
         π₁ : ∀{a δ b c}
            {Γ : DCtx γ}
            {A : Type γ a}
            {Δ : PCtx γ δ}
            {K : Skel δ a c}
            {B : Type (a :: γ) b}
            {C : Type γ c}
            → Γ / Δ ⊩ K ∶ A > {!C!}
            → Γ / Δ ⊩ (π₁ K) ∶ Σ A B > {!!}
         π₂ : ∀{a δ b c}
            {Γ : DCtx γ}
            {A : Type γ a}
            {Δ : PCtx (a :: γ) δ}
            {K : Skel δ b c}
            {B : Type (a :: γ) b}
            {C : Type γ c}
            → (Γ , A) / Δ ⊩ K ∶ B > {!!} 
            → Γ / {!Δ!} ⊩ (π₂ K) ∶ Σ A B > {!!}


      {- π₁ : ∀{a δ b c} 
         {Γ : DCtx γ}
         {A : Type γ a}
         {Δ : PCtx (a :: γ) δ}
         {K : Skel δ b c}
         {B : Type (a :: γ) b}
         {C : Type (a :: (revappend δ γ)) c}
         (K : (Γ , A) / Δ ⊩ K ∶ B > {!C!})
         → Γ / (A , {!!}) ⊩ (· {!!}) ∶ Π A B > {!!} -}