open import Prelude hiding (Σ)
open import Inverse.Minimal

module Inverse.DependentPi where

open LIST.SET public

open import Lib.List.In

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
      _∧_ : ∀{a b}
         (A : Type γ a)
         (B : Type γ b)
         → Type γ (a ∧ b)

   wkA : ∀{γ γ' a} → γ ⊆ γ' → Type γ a → Type γ' a
   wkA θ (c · K [ σ ]) = c · K [ wkσ θ σ ]
   wkA θ (Π A B) = Π (wkA θ A) (wkA (sub-cons-congr θ) B)
   wkA θ (A ∧ B) = (wkA θ A) ∧ (wkA θ B)

   subA : ∀{γ a c} → Term γ a → Type (a :: γ) c → Type γ c
   subA M (c · K [ σ ]) = c · K [ subσ M (→mσ σ) ]
   subA M (Π A B) = Π (subA M A) (subA (wk sub-wken M) (wkA sub-exch B))
   subA M (A ∧ B) = (subA M A) ∧ (subA M B)

   ssubA : ∀{δ γ a} → Subst γ δ → Type (δ ⟩⟩ γ) a → Type γ a
   ssubA τ (c · K [ σ' ])  = c · K [ ssubσ τ (→mσ σ') ]
   ssubA {δ} τ (Π A B) = 
      Π (ssubA τ A) (ssubA (wkσ sub-wken τ) (wkA (sub-ra-exch {δ}) B))
   ssubA {δ} τ (A ∧ B) = (ssubA τ A) ∧ (ssubA τ B)

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

   wkΔ : ∀{γ γ' δ} → γ ⊆ γ' → PCtx γ δ → PCtx γ' δ
   wkΔ θ ⟨⟩ = ⟨⟩
   wkΔ θ (A , Δ) = wkA θ A , wkΔ (sub-cons-congr θ) Δ

   subΔ : ∀{γ a δ} → Term γ a → PCtx (a :: γ) δ → PCtx γ δ
   subΔ M ⟨⟩ = ⟨⟩
   subΔ M (A , Δ) = subA M A , subΔ (wk sub-wken M) (wkΔ sub-exch Δ)


   data SigItem : Set where
      con : (c : String) {ch : Check (isSome (sig c))} 
         (A : Type [] (valOf (sig c) {ch}))
         → SigItem
      atm : (c : String) {ch : Check (isSome (sig c))} 
         (K : Kind [] (valOf (sig c) {ch}))
         → SigItem


   Γ→ : ∀{γ a} → a ∈ γ → DCtx γ → Type γ a
   Γ→ Z (Γ , A) = wkA sub-wken A
   Γ→ (S x) (Γ , A) = wkA sub-wken (Γ→ x Γ)




module DEPENDENT
  (sig : String → Maybe Class
   ; Sig : List (TYPES.SigItem sig)) where

   open MINIMAL sig
   open TYPES sig

   data _⊢_∶_∶head {γ : _} (Γ : DCtx γ) : ∀{a} 
         → Head γ a 
         → Type γ a → Set where
      var : ∀{a}
         {x : a ∈ γ}
         → Γ ⊢ var x ∶ Γ→ x Γ ∶head
      con : ∀{c ch}
         {A : Type [] (valOf (sig c) {ch})}
         → con c A ∈ Sig
         → Γ ⊢ con c ∶ wkA (λ ()) A ∶head

   data _/_/_⊩_∶_ {γ : _} (Γ : DCtx γ) : ∀{δ a c}
         → Type γ a
         → PCtx γ δ 
         → Skel δ a c
         → Type (δ ⟩⟩ γ) c → Set where 
      ⟨⟩ : ∀{a}
         {A : Type γ a}
         → Γ / A / ⟨⟩ ⊩ ⟨⟩ ∶ A
      ·_ : ∀{a δ b c}
         {A : Type γ a}
         {Δ : PCtx (a :: γ) δ}
         {K : Skel δ b c}
         {B : Type (a :: γ) b}
         {C : Type (δ ⟩⟩ (a :: γ)) c}
         → (Γ , A) / B / Δ ⊩ K ∶ C
         → Γ / Π A B / A , Δ ⊩ (· K) ∶ C
      π₁ : ∀{a δ b c} 
         {A : Type γ a}
         {B : Type γ b}
         {Δ : PCtx γ δ}
         {K : Skel δ a c}
         {C : Type (δ ⟩⟩ γ) c}
         → Γ / A / Δ ⊩ K ∶ C
         → Γ / A ∧ B / Δ ⊩ π₁ K ∶ C
      π₂ : ∀{a δ b c} 
         {A : Type γ a}
         {B : Type γ b}
         {Δ : PCtx γ δ}
         {K : Skel δ b c}
         {C : Type (δ ⟩⟩ γ) c}
         → Γ / B / Δ ⊩ K ∶ C
         → Γ / A ∧ B / Δ ⊩ π₂ K ∶ C

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
         _·_[_] : ∀{δ a q}
            {Δ : PCtx γ δ}
            {A : Type γ a}
            {h : Head γ a}
            {K : Skel δ a (con (atm q))}
            {C : Type (δ ⟩⟩ γ) (con (atm q))}
            {σ : Subst γ δ}
            → Γ ⊢ h ∶ A ∶head
            → Γ / A / Δ ⊩ K ∶ C
            → Γ ⊢ σ ∶ Δ ∶ctx
            → Γ ⊢ h · K [ σ ] ∶ ssubA σ C ∶type
         Λ : ∀{a b}
            {A : Type γ a}
            {B : Type (a :: γ) b}
            {N : Term (a :: γ) b}
            → (Γ , A) ⊢ N ∶ B ∶type
            → Γ ⊢ Λ N ∶ Π A B ∶type
         _,_ : ∀{a b}
            {A : Type γ a}
            {B : Type γ b}
            {N₁ : Term γ a}
            {N₂ : Term γ b}
            → Γ ⊢ N₁ ∶ A ∶type
            → Γ ⊢ N₂ ∶ B ∶type
            → Γ ⊢ N₁ , N₂ ∶ A ∧ B ∶type

   mutual
      typedsubN : ∀{γ n a c}
         {Γ : DCtx γ}
         {A : Type γ a}
         {C : Type (a :: γ) c}
         {M : Term γ a}
         {N : Term' (a :: γ) n c} 
         → Γ ⊢ M ∶ A ∶type
         → (Γ , A) ⊢ m→ N ∶ C ∶type
         → Γ ⊢ subN M N ∶ subA M C ∶type

      typedsubN {N = N₁ , N₂} D (E₁ , E₂) = typedsubN D E₁ , typedsubN D E₂

      typedsubN {c = c₁ ⊃ c₂} {A = A} {Π C₁ C₂} {M} {Λ N} D (Λ E) = 
         Λ (typedsubN {c = c₂} {A = wkA sub-wken A} {wkA sub-exch C₂} {wk sub-wken M} {wk' sub-exch N} {! weaken D!} {! E!})

      typedsubN {N = var Z · K [ σ ]} D (var · EK [ Eσ ]) = 
         typedred D {! !} {! Eσ!}

      typedsubN {N = var (S x) · K [ σ ]} D (var · EK [ Eσ ]) = {!  !}

      typedsubN {N = con c · K [ σ ]} D (con cx · EK [ Eσ ]) = {!  !}

  
      typedsubσ : ∀{γ s a δ}
         {Γ : DCtx γ}
         {M : Term γ a}
         {A : Type γ a}
         {σ : Subst' (a :: γ) s δ}
         {Δ : PCtx (a :: γ) δ}
         → Γ ⊢ M ∶ A ∶type
         → (Γ , A) ⊢ mσ→ σ ∶ Δ ∶ctx
         → Γ ⊢ subσ M σ ∶ subΔ M Δ ∶ctx

      typedsubσ {σ = ⟨⟩} D ⟨⟩ = ⟨⟩

      typedsubσ {σ = N , σ} D (EN , Eσ) = 
         typedsubN D EN , {! ? need to commute something!}
      


      typedred : ∀{δ γ a c}
         {Γ : DCtx γ}
         {Δ : PCtx γ δ}
         {A : Type γ a}
         {M : Term γ a}
         {K : Skel δ a c}
         {σ : Subst γ δ}
         {C : Type (δ ⟩⟩ γ) c}
         → Γ ⊢ M ∶ A ∶type
         → Γ / A / Δ ⊩ K ∶ C 
         → Γ ⊢ σ ∶ Δ ∶ctx
         → Γ ⊢ M • K [ σ ] ∶ ssubA σ C ∶type
      typedred DM ⟨⟩ ⟨⟩ = {! DM -- ssubA ⟨⟩ C ≡ C!}
      typedred {a :: δ} {Γ = Γ} {A , Δ} {Π .A B} {Λ M} {· K} {N , σ} {C} (Λ DM) (· DK) (DN , Dσ) = 
         {!  Q!} -- (typedsubN DN DM) {! weaken E!} {!F₂!}
       -- Prove = C [ N / x , σ ] ≡ (C [ x / x ]) [ σ [ N / x] ]
        where 
         Q = typedred {Γ = Γ} {subΔ N Δ} {subA N B} {subN N (→m M)} {K} {σ} {wkA {!!} (subA N (ssubA (wkσ sub-wken σ) C))} (typedsubN DN DM) {!DK!} {!!}

         R = typedred {Γ = Γ} {subΔ N Δ} {subA N B} {subN N (→m M)} {K} {σ} {{!C!}} (typedsubN DN DM) {!DK!} {!!}
 
      typedred (DM₁ , DM₂) (π₁ DK) Dσ = typedred DM₁ DK Dσ
      typedred (DM₁ , DM₂) (π₂ DK) Dσ = typedred DM₂ DK Dσ