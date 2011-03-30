open import Prelude hiding (Σ)
open import Inverse.Minimal2

module Inverse.DependentPi2 where

open LIST.SET hiding (refl)

-- open import Lib.List.In 

{- PART 1: TYPES, KINDS, CONTEXTS -}

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

   sbA : ∀{δ γ a} (γ' : Ctx)
      → Subst γ δ 
      → Type (γ' ++ δ ⟩⟩ γ) a 
      → Type (γ' ++ γ) a
   sbA γ' τ (c · K [ σ ]) = c · K [ sbσ γ' τ σ ]
   sbA {δ} γ' τ (Π A B) = Π (sbA γ' τ A) (sbA (_ :: γ') τ B)
   sbA {δ} γ' τ (A ∧ B) = (sbA γ' τ A) ∧ (sbA γ' τ B)

   subA : ∀{δ γ a} → Subst γ δ → Type (δ ⟩⟩ γ) a → Type γ a
   subA = sbA []


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

   sbΔ : ∀{δ γ δ'} (γ' : Ctx) 
      → Subst γ δ 
      → PCtx (γ' ++ (δ ⟩⟩ γ)) δ' 
      → PCtx (γ' ++ γ) δ'
   sbΔ γ' τ ⟨⟩ = ⟨⟩
   sbΔ γ' τ (A , Δ) = sbA γ' τ A , sbΔ (_ :: γ') τ Δ

   subΔ : ∀{δ γ δ'} → Subst γ δ → PCtx (δ ⟩⟩ γ) δ' → PCtx γ δ'
   subΔ = sbΔ []

   _,⟨⟨_ : ∀{γ δ} → DCtx γ → PCtx γ δ → DCtx (δ ⟩⟩ γ)
   Γ ,⟨⟨ ⟨⟩ = Γ
   Γ ,⟨⟨ (A , Δ) = (Γ , A) ,⟨⟨ Δ



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

{- PART 2: DEPENDENT TYPES -}

module DEPENDENT
  (sig : String → Maybe Class
   ; Sig : List (TYPES.SigItem sig)) where

   open MINIMAL sig
   open TYPES sig

   data _⊢_∶_∶head {γ : _} (Γ : DCtx γ) : ∀{a} 
         → Head γ a 
         → Type γ a → Set where
      var : ∀{a}
         (x : a ∈ γ)
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
            → Γ ⊢ σ ∶ subΔ (N , ⟨⟩) Δ ∶ctx
            → Γ ⊢ N , σ ∶ A , Δ ∶ctx

      data _⊢_∶_∶type {γ : _} (Γ : DCtx γ) : ∀{a} 
            → Term γ a
            → Type γ a → Set where
         _·_[_]_ : ∀{δ a q}
            {Δ : PCtx γ δ}
            {A : Type γ a}
            {h : Head γ a}
            {K : Skel δ a (con (atm q))}
            {C : Type (δ ⟩⟩ γ) (con (atm q))}
            {C' : Type γ (con (atm q))}
            {σ : Subst γ δ}
            → Γ ⊢ h ∶ A ∶head
            → Γ / A / Δ ⊩ K ∶ C
            → Γ ⊢ σ ∶ Δ ∶ctx
            → C' ≡ subA σ C
            → Γ ⊢ · h · K [ σ ] ∶ C' ∶type
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


   data HCtx (γ : Ctx) : Ctx → Set where 
      ⟨⟩ : HCtx γ []
      _,_ : ∀{γ' a} 
         (Γ : HCtx γ γ') 
         (A : Type (γ' ++ γ) a) 
         → HCtx γ (a :: γ')
  
   _,++_ : ∀{γ γ'} → DCtx γ → HCtx γ γ' → DCtx (γ' ++ γ)
   Γ ,++ ⟨⟩ = Γ
   Γ ,++ (Γ' , A) = (Γ ,++ Γ') , A

   sbΓ : ∀{δ γ} (γ' : Ctx)
      → Subst γ δ 
      → HCtx (δ ⟩⟩ γ) γ'
      → HCtx γ γ'
   sbΓ [] τ ⟨⟩ = ⟨⟩
   sbΓ (_ :: γ') τ (Γ , A) = sbΓ γ' τ Γ , sbA γ' τ A

   mutual
      typedsubN : ∀{γ c δ} {γ' : Ctx}
         {Γ : DCtx γ}
         (Γ' : HCtx (δ ⟩⟩ γ) γ')
         {Δ : PCtx γ δ}
         {C : Type (γ' ++ δ ⟩⟩ γ) c}
         {τ : Subst γ δ}
         {N : Term (γ' ++ δ ⟩⟩ γ) c}
         → Γ ⊢ τ ∶ Δ ∶ctx
         → ((Γ ,⟨⟨ Δ) ,++ Γ') ⊢ N ∶ C ∶type
         → (Γ ,++ sbΓ γ' τ Γ') ⊢ sbN γ' τ N ∶ sbA γ' τ C ∶type

      typedsubN {γ' = γ'} Γ' {τ = τ} D (var x · EK [ Eσ ] Refl) with Γ? γ' τ x 
      ... | Inl y = {! -- I am hereditary reduction -- !}
      ... | Inr y = var y · {! EK, with stuff!} [ typedsubσ Γ' D Eσ Refl ] {!!}

      typedsubN Γ' D (con c · EK [ Eσ ] Refl) = 
         con c · {! EK, with stuff!} [ typedsubσ Γ' D Eσ Refl ] {!!}

      typedsubN Γ' D (Λ E) = Λ (typedsubN (Γ' , _) D E)

      typedsubN Γ' D (E₁ , E₂) = typedsubN Γ' D E₁ , typedsubN Γ' D E₂
 

      typedsubσ : ∀{γ δ δ'} {γ' : Ctx}
         {Γ : DCtx γ}
         (Γ' : HCtx (δ ⟩⟩ γ) γ')
         {Δ : PCtx γ δ}
         {Δ' : PCtx (γ' ++ δ ⟩⟩ γ) δ'}
         {τ : Subst γ δ}
         {σ : Subst (γ' ++ δ ⟩⟩ γ) δ'}
         → Γ ⊢ τ ∶ Δ ∶ctx
         → ((Γ ,⟨⟨ Δ) ,++ Γ') ⊢ σ ∶ Δ' ∶ctx
         → {Δ'' : _} → Δ'' ≡ sbΔ γ' τ Δ' 
         → (Γ ,++ sbΓ γ' τ Γ') ⊢ sbσ γ' τ σ ∶ Δ'' ∶ctx
      typedsubσ Γ' D ⟨⟩ Refl = ⟨⟩
      typedsubσ {γ' = γ'} Γ' {τ = τ} D (EN , Eσ) Refl = typedsubN Γ' D EN , typedsubσ Γ' D Eσ {! 
   subΔ (sbN γ' τ N) (sbΔ (_ :: γ') τ Δ') ≡ sbΔ γ' τ (subΔ N Δ')
!} 

{-

      typedsubN γ' {N = N₁ , N₂} D (E₁ , E₂) = typedsubN D E₁ , typedsubN D E₂

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
-}