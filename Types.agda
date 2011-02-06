-- STLC with pairs experimentation
-- Rob Simmons, Salil Joshi, Frank Pfenning

open import Prelude

module Types where

infixr 5 _⊃_
infixr 4 _∧_
data Type : Set where
   con : (Q : String) → Type
   _⊃_ : (A B : Type) → Type
   _∧_ : (A B : Type) → Type

Ctx = List Type
MCtx = List (Ctx × Type)   -- Modal context
LCtx = List (Ctx × String) -- Lowered modal context

open LIST.SET public
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub

Sig : Set
Sig = String → Maybe Type