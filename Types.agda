-- STLC with pairs experimentation
-- Rob Simmons, Salil Joshi, Frank Pfenning

open import Prelude

module Types where

infixr 5 _⊃_
infixr 4 _∧_
data Type : Set where
   con : String → Type
   _⊃_ : Type → Type → Type
   _∧_ : Type → Type → Type

Ctx = List Type
MCtx = List (Ctx × Type)

open LIST.SET
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub

Sig : Set
Sig = String → Maybe Type