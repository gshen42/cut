module Ctx where

open import Prop

infix  31 _∋_
infix  31 _⊆_
infixl 32 _,_

data Ctx : Set where
  ·   : Ctx
  _,_ : Ctx → `Prop → Ctx

private
  variable
    A B : `Prop
    Γ Δ : Ctx

data _∋_ : Ctx → `Prop → Set where
  Z : Γ , A ∋ A

  S : Γ     ∋ A
    → Γ , B ∋ A

_⊆_ : Ctx → Ctx → Set
Γ ⊆ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

⊆-step : Γ ⊆ Δ → Γ , A ⊆ Δ , A
⊆-step Γ⊆Δ Z     = Z
⊆-step Γ⊆Δ (S x) = S (Γ⊆Δ x)
