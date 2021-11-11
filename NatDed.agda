module NatDed where

open import Prop
open import Ctx

infix 20 _⊢_

private
  variable
    A B C : `Prop
    Γ Δ   : Ctx

data _⊢_ : Ctx → `Prop → Set where
  ass : Γ ∋ A
      → Γ ⊢ A

  ∧I  : Γ ⊢ A
      → Γ ⊢ B
      → Γ ⊢ A `∧ B

  ∧E₁ : Γ ⊢ A `∧ B
      → Γ ⊢ A

  ∧E₂ : Γ ⊢ A `∧ B
      → Γ ⊢ B

  ⊃I  : Γ , A ⊢ B
      → Γ ⊢ A `⊃ B

  ⊃E  : Γ ⊢ A `⊃ B
      → Γ ⊢ A
      → Γ ⊢ B

  ∨I₁ : Γ ⊢ A
      → Γ ⊢ A `∨ B

  ∨I₂ : Γ ⊢ B
      → Γ ⊢ A `∨ B

  ∨E  : Γ ⊢ A `∨ B
      → Γ , A ⊢ C
      → Γ , B ⊢ C
      → Γ ⊢ C

  ⊤I  : Γ ⊢ `⊤

  ⊥E  : Γ ⊢ `⊥
      → Γ ⊢ C

struct : (Γ ⊆ Δ) → Γ ⊢ C → Δ ⊢ C
struct Γ⊆Δ (ass x)    = ass (Γ⊆Δ x)
struct Γ⊆Δ (∧I x y)   = ∧I  (struct Γ⊆Δ x) (struct Γ⊆Δ y)
struct Γ⊆Δ (∧E₁ x)    = ∧E₁ (struct Γ⊆Δ x)
struct Γ⊆Δ (∧E₂ x)    = ∧E₂ (struct Γ⊆Δ x)
struct Γ⊆Δ (⊃I x)     = ⊃I  (struct (⊆-step Γ⊆Δ) x)
struct Γ⊆Δ (⊃E x y)   = ⊃E  (struct Γ⊆Δ x) (struct Γ⊆Δ y)
struct Γ⊆Δ (∨I₁ x)    = ∨I₁ (struct Γ⊆Δ x)
struct Γ⊆Δ (∨I₂ x)    = ∨I₂ (struct Γ⊆Δ x)
struct Γ⊆Δ (∨E x y z) = ∨E  (struct Γ⊆Δ x) (struct (⊆-step Γ⊆Δ) y) (struct (⊆-step Γ⊆Δ) z)
struct Γ⊆Δ ⊤I         = ⊤I
struct Γ⊆Δ (⊥E x)     = ⊥E  (struct Γ⊆Δ x)

private
  -- examples
  ex₀ : · ⊢ A `⊃ B `⊃ A `∧ B
  ex₀ = ⊃I (⊃I (∧I (ass (S Z)) (ass Z)))

  ex₁ : · ⊢ (A `⊃ B `∧ C) `⊃ (A `⊃ B) `∧ (A `⊃ C)
  ex₁ = ⊃I (∧I (⊃I (∧E₁ (⊃E (ass (S Z)) (ass Z))))
               (⊃I (∧E₂ (⊃E (ass (S Z)) (ass Z)))))

  ex₂ : · ⊢ A `⊃ A
  ex₂ = ⊃I (ass Z)

  -- we can have two different proofs for the same proposition
  -- where this one takes a detour
  ex₃ : · ⊢ A `⊃ A
  ex₃ = ⊃I (⊃E (⊃I (ass Z)) (ass Z))
