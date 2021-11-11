module SeqCalc where

open import Prop
open import Ctx
open import NatDed hiding (struct)

open import Data.Product
  using (∃; ∃-syntax; proj₂; -,_) renaming (_,_ to infix 4 ⟨_,_⟩)
open import Data.Empty using (⊥)

infix  20 _⇒_^_
infixr 21 _+_

data Size : Set where
  zero : Size
  suc  : Size → Size
  _+_  : Size → Size → Size

private
  variable
    P       : `Atom
    A B C D : `Prop
    Γ Δ     : Ctx
    m n     : Size

-- to facilitate termination checking, each sequent is indexed by the
-- size of the derivation
data _⇒_^_ : Ctx → `Prop → Size → Set where
  idᵖ : Γ     ∋ ` P
      → Γ     ⇒ ` P   ^ zero
  -- this rule only allows atomic proposition to be concluded this
  -- matches well with the verificationist point of view the general
  -- version for all proposition is admissible (see "id" below)

  ∧R  : Γ     ⇒ A      ^ m
      → Γ     ⇒ B      ^ n
      → Γ     ⇒ A `∧ B ^ m + n

  ∧L₁ : Γ     ∋ A `∧ B
      → Γ , A ⇒ C      ^ m
      → Γ     ⇒ C      ^ suc m

  ∧L₂ : Γ     ∋ A `∧ B
      → Γ , B ⇒ C      ^ m
      → Γ     ⇒ C      ^ suc m

  ⊃R  : Γ , A ⇒ B      ^ m
      → Γ     ⇒ A `⊃ B ^ suc m

  ⊃L  : Γ     ∋ A `⊃ B
      → Γ     ⇒ A      ^ m
      → Γ , B ⇒ C      ^ n
      → Γ     ⇒ C      ^ m + n

  ∨R₁ : Γ     ⇒ A      ^ m
      → Γ     ⇒ A `∨ B ^ suc m

  ∨R₂ : Γ     ⇒ B      ^ m
      → Γ     ⇒ A `∨ B ^ suc m

  ∨L  : Γ     ∋ A `∨ B
      → Γ , A ⇒ C      ^ m
      → Γ , B ⇒ C      ^ n
      → Γ     ⇒ C      ^ m + n

  ⊤R  : Γ ⇒ `⊤         ^ zero

  ⊥L  : Γ ∋ `⊥
      → Γ ⇒ C          ^ zero

-- structural rules
struct : Γ ⊆ Δ
       → Γ ⇒ C ^ m
       → Δ ⇒ C ^ m
struct Γ⊆Δ (idᵖ a)    = idᵖ (Γ⊆Δ a)
struct Γ⊆Δ (∧R a b)   = ∧R (struct Γ⊆Δ a) (struct Γ⊆Δ b)
struct Γ⊆Δ (∧L₁ a b)  = ∧L₁ (Γ⊆Δ a) (struct (⊆-step Γ⊆Δ) b)
struct Γ⊆Δ (∧L₂ a b)  = ∧L₂ (Γ⊆Δ a) (struct (⊆-step Γ⊆Δ) b)
struct Γ⊆Δ (⊃R a)     = ⊃R (struct (⊆-step Γ⊆Δ) a)
struct Γ⊆Δ (⊃L a b c) = ⊃L (Γ⊆Δ a) (struct Γ⊆Δ b) (struct (⊆-step Γ⊆Δ) c)
struct Γ⊆Δ (∨R₁ a)    = ∨R₁ (struct Γ⊆Δ a)
struct Γ⊆Δ (∨R₂ a)    = ∨R₂ (struct Γ⊆Δ a)
struct Γ⊆Δ (∨L a b c) = ∨L (Γ⊆Δ a) (struct (⊆-step Γ⊆Δ) b) (struct (⊆-step Γ⊆Δ) c)
struct Γ⊆Δ ⊤R         = ⊤R
struct Γ⊆Δ (⊥L a)     = ⊥L (Γ⊆Δ a)

wk : Γ     ⇒ C ^ m
   → Γ , A ⇒ C ^ m
wk x = struct S x

wk′ : Γ , A     ⇒ C ^ m
    → Γ , B , A ⇒ C ^ m
wk′ x = struct (λ { Z → Z ; (S i) → S (S i) }) x

exch : Γ , A , B ⇒ C ^ m
     → Γ , B , A ⇒ C ^ m
exch x = struct ((λ { Z → S Z ; (S Z) → Z ; (S (S i)) → S (S i) })) x

-- we write ∃[ q ] ⇒ Γ ⇒ A ^ q for sequent with size we don't care,
-- the monadic binding makes manipulating them easier, though I'm not
-- sure whether they actually form a monad
_>>=_ : ∃[ q ] Γ ⇒ A ^ q
      → (∀ {m} → Γ ⇒ A ^ m → ∃[ p ] Δ ⇒ B ^ p)
     → ∃[ r ] Δ ⇒ B ^ r
⟨ _ , x ⟩ >>= f = let ⟨ _ , a ⟩ = f x
                   in -, a

-- identity theorem
-- this shows global completeness of the calculus
-- which means eliminations (left rules) are strong enough to
-- extract all the information introductions (right rule) put into
id : Γ ∋ A
   → ∃[ q ] Γ ⇒ A ^ q
id {A = ` P}    x = -, idᵖ x
id {A = A `∧ B} x = do a ← id Z
                       b ← id Z
                       -, ∧R (∧L₁ x a) (∧L₂ x b)
id {A = A `⊃ B} x = do a ← id Z
                       b ← id Z
                       -, ⊃R (⊃L (S x) a b)
id {A = A `∨ B} x = do a ← id Z
                       b ← id Z
                       -, ∨L x (∨R₁ a) (∨R₂ b)
id {A = `⊤}     x = -, ⊤R
id {A = `⊥}     x = -, ⊥L x

-- cut theorem
cut :        Γ ⇒ D     ^ m
    →        Γ , D ⇒ C ^ n
    → ∃[ q ] Γ     ⇒ C ^ q
-- idᵖ + arbitrary rule
cut (idᵖ a) b = -, struct (λ { Z → a ; (S i) → i }) b
-- arbitrary rule + idᵖ
cut a (idᵖ Z)     = -, a
cut a (idᵖ (S b)) = -, idᵖ b
-- right rule + arbitrary rule
cut (∧L₁ a b)  c = do x ← cut b (wk′ c)
                      -, ∧L₁ a x
cut (∧L₂ a b)  c = do x ← cut b (wk′ c)
                      -, ∧L₂ a x
cut (⊃L a b c) d = do x ← cut c (wk′ d)
                      -, ⊃L a b x
cut (∨L a b c) d = do x ← cut b (wk′ d)
                      y ← cut c (wk′ d)
                      -, ∨L a x y
cut (⊥L a)     b = -, ⊥L a
-- arbitrary rule + left rule
cut a (∧R b c) = do x ← cut a b
                    y ← cut a c
                    -, ∧R x y
cut a (⊃R b)   = do x ← cut (wk a) (exch b)
                    -, ⊃R x
cut a (∨R₁ b)  = do x ← cut a b
                    -, ∨R₁ x
cut a (∨R₂ b)  = do x ← cut a b
                    -, ∨R₂ x
cut a ⊤R       = -, ⊤R
-- right rule + left rule
-- the cut proposition is not used
cut o@(∧R a b) (∧L₁ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₁ c x
cut o@(⊃R a)   (∧L₁ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₁ c x
cut o@(∨R₁ a)  (∧L₁ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₁ c x
cut o@(∨R₂ a)  (∧L₁ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₁ c x
cut o@⊤R       (∧L₁ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₁ c x
cut o@(∧R a b) (∧L₂ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₂ c x
cut o@(⊃R a)   (∧L₂ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₂ c x
cut o@(∨R₁ a)  (∧L₂ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₂ c x
cut o@(∨R₂ a)  (∧L₂ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₂ c x
cut o@⊤R       (∧L₂ (S c) d)  = do x ← cut (wk o) (exch d)
                                   -, ∧L₂ c x
cut o@(∧R a b) (⊃L (S c) d e) = do x ← cut o d
                                   y ← cut (wk o) (exch e)
                                   -, ⊃L c x y
cut o@(⊃R a)   (⊃L (S c) d e) = do x ← cut o d
                                   y ← cut (wk o) (exch e)
                                   -, ⊃L c x y
cut o@(∨R₁ a)  (⊃L (S c) d e) = do x ← cut o d
                                   y ← cut (wk o) (exch e)
                                   -, ⊃L c x y
cut o@(∨R₂ a)  (⊃L (S c) d e) = do x ← cut o d
                                   y ← cut (wk o) (exch e)
                                   -, ⊃L c x y
cut o@⊤R       (⊃L (S c) d e) = do x ← cut o d
                                   y ← cut (wk o) (exch e)
                                   -, ⊃L c x y
cut o@(∧R a b) (∨L (S c) d e) = do x ← cut (wk o) (exch d)
                                   y ← cut (wk o) (exch e)
                                   -, ∨L c x y
cut o@(⊃R a)   (∨L (S c) d e) = do x ← cut (wk o) (exch d)
                                   y ← cut (wk o) (exch e)
                                   -, ∨L c x y
cut o@(∨R₁ a)  (∨L (S c) d e) = do x ← cut (wk o) (exch d)
                                   y ← cut (wk o) (exch e)
                                   -, ∨L c x y
cut o@(∨R₂ a)  (∨L (S c) d e) = do x ← cut (wk o) (exch d)
                                   y ← cut (wk o) (exch e)
                                   -, ∨L c x y
cut o@⊤R       (∨L (S c) d e) = do x ← cut (wk o) (exch d)
                                   y ← cut (wk o) (exch e)
                                   -, ∨L c x y
cut o@(∧R a b) (⊥L (S c))     = -, ⊥L c
cut o@(⊃R a)   (⊥L (S c))     = -, ⊥L c
cut o@(∨R₁ a)  (⊥L (S c))     = -, ⊥L c
cut o@(∨R₂ a)  (⊥L (S c))     = -, ⊥L c
cut o@⊤R       (⊥L (S c))     = -, ⊥L c
-- right rule + left rule
-- the cut proposition is used
cut o@(∧R a b) (∧L₁ Z d)   = do x ← cut (wk o) (exch d)
                                cut a x
cut o@(∧R a b) (∧L₂ Z d)   = do x ← cut (wk o) (exch d)
                                cut b x
cut o@(⊃R a)   (⊃L Z d e)  = do x ← cut o d
                                y ← cut x a
                                z ← cut (wk o) (exch e)
                                cut y z
cut o@(∨R₁ a)  (∨L Z d e)  = do x ← cut (∨R₁ (wk a)) (exch d)
                                cut a x
cut o@(∨R₂ a)  (∨L Z d e)  = do x ← cut (∨R₂ (wk a)) (exch e)
                                cut a x

-- sequent calculus is consistent in that `⊥ is not deducible
sc-consistent : · ⇒ `⊥ ^ m → ⊥
sc-consistent (∧L₁ () _)
sc-consistent (∧L₂ () _)
sc-consistent (⊃L () _ _)
sc-consistent (∨L () _ _)
sc-consistent (⊥L ())

-- every natural deduction derivation is a sequent calculus derivation
nd→sc : Γ ⊢ C → ∃[ q ] Γ ⇒ C ^ q
nd→sc (ass x)    = id x
nd→sc (∧I x y)   = do a ← nd→sc x
                      b ← nd→sc y
                      -, ∧R a b
nd→sc (∧E₁ x)    = do a ← nd→sc x
                      b ← id Z
                      cut a (∧L₁ Z b)
nd→sc (∧E₂ x)    = do a ← nd→sc x
                      b ← id Z
                      cut a (∧L₂ Z b)
nd→sc (⊃I x)     = do a ← nd→sc x
                      -, ⊃R a
nd→sc (⊃E x y)   = do a ← nd→sc x
                      b ← nd→sc y
                      c ← id Z
                      cut a (⊃L Z (wk b) c)
nd→sc (∨I₁ x)    = do a ← nd→sc x
                      -, ∨R₁ a
nd→sc (∨I₂ x)    = do a ← nd→sc x
                      -, ∨R₂ a
nd→sc (∨E x y z) = do a ← nd→sc x
                      b ← nd→sc y
                      c ← nd→sc z
                      cut a (∨L Z (wk′ b) (wk′ c))
nd→sc ⊤I         = -, ⊤R
nd→sc (⊥E x)     = do a ← nd→sc x
                      cut a (⊥L Z)

-- every sequent calculus derivation is a natural deduction derivation
sc→nd : Γ ⇒ C ^ m → Γ ⊢ C
sc→nd (idᵖ x)    = ass x
sc→nd (∧R x y)   = ∧I (sc→nd x) (sc→nd y)
sc→nd (∧L₁ x y)  = ⊃E (⊃I (sc→nd y)) (∧E₁ (ass x))
sc→nd (∧L₂ x y)  = ⊃E (⊃I (sc→nd y)) (∧E₂ (ass x))
sc→nd (⊃R x)     = ⊃I (sc→nd x)
sc→nd (⊃L x y z) = ⊃E (⊃I (sc→nd z)) (⊃E (ass x) (sc→nd y))
sc→nd (∨R₁ x)    = ∨I₁ (sc→nd x)
sc→nd (∨R₂ x)    = ∨I₂ (sc→nd x)
sc→nd (∨L x y z) = ∨E (ass x) (sc→nd y) (sc→nd z)
sc→nd ⊤R         = ⊤I
sc→nd (⊥L x)     = ⊥E (ass x)

-- natural deduction is also consistent in that `⊥ is not deducible
nd-consistent : · ⊢ `⊥ → ⊥
nd-consistent x = let ⟨ _ , a ⟩ = nd→sc x
                   in sc-consistent a

private
  -- examples
  ex₀ : ∃[ q ] · ⇒ A `⊃ B `⊃ A `∧ B ^ q
  ex₀ = do x ← id (S Z)
           y ← id Z
           -, ⊃R (⊃R (∧R x y))

  ex₁ : ∃[ q ] · ⇒ (A `⊃ B `∧ C) `⊃ (A `⊃ B) `∧ (A `⊃ C) ^ q
  ex₁ = do x ← id Z
           y ← id Z
           z ← id Z
           w ← id Z
           -, ⊃R (∧R (⊃R (⊃L (S Z) x (∧L₁ Z y)))
                     (⊃R (⊃L (S Z) z (∧L₂ Z w))))

  ex₂ : ∃[ q ] · ⇒ A `⊃ A ^ q
  ex₂ = do x ← id Z
           -, ⊃R x
  -- unlike natural deduction, there couldn't be any other proof of A ⊃ A
