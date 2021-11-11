module Prop where

infixr 40 _`⊃_
infixr 41 _`∨_
infixr 42 _`∧_
infix  43 `¬_
infix  44 `_

-- the atomic proposition is kept abstract
postulate
  `Atom : Set

-- to make a clear distinction between Agda terms (meta language) and
-- proposition in our logic (object language), we prefix every name
-- with a backtick (`)
data `Prop : Set where
  `_   : `Atom → `Prop
  _`∧_ : `Prop → `Prop → `Prop
  _`⊃_ : `Prop → `Prop → `Prop
  _`∨_ : `Prop → `Prop → `Prop
  `⊤   : `Prop
  `⊥   : `Prop

`¬_ : `Prop → `Prop
`¬ A = A `⊃ `⊥