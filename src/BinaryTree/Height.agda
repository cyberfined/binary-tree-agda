module BinaryTree.Height where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; _+_)

ℕ₂ : Set
ℕ₂ = Fin 2

pattern #0 = zero
pattern #1 = suc zero

infixl 6 _⊕_

_⊕_ : ℕ₂ → ℕ → ℕ
#0 ⊕ n = n
#1 ⊕ n = 1 + n
