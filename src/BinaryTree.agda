open import Relation.Binary using (StrictTotalOrder)

module BinaryTree
    {a 𝓁₁ 𝓁₂} (strictTotalOrder : StrictTotalOrder a 𝓁₁ 𝓁₂) where

open import BinaryTree.Base (strictTotalOrder) public
open import BinaryTree.Elem (strictTotalOrder) public
