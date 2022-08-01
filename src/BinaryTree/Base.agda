open import Relation.Binary using (StrictTotalOrder)

module BinaryTree.Base
    {a 𝓁₁ 𝓁₂} (strictTotalOrder : StrictTotalOrder a 𝓁₁ 𝓁₂) where

open import Data.Bool using (Bool; false; true)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Level using (Level; _⊔_)
open import Relation.Binary using (_Respects_; Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary.Sum using (_¬-⊎_)
open import Relation.Unary
open StrictTotalOrder strictTotalOrder renaming (Carrier to A)

open import BinaryTree.Height public
open import BinaryTree.Extrema (strictTotalOrder) public

data Tree (l u : A⁺) : ℕ → Set (a ⊔ 𝓁₂) where
    leaf : (l<u : l <⁺ u) → Tree l u 0
    node  : ∀ {hˡ hʳ}
          → (e : A)
          → Tree l [ e ] hˡ
          → Tree [ e ] u hʳ
          → Tree l u (suc (hˡ + hʳ))

join-left : ∀ {l u : A⁺} {hˡ hʳ : ℕ}
          → (x : A)
          → (∃ λ i → Tree l [ x ] (i ⊕ hˡ))
          → Tree [ x ] u hʳ
          → ∃ λ i → Tree l u (i ⊕ suc (hˡ + hʳ))
join-left x nodeˡ nodeʳ with nodeˡ
... | (#0 , nodeˡ) = (#0 , node x nodeˡ nodeʳ)
... | (#1 , nodeˡ) = (#1 , node x nodeˡ nodeʳ)

join-right : ∀ {l u : A⁺} {hˡ hʳ : ℕ}
           → (x : A)
           → Tree l [ x ] hˡ
           → (∃ λ i → Tree [ x ] u (i ⊕ hʳ))
           → ∃ λ i → Tree l u (i ⊕ suc (hˡ + hʳ))
join-right {hˡ = hˡ} {hʳ = hʳ} x nodeˡ nodeʳ with nodeʳ
... | (#0 , nodeʳ) = (#0 , node x nodeˡ nodeʳ)
... | (#1 , nodeʳ) rewrite sym (+-suc hˡ hʳ) = (#1 , node x nodeˡ nodeʳ)

insert : ∀ {l u : A⁺} {h : ℕ}
       → (x : A)
       → Tree l u h
       → l <⁺ [ x ]
       → [ x ] <⁺ u
       → ∃ λ i → Tree l u (i ⊕ h)
insert x (leaf l<u) l<x x<u = #1 , node x (leaf l<x) (leaf x<u)
insert x (node y _ _ ) _ _ with compare x y
insert x (node y nodeˡ nodeʳ) l<x x<u | tri< x<y _ _ =
    join-left y (insert x nodeˡ l<x [ x<y ]ᴿ) nodeʳ
insert x tree _ _ | tri≈ _ _ _ = (#0 , tree)
insert x (node {hˡ} {hʳ} y nodeˡ nodeʳ) l<x x<u | tri> _ _ x>y =
    join-right y nodeˡ (insert x nodeʳ [ x>y ]ᴿ x<u)
