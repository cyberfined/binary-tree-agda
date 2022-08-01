open import Relation.Binary using (StrictTotalOrder)

module BinaryTree.Elem
    {a 𝓁₁ 𝓁₂} (strictTotalOrder : StrictTotalOrder a 𝓁₁ 𝓁₂) where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_)
open import Relation.Binary using (_Respects_; Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary.Sum using (_¬-⊎_)
open StrictTotalOrder strictTotalOrder renaming (Carrier to A)

open import BinaryTree.Base (strictTotalOrder)

¬-× : ∀ {p q : Level} {P : Set p} {Q : Set q} → ¬ P → ¬ (P × Q)
¬-× ¬P = contraposition proj₁ ¬P

×-¬ : ∀ {p q : Level} {P : Set p} {Q : Set q} → ¬ Q → ¬ (P × Q)
×-¬ ¬Q = contraposition proj₂ ¬Q

infixr 6 _∈_

data _∈_ {l u : A⁺} : {h : ℕ} → A → Tree l u h → Set (a ⊔ 𝓁₁ ⊔ 𝓁₂) where
    here : ∀ {x y : A} {hˡ hʳ : ℕ} {nodeˡ : Tree l [ y ] hˡ} {nodeʳ : Tree [ y ] u hʳ}
         → x ≈ y
         → x ∈ (node y nodeˡ nodeʳ)
    left : ∀ {x y : A} {hˡ hʳ : ℕ} {nodeˡ : Tree l [ y ] hˡ} {nodeʳ : Tree [ y ] u hʳ}
         → l <⁺ [ x ]
         → x < y
         → x ∈ nodeˡ
         → x ∈ (node y nodeˡ nodeʳ)
    right : ∀ {x y : A} {hˡ hʳ : ℕ} {nodeˡ : Tree l [ y ] hˡ} {nodeʳ : Tree [ y ] u hʳ}
          → y < x
          → [ x ] <⁺ u
          → x ∈ nodeʳ
          → x ∈ (node y nodeˡ nodeʳ)

infixr 6 _∉_
_∉_ : ∀ {l u : A⁺} {h : ℕ} → A → Tree l u h → Set (a ⊔ 𝓁₁ ⊔ 𝓁₂)
x ∉ tree = ¬ (x ∈ tree)

x∈tree⇒x∈nodeˡ∨x∈nodeʳ : ∀ {l u : A⁺}
                           {x y : A}
                           {hˡ hʳ : ℕ}
                           {nodeˡ : Tree l [ y ] hˡ}
                           {nodeʳ : Tree [ y ] u hʳ}
                       → x ∈ (node y nodeˡ nodeʳ)
                       → x ≈ y
                       ⊎ (l <⁺ [ x ]) × (x < y) × (x ∈ nodeˡ)
                       ⊎ (y < x) × ([ x ] <⁺ u) × (x ∈ nodeʳ)
x∈tree⇒x∈nodeˡ∨x∈nodeʳ (here x≈y) = inj₁ x≈y
x∈tree⇒x∈nodeˡ∨x∈nodeʳ (left l<x x<y x∈nodeˡ) = inj₂ (inj₁ (l<x , (x<y , x∈nodeˡ)))
x∈tree⇒x∈nodeˡ∨x∈nodeʳ (right y<x x<u x∈nodeʳ) = inj₂ (inj₂ (y<x , (x<u , x∈nodeʳ)))

elem? : ∀ {l u : A⁺} {h : ℕ}
      → (x : A)
      → (tree : Tree l u h)
      → l <⁺ [ x ]
      → [ x ] <⁺ u
      → Dec (x ∈ tree)
elem? x (leaf _) _ _ = no λ ()
elem? x (node y _ _) _ _ with compare x y
elem? x (node y nodeˡ nodeʳ) l<x x<u | tri< x<y x≉y x≯y with elem? x nodeˡ l<x [ x<y ]ᴿ
... | yes x∈nodeˡ = yes (left l<x x<y x∈nodeˡ)
... | no x∉nodeˡ = let contra = x≉y ¬-⊎ (×-¬ (×-¬ x∉nodeˡ)) ¬-⊎ (¬-× x≯y)
                   in no (contraposition x∈tree⇒x∈nodeˡ∨x∈nodeʳ contra)
elem? _ _ _ _ | tri≈ _ x≈y _ = yes (here x≈y)
elem? x (node y nodeˡ nodeʳ) l<x x<u | tri> x≮y x≉y x>y with elem? x nodeʳ [ x>y ]ᴿ x<u
... | yes x∈nodeʳ = yes (right x>y x<u x∈nodeʳ)
... | no x∉nodeʳ = let contra = x≉y ¬-⊎ (×-¬ (¬-× x≮y)) ¬-⊎ (×-¬ (×-¬ x∉nodeʳ))
                   in no (contraposition x∈tree⇒x∈nodeˡ∨x∈nodeʳ contra)

tree-x<u-∧-l<x⇒tree-l<u : ∀ {l u : A⁺} {h : ℕ} {x : A}
                        → Tree [ x ] u h
                        → l <⁺ [ x ]
                        → Tree l u h
tree-x<u-∧-l<x⇒tree-l<u (leaf x<u) l<x = leaf (trans⁺ l<x x<u)
tree-x<u-∧-l<x⇒tree-l<u (node x nodeˡ nodeʳ) l<x =
    node x (tree-x<u-∧-l<x⇒tree-l<u nodeˡ l<x) nodeʳ

merge : ∀ {l u : A⁺} {hˡ hʳ : ℕ} {x : A}
      → Tree l [ x ] hˡ
      → Tree [ x ] u hʳ
      → Tree l u (hˡ + hʳ)
merge (leaf l<x) tree₁ = tree-x<u-∧-l<x⇒tree-l<u tree₁ l<x
merge {hʳ = hʳ} (node {hˡ = hˡˡ} {hʳ = hʳˡ} x nodeˡ nodeʳ) tree₁
    rewrite +-assoc hˡˡ hʳˡ hʳ = node x nodeˡ (merge nodeʳ tree₁)

delete : ∀ {l u : A⁺} {h : ℕ} {x : A}
       → (tree : Tree l u (suc h))
       → x ∈ tree
       → Tree l u h
delete (node _ nodeˡ nodeʳ) (here _) = merge nodeˡ nodeʳ
delete (node x nodeˡ@(node _ _ _) nodeʳ) (left _ _ x∈nodeˡ) =
    node x (delete nodeˡ x∈nodeˡ) nodeʳ
delete (node {hˡ = hˡ} x nodeˡ nodeʳ@(node {hˡ = hˡʳ} {hʳ = hʳʳ} _ _ _))
    (right _ _ x∈nodeʳ)
    rewrite +-suc hˡ (hˡʳ + hʳʳ) = node x nodeˡ (delete nodeʳ x∈nodeʳ)
