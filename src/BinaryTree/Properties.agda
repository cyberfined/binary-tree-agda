open import Relation.Binary using (StrictTotalOrder; IsEquivalence)

module BinaryTree.Properties
    {a 𝓁₁ 𝓁₂} (strictTotalOrder : StrictTotalOrder a 𝓁₁ 𝓁₂) where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Nat.Properties using (+-suc; +-assoc)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary using (_Respects_; Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition; contradiction)
open import Relation.Nullary.Sum using (_¬-⊎_)
open StrictTotalOrder strictTotalOrder renaming (Carrier to A)

open import BinaryTree.Elem (strictTotalOrder)
open import BinaryTree.Base (strictTotalOrder)

-- common proofs

tree⇒l<u : {l u : A⁺} {h : ℕ} → Tree l u h → l <⁺ u
tree⇒l<u (leaf l<u) = l<u
tree⇒l<u (node _ nodeˡ nodeʳ) = let l<e = tree⇒l<u nodeˡ
                                    e<u = tree⇒l<u nodeʳ
                                in trans⁺ l<e e<u

x∈tree⇒x<u : ∀ {l u : A⁺}
               {x y : A}
               {hˡ hʳ : ℕ}
               {nodeˡ : Tree l [ y ] hˡ}
               {nodeʳ : Tree [ y ] u hʳ}
           → x ∈ (node y nodeˡ nodeʳ)
           → [ x ] <⁺ u
x∈tree⇒x<u {nodeʳ = nodeʳ} (here x≈y) =
    let y<u = tree⇒l<u nodeʳ
    in (proj₂ <⁺-resp-≈⁺) [ Eq.sym x≈y ]ᴱ y<u
x∈tree⇒x<u {nodeˡ = nodeˡ} {nodeʳ = nodeʳ} (left _ x<y _) =
    let y<u = x∈tree⇒x<u {nodeˡ = nodeˡ} {nodeʳ = nodeʳ} (here (Eq.reflexive refl))
    in trans⁺ [ x<y ]ᴿ y<u
x∈tree⇒x<u (right _ x<u _ ) = x<u

x∈tree⇒l<x : ∀ {l u : A⁺}
               {x y : A}
               {hˡ hʳ : ℕ}
               {nodeˡ : Tree l [ y ] hˡ}
               {nodeʳ : Tree [ y ] u hʳ}
           → x ∈ (node y nodeˡ nodeʳ)
           → l <⁺ [ x ]
x∈tree⇒l<x {nodeˡ = nodeˡ} (here x≈y) =
    let l<y = tree⇒l<u nodeˡ
    in (proj₁ <⁺-resp-≈⁺) [ Eq.sym x≈y ]ᴱ l<y
x∈tree⇒l<x (left l<x _ _) = l<x
x∈tree⇒l<x {nodeˡ = nodeˡ} {nodeʳ = nodeʳ} (right y<x _ _) =
    let l<y = x∈tree⇒l<x {nodeˡ = nodeˡ} {nodeʳ = nodeʳ} (here (Eq.reflexive refl))
    in trans⁺ l<y [ y<x ]ᴿ

private
    infix 4 _≉_
    _≉_ : A → A → Set 𝓁₁
    x ≉ y = ¬ (x ≈ y) 

    x<y⇒x≉y : ∀ {x y : A} → x < y → x ≉ y
    x<y⇒x≉y {x} {y} x<y with compare x y
    ... | tri< _ x≉y _ = x≉y
    ... | tri≈ x≮y _ _ = contradiction x<y x≮y
    ... | tri> _ x≉y _ = x≉y

    x<y⇒¬y<x : ∀ {x y : A} → x < y → ¬ (y < x)
    x<y⇒¬y<x {x} {y} x<y with compare x y
    ... | tri< _ _ x≯y = x≯y
    ... | tri≈ _ _ x≯y = x≯y
    ... | tri> x≮y _ _ = contradiction x<y x≮y

    x≮y⇒x≮⁺y : ∀ {x y : A} → ¬ (x < y) → ¬ ([ x ] <⁺ [ y ])
    x≮y⇒x≮⁺y x≮y x<⁺y = contradiction (<⁺-injective x<⁺y) x≮y

    x∉tree⇒root≉x : ∀ {l u : A⁺}
                      {x y : A}
                      {hˡ hʳ : ℕ}
                      {nodeˡ : Tree l [ y ] hˡ}
                      {nodeʳ : Tree [ y ] u hʳ}
                  → x ∉ (node y nodeˡ nodeʳ)
                  → x ≉ y
    x∉tree⇒root≉x x∉tree x≈y = contradiction (here x≈y) x∉tree

    insert-left⇒x∈tree : ∀ {l u : A⁺}
                           {hˡ hʳ : ℕ}
                           {x y : A}
                       → (l<x : l <⁺ [ x ])
                       → (x<y : x < y)
                       → (nodeˡ : ∃ λ i → Tree l [ y ] (i ⊕ hˡ))
                       → (nodeʳ : Tree [ y ] u hʳ)
                       → x ∈ proj₂ nodeˡ
                       → x ∈ proj₂ (join-left y nodeˡ nodeʳ)
    insert-left⇒x∈tree _ _ (#0 , leaf _) _ ()
    insert-left⇒x∈tree l<x x<y (#0 , node _ _ _ ) _ x∈tree = left l<x x<y x∈tree
    insert-left⇒x∈tree l<x x<y (#1 , node _ _ _ ) _ x∈tree = left l<x x<y x∈tree

    insert-right⇒x∈tree : ∀ {l u : A⁺}
                            {hˡ hʳ : ℕ}
                            {x y : A}
                        → (y<x : y < x)
                        → (x<u : [ x ] <⁺ u)
                        → (nodeˡ : Tree l [ y ] hˡ)
                        → (nodeʳ : ∃ λ i → Tree [ y ] u (i ⊕ hʳ))
                        → x ∈ proj₂ nodeʳ
                        → x ∈ proj₂ (join-right y nodeˡ nodeʳ)
    insert-right⇒x∈tree _ _ _ (#0 , leaf _) ()
    insert-right⇒x∈tree y<x x<u _ (#0 , node _ _ _) x∈tree = right y<x x<u x∈tree
    insert-right⇒x∈tree {hˡ = hˡ} {hʳ = hʳ} y<x x<u _ (#1 , node _ _ _) x∈tree
        rewrite sym (+-suc hˡ hʳ) = right y<x x<u x∈tree

    insert-left⇒suc-length : ∀ {l u : A⁺} {hˡ hʳ : ℕ}
                       → (x : A)
                       → (nodeˡ : ∃ λ i → Tree l [ x ] (i ⊕ hˡ))
                       → (nodeʳ : Tree [ x ] u hʳ)
                       → proj₁ nodeˡ ≡ #1
                       → proj₁ (join-left x nodeˡ nodeʳ) ≡ #1
    insert-left⇒suc-length x nodeˡ nodeʳ refl = refl

    insert-right⇒suc-length : ∀ {l u : A⁺} {hˡ hʳ : ℕ}
                        → (x : A)
                        → (nodeˡ : Tree l [ x ] hˡ)
                        → (nodeʳ : ∃ λ i → Tree [ x ] u (i ⊕ hʳ))
                        → proj₁ nodeʳ ≡ #1
                        → proj₁ (join-right x nodeˡ nodeʳ) ≡ #1
    insert-right⇒suc-length {hˡ = hˡ} {hʳ = hʳ} x nodeˡ nodeʳ refl
        rewrite sym (+-suc hˡ hʳ) = refl

    root∉nodeˡ-lem : ∀ {l : A⁺}
                       {x y z : A}
                       {hˡ hʳ : ℕ}
                       {nodeˡ : Tree l [ z ] hˡ}
                       {nodeʳ : Tree [ z ] [ y ] hʳ}
                   → x ∈ (node z nodeˡ nodeʳ)
                   → x ≈ y
                   → ⊥
    root∉nodeˡ-lem x∈nodeˡ x≈y = let x<y = <⁺-injective (x∈tree⇒x<u x∈nodeˡ)
                                     x≉y = x<y⇒x≉y x<y
                                 in contradiction x≈y x≉y

    root∉nodeʳ-lem : ∀ {u : A⁺}
                       {x y z : A}
                       {hˡ hʳ : ℕ}
                       {nodeˡ : Tree [ y ] [ z ] hˡ}
                       {nodeʳ : Tree [ z ] u hʳ}
                   → x ∈ (node z nodeˡ nodeʳ)
                   → x ≈ y
                   → ⊥
    root∉nodeʳ-lem x∈nodeʳ x≈y = let y<x = <⁺-injective (x∈tree⇒l<x x∈nodeʳ)
                                     y≉x = x<y⇒x≉y y<x
                                 in contradiction (Eq.sym x≈y) y≉x

leaf⇒x∉tree : ∀ {l u : A⁺} {x : A} → (tree : Tree l u 0) → x ∉ tree
leaf⇒x∉tree {x = x} (leaf l<u) ()

l≮x⇒x∉tree : ∀ {l u : A⁺} {x : A} {h : ℕ}
           → (tree : Tree l u h)
           → ¬ (l <⁺ [ x ])
           → x ∉ tree
l≮x⇒x∉tree (leaf l<u) _ = leaf⇒x∉tree (leaf l<u)
l≮x⇒x∉tree (node _ _ _) l≮x x∈tree = contradiction (x∈tree⇒l<x x∈tree) l≮x

x≮u⇒x∉tree : ∀ {l u : A⁺} {x : A} {h : ℕ}
           → (tree : Tree l u h)
           → ¬ ([ x ] <⁺ u)
           → x ∉ tree
x≮u⇒x∉tree (leaf l<u) _ = leaf⇒x∉tree (leaf l<u)
x≮u⇒x∉tree (node _ _ _) x≮u x∈tree = contradiction (x∈tree⇒x<u x∈tree) x≮u

x∉tree⇒x∉nodeˡ : ∀ {l u : A⁺}
                   {x y : A}
                   {hˡ hʳ : ℕ} 
                   {nodeˡ : Tree l [ y ] hˡ}
                   {nodeʳ : Tree [ y ] u hʳ}
               → x ∉ (node y nodeˡ nodeʳ) 
               → x ∉ nodeˡ
x∉tree⇒x∉nodeˡ {l = l} {x = x} x∉tree x∈nodeˡ with compare⁺ l [ x ]
x∉tree⇒x∉nodeˡ {x = x} {y = y} {nodeˡ = nodeˡ} x∉tree x∈nodeˡ | tri< l<x l≉x l≯x
    with compare x y | nodeˡ
... | tri< x<y _ _ | _ = contradiction (left l<x x<y x∈nodeˡ) x∉tree
... | tri≈ _ x≈y _ | _ = contradiction (here x≈y) x∉tree
... | tri> _ _ x>y | leaf l<u = leaf⇒x∉tree (leaf l<u) x∈nodeˡ
... | tri> x≮y _ x>y | node yˡ nodeˡˡ nodeʳˡ =
    let yˡ<y = x∈tree⇒x<u {nodeˡ = nodeˡˡ} {nodeʳ = nodeʳˡ} (here (Eq.reflexive refl))
        yˡ<x = <⁺-injective (trans⁺ yˡ<y [ x>y ]ᴿ)
        x≮yˡ = asym yˡ<x
        x≉yˡ x≈yˡ = contradiction (Eq.sym x≈yˡ) (x<y⇒x≉y yˡ<x)
        contra = x≉yˡ ¬-⊎ (×-¬ (¬-× x≮yˡ)) ¬-⊎ (×-¬ (¬-× (x≮y⇒x≮⁺y x≮y)))
    in (contraposition x∈tree⇒x∈nodeˡ∨x∈nodeʳ contra) x∈nodeˡ
x∉tree⇒x∉nodeˡ {nodeˡ = nodeˡ} _ x∈nodeˡ | tri≈ l≮x _ _ =
    contradiction x∈nodeˡ (l≮x⇒x∉tree nodeˡ l≮x)
x∉tree⇒x∉nodeˡ {nodeˡ = nodeˡ} _ x∈nodeˡ | tri> l≮x _ _ =
    contradiction x∈nodeˡ (l≮x⇒x∉tree nodeˡ l≮x)

x∉tree⇒x∉nodeʳ : ∀ {l u : A⁺}
                   {x y : A}
                   {hˡ hʳ : ℕ}
                   {nodeˡ : Tree l [ y ] hˡ}
                   {nodeʳ : Tree [ y ] u hʳ}
               → x ∉ (node y nodeˡ nodeʳ)
               → x ∉ nodeʳ
x∉tree⇒x∉nodeʳ {u = u} {x = x} x∉tree x∈nodeʳ with compare⁺ [ x ] u
x∉tree⇒x∉nodeʳ {x = x} {y = y} {nodeʳ = nodeʳ} x∉tree x∈nodeʳ | tri< x<u x≉u x≯u
    with compare x y | nodeʳ
... | tri< x<y _ _ | leaf l<u = leaf⇒x∉tree (leaf l<u) x∈nodeʳ
... | tri< x<y _ _ | node yʳ nodeˡʳ nodeʳʳ =
    let y<yʳ = x∈tree⇒l<x {nodeˡ = nodeˡʳ} {nodeʳ = nodeʳʳ} (here (Eq.reflexive refl))
        x<yʳ = <⁺-injective (trans⁺ [ x<y ]ᴿ y<yʳ)
        y≮x = asym⁺ [ x<y ]ᴿ
        x≉yʳ x≈yʳ = contradiction x≈yʳ (x<y⇒x≉y x<yʳ)
        contra = x≉yʳ ¬-⊎ (¬-× y≮x) ¬-⊎ (¬-× (asym x<yʳ))
    in (contraposition x∈tree⇒x∈nodeˡ∨x∈nodeʳ contra) x∈nodeʳ
... | tri≈ _ x≈y _ | _ = contradiction (here x≈y) x∉tree
... | tri> _ _ x>y | _ = contradiction (right x>y x<u x∈nodeʳ) x∉tree
x∉tree⇒x∉nodeʳ {nodeʳ = nodeʳ} x∉tree x∈nodeʳ | tri≈ x≮u _ _ =
    contradiction x∈nodeʳ (x≮u⇒x∉tree nodeʳ x≮u)
x∉tree⇒x∉nodeʳ {nodeʳ = nodeʳ} x∉tree x∈nodeʳ | tri> x≮u _ _ =
    contradiction x∈nodeʳ (x≮u⇒x∉tree nodeʳ x≮u)

-- insert proofs

insert⇒x∈tree : ∀ {l u : A⁺}
              → {x : A}
              → {h : ℕ}
              → {tree : Tree l u h}
              → {l<x : l <⁺ [ x ]}
              → {x<u : [ x ] <⁺ u}
              → x ∉ tree
              → x ∈ proj₂ (insert x tree l<x x<u)
insert⇒x∈tree {tree = tree} x∉tree with tree
insert⇒x∈tree x∉tree | leaf l<u = here (Eq.reflexive refl)
insert⇒x∈tree {x = x} {l<x = l<x} {x<u = x<u} x∉tree | node y nodeˡ nodeʳ
    with compare x y
... | tri< x<y _ _ =
    let x∈proj₂ = insert⇒x∈tree {l<x = l<x} {x<u = [ x<y ]ᴿ} (x∉tree⇒x∉nodeˡ x∉tree)
    in insert-left⇒x∈tree {x = x} l<x x<y (insert x nodeˡ l<x [ x<y ]ᴿ) nodeʳ x∈proj₂
... | tri≈ _ x≈y _ = here x≈y
... | tri> _ _ x>y =
    let x∈proj₂ = insert⇒x∈tree {l<x = [ x>y ]ᴿ} {x<u = x<u} (x∉tree⇒x∉nodeʳ x∉tree)
    in insert-right⇒x∈tree {x = x} x>y x<u nodeˡ (insert x nodeʳ [ x>y ]ᴿ x<u) x∈proj₂

insert⇒suc-length : ∀ {l u : A⁺}
                  {x : A}
                  {h : ℕ}
                  {tree : Tree l u h}
                  {l<x : l <⁺ [ x ]}
                  {x<u : [ x ] <⁺ u}
              → x ∉ tree
              → proj₁ (insert x tree l<x x<u) ≡ #1
insert⇒suc-length {tree = tree} x∉tree with tree
insert⇒suc-length x∉tree | leaf l<u = refl
insert⇒suc-length {x = x} x∉tree | node y _ _ with compare x y
insert⇒suc-length {x = x} {l<x = l<x} x∉tree | node y nodeˡ nodeʳ | tri< x<y _ _ =
    let proj₁≡1 = insert⇒suc-length {l<x = l<x} {x<u = [ x<y ]ᴿ} (x∉tree⇒x∉nodeˡ x∉tree)
    in insert-left⇒suc-length y (insert x nodeˡ l<x [ x<y ]ᴿ) nodeʳ proj₁≡1
insert⇒suc-length x∉tree | node _ _ _ | tri≈ _ x≈y _ = contradiction (here x≈y) x∉tree
insert⇒suc-length {x = x} {x<u = x<u} x∉tree | node y nodeˡ nodeʳ | tri> _ _ x>y =
    let proj₁≡1 = insert⇒suc-length {l<x = [ x>y ]ᴿ} {x<u = x<u} (x∉tree⇒x∉nodeʳ x∉tree)
    in insert-right⇒suc-length y nodeˡ (insert x nodeʳ [ x>y ]ᴿ x<u) proj₁≡1

-- delete proofs

x∉tree-x<u-∧-l<x⇒x∉tree-l<u : ∀ {l u : A⁺} {h : ℕ} {x y : A}
                            → (tree : Tree [ x ] u h)
                            → (l<x : l <⁺ [ x ])
                            → y ∉ tree
                            → y ∉ (tree-x<u-∧-l<x⇒tree-l<u tree l<x)
x∉tree-x<u-∧-l<x⇒x∉tree-l<u (leaf _) _ _ ()
x∉tree-x<u-∧-l<x⇒x∉tree-l<u (node x nodeˡ nodeʳ) l<x y∉tree y∈tree with y∈tree
... | here y≈x = contradiction (here y≈x) y∉tree
... | left _ y<x y∈nodeˡ =
    let y∉nodeˡ = x∉tree-x<u-∧-l<x⇒x∉tree-l<u nodeˡ l<x (x∉tree⇒x∉nodeˡ y∉tree)
    in contradiction y∈nodeˡ y∉nodeˡ
... | right x<y y<u y∈nodeʳ =
    let y∉nodeʳ = x∉tree⇒x∉nodeʳ y∉tree
    in contradiction y∈nodeʳ y∉nodeʳ

merge-children⇒root∉tree : ∀ {l u : A⁺} {x y : A} {hˡ hʳ : ℕ}
                         → (nodeˡ : Tree l [ y ] hˡ)
                         → (nodeʳ : Tree [ y ] u hʳ)
                         → x ∉ nodeˡ
                         → x ∉ nodeʳ
                         → x ∉ merge nodeˡ nodeʳ
merge-children⇒root∉tree (leaf l<x) nodeʳ x∉nodeˡ x∉nodeʳ =
    x∉tree-x<u-∧-l<x⇒x∉tree-l<u nodeʳ l<x x∉nodeʳ
merge-children⇒root∉tree {hʳ = hʳ} (node {hˡ = hˡˡ} {hʳ = hʳˡ} x nodeˡˡ nodeʳˡ)
    nodeʳ x∉nodeˡ x∉nodeʳ rewrite +-assoc hˡˡ hʳˡ hʳ =
    let x∉nodeʳˡ = x∉tree⇒x∉nodeʳ x∉nodeˡ
        x∉nodeˡˡ = x∉tree⇒x∉nodeˡ x∉nodeˡ
        x∉nodeʳ' = merge-children⇒root∉tree nodeʳˡ nodeʳ x∉nodeʳˡ x∉nodeʳ
        x≉y x≈y = contradiction (here x≈y) x∉nodeˡ
        contra = x≉y ¬-⊎ (×-¬ (×-¬ x∉nodeˡˡ)) ¬-⊎ (×-¬ (×-¬ x∉nodeʳ'))
    in contraposition x∈tree⇒x∈nodeˡ∨x∈nodeʳ contra

root∉nodeˡ : ∀ {l u : A⁺}
               {x y : A}
               {hˡ hʳ : ℕ}
               {nodeˡ : Tree l [ y ] hˡ}
               {nodeʳ : Tree [ y ] u hʳ}
           → x ∈ (node y nodeˡ nodeʳ)
           → x ≈ y
           → x ∉ nodeˡ
root∉nodeˡ (here x≈y) _ x∈nodeˡ@(here _) = root∉nodeˡ-lem x∈nodeˡ x≈y
root∉nodeˡ (here x≈y) _ x∈nodeˡ@(left _ _ _) = root∉nodeˡ-lem x∈nodeˡ x≈y
root∉nodeˡ (here x≈y) _ x∈nodeˡ@(right _ _ _) = root∉nodeˡ-lem x∈nodeˡ x≈y
root∉nodeˡ (left l<x x<y _) x≈y = contradiction x≈y (x<y⇒x≉y x<y)
root∉nodeˡ (right y<x x<u _) x≈y = contradiction (Eq.sym x≈y) (x<y⇒x≉y y<x)

root∉nodeʳ : ∀ {l u : A⁺}
               {x y : A}
               {hˡ hʳ : ℕ}
               {nodeˡ : Tree l [ y ] hˡ}
               {nodeʳ : Tree [ y ] u hʳ}
           → x ∈ (node y nodeˡ nodeʳ)
           → x ≈ y
           → x ∉ nodeʳ
root∉nodeʳ (here x≈y) _ x∈nodeʳ@(here _) = root∉nodeʳ-lem x∈nodeʳ x≈y
root∉nodeʳ (here x≈y) _ x∈nodeʳ@(left _ _ _) = root∉nodeʳ-lem x∈nodeʳ x≈y
root∉nodeʳ (here x≈y) _ x∈nodeʳ@(right _ _ _) = root∉nodeʳ-lem x∈nodeʳ x≈y
root∉nodeʳ (left l<x x<y _) x≈y = contradiction x≈y (x<y⇒x≉y x<y)
root∉nodeʳ (right y<x x<u _) x≈y = contradiction (Eq.sym x≈y) (x<y⇒x≉y y<x)

delete⇒x∉tree : ∀ {l u : A⁺}
                  {x y : A}
                  {hˡ hʳ : ℕ}
                  {nodeˡ : Tree l [ y ] hˡ}
                  {nodeʳ : Tree [ y ] u hʳ}
              → (x∈tree : x ∈ (node y nodeˡ nodeʳ))
              → x ∉ delete (node y nodeˡ nodeʳ) x∈tree
delete⇒x∉tree {nodeˡ = nodeˡ} {nodeʳ = nodeʳ} x∈tree@(here x≈y) =
    let x∉nodeˡ = root∉nodeˡ x∈tree x≈y
        x∉nodeʳ = root∉nodeʳ x∈tree x≈y
    in merge-children⇒root∉tree nodeˡ nodeʳ x∉nodeˡ x∉nodeʳ
delete⇒x∉tree {nodeˡ = nodeˡ} (left _ x<y x∈nodeˡ) with nodeˡ
... | node _ _ _ =
    let x∉nodeˡ' = delete⇒x∉tree x∈nodeˡ
        x≉y = x<y⇒x≉y x<y
        y≮x = x<y⇒¬y<x x<y
        contra = x≉y ¬-⊎ (×-¬ (×-¬ x∉nodeˡ')) ¬-⊎ (¬-× y≮x)
    in contraposition x∈tree⇒x∈nodeˡ∨x∈nodeʳ contra
delete⇒x∉tree {hˡ = hˡ} {nodeʳ = nodeʳ} (right y<x _ x∈nodeʳ) with nodeʳ
... | node {hˡ = hˡʳ} {hʳ = hʳʳ} _ _ _ rewrite +-suc hˡ (hˡʳ + hʳʳ) =
    let x∉nodeʳ' = delete⇒x∉tree x∈nodeʳ
        x≉y x≈y = contradiction (Eq.sym x≈y) (x<y⇒x≉y y<x)
        x≮y = x<y⇒¬y<x y<x
        contra = x≉y ¬-⊎ (×-¬ (¬-× x≮y)) ¬-⊎ (×-¬ (×-¬ x∉nodeʳ'))
    in contraposition x∈tree⇒x∈nodeˡ∨x∈nodeʳ contra
