open import Relation.Binary using (StrictTotalOrder; IsStrictPartialOrder; _Respects₂_)

module BinaryTree.Extrema
    {a 𝓁₁ 𝓁₂} (sto : StrictTotalOrder a 𝓁₁ 𝓁₂) where

open import Relation.Nullary.Construct.Add.Extrema as SetExtrema using (_±)
import Relation.Binary.Construct.Add.Extrema.Equality as EqualityExtrema
import Relation.Binary.Construct.Add.Extrema.Strict as RelationExtrema
open StrictTotalOrder sto renaming (Carrier to A) using (_<_; _≈_; isStrictTotalOrder)

A⁺ : Set a
A⁺ = A ±

open SetExtrema public using ([_])

open EqualityExtrema _≈_ public
    using () renaming
    ( _≈±_ to _≈⁺_
    ; [_]  to [_]ᴱ
    )

open RelationExtrema _<_ public
    using () renaming
    ( _<±_          to _<⁺_
    ; [_]           to [_]ᴿ
    ; [<]-injective to <⁺-injective
    )

private
    strictTotalOrder : StrictTotalOrder _ _ _
    strictTotalOrder = record {
            Carrier = A⁺;
            isStrictTotalOrder = RelationExtrema.<±-isStrictTotalOrder
                STO._<_ STO.isStrictTotalOrder
      }
      where module STO = StrictTotalOrder sto

open StrictTotalOrder strictTotalOrder public
    using() renaming
    ( compare to compare⁺
    ; trans   to trans⁺
    ; asym    to asym⁺
    )

open StrictTotalOrder strictTotalOrder
    using (isStrictPartialOrder)

<⁺-resp-≈⁺ : _<⁺_ Respects₂ _≈⁺_
<⁺-resp-≈⁺ = isStrictPartialOrder .IsStrictPartialOrder.<-resp-≈
