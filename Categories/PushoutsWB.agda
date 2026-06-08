{-# OPTIONS --cubical --guardedness --lossy-unification --allow-unsolved-metas #-}
{-
Pushouts in a wild bicategory C.

Records the data of a pushout of a cospan (f : X → A, g : X → B)
in C: an apex P with a cocone (i, j, sq), and the universal
property stated as: the "restrict to cocone" map is an
equivalence at every test object Q.

This is the abstract analog of `Cubical.HITs.Pushout` (which works
in U).  Consumers would build the pushout-product on Map(C) by
applying this to specific spans built from arrows of C.
-}
module Categories.PushoutsWB where

open import Categories.WildBicat
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.WildCat.Base

private
  variable
    ℓ₁ ℓ₂ : Level

module _ (C : WildBicat ℓ₁ ℓ₂) where
  open WildBicat C

  -- Cocone over a cospan (f, g) at apex Q.
  Cocone : {X A B : ob} (f : Hom[ X , A ]) (g : Hom[ X , B ]) (Q : ob) → Type ℓ₂
  Cocone {X} {A} {B} f g Q =
    Σ[ i ∈ Hom[ A , Q ] ]
    Σ[ j ∈ Hom[ B , Q ] ]
    (f ⋆ i ≡ g ⋆ j)

  -- A pushout of (f, g) is an apex P with a cocone (i, j, sq)
  -- such that for every Q, "restrict m to its cocone (i⋆m, j⋆m,
  -- the induced square)" is an equivalence.
  record hasPushout {X A B : ob}
    (f : Hom[ X , A ]) (g : Hom[ X , B ]) : Type (ℓ-max ℓ₁ ℓ₂) where
    field
      P  : ob
      i  : Hom[ A , P ]
      j  : Hom[ B , P ]
      sq : f ⋆ i ≡ g ⋆ j

    restrict : (Q : ob) → Hom[ P , Q ] → Cocone f g Q
    restrict Q m = (i ⋆ m) , (j ⋆ m) ,
      ( sym (⋆Assoc f i m)
      ∙ cong (_⋆ m) sq
      ∙ ⋆Assoc g j m )

    field
      UP : (Q : ob) → isEquiv (restrict Q)

  -- C has all pushouts:
  hasAllPushouts : Type (ℓ-max ℓ₁ ℓ₂)
  hasAllPushouts = ∀ {X A B} (f : Hom[ X , A ]) (g : Hom[ X , B ]) → hasPushout f g
