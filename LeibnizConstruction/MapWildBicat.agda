{-# OPTIONS --cubical --guardedness --lossy-unification --allow-unsolved-metas #-}
{-
Parallel of LeibnizConstruction.Map for an arbitrary wild
bicategory C.

The existing development fixes C = U and defines _⊠ᵐ_, _⋔ᵐ_
concretely via Σ, Π, and the HIT join.  Here we work abstractly.

  * _≅Map_ is the wild iso of maps — the right "equality" of
    objects in Map(C) absent univalence.

  * LeibnizStructure packages the pushout-product ⊠ and pullback-
    exponential ⋔ on Map(C), plus the adjointness ⊠ ⊣ ⋔ and the
    associator of ⊠.  These are the minimal data 3.17 will
    Yoneda-chase against.

  * The forward and backward maps of 3.17 are constructed
    explicitly from the adjointness and associator (see Yoneda
    diagram in the body).  What is left as holes is the section
    and retract — i.e., that forward∘backward and backward∘
    forward equal the identity.  These holes are where the
    pentagon and triangle of C should enter, together with
    naturality of adj and assoc⊠.

Research targets:

  B. Fill the section/retract holes from pentagon+triangle of C
     plus naturality of adj/assoc⊠.

  A. Exhibit C : WildBicat and S : LeibnizStructure with all
     fields filled such that no Corollary-3-17 inhabitant exists.
-}
module LeibnizConstruction.MapWildBicat where

-- Local imports
open import Categories.WildBicat
open import Categories.MapWildBicat

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.WildCat.Base

private
  variable
    ℓ₁ ℓ₂ : Level

module _ (C : WildBicat ℓ₁ ℓ₂) where
  open WB C

  -- Wild iso of maps: a parallel pair of mutually-inverse Map-
  -- morphisms.  Replacement for path-equality (which would need
  -- univalenceMap).
  _≅Map_ : Map → Map → Type ℓ₂
  m ≅Map m' = Σ[ F ∈ Map[ m , m' ] ]
              Σ[ G ∈ Map[ m' , m ] ]
                ( compHomMap m m' m F G ≡ idHomMap )
                × ( compHomMap m' m m' G F ≡ idHomMap )

  -- Data of a Leibniz adjunction on Map(C).  Naturality of adj
  -- and assoc⊠ is required for the section/retract proofs of
  -- 3.17 but is omitted here.
  record LeibnizStructure : Type (ℓ-max ℓ₁ ℓ₂) where
    field
      _⊠_ : Map → Map → Map
      _⋔_ : Map → Map → Map
      adj : (a b c : Map) → Map[ (a ⊠ b) , c ] ≃ Map[ a , (b ⋔ c) ]
      assoc⊠ : (a b c : Map) → ((a ⊠ b) ⊠ c) ≅Map (a ⊠ (b ⊠ c))

  module _ (S : LeibnizStructure) where
    open LeibnizStructure S

    module _ (i j f : Map) where
      private
        X = (i ⊠ j) ⋔ f
        Y = i ⋔ (j ⋔ f)

      -- Forward map of 3.17, by Yoneda chase starting from
      -- idHomMap : X → X = X → (i⊠j)⋔f:
      --   ↦ X⊠(i⊠j) → f                  (invEq adj)
      --   ↦ (X⊠i)⊠j → f                  (precompose (assoc⊠ X i j).fst)
      --   ↦ X⊠i → j⋔f                    (adj)
      --   ↦ X → i⋔(j⋔f)                  (adj)
      forward : Map[ X , Y ]
      forward =
        let s1 = invEq (adj X (i ⊠ j) f) idHomMap
            s2 = compHomMap _ _ _ (fst (assoc⊠ X i j)) s1
            s3 = equivFun (adj (X ⊠ i) j f) s2
        in equivFun (adj X i (j ⋔ f)) s3

      -- Backward map, dually:
      --   idHomMap : Y → Y = Y → i⋔(j⋔f)
      --   ↦ Y⊠i → j⋔f                    (invEq adj)
      --   ↦ (Y⊠i)⊠j → f                  (invEq adj)
      --   ↦ Y⊠(i⊠j) → f                  (precompose (assoc⊠ Y i j).snd.fst)
      --   ↦ Y → (i⊠j)⋔f                  (adj)
      backward : Map[ Y , X ]
      backward =
        let t1 = invEq (adj Y i (j ⋔ f)) idHomMap
            t2 = invEq (adj (Y ⊠ i) j f) t1
            t3 = compHomMap _ _ _ (fst (snd (assoc⊠ Y i j))) t2
        in equivFun (adj Y (i ⊠ j) f) t3

      -- Corollary 3.17.  The maps are explicit; the section and
      -- retract are the actual research content.
      Corollary-3-17 : X ≅Map Y
      Corollary-3-17 = forward , backward , ? , ?
      --                                    ^   ^
      --                          section ──┘   └── retract
      -- Both holes require naturality of adj and assoc⊠ and the
      -- pentagon + triangle of C to discharge.
