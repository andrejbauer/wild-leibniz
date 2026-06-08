{-# OPTIONS --cubical --guardedness #-}
module Categories.WildBicat where

open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base

private
  variable
    ℓ ℓ' : Level

record WildBicat ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    wildcat : WildCat ℓ ℓ'
  open WildCat wildcat public
  field
    pentagon : ∀ {a b c d e}
      (f : Hom[ a , b ]) (g : Hom[ b , c ])
      (h : Hom[ c , d ]) (k : Hom[ d , e ])
      → ⋆Assoc (f ⋆ g) h k ∙ ⋆Assoc f g (h ⋆ k)
        ≡ cong (_⋆ k) (⋆Assoc f g h)
        ∙ ⋆Assoc f (g ⋆ h) k
        ∙ cong (f ⋆_) (⋆Assoc g h k)
    triangle : ∀ {a b c}
      (f : Hom[ a , b ]) (g : Hom[ b , c ])
      → ⋆Assoc f id g ∙ cong (f ⋆_) (⋆IdL g)
        ≡ cong (_⋆ g) (⋆IdR f)
    -- Additional unit coherences.  In a strict 2-category these
    -- follow from pentagon + triangle (MacLane); in a wild
    -- setting they must be postulated separately.  Specifically,
    -- the unit laws of Map(C) (see Categories.MapWildBicat) need
    -- these:  triangle above only covers `id` in the *middle* of
    -- three composed morphisms.
    idL-coh : ∀ {a b c}
      (f : Hom[ a , b ]) (g : Hom[ b , c ])
      → cong (_⋆ g) (⋆IdL f)
        ≡ ⋆Assoc id f g ∙ ⋆IdL (f ⋆ g)
    idR-coh : ∀ {a b c}
      (f : Hom[ a , b ]) (g : Hom[ b , c ])
      → ⋆Assoc f g id ∙ cong (f ⋆_) (⋆IdR g)
        ≡ ⋆IdR (f ⋆ g)
