{-# OPTIONS --cubical --guardedness --lossy-unification --allow-unsolved-metas #-}
{-
This file constructs Map(C) as a wild category, parallel to
Categories.Map (which fixes C = U). C is taken to be a wild
bicategory; pentagon and triangle of C are intended to discharge
the associativity and unit laws of Map(C).

Everything is packaged inside the submodule WB, parameterised by
the wild bicategory C, so consumers can write `open WB C` to bring
the whole development into scope at a specific C.

Status: structural skeleton + WildCat instance.  The α- and β-
components of the unit and associativity equations are immediate
(⋆IdL, ⋆IdR, ⋆Assoc of C); the third (square-coherence) component
is a PathP that demands pentagon (for assocMap) and triangle (for
MapIdL/MapIdR) of C.  These three squares are left as holes,
flagged below.  This is the first concrete point at which the
bicategorical coherences enter the abstracted development.
-}
module Categories.MapWildBicat where

-- Local imports
open import Categories.WildBicat

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.WildCat.Base

private
  variable
    ℓ₁ ℓ₂ : Level

  -- Helper: transport in a path type whose endpoints vary.
  transport-≡-shape : ∀ {ℓ} {A : Type ℓ} {x x' y y' : A}
    (p : x ≡ x') (q : y ≡ y') (r : x ≡ y)
    → transport (λ i → p i ≡ q i) r ≡ sym p ∙ r ∙ q
  transport-≡-shape {x = x} {y = y} p q r =
    J (λ _ p' → ∀ q'' → transport (λ i → p' i ≡ q'' i) r ≡ sym p' ∙ r ∙ q'')
      (λ q'' → J (λ _ q''' → transport (λ i → x ≡ q''' i) r ≡ sym refl ∙ r ∙ q''')
                  (transportRefl r ∙ lUnit r ∙ cong (refl ∙_) (rUnit r))
                  q'')
      p q

module WB (C : WildBicat ℓ₁ ℓ₂) where
  open WildBicat C public

  -- The type of maps in C (wild arrow category over C)
  Map : Type (ℓ-max ℓ₁ ℓ₂)
  Map = Σ[ A ∈ ob ] Σ[ B ∈ ob ] Hom[ A , B ]

  Dom : Map → ob
  Dom = fst

  Cod : Map → ob
  Cod m = fst (snd m)

  -- Hom types
  Map[_,_] : Map → Map → Type ℓ₂
  Map[_,_] (A , B , f) (A' , B' , f') =
    Σ[ α ∈ Hom[ A , A' ] ] Σ[ β ∈ Hom[ B , B' ] ] (f ⋆ β ≡ α ⋆ f')

  -- Composition
  compHomMap : (c d e : Map) → Map[ c , d ] → Map[ d , e ] → Map[ c , e ]
  compHomMap (A , B , f) (A' , B' , f') (A'' , B'' , f'')
             (α , β , p) (α' , β' , q) =
    (α ⋆ α') ,
    (β ⋆ β') ,
    (sym (⋆Assoc f β β')
      ∙ cong (_⋆ β') p
      ∙ ⋆Assoc α f' β'
      ∙ cong (α ⋆_) q
      ∙ sym (⋆Assoc α α' f''))

  -- Identity
  idHomMap : {c : Map} → Map[ c , c ]
  idHomMap {c = A , B , f} = id , id , (⋆IdR f ∙ sym (⋆IdL f))

  -- Associativity. α- and β-components are immediate; the square
  -- coherence requires pentagon (left as a hole — research point).
  assocMap : {c d e k : Map}
    (F : Map[ c , d ]) (G : Map[ d , e ]) (H : Map[ e , k ])
    → compHomMap c e k (compHomMap c d e F G) H
     ≡ compHomMap c d k F (compHomMap d e k G H)
  assocMap {A , B , f} {A' , B' , f'} {A'' , B'' , f''} {A''' , B''' , f'''}
           (α , β , p) (α' , β' , q) (α'' , β'' , r) =
    ΣPathP (⋆Assoc α α' α'' ,
      ΣPathP (⋆Assoc β β' β'' , ?))   -- square coherence — needs pentagon

  -- Unit laws.
  --
  -- The α- and β-components are immediate (⋆IdL / ⋆IdR of C).
  -- The square component is a PathP that — after toPathP and
  -- path-algebra — reduces to an equation provable from:
  --   * middle-triangle (`triangle` of C),
  --   * outer-id-coherence (`idL-coh` or `idR-coh` of C — the
  --     coherences we added because pentagon+middle-triangle alone
  --     are insufficient in a wild setting),
  --   * naturality of ⋆IdL / ⋆IdR (automatic in cubical via cong).
  MapIdL : {c d : Map} (F : Map[ c , d ])
    → compHomMap c c d idHomMap F ≡ F
  MapIdL {A , B , f} {A' , B' , f'} (α , β , p) =
    ΣPathP (⋆IdL α , ΣPathP (⋆IdL β , toPathP path-eq))
    where
      -- Naturality of ⋆IdL applied to any path q : a ≡ b
      -- (the bicategorical "left-unitor is a natural transformation"
      -- statement — here automatic via cubical's cong).
      nat-IdL : ∀ {x y} {a b : Hom[ x , y ]} (q : a ≡ b)
        → sym (⋆IdL a) ∙ cong (id ⋆_) q ∙ ⋆IdL b ≡ q
      nat-IdL {a = a} = J (λ b q → sym (⋆IdL a) ∙ cong (id ⋆_) q ∙ ⋆IdL b ≡ q)
        ( cong (sym (⋆IdL a) ∙_) (sym (lUnit (⋆IdL a)))
        ∙ lCancel (⋆IdL a) )

      -- The square produced by composition compHomMap c c d idHomMap F:
      sq : f ⋆ (id ⋆ β) ≡ (id ⋆ α) ⋆ f'
      sq = sym (⋆Assoc f id β)
           ∙ cong (_⋆ β) (⋆IdR f ∙ sym (⋆IdL f))
           ∙ ⋆Assoc id f β
           ∙ cong (id ⋆_) p
           ∙ sym (⋆Assoc id α f')

      -- Path-algebra chain (4 steps).  After toPathP and the
      -- standard transport-in-path-type formula, the goal reduces
      -- to:
      --   sym (cong (f ⋆_) (⋆IdL β)) ∙ sq ∙ cong (_⋆ f') (⋆IdL α) ≡ p
      -- Step 1 absorbs `sym (⋆Assoc f id β) ∙ cong (_⋆ β) (⋆IdR f)`
      -- against `sym (cong (f ⋆_) (⋆IdL β))` via `triangle f β`.
      -- Step 2 absorbs `cong (_⋆ β) (sym (⋆IdL f)) ∙ ⋆Assoc id f β`
      -- via `idL-coh f β`.
      -- Step 3 absorbs `sym (⋆Assoc id α f') ∙ cong (_⋆ f') (⋆IdL α)`
      -- via `idL-coh α f'`.
      -- Step 4 collapses via `nat-IdL p`.
      --
      -- Each step is a routine path-algebra rearrangement; the
      -- proof skeleton is laid out with one hole per step.  The
      -- final step (`nat-IdL p`) is fully discharged.
      path-eq : transport (λ i → f ⋆ (⋆IdL β i) ≡ (⋆IdL α i) ⋆ f') sq ≡ p
      path-eq =
          transport (λ i → f ⋆ (⋆IdL β i) ≡ (⋆IdL α i) ⋆ f') sq
        ≡⟨ transport-≡-shape (cong (f ⋆_) (⋆IdL β)) (cong (_⋆ f') (⋆IdL α)) sq ⟩
          sym (cong (f ⋆_) (⋆IdL β)) ∙ sq ∙ cong (_⋆ f') (⋆IdL α)
        ≡⟨ -- step 1: flatten + absorb via triangle.  Pattern mirrors MapIdR step 1
            -- but with an extra cong-∙ to split `cong (_⋆ β) (⋆IdR f ∙ sym (⋆IdL f))`
            -- before the triangle absorption can apply.
            (let
               -- the rest of sq after the leading sym (⋆Assoc f id β) and the
               -- (yet-to-be-split) cong (_⋆ β) (⋆IdR f ∙ sym (⋆IdL f)):
               tail = ⋆Assoc id f β ∙ cong (id ⋆_) p ∙ sym (⋆Assoc id α f')
               -- the post-step-1 right-hand side without the trailing G:
               rest_after = cong (_⋆ β) (sym (⋆IdL f)) ∙ tail
               -- helper: sym (cong (f ⋆_) (⋆IdL β)) ∙ sq ≡ rest_after
               helper : sym (cong (f ⋆_) (⋆IdL β)) ∙ sq ≡ rest_after
               helper =
                 -- Substitute cong-∙ inside sq, turning
                 --   cong (_⋆ β) (⋆IdR f ∙ sym (⋆IdL f))
                 -- into cong (_⋆ β) (⋆IdR f) ∙ cong (_⋆ β) (sym (⋆IdL f)).
                   cong (λ x → sym (cong (f ⋆_) (⋆IdL β)) ∙ sym (⋆Assoc f id β) ∙ x ∙ tail)
                        (cong-∙ (_⋆ β) (⋆IdR f) (sym (⋆IdL f)))
                 -- Now bracket the leading three factors and absorb to refl.
                 -- Right-assoc form: sym ∙ (sym ∙ ((C₁ ∙ C₂) ∙ tail))
                 -- Reassoc to (sym ∙ (sym ∙ C₁)) ∙ (C₂ ∙ tail), then collapse first.
                 -- Concretely the assoc/absorb-T pattern:
                 ∙ cong (sym (cong (f ⋆_) (⋆IdL β)) ∙_)
                       ( cong (sym (⋆Assoc f id β) ∙_)
                           ( sym (assoc (cong (_⋆ β) (⋆IdR f)) (cong (_⋆ β) (sym (⋆IdL f))) tail) )
                       ∙ assoc (sym (⋆Assoc f id β)) (cong (_⋆ β) (⋆IdR f)) (cong (_⋆ β) (sym (⋆IdL f)) ∙ tail) )
                 ∙ assoc (sym (cong (f ⋆_) (⋆IdL β)))
                          (sym (⋆Assoc f id β) ∙ cong (_⋆ β) (⋆IdR f))
                          (cong (_⋆ β) (sym (⋆IdL f)) ∙ tail)
                 ∙ cong (_∙ (cong (_⋆ β) (sym (⋆IdL f)) ∙ tail))
                        ( -- absorb-T: sym ∙ (sym ∙ cong (_⋆β) (⋆IdR f)) ≡ refl via triangle
                          cong (sym (cong (f ⋆_) (⋆IdL β)) ∙_)
                               ( cong (sym (⋆Assoc f id β) ∙_) (sym (triangle f β))
                               ∙ assoc (sym (⋆Assoc f id β)) (⋆Assoc f id β) (cong (f ⋆_) (⋆IdL β))
                               ∙ cong (_∙ cong (f ⋆_) (⋆IdL β)) (lCancel (⋆Assoc f id β))
                               ∙ sym (lUnit (cong (f ⋆_) (⋆IdL β))) )
                        ∙ lCancel (cong (f ⋆_) (⋆IdL β)))
                 ∙ sym (lUnit (cong (_⋆ β) (sym (⋆IdL f)) ∙ tail))
             in
                 assoc (sym (cong (f ⋆_) (⋆IdL β))) sq (cong (_⋆ f') (⋆IdL α))
               ∙ cong (_∙ cong (_⋆ f') (⋆IdL α)) helper
               ∙ sym (assoc (cong (_⋆ β) (sym (⋆IdL f))) tail (cong (_⋆ f') (⋆IdL α)))
               ∙ cong (cong (_⋆ β) (sym (⋆IdL f)) ∙_)
                   ( sym (assoc (⋆Assoc id f β)
                                (cong (id ⋆_) p ∙ sym (⋆Assoc id α f'))
                                (cong (_⋆ f') (⋆IdL α)))
                   ∙ cong (⋆Assoc id f β ∙_)
                       (sym (assoc (cong (id ⋆_) p)
                                   (sym (⋆Assoc id α f'))
                                   (cong (_⋆ f') (⋆IdL α))))))
          ⟩  -- step 1: cong-∙ split + triangle f β absorbs the leading triple
          cong (_⋆ β) (sym (⋆IdL f))
          ∙ ⋆Assoc id f β
          ∙ cong (id ⋆_) p
          ∙ sym (⋆Assoc id α f')
          ∙ cong (_⋆ f') (⋆IdL α)
        ≡⟨ assoc (cong (_⋆ β) (sym (⋆IdL f))) (⋆Assoc id f β)
                  (cong (id ⋆_) p ∙ sym (⋆Assoc id α f') ∙ cong (_⋆ f') (⋆IdL α))
         ∙ cong (_∙ (cong (id ⋆_) p ∙ sym (⋆Assoc id α f') ∙ cong (_⋆ f') (⋆IdL α)))
              ( cong (_∙ ⋆Assoc id f β)
                  (cong sym (idL-coh f β)
                  ∙ symDistr (⋆Assoc id f β) (⋆IdL (f ⋆ β)))
              ∙ sym (assoc (sym (⋆IdL (f ⋆ β))) (sym (⋆Assoc id f β)) (⋆Assoc id f β))
              ∙ cong (sym (⋆IdL (f ⋆ β)) ∙_) (lCancel (⋆Assoc id f β))
              ∙ sym (rUnit (sym (⋆IdL (f ⋆ β)))) )
         ⟩  -- step 2: idL-coh f β
          sym (⋆IdL (f ⋆ β))
          ∙ cong (id ⋆_) p
          ∙ sym (⋆Assoc id α f')
          ∙ cong (_⋆ f') (⋆IdL α)
        ≡⟨ cong (sym (⋆IdL (f ⋆ β)) ∙_)
             (cong (cong (id ⋆_) p ∙_)
               ( cong (sym (⋆Assoc id α f') ∙_) (idL-coh α f')
               ∙ assoc (sym (⋆Assoc id α f')) (⋆Assoc id α f') (⋆IdL (α ⋆ f'))
               ∙ cong (_∙ ⋆IdL (α ⋆ f')) (lCancel (⋆Assoc id α f'))
               ∙ sym (lUnit (⋆IdL (α ⋆ f'))) )) ⟩  -- step 3: idL-coh α f'
          sym (⋆IdL (f ⋆ β)) ∙ cong (id ⋆_) p ∙ ⋆IdL (α ⋆ f')
        ≡⟨ nat-IdL p ⟩
          p ∎

  MapIdR : {c d : Map} (F : Map[ c , d ])
    → compHomMap c d d F idHomMap ≡ F
  MapIdR {A , B , f} {A' , B' , f'} (α , β , p) =
    ΣPathP (⋆IdR α , ΣPathP (⋆IdR β , toPathP path-eq))
    where
      -- Naturality of ⋆IdR (dual to nat-IdL).
      nat-IdR : ∀ {x y} {a b : Hom[ x , y ]} (q : a ≡ b)
        → sym (⋆IdR a) ∙ cong (_⋆ id) q ∙ ⋆IdR b ≡ q
      nat-IdR {a = a} = J (λ b q → sym (⋆IdR a) ∙ cong (_⋆ id) q ∙ ⋆IdR b ≡ q)
        ( cong (sym (⋆IdR a) ∙_) (sym (lUnit (⋆IdR a)))
        ∙ lCancel (⋆IdR a) )

      sq : f ⋆ (β ⋆ id) ≡ (α ⋆ id) ⋆ f'
      sq = sym (⋆Assoc f β id)
           ∙ cong (_⋆ id) p
           ∙ ⋆Assoc α f' id
           ∙ cong (α ⋆_) (⋆IdR f' ∙ sym (⋆IdL f'))
           ∙ sym (⋆Assoc α id f')

      -- Path-algebra chain dual to MapIdL: uses `idR-coh` (at
      -- (f, β) and at (α, f')) and `triangle` (at (α, f')),
      -- ending in `nat-IdR p`.
      path-eq : transport (λ i → f ⋆ (⋆IdR β i) ≡ (⋆IdR α i) ⋆ f') sq ≡ p
      path-eq =
          transport (λ i → f ⋆ (⋆IdR β i) ≡ (⋆IdR α i) ⋆ f') sq
        ≡⟨ transport-≡-shape (cong (f ⋆_) (⋆IdR β)) (cong (_⋆ f') (⋆IdR α)) sq ⟩
          sym (cong (f ⋆_) (⋆IdR β)) ∙ sq ∙ cong (_⋆ f') (⋆IdR α)
        ≡⟨ -- step 1
            -- Helper: `sym (cong (f ⋆_) (⋆IdR β)) ∙ sq ≡ sym (⋆IdR (f⋆β)) ∙ rest_of_sq`.
            -- The assoc/cong/symDistr structure mirrors MapIdL step 2.
            (let
               rest_of_sq = cong (_⋆ id) p ∙ ⋆Assoc α f' id ∙ cong (α ⋆_) (⋆IdR f' ∙ sym (⋆IdL f')) ∙ sym (⋆Assoc α id f')
               helper : sym (cong (f ⋆_) (⋆IdR β)) ∙ sq ≡ sym (⋆IdR (f ⋆ β)) ∙ rest_of_sq
               helper = assoc (sym (cong (f ⋆_) (⋆IdR β))) (sym (⋆Assoc f β id)) rest_of_sq
                      ∙ cong (_∙ rest_of_sq)
                          ( sym (symDistr (⋆Assoc f β id) (cong (f ⋆_) (⋆IdR β)))
                          ∙ cong sym (idR-coh f β) )
             in
               assoc (sym (cong (f ⋆_) (⋆IdR β))) sq (cong (_⋆ f') (⋆IdR α))
             ∙ cong (_∙ cong (_⋆ f') (⋆IdR α)) helper
             ∙ sym (assoc (sym (⋆IdR (f ⋆ β))) rest_of_sq (cong (_⋆ f') (⋆IdR α)))
             ∙ cong (sym (⋆IdR (f ⋆ β)) ∙_)
                 ( sym (assoc (cong (_⋆ id) p)
                              (⋆Assoc α f' id ∙ cong (α ⋆_) (⋆IdR f' ∙ sym (⋆IdL f')) ∙ sym (⋆Assoc α id f'))
                              (cong (_⋆ f') (⋆IdR α)))
                 ∙ cong (cong (_⋆ id) p ∙_)
                     ( sym (assoc (⋆Assoc α f' id)
                                  (cong (α ⋆_) (⋆IdR f' ∙ sym (⋆IdL f')) ∙ sym (⋆Assoc α id f'))
                                  (cong (_⋆ f') (⋆IdR α)))
                     ∙ cong (⋆Assoc α f' id ∙_)
                         (sym (assoc (cong (α ⋆_) (⋆IdR f' ∙ sym (⋆IdL f')))
                                     (sym (⋆Assoc α id f'))
                                     (cong (_⋆ f') (⋆IdR α)))))))
          ⟩  -- step 1: idR-coh f β absorbs leading factors
          sym (⋆IdR (f ⋆ β))
          ∙ cong (_⋆ id) p
          ∙ ⋆Assoc α f' id
          ∙ cong (α ⋆_) (⋆IdR f' ∙ sym (⋆IdL f'))
          ∙ sym (⋆Assoc α id f')
          ∙ cong (_⋆ f') (⋆IdR α)
        ≡⟨ -- step 2: collapse the tail `⋆Assoc α f' id ∙ cong (α ⋆_) … ∙ sym (⋆Assoc α id f') ∙ cong (_⋆ f') (⋆IdR α)`
            -- to `⋆IdR (α ⋆ f')`.  Uses cong-∙ split + idR-coh α f' + triangle α f'.
            cong (sym (⋆IdR (f ⋆ β)) ∙_)
                 (cong (cong (_⋆ id) p ∙_)
                    (let
                       tail-collapse :
                         cong (α ⋆_) (sym (⋆IdL f')) ∙ (sym (⋆Assoc α id f') ∙ cong (_⋆ f') (⋆IdR α)) ≡ refl
                       tail-collapse =
                           cong (cong (α ⋆_) (sym (⋆IdL f')) ∙_)
                             ( cong (sym (⋆Assoc α id f') ∙_) (sym (triangle α f'))
                             ∙ assoc (sym (⋆Assoc α id f')) (⋆Assoc α id f') (cong (α ⋆_) (⋆IdL f'))
                             ∙ cong (_∙ cong (α ⋆_) (⋆IdL f')) (lCancel (⋆Assoc α id f'))
                             ∙ sym (lUnit (cong (α ⋆_) (⋆IdL f'))) )
                         ∙ sym (cong-∙ (α ⋆_) (sym (⋆IdL f')) (⋆IdL f'))
                         ∙ cong (cong (α ⋆_)) (lCancel (⋆IdL f'))
                     in
                         cong (⋆Assoc α f' id ∙_)
                              (cong (_∙ (sym (⋆Assoc α id f') ∙ cong (_⋆ f') (⋆IdR α)))
                                    (cong-∙ (α ⋆_) (⋆IdR f') (sym (⋆IdL f'))))
                       ∙ cong (⋆Assoc α f' id ∙_)
                              (sym (assoc (cong (α ⋆_) (⋆IdR f'))
                                          (cong (α ⋆_) (sym (⋆IdL f')))
                                          (sym (⋆Assoc α id f') ∙ cong (_⋆ f') (⋆IdR α))))
                       ∙ assoc (⋆Assoc α f' id) (cong (α ⋆_) (⋆IdR f'))
                                (cong (α ⋆_) (sym (⋆IdL f')) ∙ (sym (⋆Assoc α id f') ∙ cong (_⋆ f') (⋆IdR α)))
                       ∙ cong (_∙ (cong (α ⋆_) (sym (⋆IdL f')) ∙ (sym (⋆Assoc α id f') ∙ cong (_⋆ f') (⋆IdR α))))
                              (idR-coh α f')
                       ∙ cong (⋆IdR (α ⋆ f') ∙_) tail-collapse
                       ∙ sym (rUnit (⋆IdR (α ⋆ f')))))
          ⟩  -- step 2: triangle/idR-coh α f' collapses the tail
          sym (⋆IdR (f ⋆ β)) ∙ cong (_⋆ id) p ∙ ⋆IdR (α ⋆ f')
        ≡⟨ nat-IdR p ⟩
          p ∎

  -- Map(C) as a wild category
  𝑴𝑨𝑷 : WildCat (ℓ-max ℓ₁ ℓ₂) ℓ₂
  𝑴𝑨𝑷 .WildCat.ob = Map
  𝑴𝑨𝑷 .WildCat.Hom[_,_] = Map[_,_]
  𝑴𝑨𝑷 .WildCat.id = idHomMap
  𝑴𝑨𝑷 .WildCat._⋆_ {x = x} {y} {z} = compHomMap x y z
  𝑴𝑨𝑷 .WildCat.⋆IdL = MapIdL
  𝑴𝑨𝑷 .WildCat.⋆IdR = MapIdR
  𝑴𝑨𝑷 .WildCat.⋆Assoc = assocMap
