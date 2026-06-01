{-# OPTIONS --cubical --guardedness #-}
{-
This file acts an interface between the paper and the formalisation.
It has terms for each numbered environment of the paper.

Note: for the sake of presentation we avoid having to juggle with
universe levels and instantiate most constructions here at universe
level zero.

-}

module Paper where

-- Library imports
open import Prelude renaming (Const to const)
open import Categories.Fam renaming (Fam to fam ; 𝑭𝑨𝑴 to famCat)
open import Categories.Map renaming (Map to map ; 𝑴𝑨𝑷 to mapCat)
open import Categories.FamMapEquiv as fm≃mp
open import Categories.ProtoWildCat

open import PushoutProdFib as Rijke

open import LeibnizConstruction.Fam
open import LeibnizConstruction.Map
open import LeibnizConstruction.Adjunction
open import LeibnizConstruction.Orthogonality

open import STT.Interval

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function hiding (const)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as Empty renaming (⊥ to ∅)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Inductive hiding (eq)

open import Cubical.HITs.Pushout.PushoutProduct renaming (_×̂_ to _×^_)
open import Cubical.HITs.Join hiding (join) renaming (joinPushout to join)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C X Y : Type

π₁ : {A : Type ℓ} {B : A → Type ℓ'} → Σ A B → A
π₁ = fst
π₂ : {A : Type ℓ} {B : A → Type ℓ'} → (a : Σ A B) → B (fst a)
π₂ = snd


----- 3. The Leibniz Adjunction for Types -----

Definition-3-1 : (A : WildCat ℓ₁ ℓ₂) (B : WildCat ℓ₃ ℓ₄)
               → WildFunctor A B → Type _
Definition-3-1 A B = isWildEquiv
  where
  -- in practice, as mentioned in Remark 3.2, we often use the
  -- identical notion of equivalence between underlying proto wild categories
  protoEquiv = isEquivProtoWildFunctor
  -- the type of such equivalences coincide with the usual definition
  -- of wild categories
  equivDefsCoincide : (A ≃ᵂ B) -- ← Type of equivalences between A and B
                    ≡ (⌈ A ⌉ ≅ᴾᵂ ⌈ B ⌉) -- ← Type of equivalences between their
                                      -- underlying wild categories
  equivDefsCoincide = ua Equiv-≃ᵂ-≅ᴾᵂ

-- Proto-wild categories and univalence for them
Remark-3-2 : Type₁
           × ({A B : ProtoWildCat ℓ-zero ℓ-zero} → (A ≡ B) ≃ (A ≅ᴾᵂ B))
Remark-3-2 .fst = ProtoWildCat ℓ-zero ℓ-zero
Remark-3-2 .snd = univalenceProtoWildCat
  where
  WCat = WildCat ℓ-zero ℓ-zero
  PWCat = ProtoWildCat ℓ-zero ℓ-zero

  -- More specifically: we can transport properties of wild categories
  -- as long as they do not mention equations (i.e. mention only the
  -- underlying proto-wild categorical structure
  transportWildCatProperty : (P : PWCat → Type) (C D : WCat)
    → C ≃ᵂ D → P ⌈ C ⌉ → P ⌈ D ⌉
  transportWildCatProperty P C D e p =
    subst P (invEq univalenceProtoWildCat (≃ᵂ→≅ᴾᵂ e)) p

Map = map ℓ-zero
Fam = fam ℓ-zero

-- Arrow category
𝑴𝑨𝑷 = mapCat ℓ-zero

3-1-1 : WildCat (ℓ-suc ℓ-zero) ℓ-zero
3-1-1 = 𝑴𝑨𝑷

pushout-product : Map → Map → Map
pushout-product f g = f ⊠ᵐ g
dagger = pushout-product

NB₁ : (f g : Map) → (f ⊠ᵐ g)⃗ ≡ (f ⃗) ×^ (g ⃗)
NB₁ f g = refl

pullback-hom : Map → Map → Map
pullback-hom f g = f ⋔ᵐ g
double-dagger = pullback-hom

NB₂ : (f g : Map) → (f ⋔ᵐ g)⃗ ≡ (f ⃗) ⋔ (g ⃗)
NB₂ f g = refl

-- Category of families
𝑭𝑨𝑴 = famCat ℓ-zero

3-1-2 : WildCat (ℓ-suc ℓ-zero) ℓ-zero
3-1-2 = 𝑭𝑨𝑴

-- Same two categories as 'proto wild categories' (wild categories
-- without equation)
𝑭𝑨𝑴₋ = ⌈ 𝑭𝑨𝑴 ⌉
𝑴𝑨𝑷₋ = ⌈ 𝑴𝑨𝑷 ⌉

χ : Map → Fam
χ = Map→Fam

χ⁻¹ : Fam → Map
χ⁻¹ = Fam→Map

Proposition-3-3 : ⌈ 𝑭𝑨𝑴 ⌉ ≅ᴾᵂ ⌈ 𝑴𝑨𝑷 ⌉
Proposition-3-3 = 𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷

Proposition-3-4 : {f : A → B} {g : X → Y} (b : B) (y : Y)
  → fiber (f ×^ g) (b , y) ≃ join (fiber f b) (fiber g y)
Proposition-3-4 = Rijke.Fib×^≃JoinFib

Definition-3-5 : Fam → Fam → Fam
Definition-3-5 = _⊠ᶠ_

Proposition-3-6 : ({f g : Map} → χ (f ⊠ᵐ g) ≡ (χ f ⊠ᶠ χ g))
                × ({A⸴B X⸴Y : Fam} → χ⁻¹ (A⸴B ⊠ᶠ X⸴Y) ≡ (χ⁻¹ A⸴B ⊠ᵐ χ⁻¹ X⸴Y))
Proposition-3-6 .fst = Map→FamPres⊠≡
Proposition-3-6 .snd =
  cong χ⁻¹ (cong₂ _⊠ᶠ_ (sym (invEq univalenceFam (Fam→Map→Fam _)))
                      (sym (invEq univalenceFam (Fam→Map→Fam _))))
  ∙ Fam→MapPres⊠≡

Proposition-3-7 : hasBiProtoFunctorStructure 𝑭𝑨𝑴₋ 𝑭𝑨𝑴₋ 𝑭𝑨𝑴₋ _⊠ᶠ_
Proposition-3-7 = hasBiProtoFunctorStructure⊠ᶠ

Definition-3-8 : (f : A → B) → Type
Definition-3-8 = const

Lemma-3-9 : (Σ[ f ∈ (A → B) ] (const f)) ≃ B
Lemma-3-9 = isoToEquiv TotConstIso

Definition-3-10 : Fam → Fam → Fam
Definition-3-10 = _⋔ᶠ_

Lemma-3-11 : {A⹁B X⹁Y : Fam} → TotFam (A⹁B ⋔ᶠ X⹁Y) ≃ (π₁ A⹁B → TotFam X⹁Y)
Lemma-3-11 = isoToEquiv Iso-TotFam⋔ᶠ-[BaseFam→TotFam]

Proposition-3-12 : ({f g : Map} → χ (f ⋔ᵐ g) ≡ (χ f ⋔ᶠ χ g))
                 × ({A⹁B X⹁Y : Fam} → χ⁻¹ (A⹁B ⋔ᶠ X⹁Y) ≡ (χ⁻¹ A⹁B ⋔ᵐ χ⁻¹ X⹁Y))
Proposition-3-12 .fst {f = f} {g} =
    cong χ (cong₂ _⋔ᵐ_ (sym (invEq univalenceMap (Map→Fam→Map f)))
                       (sym (invEq (univalenceMap {B = g}) (Map→Fam→Map g)))
          ∙ Fam→MapPres⋔≡ {C = χ f} {χ g})
  ∙ (invEq univalenceFam (Fam→Map→Fam (χ f ⋔ᶠ χ g)))
Proposition-3-12 .snd = sym Fam→MapPres⋔≡

Proposition-3-13 : hasBiProtoFunctorStructure (𝑭𝑨𝑴₋ ^opᵖʳ) 𝑭𝑨𝑴₋ 𝑭𝑨𝑴₋ _⋔ᶠ_
Proposition-3-13 = hasBiProtoFunctorStructure⋔ᶠ

Lemma-3-14 : (f g h : Map)
           → ((f ⊠ᵐ g) ⊠ᵐ h ≡ f ⊠ᵐ (g ⊠ᵐ h))
           × (f ⊠ᵐ g ≡ g ⊠ᵐ f)
Lemma-3-14 f g h = (assoc⊠ᵐ f g h , invEq univalenceMap (comm⊠ᵐ f g))

Lemma-3-15 : ((join A B → C) ≃ (Σ[ f ∈ (A → C) ] (B → const f)))
           × ((join A B → C) ≃ (Σ[ g ∈ (B → C) ] (A → const g)))
Lemma-3-15 .fst = JoinFun≃ConstL
Lemma-3-15 .snd = JoinFun≃ConstR

Theorem-3-16 : areAdjointBiFunctors 𝑭𝑨𝑴₋ _⊠ᶠ_ _⋔ᶠ_
Theorem-3-16 = areAdjointBiFunctors-⊠ᶠ-⋔ᶠ

Corollary-3-17 : (i j f : Map) → ((i ⊠ᵐ j) ⋔ᵐ f) ≡ (i ⋔ᵐ (j ⋔ᵐ f))
Corollary-3-17 = Iso-[[⊠ᵐ]-⋔ᵐ]-[⋔ᵐ-[⋔ᵐ]]

----- 4. Application: Orthogonality and Simplicial Type Theory -----

Definition-4-1 : _
Definition-4-1 = Fill

Definition-4-2 : _
Definition-4-2 = _⊥_

Lemma-4-3 : (i f : Map) → (i ⊥ f) ↔ isEquivMap (i ⋔ᵐ f)
Lemma-4-3 = ⊥↔isEquiv⋔

Lemma-4-4 : (e g : Map) → isEquivMap e → (e ⊥ g) × (g ⊥ e)
Lemma-4-4 e g eq .fst = ⊥Equiv e g eq
Lemma-4-4 e g eq .snd = Equiv⊥ e g eq

Lemma-4-5 : (i j f : Map) → i ⊥ f → (i ⊠ᵐ j) ⊥ f
Lemma-4-5 = ⊠⊥

Lemma-4-6 : (i j f : Map) → retractMap j i → i ⊥ f → j ⊥ f
Lemma-4-6 = retract⊥


--- 4.2 Simplicial Type Theory ---

Assumption : Interval ℓ-zero ≡ (Σ[ I ∈ Type ℓ-zero ] BoundedDistLatticeStr I)
Assumption = refl

module STT (I : Interval ℓ-zero) where -- we assume the existence of an interval type
  open HornLifting I

  Definition-4-8 : (Type → Type) × (Map → Type₁)
  Definition-4-8 .fst = isSegal
  Definition-4-8 .snd = isInnerAnodyne

  Theorem-4-9 : (n k : ℕ) (p : 0 <ᵗ k) (q : k <ᵗ n)
              → isInnerAnodyne ⦅ ƛ n (k , <ᵗ-trans-suc {k} q) ⦆
  Theorem-4-9 n k p q = isInnerAnodyneHornInclusion n 𝕜 p' q'
   where
    𝕜 : Fin (suc n)
    𝕜 = (k , <ᵗ-trans-suc {k} q)
    p' : ¬ fzero ≡ 𝕜
    p' h = Empty.rec (¬m<ᵗm {k} (subst (_<ᵗ k) (cong fst h) p))
    q' : ¬ flast ≡ 𝕜
    q' h = Empty.rec (¬m<ᵗm {k} (subst (k <ᵗ_) (cong fst h) q))

  Remark-4-11 : (n k : ℕ) (p : 0 <ᵗ k) (q : k <ᵗ n)
              → isInnerAnodyneFib ⦅ ƛ n (k , <ᵗ-trans-suc {k} q) ⦆
  Remark-4-11 n k p q = isInnerAnodyneFibHornInclusion n 𝕜 p' q'
   where
    𝕜 : Fin (suc n)
    𝕜 = (k , <ᵗ-trans-suc {k} q)
    p' : ¬ fzero ≡ 𝕜
    p' h = Empty.rec (¬m<ᵗm {k} (subst (_<ᵗ k) (cong fst h) p))
    q' : ¬ flast ≡ 𝕜
    q' h = Empty.rec (¬m<ᵗm {k} (subst (k <ᵗ_) (cong fst h) q))
