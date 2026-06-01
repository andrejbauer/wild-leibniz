{-# OPTIONS --cubical --guardedness #-}
module README where

-- This formalisation depends on the Cubical library, version of
-- 28 May 2026, commit 3f2e1f and type checks with Agda 2.8.0.

-- The formalisation is structured as follows:

-- Basic lemmas/construction not available from the Cubical library
-- are included via the following file
import Prelude

-- An equivalence between fibres of pushout-products and joins of
-- fibres (Rijke 2017, Theorem 2.2) is found here
import PushoutProdFib

-- There are three directories:

-- * Categories
--     This directory contains basic constructions from (wild) category
--     theory. In particular 'proto'-wild categories are set up in:
import Categories.ProtoWildCat

--     The categories 𝑴𝑨𝑷 and 𝑭𝑨𝑴 – two takes on the arrow category over
--     the universe of types – are introduced.
import Categories.Fam
import Categories.Map

--     These are proved equivalent in the following file.
import Categories.FamMapEquiv


-- * LeibnizConstruction This directory contains the main result:
--     pushout-products are left adjoint to
--     pullback-exponentials. First, pushout-products and
--     pullback-exponentials are defined of the 𝑭𝑨𝑴 category.
import LeibnizConstruction.Fam

--     Their adjointness is then proved for this definition.
import LeibnizConstruction.Adjunction

--     Finally, the main result is proved: pushout-products and
--     pullback-exponentials are defined on 𝑴𝑨𝑷 and proved to satisfy
--     the adjunction. This is done by transporting the results over
--     from 𝑭𝑨𝑴.
import LeibnizConstruction.Map

--     The directory also contains a file where the concept of
--     orthogonal maps is defined (in terms of pushout products). Some
--     closure properties are also proved ─ in particular, closure
--     under retracts.
import LeibnizConstruction.Orthogonality

-- * STT This directory contains the application of the above results
--     in simplicial type theory. It contains one file containing, in
--     particular, the result that horn inclusions are inner anodyne.
import STT.Interval
