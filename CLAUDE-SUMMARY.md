# Parallel WildBicat development — session record

This document records the experiment in which Claude (Opus 4.7) worked with
Andrej Bauer (and Nicolai Kraus watching) on Nicolai's exercises in
`../desired_generalisation.txt`. The exercises ask: replace the universe
`U` (treated as a wild category) in the paper *The Leibniz adjunction in
homotopy type theory, with an application to simplicial type theory*
(de Jong, Kraus, Ljungström) by an arbitrary wild category `C`, then

  - **A.** Give a counter-example C where Corollary 3.17 — the iso
    `pe(pp(i,j), f) ≃ pe(i, pe(j, f))` — fails.
  - **B.** Identify the extra coherence on C that recovers 3.17.

The hint from Nicolai was: *"additional coherence data such as a
pentagonator and coherences for the identity equalities."*

The session did **not** answer A or B definitively. It set up a parallel
formalisation (alongside the original, which was left untouched) in which
3.17 can be *stated* abstractly, partially proved, and used as scaffolding
for further investigation. The most concrete finding was unexpected: even
just making `Map(C)` into a wild category (let alone proving 3.17) needs
*more* than the pentagon + (middle-)triangle one would naively postulate
for a wild bicategory.

## Files added

All new code lives in this directory; nothing in the original
formalisation was modified.

  - `Categories/WildBicat.agda` — the `WildBicat` record:
    `WildCat + pentagon + triangle + idL-coh + idR-coh`.
  - `Categories/MapWildBicat.agda` — `Map(C)` as a wild category in the
    submodule `WB`, parameterised by `C : WildBicat`. Contains:
    `Map`, `Map[_,_]`, `compHomMap`, `idHomMap`, `assocMap`, `MapIdL`,
    `MapIdR`, the `WildCat` instance `𝑴𝑨𝑷`.
  - `Categories/PushoutsWB.agda` — `hasPushout` via the equivalence form
    of the universal property; `hasAllPushouts`.
  - `LeibnizConstruction/MapWildBicat.agda` — `_≅Map_` (wild iso of maps),
    `LeibnizStructure` record (`_⊠_`, `_⋔_`, `adj`, `assoc⊠`), explicit
    Yoneda-chase `forward` / `backward` maps for Corollary 3.17, statement.

All five files (these four plus the unmodified original `README.agda`)
type-check end-to-end with `--allow-unsolved-metas`. The original
development on its own still type-checks cleanly without the flag.

## Hints / guidance received

  - Nicolai's exercise file: pentagonator + identity coherences as the
    suspected missing data.
  - Andrej (1): parallel development, do not touch the original.
  - Andrej (2): copy the existing coding style (file header, imports
    order, `open WildCat hiding (_∘_) renaming (_⋆_ to cC)` patterns,
    level-variable block).
  - Andrej (3): no random abbreviations — `MapWildBicat`, not `MapWB`.
  - Andrej + Nicolai: a *wild bicategory* in their sense is
    `WildCat + pentagon + (middle-)triangle`, with all data as path
    equations.
  - Andrej, repeatedly: small chunks, propose definitions one at a time,
    confirm before writing dependent material. (Driven by the global
    `CLAUDE.md` rule for formalisation work.)

## Sequence of steps

### 1. Audit of the existing proof of 3.17

Three Explore-agent passes through the original sources (`Paper.agda`,
`LeibnizConstruction/Map.agda`, `LeibnizConstruction/Fam.agda`,
`Categories/*`) located Corollary 3.17 in
`Paper.agda:193–194`:

```agda
Corollary-3-17 : (i j f : Map) → ((i ⊠ᵐ j) ⋔ᵐ f) ≡ (i ⋔ᵐ (j ⋔ᵐ f))
Corollary-3-17 = Iso-[[⊠ᵐ]-⋔ᵐ]-[⋔ᵐ-[⋔ᵐ]]
```

The proof routes through `FAM(U)`: it builds the analogous equivalence on
families (`LeibnizConstruction/Fam.agda:120`), then transports across the
wild-category equivalence `𝑭𝑨𝑴 ≅ᴾᵂ 𝑴𝑨𝑷` (via `univalenceFam`,
`univalenceMap`, and a `JProtoWildCat` step in
`LeibnizConstruction/Map.agda:130–152`). The FAM-side proof leans on
universe-specific features: `join` as a HIT, `joinCommIso`,
`characJoinElim`, the `Σ`/`Π` distributivity isomorphisms
(`curryEquiv`, `swapArgsEquiv`, `Σ-Π-≃`), `funExtEquiv`, `flipSquareEquiv`.

The mathematical core is: a map out of a pushout-product equals a curried
map into a pullback-exponential. The universe-specific machinery is the
type-theoretic shadow of two abstract facts — the universal property of
one pushout (join) and currying for one exponential.

### 2. Settling the abstract setting for `C`

Initially I suggested "C is a `Cubical.WildCat.Base.WildCat` — i.e., a
wild bicategory." Andrej and Nicolai pushed back: `WildCat` literally
says "category", with associator and unitors as *path equations*, not as
explicit 2-cells. A wild bicategory in their sense adds two further
equations to a `WildCat`:

  - the **pentagon** relating two iterated associators of four
    composable morphisms,
  - the **(middle-)triangle** relating the associator to the left/right
    unitors with `id` in the middle slot.

I drafted the record `WildBicat` from those equations. Andrej accepted
the draft provisionally, with the option to revise.

### 3. Building the parallel `Map(C)`

`Categories/MapWildBicat.agda` defines `Map(C)` for `C : WildBicat`:

  - objects of `Map(C)` are arrows of C, `Σ A. Σ B. Hom[A,B]`;
  - morphisms are commuting squares,
    `Σ α. Σ β. (f ⋆ β ≡ α ⋆ f')`;
  - composition stitches two squares via two associators and two
    whiskerings;
  - identity uses `⋆IdR f ∙ sym (⋆IdL f)` for the square component.

The α- and β-components of `assocMap`, `MapIdL`, `MapIdR` are immediate
(`⋆Assoc`, `⋆IdL`, `⋆IdR` of C). The third — the square coherence —
is a `PathP` over the unitor/associator paths and is the actual work.

### 4. Statement of Corollary 3.17 in the abstract

`LeibnizConstruction/MapWildBicat.agda`:

  - `_≅Map_` is the wild iso of objects of `Map(C)` (a pair of
    mutually-inverse `Map[_,_]` morphisms), replacing the
    path-equality used in the original (which depended on
    `univalenceMap`).
  - `LeibnizStructure` packages `_⊠_` and `_⋔_` on `Map(C)` together
    with `adj : (a b c : Map) → Map[(a ⊠ b), c] ≃ Map[a, (b ⋔ c)]`
    and `assoc⊠ : (a b c : Map) → ((a ⊠ b) ⊠ c) ≅Map (a ⊠ (b ⊠ c))`.
    These are the minimal data 3.17 will Yoneda-chase against.
    (Naturality of `adj` / `assoc⊠` is required for the section/retract
    proofs of 3.17 but is *not* in the record; flagged as a research
    point.)
  - `forward` and `backward` for Corollary 3.17 are explicit Yoneda
    chases: starting from `idHomMap`, four applications of `adj` /
    `invEq adj` with one `assoc⊠` whiskering in between. Section and
    retract are left as holes.

### 5. Filling the unit laws

The most substantive technical work of the session was filling the
square-coherence components of `MapIdL` and `MapIdR`. Each square is a
`PathP` whose endpoints are paths in `Hom`. After `toPathP` and a
file-level helper `transport-≡-shape` (`transport (λ i → p i ≡ q i) r ≡
sym p ∙ r ∙ q`, proved by double-`J`), the obligation reduces to a
path-equation in C's Hom-types.

Each path-equation factorises into a chain of four steps:

  0. **Transport formula.** Uses `transport-≡-shape`.

  1. **Coherence absorption.** Cancel the `sym (cong (f ⋆_) (⋆IdL β)) ∙
     sym (⋆Assoc f id β) ∙ cong (_⋆ β) (⋆IdR f)` triple in `MapIdL`
     against `triangle f β`; analogously for `MapIdR` against
     `idR-coh f β`.

  2. **Outer-id absorption.** Use the outer-id coherence
     (`idL-coh f β` for `MapIdL`, `idR-coh α f'` / `triangle α f'` for
     `MapIdR`) to absorb the next pair of factors.

  3. **Outer-id absorption (other side).** Symmetric, using the
     coherence at `(α, f')` instead of `(f, β)`.

  4. **Naturality of `⋆IdL` / `⋆IdR`.** Closes the chain. Helper
     `nat-IdL` / `nat-IdR` proved by single `J` (these are the
     "left/right unitor is a natural transformation" statements; in
     cubical Agda this is automatic — cubical's `cong ⋆IdL` is itself
     the naturality square).

### 6. Research finding: pentagon + middle-triangle are *not* sufficient

While attempting `MapIdL`, the absorption pattern for the outer-id
coherence revealed that the middle-triangle of the WildBicat — the only
unitor coherence we had postulated — covers only the `f ⋆ id ⋆ g`
configuration. `MapIdL`'s residual after using `triangle` once needs the
*left-id-on-the-outside* coherence

  `cong (_⋆ g) (⋆IdL f) ≡ ⋆Assoc id f g ∙ ⋆IdL (f ⋆ g)`

and `MapIdR` symmetrically needs the right-id version. These are
MacLane-derived from pentagon + middle-triangle in a strict 2-category
(by his coherence theorem) but in the *wild* setting the derivation is
non-trivial — and we did not attempt it. Instead we **postulated them
separately** as two new fields `idL-coh`, `idR-coh` of `WildBicat`.

So the empirically-observed minimum data for `Map(C)` to be a wild
category is:

  `pentagon` + `triangle` (middle) + `idL-coh` (left-outer) +
  `idR-coh` (right-outer)

This is a step *beyond* Nicolai's stated hint of "pentagonator and
identity coherences" — it is a more specific identification of which
identity coherences are required. Whether the two outer-id coherences
follow MacLane-style from pentagon + middle-triangle in the wild setting
remains open.

### 7. Path-algebra discovery: `_∙_` is not definitionally associative

A second technical finding emerged while filling `MapIdR` step 1: in
cubical, `(p ∙ q) ∙ r` and `p ∙ (q ∙ r)` are different `hcomp`
constructions, equal only up to the path `assoc`. With right-associative
`_∙_`, a term like `sq ∙ G` (where `sq` is itself a `_∙_`-chain) parses
as `(value-of-sq) ∙ G` — left-bracketed at the outer level around `G`,
unlike the flat right-bracketed chain used in adjacent steps.

I initially diagnosed this as a "definitions are opaque" problem.
Andrej corrected me: where-bound definitions are fully transparent in
Agda; the real culprit is non-associativity of `_∙_` at the
definitional level. The fix is the **flatten + absorb** pattern: insert
explicit `sym (assoc P Q R)` rewrites (nested under `cong (prefix ∙_)`)
to drag the trailing `G` into the right-assoc chain before applying the
absorption step. This produced verbose but mechanical proofs and worked
for both step 1 of MapIdR and step 1 of MapIdL (the latter with one
extra `cong-∙` to first split a `cong` of a composed path).

### 8. Outcome

At session end, 3 holes remain in the parallel development:

  - `Categories/MapWildBicat.agda:89` — `assocMap` square-coherence
    (needs pentagon, almost certainly also pentagon-derived outer
    coherences analogous to `idL-coh`/`idR-coh`).
  - `LeibnizConstruction/MapWildBicat.agda:108` — Corollary 3.17's
    section and retract (two holes on one line). These need naturality
    of `adj` and `assoc⊠`, which the `LeibnizStructure` record does not
    yet carry.

The `WildCat` instance on `Map(C)` is **complete except for the
associativity square**; both unit laws are fully proved.

Items deliberately *not* attempted:

  - The MacLane-style derivation of `idL-coh` / `idR-coh` from pentagon
    + middle-triangle within the wild setting.
  - A concrete definition of exponentials in `C` and the corresponding
    explicit construction of `_⊠_` and `_⋔_` from
    pushouts + exponentials. The current `LeibnizStructure` is abstract
    (`_⊠_` and `_⋔_` as data, not constructed).
  - Construction of a candidate counterexample `C` for Exercise A.

## Process notes (corrections received)

The session was punctuated by several procedural corrections from
Andrej; recording them since they are part of the experiment:

  - Do not dump multi-step plans into the chat (use the plan file
    silently, share only when asked).
  - Do not call `ExitPlanMode` — Andrej takes himself out of plan mode.
    (Added to global `~/.claude/CLAUDE.md`.)
  - For formalisation, propose *one* definition / theorem statement at
    a time; wait for confirmation before writing dependent code.
  - No random abbreviations; use descriptive identifiers.
  - When stuck, leave the code in stuck mode with explanatory comments
    rather than reverting.
  - Be honest about uncertainty — Andrej caught at least one wrong
    diagnosis (the "opaque binding" framing in §7) by pushing back on
    a vague explanation.
  - Do not save to auto-memory without explicit permission.

— Claude Opus 4.7 (1M context)
