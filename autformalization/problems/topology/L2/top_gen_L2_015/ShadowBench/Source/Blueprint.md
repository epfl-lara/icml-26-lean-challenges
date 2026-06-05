# Formalization Blueprint: `topology/L2/top_gen_L2_015`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization for the normalized Moore complex definition and the source theorem named `normalizedMooreComplex_objD`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target is included in the project root module and in ordinary `lake build` coverage.

## Import Plan

```lean
import Mathlib.AlgebraicTopology.MooreComplex
```

The target Lean file uses this direct import because Mathlib already contains the normalized Moore complex construction in `Mathlib.AlgebraicTopology.MooreComplex`. That module directly provides `AlgebraicTopology.normalizedMooreComplex`, `AlgebraicTopology.NormalizedMooreComplex.objX`, `objD`, `map`, and the chain-complex proof obligations.

## Suggested Search Modules

These are search hints for future proof turns only, not required direct imports in `Main.lean` unless a later verified proof edit needs them.

- `Mathlib.Algebra.Homology.HomologicalComplex`
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`
- `Mathlib.CategoryTheory.Abelian.Basic`
- `Mathlib.AlgebraicTopology.DoldKan.Normalized`

## Search Log

- `lean_search "normalized Moore complex simplicial object"` found `AlgebraicTopology.normalizedMooreComplex` and the implementation module `Mathlib.AlgebraicTopology.MooreComplex`.
- The Mathlib construction defines the degree subobjects with `NormalizedMooreComplex.objX`, differentials with `NormalizedMooreComplex.objD`, proves `d_squared`, defines object complexes with `NormalizedMooreComplex.obj`, defines morphism maps with `NormalizedMooreComplex.map`, and packages these as the functor `AlgebraicTopology.normalizedMooreComplex`.
- Candidate skeletons 1--4 all suggested the required names but left the definition as `sorry` and weakened the theorem to `true`; they were used only as name/import hints, not as source-faithful theorem statements.

## Required Names

- `normalizedMooreComplex`
- `normalizedMooreComplex_objD`

## Detected Theorem-Like Blocks

1. `line-17` (definition, lines 17--30) - normalizedMooreComplex
2. `line-31` (theorem, lines 31--33; proof lines 33--51) - normalizedMooreComplex_objD

## Source Map

- line-17 -> `normalizedMooreComplex` (`docs/source.tex` lines 17--30)
- line-31 -> `normalizedMooreComplex_objD` (`docs/source.tex` theorem lines 31--33; proof lines 33--51)

## Source inventory

- label: line-17
  source_id: line-17
  kind: definition
  source_title: normalizedMooreComplex
  planned_lean_declaration: normalizedMooreComplex
  source_locator: docs/source.tex lines 17--30
  details: Full statement-fidelity details and implementation notes are in the matching source statement inventory entry below.
- label: line-31
  source_id: line-31
  kind: theorem
  source_title: normalizedMooreComplex_objD
  planned_lean_declaration: normalizedMooreComplex_objD
  source_locator: docs/source.tex theorem lines 31--33, proof lines 33--51
  details: Full statement-fidelity details, complete source proof text, and prover notes are in the matching source statement inventory entry below.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`.
- Source label: `line-17`.
- Source inventory label: `line-17`.
- Source block label: `line-17`.
- Preflight label: `line-17`.
- Source kind: definition.
- Source locator: `docs/source.tex`, lines 17--30.
- Planned Lean declaration: `normalizedMooreComplex`.
- Lean declaration kind: `def`.
- Lean statement:

```lean
def normalizedMooreComplex (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ :=
  AlgebraicTopology.normalizedMooreComplex C
```

- Skeleton candidate used: the common skeleton shape suggested the required name and basic imports, but its `def ... := sorry` construction was not adopted. The final statement is shaped by the source and by Mathlib's existing construction.
- Dependencies: `Mathlib.AlgebraicTopology.MooreComplex`; internally this relies on `AlgebraicTopology.NormalizedMooreComplex.objX`, `AlgebraicTopology.NormalizedMooreComplex.objD`, `AlgebraicTopology.NormalizedMooreComplex.d_squared`, `AlgebraicTopology.NormalizedMooreComplex.obj`, `AlgebraicTopology.NormalizedMooreComplex.map`, and `AlgebraicTopology.normalizedMooreComplex`.
- Complete source statement: Let $C$ be an abelian category. We define the normalized Moore complex to be a functor
  $N_\bullet : \mathbf{sC} \to \mathbf{Ch}_{\ge 0}(C)$, $X \mapsto N_\bullet(X)$, from simplicial objects of $C$ to non-negative chain complexes in $C$, where $N_0(X)=X_0$ and, for $n>0$, $N_n(X)=\bigcap_{i=1}^n \ker(d_i^n : X_n \to X_{n-1})$. The differentials are $d_n=d_0^n|_{N_n(X)} : N_n(X) \to N_{n-1}(X)$. For a morphism $f:X\to Y$ in simplicial objects, $N_\bullet(f)$ is defined degreewise by restricting $f_n$ to $N_n(X)\to N_n(Y)$.
- Source qualifiers:
  - Mathematical object class: an abelian category `C` with a category structure.
  - Domain: the category of simplicial objects in `C`, formalized as `SimplicialObject C`.
  - Codomain: non-negative chain complexes in `C`, formalized as `ChainComplex C ℕ`.
  - Object formula: degree zero is the full/top subobject of `X_0`; positive degree is the intersection of kernels of positive face maps.
  - Differential: induced by the zero-th face map, restricted/factored through the normalized subobjects.
  - Morphism formula: component maps are restrictions/factorizations of the simplicial morphism components.
- Lean coverage: full, modulo Mathlib's standard representation of intersections of kernels as `Subobject` infima and non-negative chain complexes as `ChainComplex C ℕ`. The definition is an alias to Mathlib's certified normalized Moore complex functor.
- Scope changes: no mathematical weakening intended. Representation changes are the use of `Subobject` representatives, `op ⦋n⦌` for simplex indexing, and `ChainComplex C ℕ` for `\mathbf{Ch}_{\ge 0}(C)`.
- Formal statement review: the Lean type explicitly packages the construction as a functor from simplicial objects to chain complexes, while the object, differential, and morphism formulas are supplied by Mathlib's `MooreComplex` implementation.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: this is a definition, so no source proof is attached. The construction gap is closed by using Mathlib's implemented functor rather than a `sorry` definition.

### line-31

- Source inventory entry: `line-31`.
- Source label: `line-31`.
- Source inventory label: `line-31`.
- Source block label: `line-31`.
- Preflight label: `line-31`.
- Source kind: theorem.
- Source locator: `docs/source.tex`, theorem lines 31--33; proof lines 33--51.
- Planned Lean declaration: `normalizedMooreComplex_objD`.
- Lean declaration kind: `theorem`.
- Lean statement:

```lean
theorem normalizedMooreComplex_objD (C : Type u) [Category.{v} C] [Abelian C] :
    normalizedMooreComplex C = AlgebraicTopology.normalizedMooreComplex C := by
  sorry
```

- Skeleton candidate used: the skeleton theorem statement `true` was rejected as too weak. The final statement records the Lean encoding of “well-defined functor” by identifying the source-named construction with Mathlib's well-defined normalized Moore complex functor.
- Dependencies: `normalizedMooreComplex`, `AlgebraicTopology.normalizedMooreComplex`, and the Mathlib construction/proofs behind `Mathlib.AlgebraicTopology.MooreComplex`.
- Complete source statement: `$N_\bullet$ is a well-defined functor.`
- Complete source proof text: We first show that it is well-defined on objects. That is, for each simplicial object $X$ in $C$, the sequence $N_\bullet(X)$ together with $d_\bullet$ is a chain complex. It suffices to prove that for each $n=1,2,\cdots$, $d_n:N_n(X) \to N_{n-1}(X)$ is well-defined and $d_{n-1} \circ d_n$ is the zero map. For well-definedness, it suffices to check $d_i^{n-1} \circ d_0^n|_{N_n(X)} : N_n(X) \to X_{n-1} \to X_{n-2}=0$ for all $i=1,2,\cdots,n-1$. Indeed, by simplicial identities, we have $d_i^{n-1} \circ d_0^n|_{N_n(X)} = d_0^{n-1} \circ d_{i+1}^n|_{N_n(X)} = 0$ by construction of $N_n(X)$. Similarly, $d_{n-1} \circ d_n = d_0^{n-1} \circ d_0^n|_{N_n(X)} = d_0^{n-1} \circ d_1^n|_{N_n(X)} = 0$. Now we prove that $N_\bullet$ is well-defined on morphisms. A morphism $f:X \to Y$ in $\mathbf{sC}$ is a collection of morphisms $f_n:X_n \to Y_n$ compatible with face maps, so $f_{n-1}\circ d_i^n=d_i^n\circ f_n$ for all $n\ge0$. Then for all $i=1,\cdots,n$, $d_i^n \circ N_n(f)=d_i^n\circ f_n|_{N_n(X)}=f_{n-1}\circ d_i^n|_{N_n(X)}=0$, so $f_n|_{N_n(X)}$ factors through $N_n(Y)$ and gives a well-defined morphism $N_n(X)\to N_n(Y)$.
- Source qualifiers:
  - Quantifier order: for every abelian category `C`, the construction from the previous definition is a functor.
  - Object well-definedness: the zero-th face map sends `N_n(X)` into `N_{n-1}(X)`.
  - Chain-complex side condition: consecutive differentials compose to zero.
  - Morphism well-definedness: a simplicial morphism restricts/factors to normalized subobjects in every degree.
  - Functoriality: identity and composition laws are included in Lean's `Functor` structure.
- Lean coverage: the separate source assertion “is a well-defined functor” is represented in Lean by (1) the type of `normalizedMooreComplex`, which is already a `Functor`, and (2) this theorem identifying the source-named construction with Mathlib's implemented functor. Mathlib's implementation contains the object, differential, `d_squared`, morphism factorization, and functor packaging proof obligations.
- Scope changes: the theorem is not restated as a standalone predicate because Lean has no extra well-definedness proposition for a successfully constructed `Functor`; well-definedness is encoded by type correctness and by equality to the certified Mathlib construction. No mathematical weakening is intended, but this representation bridge should be checked by the independent statement/source reviewer.
- Formal statement review: source theorem is metamathematical; the Lean statement is a bridge theorem asserting the drafted name denotes Mathlib's well-defined functor. If a reviewer wants a more computational statement, a companion theorem can be added for `((normalizedMooreComplex C).obj X).d (n+1) n = AlgebraicTopology.NormalizedMooreComplex.objD X n`, mirroring Mathlib's theorem of the same suffix.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: unfold `normalizedMooreComplex`; Mathlib's `AlgebraicTopology.normalizedMooreComplex` is built from `NormalizedMooreComplex.obj` and `NormalizedMooreComplex.map`, where `objD` factors `δ 0` through intersections of kernels using simplicial identities and `d_squared` proves the zero composite. The planned equality theorem should close by definitional equality after review, but the proof is intentionally left as `sorry` for the subsequent `/prove` workflow.

## Review Gate

- Statement/source review accepted by formalization PASS and 2026-06-05 audit; proof handoff is ready for the later prove workflow.
- No source-backed theorem statement has been marked approved by this drafting pass.
- Suggested next proof command after independent review approves or corrects the draft: `/prove ShadowBench/Source/Main.lean`.
