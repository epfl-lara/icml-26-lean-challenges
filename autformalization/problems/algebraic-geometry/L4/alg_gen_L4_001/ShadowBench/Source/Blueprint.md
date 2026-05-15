# Formalization Blueprint: `algebraic-geometry/L4/alg_gen_L4_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `P2`
- `CayleyBacharach`
- `VanishesAt`
- `Locus`
- `ExcessLociCrossings`
- `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_6`
- `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_7`
- `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_8`
- `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_9`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open scoped LinearAlgebra.Projectivization

/-
Formalize in Lean the following named items from Text.

1. Definition (P2)
   The definition must be named `P2`.
   Matched text (candidate 0, paragraph): Theorem(`CayleyBacharach`)
2. Definition (VanishesAt)
   The definition must be named `VanishesAt`.
   Matched text (candidate 1, paragraph): Suppose two cubic curves $C_1$ and $C_2$ on a projective plane $\mathbb{P}^2(K)$ meet on
                                          nine distinct points. If a cubic curve $C_3$ passes eight of them, then $C_3$ passes all the
                                          nine points.
3. Definition (Locus)
   The definition must be named `Locus`.
   Matched text (candidate 2, paragraph): Proof.
4. Theorem (ExcessLociCrossings)
   The theorem must be named `ExcessLociCrossings`.
   Matched text (candidate 3, paragraph): Suppose each $C_i$(where $i = 1, 2, 3$) is defined by a cubic homogeneous polynomial
                                          $\varphi_i(x, y, z)$. If $\varphi_3$ is not already a linear combination of $\varphi_1$ and
                                          $\varphi_2$, then for any pair of points $P, P' \in \mathbb{P}^2(K)$ there is a linear
                                          combination $a_1\varphi_1 + a_2\varphi_2 + a_3\varphi_3$($a_i \in K$) such that its curve
                                          passes both $P$ and $P'$.
5. Theorem (CayleyBacharach)
   The theorem must be named `CayleyBacharach`.
   Matched text (candidate 4, paragraph): Note as a lemma that if two algebraic curves $\Gamma_1$ and $\Gamma_2$ each of degree $m$
                                          and $n$ meets on more than $mn$ points, then there is an algebraic curve $\Gamma$ which is
                                          fully contained in $\Gamma_1 \cap \Gamma_2$. Thanks to this fact, among the eight
                                          intersecting points of the three cubics, no combinations of four points lie on some line,
                                          and no combinations of seven points lie on some conic.
6. Theorem (ABM_algebraic_geometry_L4_alg_gen_L4_001_item_6)
   The theorem must be named `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_6`.
   Matched text (candidate 5, paragraph): Suppose three intersecting points $P_1, P_2, P_3$ are on a line $L$. Take another point $P$
                                          from $L$, and consider the unique conic $Q$ which goes through the five remaining
                                          intersections $P_4, P_5, P_6, P_7, P_8$. Further taking a point $P' \notin L \cup Q$, we
                                          have a cubic defined by a linear combination, namely $C : a_1 \varphi_1 + a_2 \varphi_2 +
                                          a_3 \varphi_3 = 0$. From the above lemma, $L \cup Q = C$, but this…
7. Theorem (ABM_algebraic_geometry_L4_alg_gen_L4_001_item_7)
   The theorem must be named `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_7`.
   Matched text (candidate 6, paragraph): We do the same work with conics. Suppose six intersecting points $P_1, \cdots, P_6$ are on a
                                          conic $Q$. Again, take another point $P$ from $Q$. There is a unique line $L$ going through
                                          the other two intersections $P_7$ and $P_8$; take a point $P' \notin L \cup Q$. Similarly
                                          considering $C : a_1 \varphi_1 + a_2 \varphi_2 + a_3 \varphi_3 = 0$ which goes through $P$
                                          and $P'$, we have $L \cup Q = C$ from the above lemma…
8. Theorem (ABM_algebraic_geometry_L4_alg_gen_L4_001_item_8)
   The theorem must be named `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_8`.
   Matched text (candidate 7, paragraph): Now, take the line $L$ and the conic $Q$, each going through two points $P_1, P_2$ and five
                                          points $P_3, \cdots, P_7$ respectively. Take $P$ from $L$ other than $P_1$ and $P_2$, and
                                          take $P' \notin L \cup Q$. Again, there is $C : a_1 \varphi_1 + a_2 \varphi_2 + a_3
                                          \varphi_3 = 0$ which goes through $P$ and $P'$. From the above lemma, $L \cup Q = C$, hence
                                          the last intersecting point $P_8$ is in $L \cup Q$, but this…
9. Theorem (ABM_algebraic_geometry_L4_alg_gen_L4_001_item_9)
   The theorem must be named `ABM_algebraic_geometry_L4_alg_gen_L4_001_item_9`.
   Matched text (candidate 8, paragraph): The contradiction bases on the assumption that $\varphi_3$ is not a linear combination of
                                          $\varphi_1$ and $\varphi_2$. Therefore as a result, $\varphi_3$ is a linear combination of
                                          $\varphi_1$ and $\varphi_2$, and the curve defined by $\varphi_3$ is forced to go through
                                          the ninth intersection of the other two.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
