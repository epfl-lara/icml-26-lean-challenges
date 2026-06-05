# Formalization Blueprint: `topology/L3/top_gen_L3_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem skeleton `exists_lift_nhds`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so a project build reaches the generated target module.

No split into additional generated Lean files is planned: the source has one theorem and no named auxiliary statements.

## Import Plan

```lean
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
```

These are exactly the direct imports used by `ShadowBench/Source/Main.lean`.

## Suggested Search Modules

Non-gating hints for the future prover:

- `Mathlib.Topology.Covering.Basic` for `IsLocalHomeomorph` and local-homeomorphism API.
- `Mathlib.Topology.UnitInterval` for the unit interval type alias `unitInterval.I`.
- Search terms already tried: `IsLocalHomeomorph`, `ContinuousOn`, `unitInterval`, product subsets `Set.univ ×ˢ N`, and neighborhood/filter notation.

## Required Names

- `exists_lift_nhds`

## Candidate Skeleton Review

- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` use the required name and import block, but omit the lift hypothesis `p ∘ g = f`; they also omit the conclusion that the constructed map remains a lift of `f`. They are therefore not source-faithful as final statements.
- `Skeleton4.lean` supplies the better source shape: implicit topological spaces, `I × A`, an `IsLocalHomeomorph p` hypothesis, the lift hypothesis `p ∘ g = f`, and `ContinuousOn g` on `{0} × A ∪ I × {a}`. The final Lean draft adopts this skeleton's domain/quantifier style but uses `IsOpen N ∧ a ∈ N` to reflect the open neighborhood constructed in the proof and adds the maintained lift conclusion `p ∘ g' = f` recorded in the source proof.

## Search Log

- `lean_search "IsLocalHomeomorph"` found the Mathlib declaration `IsLocalHomeomorph` and related `IsLocalHomeomorphOn`.
- Semantic search for unit interval/product continuity found `unitInterval.univ_eq_Icc`, `ContinuousOn`, and related product/continuity declarations. No extra direct imports were needed beyond the allowed import block.
- Type-pattern search for neighborhoods/product continuous-on statements returned general `ContinuousOn` and `Set.univ` facts; no local project lemma already formalizes this theorem.

## Source Statement Inventory

### line-17

- Source item: theorem `exists_lift_nhds`

- Source locator: `docs/source.tex`, theorem block at lines 17--18, proof lines 19--225.
- Source statement:

  Let `p : E → X` be a local homeomorphism. Denote the unit interval `[0,1]` by `I`. Suppose `f : I × A → X` is continuous and `g : I × A → E` is a lift of `f` continuous on `{0} × A ∪ I × {a}` for some `a ∈ A`. Then there exists a neighborhood `N` of `a` and `g' : I × A → E` continuous on `I × N` that agrees with `g` on `{0} × A ∪ I × {a}`.

- Planned Lean declarations: `exists_lift_nhds` in `ShadowBench/Source/Main.lean`.
- Skeleton candidate used: primarily `docs/skeletons/Skeleton4.lean`, corrected as described above.
- Direct dependencies: `TopologicalSpace`, `IsLocalHomeomorph`, `Continuous`, `ContinuousOn`, product subsets `×ˢ`, singleton/universal sets, and the unit interval alias `I` from `Mathlib.Topology.UnitInterval`.
- Planned Lean statement:

```lean
theorem exists_lift_nhds {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    {p : E → X} (hp : IsLocalHomeomorph p)
    {f : I × A → X} (hf : Continuous f)
    {g : I × A → E} (hg_lift : p ∘ g = f) (a : A)
    (hg_cont : ContinuousOn g ((({0} : Set I) ×ˢ Set.univ) ∪ (Set.univ ×ˢ {a}))) :
    ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ ∃ g' : I × A → E,
      ContinuousOn g' (Set.univ ×ˢ N) ∧
      p ∘ g' = f ∧
      ∀ x ∈ (({0} : Set I) ×ˢ Set.univ) ∪ (Set.univ ×ˢ {a}), g' x = g x
```

- Source qualifiers:
  - Mathematical object class: arbitrary topological spaces `E`, `X`, and `A`.
  - Main structured hypothesis: `p : E → X` is a local homeomorphism.
  - Parameter domain: the source unit interval `I = [0,1]`, represented by Mathlib's `unitInterval.I`.
  - Input map: `f : I × A → X` is continuous.
  - Lift map: `g : I × A → E` satisfies `p ∘ g = f`.
  - Distinguished parameter: `a : A` (membership in `A` is by typing).
  - Partial continuity side condition: `g` is continuous on `{0} × A ∪ I × {a}`.
  - Output: an open neighborhood `N : Set A` of `a` and a map `g' : I × A → E`.
  - Continuity conclusion: `g'` is continuous on `I × N`.
  - Equality/image conclusion: `g'` agrees with `g` on `{0} × A ∪ I × {a}`.
  - Follow-on lift conclusion: the source proof preserves and finally states `p ∘ g' = f`; the Lean statement includes this as part of the theorem conclusion.
- Lean coverage:
  - Topological spaces are explicit typeclass parameters.
  - Local homeomorphism is `hp : IsLocalHomeomorph p`.
  - The unit interval is `I`; products are `I × A`.
  - Continuity of `f` is `hf : Continuous f`.
  - The lift hypothesis is `hg_lift : p ∘ g = f`.
  - Continuity of `g` on the source union is `hg_cont : ContinuousOn g ((({0} : Set I) ×ˢ Set.univ) ∪ (Set.univ ×ˢ {a}))`.
  - The neighborhood is represented by `IsOpen N ∧ a ∈ N`, matching the open neighborhoods used throughout the source proof.
  - `I × N` is represented as `Set.univ ×ˢ N` because `I` is the whole first-coordinate type.
  - Agreement on `{0} × A ∪ I × {a}` is represented by a pointwise equality over the same product-set union.
  - The maintained lift property of `g'` is represented by `p ∘ g' = f`.
- Scope changes: none intended. Representation choices are: `a ∈ A` is implicit in the type `a : A`; the source interval `I = [0,1]` is Mathlib's `unitInterval.I`; and "neighborhood" is formalized as an open set containing `a`, as constructed in the proof. The included conclusion `p ∘ g' = f` is recorded as source content because the theorem describes `g` as a lift and the proof explicitly proves and announces the same lift property for the constructed `g'` in the final paragraph.
- Formal statement review: The Lean statement preserves the source quantifier order up to implicit Lean parameters, the local-homeomorphism object class, the continuity and lift hypotheses, the distinguished point, the restricted continuity domain, the existence of a neighborhood and replacement lift, the `I × N` continuity domain, and the agreement set. No source theorem, lemma, or definition is intentionally omitted.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: compactness-and-induction proof on the unit interval; see the complete source proof text and prover notes below for the subdivision, tube-lemma, inverse-chart, frontier-agreement, lift-preservation, and agreement-on-the-union steps.

#### Complete source proof text

```text
For each \(e \in E\), choose a local homeomorphism \(q_e:U_e \to V_e \subseteq X\) from an open neighborhood \(U_e\) of \(e\) such that \(q_e = p|_{U_e}\).

Using the continuity of the map \(t \mapsto g(t,a)\), we cover $I$ by the open sets $g(\cdot,a)^{-1}(U_e)$, and by the compactness of $I$, we may choose a monotone subdivision
\[
0=t_0 \le t_1 \le \cdots \le t_{n_{\max}} = 1
\]
such that for every \(n\), there exists some \(e \in E\) such that
\[
g\bigl([t_n,t_{n+1}] \times \{a\}\bigr) \subseteq U_e.
\]

We claim that for every \(n\), there exist an open set \(N \subseteq A\) with $a \in N$, and a map
\[
g' : I \times A \to E
\]
such that:
\begin{enumerate}
  \item \(g'\) is continuous on \([0,t_n]\times N\);
  \item \(p \circ g' = f\) on all of \(I \times A\);
  \item \(g'(0,a') = g(0,a')\) for all \(a' \in A\);
  \item for every \(t' \le t_n\), one has
  \[
  g'(t',a)=g(t',a).
  \]
\end{enumerate}

Once this is proved, we apply it with \(n=n_{\max}\). Since \(t_{n_{\max}}=1\), the continuity statement becomes continuity on
\[
[0,1]\times N = I\times N,
\]
and the last condition becomes \(g'(t,a)=g(t,a)\) for every \(t\in I\). This gives the theorem.

We now prove the claim by induction on \(n\).

\noindent\textbf{Base case \(n=0\).}
Take
\[
N=A,\qquad g'=g.
\]
Then \(a \in A\), and \(A\) is open in itself. Also \(p\circ g'=f\) by hypothesis, and clearly
\[
g'(0,a')=g(0,a') \quad\text{for all } a',
\]
and
\[
g'(t',a)=g(t',a)
\]
for every \(t'\le t_0\).

It remains to prove continuity of \(g'\) on \([0,t_0]\times A\). Since \(t_0=0\), this set is just \(\{0\}\times A\) and the map \(g'=g\) is continuous on this set by assumption.

\noindent\textbf{Inductive step.}
Assume the statement holds for some \(n\), with corresponding open neighborhood \(N\) of \(a\) and a map \(g':I \times A \to E\).

By construction of the subdivision, choose \(e \in E\) such that
\[
g\bigl([t_n,t_{n+1}] \times \{a\}\bigr) \subseteq U_e.
\]
Since \(p\circ g=f\) and \(q_e=p\) on \(U_e\), it follows that
\[
[t_n,t_{n+1}] \times \{a\} \subseteq f^{-1}(V_e).
\]

Now \(V_e\) is open, and \([t_n,t_{n+1}]\) is compact. By the generalized tube lemma, there exist open sets \(u \subseteq I\) and \(v \subseteq A\) such that
\[
[t_n,t_{n+1}] \subseteq u,\qquad a \in v,
\qquad\text{and}\qquad
u \times v \subseteq f^{-1}(V_e).
\]
In particular,
\[
f\bigl([t_n,t_{n+1}] \times v\bigr) \subseteq V_e.
\]

We now define
\[
N_{n+1}
:=
v \cap N \cap \{\,a' \in A : g'(t_n,a') \in U_e\,\}.
\]
This set is open, since \(v\) and \(N\) are open and \(a' \mapsto g'(t_n,a')\) is continuous on \(N\).
Also \(a \in N_{n+1}\). Indeed, \(a\in v\), \(a\in N\) by the induction hypothesis, and
\[
g'(t_n,a)=g(t_n,a)\in U_e,
\]
because \(g'(t_n,a)=g(t_n,a)\) by the induction hypothesis and
\[
g\bigl([t_n,t_{n+1}] \times \{a\}\bigr)\subseteq U_e.
\]

Define a new map
\[
g_{n+1}' : I \times A \to E
\]
by
\[
g_{n+1}'(t,a')=
\begin{cases}
g'(t,a') & \text{if } t \le t_n,\\
q_e^{-1}(f(t,a')) & \text{if } t>t_n \text{ and } f(t,a') \in V_e,\\
g(t,a') & \text{otherwise.}
\end{cases}
\]

We verify that \(N_{n+1}\) and \(g_{n+1}'\) satisfy the required properties.

\medskip

\noindent\emph{Continuity on \([0,t_{n+1}] \times N_{n+1}\).}
On the closed subset \(\{(t,a'):t \le t_n, a' \in N_{n+1}\}\), the map \(g_{n+1}'\) agrees with \(g'\), hence is continuous there by the induction hypothesis.

On the subset \(\{(t,a'):t>t_n,a' \in N_{n+1}\}\), \(a' \in N_{n+1}\subseteq v\), and \(t \in [0,t_{n+1}]\), we have \(t \in u\) whenever \(t\ge t_n\), hence
\[
f(t,a') \in V_e.
\]
Therefore on this region
\[
g_{n+1}'(t,a') = q_e^{-1}(f(t,a')),
\]
which is continuous.

It remains to check agreement on the frontier \(t=t_n\). Let \((t_n,a') \in [0,t_{n+1}] \times N_{n+1}\). Since \(a' \in N_{n+1}\), we know
\[
g'(t_n,a') \in U_e.
\]
Also \(f(t_n,a') \in V_e\). Now
\[
q_e(g'(t_n,a')) = p(g'(t_n,a')) = f(t_n,a'),
\]
because \(p\circ g'=f\). Hence
\[
g'(t_n,a') = q_e^{-1}(f(t_n,a')),
\]
by injectivity of \(q_e\) on its source. So the two definitions agree on the frontier, and therefore \(g_{n+1}'\) is continuous on \([0,t_{n+1}] \times N_{n+1}\).

\medskip

\noindent\emph{Lift property.}
We show
\[
p \circ g_{n+1}' = f.
\]
If \(t \le t_n\), then \(g_{n+1}'=g'\), so this follows from the induction hypothesis. If \(t>t_n\) and \(f(t,a')\in V_e\), then
\[
g_{n+1}'(t,a') = q_e^{-1}(f(t,a')),
\]
hence
\[
p(g_{n+1}'(t,a')) = q_e(q_e^{-1}(f(t,a'))) = f(t,a').
\]
Otherwise \(g_{n+1}'=g\), and \(p\circ g=f\) by hypothesis.

\medskip

\noindent\emph{Agreement on \(\{0\}\times A\).}
Since \(0 \le t_n\), the first branch applies, so
\[
g_{n+1}'(0,a') = g'(0,a') = g(0,a')
\]
for all \(a' \in A\).

\medskip

\noindent\emph{Agreement on \(I\times\{a\}\) up to \(t_{n+1}\).}
Let \(t' \le t_{n+1}\). We must show
\[
g_{n+1}'(t',a)=g(t',a).
\]
There are three cases.

If \(t' \le t_n\), then
\[
g_{n+1}'(t',a)=g'(t',a)=g(t',a)
\]
by the induction hypothesis.

If \(t'>t_n\) and \(f(t',a)\in V_e\), then
\[
g_{n+1}'(t',a)=q_e^{-1}(f(t',a)).
\]
But also \(g(t',a)\in U_e\), because
\[
g\bigl([t_n,t_{n+1}] \times \{a\}\bigr)\subseteq U_e,
\]
and
\[
q_e(g(t',a)) = p(g(t',a)) = f(t',a).
\]
Hence by injectivity of \(q_e\),
\[
g'_{n+1}(t',a)=q_e^{-1}(f(t',a))=g(t',a).
\]

Finally, if \(t'>t_n\) and \(f(t',a)\notin V_e\), then by definition
\[
g_{n+1}'(t',a)=g(t',a).
\]

Thus all required properties hold for \(n+1\). This completes the induction.

Applying the result to \(n_{\max}\), we obtain an open neighborhood \(N\) of \(a\) and a map
\[
g' : I \times A \to E
\]
such that \(g'\) is continuous on \(I\times N\), satisfies \(p\circ g'=f\), agrees with \(g\) on \(\{0\}\times A \cup I\times\{a\}\). This is exactly the desired conclusion.
```

#### Prover notes

The source proof is a compactness-and-induction argument along the unit interval. A future proof should first obtain local-homeomorphism charts for `p`, then cover the path `fun t : I => g (t, a)` by chart domains and use compactness of `I` to extract a monotone finite subdivision. The inductive invariant constructs an open neighborhood in `A` and a partial replacement lift continuous up to the current subdivision time. In the inductive step, use the generalized tube lemma around the compact subinterval and point `a` to keep `f` inside the selected chart range, shrink the parameter neighborhood by requiring `g' (t_n, a')` to lie in the chart source, define the new map by using the old lift before `t_n` and the inverse chart after `t_n`, then prove continuity by agreement on the frontier and preserve the lift/agreement conditions. The final `N` and `g'` come from the terminal subdivision time `1`.

## Handoff Checklist

- [x] Source document inspected with theorem block `line-17` recorded.
- [x] Candidate skeletons compared against the source.
- [x] Blueprint has source qualifiers, Lean coverage, scope changes, and proof/prover notes.
- [x] Generated target module is reached by the root project imports.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue has eliminated the `sorry` placeholder.
