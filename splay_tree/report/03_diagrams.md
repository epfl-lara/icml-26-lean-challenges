# Figures

Mermaid sources for the figures in the report (render on GitHub / arXiv-HTML;
convert to TikZ for the LaTeX submission). Node labels are the exact Lean
declaration names so each figure cross-references the formalization.

**Camera-ready asset.** A standalone, self-styled SVG of Figure 2 (light/dark
agnostic, embeddable directly in arXiv-HTML or convertible to PDF/TikZ) is at
`figure2_deque_reduction.svg`. It is the authoritative version of the Deque
reduction figure; the mermaid below is the editable source.

## Figure 1. Status of the four splay access problems

```mermaid
graph TD
  R["Splay-tree access cost<br/>splay.sequence_cost (Sleator–Tarjan model)"]
  R --> SEQ["Sequential access<br/>Splay.sequential — SOLVED"]
  R --> DQ["Deque, O(n·α(n))<br/>Splay.deque — open (sound reduction)"]
  R --> DC["Deque Conjecture, O(n)<br/>Splay.deque (linear) — open"]
  R --> TR["Traversal Conjecture<br/>traversal_conjecture — partial"]

  classDef base fill:#F1EFE8,stroke:#5F5E5A,color:#2C2C2A;
  classDef done fill:#E1F5EE,stroke:#0F6E56,color:#04342C;
  classDef todo fill:#FCEBEB,stroke:#A32D2D,color:#501313;
  class R base; class SEQ done; class DQ,DC,TR todo;
```

## Figure 2. The Deque O(n·α(n)) reduction: proven chain and the residual core

```mermaid
graph TD
  G["Splay.deque<br/>splay.sequence_cost ≤ c·n·α(n)"]
  C["deque_challenge_CLOSED_of_touched<br/>sequence_cost = Σ costN ≤ Σ tpLenN + n"]
  T["TouchedSumAlpha<br/>Σ tpLenN ≤ c·n·α(n)"]
  TEL["recursion_telescope<br/>flat per level + O(α) depth ⟹ n·α"]
  S1["inblock_touched_eq_depth_projection<br/>(STEP 1, depth-projection identity)"]
  RA["Blocking_reaffiliationLinear<br/>Σ ≤ c·n (linear)"]
  RE["Blocking_reentryPerSwitch<br/>Σ ≤ c·n (linear)"]
  R5["Blocking_inblock_recursion<br/>Σ inBlockTp ≤ Σ g(b) — Sundar §5 core"]

  G --> C --> T
  T --> TEL
  T --> RA
  T --> RE
  T --> R5
  R5 --> S1

  classDef goal fill:#F1EFE8,stroke:#5F5E5A,color:#2C2C2A;
  classDef done fill:#E1F5EE,stroke:#0F6E56,color:#04342C;
  classDef todo fill:#FCEBEB,stroke:#A32D2D,color:#501313;
  class G,T goal;
  class C,TEL,S1 done;
  class RA,RE,R5 todo;
```

*Green: machine-checked, standard axioms. Red: open. The inverse-Ackermann factor
is confined to `Blocking_inblock_recursion`; the two linear residuals and the
entire chain `deque_challenge_CLOSED_of_touched ∘ recursion_telescope ∘
inblock_touched_eq_depth_projection` are discharged.*

## Figure 3. The Sequential Access Theorem (solved): proof dependency

```mermaid
graph TD
  S["Splay.sequential<br/>splay.sequence_cost ≤ c·n"]
  AX["sequential_access_theorem"]
  MS["sequence_cost_eq_seqCost<br/>(min-splay reframing)"]
  LK["two_splayLinks_le_cost<br/>2·splayLinks ≤ splay.cost"]
  TL["totalLinks_le<br/>Σ splayLinks ≤ 13·n"]
  POT["omegaNB potential<br/>omegaNB_base_le · omegaNB_step · fresh_le_mu"]
  TLS["links_telescope"]

  S --> AX
  AX --> MS
  AX --> LK
  AX --> TL
  TL --> TLS --> POT

  classDef done fill:#E1F5EE,stroke:#0F6E56,color:#04342C;
  class S,AX,MS,LK,TL,POT,TLS done;
```

*All nodes machine-checked (`Challenge_Splay_Sequential.lean`, standard axioms).*
