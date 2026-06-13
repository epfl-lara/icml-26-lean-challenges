# Lean blueprint — splay-tree access conjectures

This is a [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint)-style
blueprint for the splay formalization. The **content** (`src/content.tex`) is the
meaningful artifact: it encodes every result as a node with its Lean declaration
name and dependency edges, so the generated dependency graph shows at a glance
the **proven spine** (green, `\leanok`) and the **open core** (red, no `\leanok`).

## What the graph shows

- **Green (proved, standard axioms):** the Sequential Access Theorem
  (`Splay.sequential`) and its sub-lemmas; the entire Deque *reduction* —
  `deque_challenge_CLOSED_of_touched`, `recursion_telescope`,
  `inblock_touched_eq_depth_projection`, the DS toolkit (`middlesKey_proved`,
  `gamma_poly_alpha_proved`).
- **Red (open):** `Splay.deque` and `TouchedSumAlpha` (follow from the layer
  once the residuals close), the two linear outside-channel residuals
  (`Blocking_reaffiliationLinear`, `Blocking_reentryPerSwitch` — tractable), and
  `Blocking_inblock_recursion` — the single hard inverse-Ackermann core.

## Status of this scaffold

This is a **scaffold**, honestly labeled: `src/content.tex`, `src/web.tex`,
`src/print.tex`, and the macros are written and ready. The full web build
(`leanblueprint pdf && leanblueprint web`) additionally requires:

1. The `leanblueprint` Python package + `plastex` toolchain installed.
2. The Lean declarations to live in a single **lake-importable** module so the
   `\lean{}`/`\leanok` cross-checks resolve. Currently the proofs are spread
   across importable challenge files (`Challenge_Splay_Sequential.lean`, the
   `Challenges.ZBK` olean) and untracked scratch (`.tmp_claude_*`); consolidating
   them into one `Splay/` library module is the remaining mechanical step (it is
   the same merge that discharges `RecursionTelescopedBound`).

To build once consolidated:
```
pip install leanblueprint
cd blueprint && leanblueprint pdf && leanblueprint web
```

The `\leanok` marks here were set by hand to reflect the audited compile status
(see `../report/00_splay_formalization_report.md` §3.4); after consolidation,
`leanblueprint checkdecls` would verify each `\lean{}` name against the actual
library and flag any drift.
