---
license: cc-by-4.0
task_categories:
  - text-generation
language:
  - en
tags:
  - lean4
  - theorem-proving
  - autoformalization
  - mathematics
  - benchmark
pretty_name: ShadowBench
configs:
  - config_name: default
    data_files:
      - split: test
        path: test.jsonl
---

# ShadowBench

Test split for the **ICML 2026 AI4Math Workshop & Challenge 4 — ShadowBench**: end-to-end autoformalization and theorem proving in Lean 4. Given a natural-language proof, a list of allowed Lean 4 imports, and formalization rules, produce a Lean 4 snippet that states the canonical theorem and proves it.

## Fields

| Field | Description |
|---|---|
| `idx` | Problem id. Path encodes the namespace: `ABM.<area>.<level>.<problem_slug>`. |
| `informal_proof` | LaTeX problem statement / informal proof |
| `formalization_rules` | Per-problem hints, including the canonical declaration name |
| `imports` | Lean 4 import lines available to your proof |

## Submission

Submit on **Codabench**. One `.jsonl` per submission, one row per problem:

```json
{"idx": "...", "formal_proof": "<full Lean snippet>", "llm_history": [{"role": "...", "content": "..."}]}
```

`llm_history` is **required** (non-empty chain of role/content messages).

See the competition page for full rules and grading.
