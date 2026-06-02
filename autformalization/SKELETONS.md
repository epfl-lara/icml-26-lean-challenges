# ShadowBench Skeleton Context

Primary dataset:

- `Lemmy00/ShadowBench-skeletons-prod`
- Private Hugging Face dataset; regenerate with `HF_TOKEN` set.
- Current fields: `idx`, `informal_proof`, `formalization_rules`, `skeleton1`, `skeleton2`, `skeleton3`, `skeleton4`.

Each generated problem writes the four candidates here:

```text
docs/skeletons/Skeleton1.lean
docs/skeletons/Skeleton2.lean
docs/skeletons/Skeleton3.lean
docs/skeletons/Skeleton4.lean
```

How to use them:

- Treat skeletons as candidate initial statement/definition shapes.
- Compare candidates against `docs/source.tex` and `docs/instructions.md` before adopting one.
- Record in `ShadowBench/Source/Blueprint.md` which skeleton, if any, was used.
- Preserve required theorem/definition names from the formalization rules.
- Do not silently weaken or strengthen a source claim just because a skeleton is easier to prove.
- The final answer still belongs in `ShadowBench/Source/Main.lean`.
- EPFLemma runner scripts pass `skills/shadowbench-formalization-context/SKILL.md` with `--additional-skill` so this context is part of formalization and proof runs.

Regeneration:

```bash
export HF_TOKEN=...
python3 scripts/prepare_shadowbench.py --refresh --reset-problems --overwrite-lean --overwrite-blueprint
```

If the dataset has already been cached in `data/test.jsonl`, `HF_TOKEN` is not needed for ordinary reruns.

Local private-Parquet regeneration:

```bash
/localhome/milikic/miniconda3/bin/python scripts/prepare_shadowbench.py \
  --local-parquet /tmp/shadowbench_skeletons/test.parquet \
  --reset-problems --overwrite-lean --overwrite-blueprint
```
