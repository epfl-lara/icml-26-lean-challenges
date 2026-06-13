Welcome to the 3rd AI4Math @ ICML 2026 Challenge!
Mathematical reasoning is one of the most demanding frontiers in AI research. The rapid advance of large language models has opened new ground at the intersection of AI and mathematics, formal verification, automated theorem proving, and scientific problem solving. This challenge, co-located with the 3rd AI4Math Workshop at ICML 2026, asks how AI systems can rigorously understand and advance mathematical knowledge. A central question motivating this track is:

How well can a model take an informal mathematical argument and turn it into a fully verified Lean 4 proof — choosing the right statement, the right namespace, and a proof that actually compiles against the same library a human would use?

For details about the workshop and the other tracks, see the AI4Math @ ICML 2026 website.

Track 4: End-to-End Autoformalization and Theorem Proving
Autoformalization translates an informal mathematical argument into a machine-checkable Lean 4 proof. Most existing benchmarks stop at either the statement (autoformalization) or the proof (proving over a fixed library). A few measure the joint task of producing a single Lean snippet that both states the right theorem and proves it on a real library. Unlike existing benchmark, this track challenges the autoformalizer to generate formal proof including the statement given the informal proof.

This track is built on ShadowBench, a curated benchmark of mathematics problems in the level of graduate school to research paper.

For each problem you are given:

an informal proof (the problem statement and a natural-language argument),
a list of allowed imports that your proof may rely on,
a set of formalization rules that fix the canonical declaration name, any open scoped … notations to assume, and other constraints on the formalization.
What you do not see is a hidden reference for each problem. Your declaration is checked against this reference by compiling it together with a hidden checker inside the same namespace.

Participants submit a single Lean 4 code block per problem, namespace-wrapped to live inside ABM.<area>.<level>.<problem_slug>, where the path components come from idx. The submission is compiled on top of the ShadowBench Lean project (Mathlib + the library that ships with the benchmark).

The leaderboard reports two metrics: SA-Pass Rate (primary, the fraction of problems whose theorem is semantically aligned with the hidden reference) and Compile Rate (companion, the fraction that type-check at all). Proofs must also respect the standard axiom whitelist {propext, Quot.sound, Classical.choice}, that is use of sorry or other axioms is disallowed.

Submissions also carry a required llm_history field, which is the chain of messages exchanged with your model, for challenge participants to certify the way of their answer generation, which will also be used by organizers for analysis. Rows without a valid llm_history are disqualified for that problem, even if the proof would otherwise be correct.

The test set is released on Hugging Face at DicoTiar/ShadowBench. See the Data, Getting Started, and Evaluation pages for the full schema, submission protocol, and metric definitions.


Evaluation
Metric	Description
overall_score	Equal to sa_pass_rate. Primary leaderboard sort key.
sa_pass_rate	Fraction whose theorem is semantically aligned with the hidden reference (the hidden checker type-checks). Used for prize ranking.
compile_rate	Fraction whose Lean snippet type-checks at all. Companion signal; every SA-Pass row is also a Compile row.
Scoring Pipeline
For each problem, the evaluation container collects the followings and compile to check the SA-pass.

The imports listed for the problem.
Your formal_proof block.
A hidden checker that the organizers wrote for this problem, placed inside the same namespace via open _root_.ABM.<area>.<level>.<problem_slug>. The checker uses your declaration with concrete arguments; for it to type-check, your declaration must be semantically aligned with the canonical statement.
Mathlib is pre-built in the evaluation container you do not need to add import Mathlib style lines yourself, and you do not need to redeclare anything in imports. Just write the namespace-wrapped statement and proof.

What is SA-Pass?
Semantic Aligned Pass (SA-Pass) counts a problem whose submitted theorem semantically matches the hidden reference. Concretely, the hidden checker example declarations type-check against your declaration. It is the primary metric for this track.

Compile Rate is the companion signal: the fraction of rows whose Lean snippet type-checks at all, regardless of semantic alignment.

Gate: llm_history (required)
Each prediction row must include a non-empty llm_history list, where every element is a {role, content} object. Submissions without a valid history are disqualified for that problem regardless of whether the proof is correct. The history is preserved verbatim in the per-problem logs for organizer analysis of model behavior.

Stage A: Lean Compilation
The grader assembles a single Lean 4 source file from three pieces:

The imports listed for the problem,
your namespace-wrapped formal_proof,
a hidden checker that the organizers wrote for this problem, placed inside the same namespace.
It then runs the Lean 4 compiler against the ShadowBench project — pinned Lean toolchain + Mathlib + the ShadowBench Lean library — and records whether the whole file type-checks. The first compiler error (sanitized of any hidden-checker content) is preserved and shown on the Visualization tab.

Stage B: Semantic Aligned Pass (SA-Pass)
A problem earns sa_pass = true if the hidden checker compiles successfully on top of your submission. The checker consists of example declarations that reference your theorem with concrete arguments; for them to type-check, your theorem must be semantically aligned with the canonical statement — the same conclusion, with compatible types and quantifier structure.

If Stage A already succeeded, SA-Pass is granted automatically. Otherwise, the grader applies a normalized exact-string comparison to the theorem signature; failing that, a DeepSeek LLM judge is asked whether the two statements express the same mathematical claim, allowing logically equivalent reformulations. The judge sees only the two statements, not your proof, and the comparison is logged only as a numeric score.

Stage C: Axiom Whitelist
The proof's transitive axiom dependency must be a subset of {propext, Quot.sound, Classical.choice}. Use of sorry, additional axiom declarations, native_decide, or unsafe metaprogramming is disallowed. Violations are recorded internally and excluded from the strict "solved" definition. The public SA-Pass Rate still counts a row when Stage B succeeds, so participants should treat the whitelist as a binding rule rather than a soft preference.

Fallback Behavior
If the evaluation cannot complete (e.g. infrastructure error), it always writes a scores.json with overall_score: 0.0 and an error field containing the traceback. Submissions that the grader cannot parse (missing idx, malformed JSONL, etc.) are treated as zero on every stage.

Time and Resource Limits
Resource	Limit
Per-problem compile timeout	120 seconds
Per-submission total time budget	60 minutes
Per-problem peak memory	8 GB
Submissions exceeding the total time budget are scored on whatever problems finished; the rest are recorded as compile_failed.


Forum Questions / Addenda

Q1: Is it allowed to add extra helper lemmas and definitions in the solution beyond those required by the problem statement? This at least sometimes seems helpful, but I am not sure if this is punished in any way.
Yes. Extra helper lemmas and definitions are fine and not penalized.
The only restriction is on axioms: only the global whitelist (propext, Quot.sound, Classical.choice) plus any axioms declared in the problem's target_code are accepted. Any new axiom you introduce is rejected.

Q2: Evaluation in this project seems tricky, will at any point intermediate evaluations be run to ensure our submissions abide by the various rules, and to see how well we perform? This would be extremely useful, especially since this benchmark has a much less clear evaluation methodology than the other competitions.
Evaluation has two stages, as stated.
(1) Compilation: your formal_proof must type-check.
(2) Hidden checker: once it compiles, a private checker theorem is applied to your declaration to verify that the theorem is stated in the form the problem intended.
If your theorem proves a weaker or differently shaped statement, the checker fails to compile against it, and the row does not pass.
The checker must remain hidden because revealing it would expose the canonical statement.
Please check the number of hidden checker passes as your intermediate result.

Operational consequences for this repository:

- Helper `def`, `abbrev`, `lemma`, `theorem`, local structures, and copied library support code are allowed inside a problem's single `formal_proof`.
- Do not introduce new `axiom`, `constant`, `opaque`, `unsafe`, `native_decide`, `sorry`, or `admit` shortcuts.
- Do not encode a mathematical conclusion as `Prop := True`, `theorem ... : True`, `by trivial`, or an equivalent vacuous placeholder. A compiling row with a weakened or vacuous statement is not a solved row.
- Every required declaration name from the problem rules must be declared explicitly in that problem's `ShadowBench/Source/Main.lean`. Do not rely on the exporter to synthesize `_root_` bridge declarations for missing theorem bodies.
- When an allowed import is missing a declaration that a proof needs, either copy the real definitions and proof lemmas needed into the same problem file or leave the problem as a known failure. Do not replace rich source notions by weaker placeholder definitions just to compile.
- Preserve the intended declaration name, theorem shape, hypotheses, conclusion, and namespace. The hidden checker applies the submitted declaration directly, so compile-only fixes can still fail SA-Pass if they change the statement.
- Local audits and export checks run with `set_option autoImplicit false` before the submitted proof. Unknown identifiers must be real imported or locally declared names, not silently created implicit variables.
