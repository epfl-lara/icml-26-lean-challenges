Here is some answer from my GPT5-Pro advisor:

No — for your exact task, Goedel-Prover-V2-32B is not the best first choice. It is a very strong Lean proof-generation model once the statement is already formalized, but your task is autoformalization: natural-language / LaTeX math → Lean 4 theorem statement ending in by sorry. For that, you want a formalizer, not a prover.

My current ranking for HF-loadable, specialized Lean 4 statement formalization models ≤ ~40B is:

Rank	Model	Best use	My take
1	GuoxinChen/ReForm-32B	Reflective NL/LaTeX → Lean 4 statement	Most promising current 32B formalizer; designed specifically for generate–verify–refine autoformalization.
2	Buchilaguo/ATF-32B	Tool-feedback formalization	Very strong if you can run syntax/consistency feedback loop; likely best pipeline-style option.
3	stepfun-ai/StepFun-Formalizer-32B	Simple direct formalization	Strong, clean HF model card, solid public BEq numbers; easiest serious baseline.
4	Goedel-LM/Goedel-Formalizer-V2-32B	Goedel ecosystem formalization	Good, but public comparative evaluations suggest it is not clearly best for pure formalization.
5	AI-MO/Kimina-Autoformalizer-7B	Lightweight baseline	Only 7B, but directly trained for “NL problem → Lean 4 code ending with by sorry.”
Not for this primary task	Goedel-LM/Goedel-Prover-V2-32B	Proving already-formal Lean statements	Excellent prover, but not the model I would choose to produce the initial Lean statement.

Why not Goedel-Prover-V2-32B?

Goedel-Prover-V2-32B is advertised and benchmarked as an automated formal proof generation model, with very strong MiniF2F / PutnamBench results: its model card reports 88.0% MiniF2F Pass@32 in standard mode and 90.4% with self-correction, plus strong PutnamBench results. But that is the proving stage, not necessarily the statement translation stage. The model card itself frames it as proof generation, and its quick-start examples are for theorem proving rather than “LaTeX statement → theorem … := by sorry.”  ￼

The better architecture is:

LaTeX / natural language theorem
        ↓
formalizer model
        ↓
Lean 4 statement with ⁠ by sorry ⁠
        ↓
Lean compile/typecheck filter + maybe semantic consistency check
        ↓
optional prover model: Goedel-Prover-V2-32B / Kimina-Prover / BFS-Prover

Best practical choices

1.⁠ ⁠GuoxinChen/ReForm-32B — my top pick to test first.
ReForm is explicitly an autoformalization model: the arXiv abstract defines the task as translating natural-language mathematics into machine-verifiable formal statements, and the HF model card says it uses a reflective “generate → verify → refine” loop. The model card reports an average +22.6 percentage-point improvement over the strongest baseline across four formalization benchmarks: miniF2F, ProofNet, Putnam, and AIME 2025. It is also exactly in your target size range: 33B BF16 on HF.  ￼

Use it like:

from transformers import AutoTokenizer, AutoModelForCausalLM
import torch
model_name = "GuoxinChen/ReForm-32B"
tokenizer = AutoTokenizer.from_pretrained(model_name)
model = AutoModelForCausalLM.from_pretrained(
    model_name,
    torch_dtype=torch.bfloat16,
    device_map="auto",
)
problem = r"""
Let \(f : \mathbb{R} \to \mathbb{R}\) be continuous and suppose
\(f(x+y)=f(x)+f(y)\) for all real \(x,y\). Prove that there exists a real
constant \(c\) such that \(f(x)=cx\) for all \(x\).
"""
prompt = f"""Think step by step to translate the mathematical problem in natural language to Lean 4, and verify the consistency.
Return only Lean 4 code. Use theorem name ⁠ my_theorem ⁠. The proof should be ⁠ by sorry ⁠.
{problem}
"""
inputs = tokenizer(prompt, return_tensors="pt").to(model.device)
out = model.generate(
    **inputs,
    max_new_tokens=4096,
    do_sample=True,
    temperature=0.6,
    top_p=0.95,
)
print(tokenizer.decode(out[0], skip_special_tokens=True))

2.⁠ ⁠Buchilaguo/ATF-32B — probably best if you want a feedback-loop pipeline.
ATF is also directly designed for natural-language math → Lean 4 formal statements. Its paper/model card emphasize syntax checking and semantic consistency checking as tools, and the paper reports that ATF-32B outperforms baselines on syntax and consistency metrics; for example, the paper reports Pass@1 consistency scores of 94.51% on FormalMath-Lite, 89.78% on ProverBench, and 65.38% on CombiBench, beating Goedel-V2-Formalizer-32B by 9.1, 10.08, and 29.13 percentage points respectively.  ￼

This one is especially interesting if you can actually run Lean as a checker and feed failures back. Without tools, it still supports direct generation, but its main advantage is the feedback loop. The HF card says direct mode is available by setting enable_thinking=False, while the full system prompt expects syntax_check and consistency_check style tools.  ￼

3.⁠ ⁠stepfun-ai/StepFun-Formalizer-32B — strongest clean “direct formalizer” baseline.
StepFun-Formalizer is explicitly “designed to translate natural-language mathematical problems into formal statements in Lean 4.” Its paper reports SOTA BEq@1 scores of 40.5% on FormalMATH-Lite and 26.7% on ProverBench, and the HF card gives a simple vLLM-style prompt for Lean 4 formalization with a header.  ￼

A nice property: it is straightforward to run, and its prompt is exactly close to what you want:

from vllm import LLM, SamplingParams
from transformers import AutoTokenizer
MODEL_DIR = "stepfun-ai/StepFun-Formalizer-32B"
def get_prompt(problem: str, theorem_name: str = "my_theorem") -> str:
    return (
        "Please autoformalize the following problem in Lean 4 with a header. "
        f"Use the following theorem names: {theorem_name}.\n\n"
        f"{problem}\n\n"
        "Your code should start with:\n⁠ Lean4\nimport Mathlib\n ⁠\n"
        "End the theorem proof with ⁠ by sorry ⁠."
    )
llm = LLM(MODEL_DIR, tensor_parallel_size=1)
sampling = SamplingParams(temperature=0.6, top_p=0.95, max_tokens=4096)
problem = r"""
Let \(n\) be a positive integer. Prove that \(n^2+n\) is even.
"""
outputs = llm.generate(get_prompt(problem), sampling)
print(outputs[0].outputs[0].text)

4.⁠ ⁠Goedel-LM/Goedel-Formalizer-V2-32B — use this, not Goedel-Prover-V2-32B, if you want the Goedel option.
Goedel has a separate formalizer: Goedel-Formalizer-V2-32B. The HF repo exists as a 33B Qwen3 safetensors model, and the README/commit notes say it is for translating informal math problems into Lean 4 statements, with an internal Omni-MATH evaluation reporting around 226/300 or 228/300 successes depending on README revision text.  ￼

The caveat: independent/comparative formalizer papers do not make it look unambiguously best. StepFun’s appendix compares against Goedel-Formalizer-V2 and reports lower BEq scores for Goedel-V2 on ProverBench and CombiBench, while noting that Goedel’s header/prompt behavior may cause underestimation in BEq evaluation.  ￼

5.⁠ ⁠AI-MO/Kimina-Autoformalizer-7B — small but directly aligned.
Kimina-Autoformalizer-7B is explicitly described as translating competition-style natural-language problems to Lean 4 code ending with by sorry. It is only 7B, so it is not the top option if you can run 32B, but it is a good cheap baseline and was important in later formalizer comparisons.  ￼

Where the prover models fit

Goedel-Prover-V2-32B, Kimina-Prover-72B, DeepSeek-Prover-V2, and BFS-Prover-V2-32B are mostly useful after you already have the Lean theorem statement. Kimina-Prover-72B, for example, is described as a theorem-proving model focused on Lean 4 competition problems and is 73B, outside your 30B–40B limit. BFS-Prover-V2-32B is a step-level prover that expects a Lean tactic state in the format "{state}:::", so it is not suitable as a direct NL/LaTeX → Lean statement formalizer.  ￼

My concrete recommendation

For your use case, I would set up a multi-sample formalization pipeline like this:

Primary formalizer:
  ReForm-32B or ATF-32B
Fallback / ensemble:
  StepFun-Formalizer-32B
  Goedel-Formalizer-V2-32B
Filter:
  Lean 4 compile/typecheck
  reject theorem statements that do not compile
  optionally ask a judge model to compare NL theorem vs Lean theorem
Optional proof stage:
  Goedel-Prover-V2-32B

For a single model, I would start with GuoxinChen/ReForm-32B. For a robust research pipeline, I would run ReForm-32B + StepFun-Formalizer-32B + Goedel-Formalizer-V2-32B, sample 8–16 candidates each, then typecheck in Lean and rank by semantic consistency. For proof generation after that, then use Goedel-Prover-V2-32B.

So the direct answer is: Goedel-Prove