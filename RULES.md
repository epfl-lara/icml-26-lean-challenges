Rules
Only fill in the sorry placeholders in the challenge files. Do not modify any other part of those files.
Do not change the import statements in the challenge files.
Non-challenge files (definitions, lakefile.toml, lean-toolchain) must not be altered.
You may create new auxiliary files if needed, but the proofs must compile without additional imports beyond what is already in each challenge file.
Only the three standard axioms are permitted: propext, Quot.sound, and Classical.choice.
Tie breaks, scoring details, and the audit requirement for finalists are on the Scoring Rules page.

Track 2 Scoring Rules
How submissions are scored and how the final ranking is determined for the TCS Proving in Lean track.

Overview
Track 2 has 34 scored challenges worth 1000 points in total, split across two phases.

Phase	Area	Challenges	Points
Phase 1	Binary Heap and Dijkstra	7	200
Minimum Spanning Tree	1	100
Segment Tree	4	100
Treap analysis (probabilistic)	2	40
Treap algorithms	15	60
Phase 2	Splay Tree sequential	1	50
Splay Tree deque	1	50
Splay Tree Deque Conjecture (open problem)	1	100
Splay Tree Traversal Conjecture (open problem)	1	200
Spanner	1	100
Total	34	1000
The Splay Tree challenges include two long standing open problems in dynamic data structures, both due to Sleator and Tarjan. The Deque Conjecture (file Challenge_Splay_DequeConjecture.lean, 100 pts) asks for a tighter c · n bound on the same input class as the regular Splay deque challenge (sequences avoiding both 213 and 231). The Traversal Conjecture (file Challenge_Splay_TraversalConjecture.lean, 200 pts) asks for the same c · n bound on the broader class of sequences avoiding only 231, which covers BST preorder, postorder, and other traversal patterns. A successful resolution of either would be a major theoretical result in its own right.

Per problem scoring
A challenge scores its full points if and only if all of the following hold for the named scored declaration in the submitted file.

The file builds with no error under the locked toolchain (Lean v4.28.0, Mathlib v4.28.0, CSLib v4.28.0).
The proof uses no sorry and introduces no custom axioms (only Lean's three classical axioms propext, Quot.sound, Classical.choice are permitted).
The declaration's type matches the reference signature. Changing the statement (loosening the bound, removing hypotheses, adding parameters, etc.) is rejected.
All three checks are performed in one step by the SafeVerify tool, which compares the participant olean against the reference olean for each scored theorem. There is no partial credit on a single challenge: a challenge either earns its full point value or zero.

Final ranking cascade
The final ranking is computed on the combined Phase 1 and Phase 2 score out of 700. Two submissions are ranked by the first criterion below on which they differ.

Total score (descending).
Higher total wins.
Smaller constant on the Traversal Conjecture (ascending).
If both submissions solved this problem, the one proving the tighter constant in the time bound wins. A submission that did not solve the problem ranks below one that did. If neither solved it, this level is skipped. This is the top quality tie break because the Traversal Conjecture is the hardest scored challenge in the track.
Smaller constant on the Deque Conjecture (ascending).
Same idea, applied to the Deque Conjecture.
Smaller constant on the Splay Tree deque problem (ascending).
Same idea, applied to the regular Splay deque challenge.
Smaller constant on the Splay Tree sequential problem (ascending).
Same idea, applied to the Splay sequential challenge.
Proof heartbeats (ascending).
Heartbeats are Lean's deterministic measure of elaboration work, machine independent and stable run to run for a fixed toolchain. The more efficient proof wins.
Proof file size in bytes (ascending).
UTF-8 bytes of the submitted files with all comments stripped. The more concise proof wins.
Submission time (ascending).
The earlier submission wins.
Why this order
Track 2 is a TCS theorem proving challenge, so we want the final ranking to reflect proof quality as directly as possible. The Splay Tree constants are the most direct signal we have, because they are part of the theorem statement that you either prove or do not prove. Heartbeats and file size are coarser quality proxies that we keep as further fallbacks. Submission time sits at the very end on purpose. On a track where solution quality is the whole point, we do not want first mover advantage to dominate solution quality.

About proof heartbeats
A heartbeat in Lean is an internal unit used to bound how long elaboration and tactics are allowed to run. Roughly speaking, one user-facing heartbeat corresponds to about 1000 small memory allocations, so it is not equivalent to wall-clock time, but it gives a deterministic measure of work. That is why Lean's timeout messages say (deterministic) timeout: the result does not depend on how fast your machine is.

This is exactly the property we need from a ranking tie-breaker. Wall-clock build time would not be reproducible across grading machines, but heartbeats are. The number we record per submission is the delta of IO.getNumHeartbeats across one fresh re-elaboration of each passing challenge file with Elab.async set to false, summed across passing challenges. The same proof on the same toolchain produces the same number on any machine.

For background, see Leo de Moura's note in the Heartbeats topic on the Lean Zulip and the Lean reference documentation on IO timing.

Phase note
The same cascade applies to both phases. Phase 1 submissions that did not attempt Phase 2 are scored against the same combined total of 700 and ranked alongside submissions that attempted both. No retroactive penalty is applied to early submissions; the Splay Tree levels of the cascade simply do not differentiate submissions that did not solve those problems, and the ranking falls through to heartbeats, bytes, and time.