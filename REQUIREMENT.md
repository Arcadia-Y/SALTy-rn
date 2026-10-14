# Adding full verification support based on Lean for SALTY-rn

The current SALTY-rn is a LLM-powered SIMD kernel translation pipeline (Neon → RVV), with **bounded formal verification** of every translation. Your goal is to add full verification of the behavior equivalence of the input kernel and the outpur kernel based on Lean 4 theorem prover.

Specifically, you need to produce the following the artifacts:
- A Lean framework for proving the equivalence between Neon and RVV kernels (including Neon-Neno, RVV-RVV and Neon-RVV).
- Equivalence theorems for all 40 kernels in the test suite.
- A clean and highly readable technical report in the PDF form and no more than 12 pages (excluding references).

For the verification frameworks:
- The overall goal is to make the specification highly readable and human-understandable, but also provide reliable and strong enough guarantee.
- The specification is not limited to the final correctness theorem, but also the whole theory underlying the final theorem, including semantics, specification predicates, etc, that human needs to understand and trust.
- The framework should have necessary proof infrastructure, but since proof should be written completely by AI agents, this is less important than specification as long as it is completed.
- The semantic model is preferred to be built on the assembly level instead of the C level, as this is closer to the abstraction layer of the kernel.
- You can refer to the neighboring folder `assembly-verification` as a starting point, but you are not required to build upon that framework.

About the verification of the 40 kernels:
- It is preferred that the 40 kernels (or more precisely, series of kernels produced in the same translation procedure) share the same specification possibly with different parameters, because they intuitively are saying the same thing: "the two kernels have the same observable behaviors".
- You should not add Lean verification agent into the pipeline. All you need to do is a reusable verification framework as the foundation and the proved correctness theorems for all existing kernel testcases.

About the technical report:
- Like other technical reports, this report should present the core design of the semantics, specification and the proof framework cleanly.
- You should assuem readers have basic background in PL/verification and the SALTy-rn project.

Finally, you should create two sub-agents:
- one to review the code and check whether it satisfyingly implements this requirements.
- one to review the technical report and check whether it is readable, well-writtedn, reliable and faithful to the implementation.

You should stop working only if you've completely implemented the requirement and two review agents have both approved.