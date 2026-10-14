# Lean verification

**11 of 36 implemented NEON/RVV pairs have source-linked, unbounded behavior
proofs.** The other 25 remain unproved; four missing or empty targets are excluded.
At the user's direction, proof expansion stopped after the signed/unsigned row-sum
family. The delivery focuses on reviewable specifications, checked results, and
the [technical report](../output/pdf/report.pdf). No Lean agent is added to the pipeline.

## Read the specifications and established results

Start with [the common behavior definition](lean/Salty/Model/Behavior.lean), then
choose a family below. Each **Spec** file contains the actual caller contract and
reference result, without importing implementation proofs. Each **Results** file
states the checked whole-function guarantee explicitly. You do not need to read
loop invariants or proof tactics to determine what is claimed.

| Kernel pairs | Specification | Final results | Reference behavior |
| --- | --- | --- | --- |
| `s8-vclamp` | [S8Clamp](lean/Salty/Spec/S8Clamp.lean) | [S8Clamp](lean/Salty/Results/S8Clamp.lean) | Signed byte clamp using loaded, narrowed bounds |
| `qs8-vcvt` | [QS8Convert](lean/Salty/Spec/QS8Convert.lean) | [QS8Convert](lean/Salty/Results/QS8Convert.lean) | Wrapped difference/shift, rounded saturating product and output offset |
| `qs8-vlrelu` | [QS8Leaky](lean/Salty/Spec/QS8Leaky.lean) | [QS8Leaky](lean/Salty/Results/QS8Leaky.lean) | Quantized conversion with a sign-selected multiplier |
| `qs8-vadd-minmax` | [QS8Add](lean/Salty/Spec/QS8Add.lean) | [QS8Add](lean/Salty/Results/QS8Add.lean) | Signed two-input quantized clamped addition |
| `qu8-vadd-minmax` | [QU8Add](lean/Salty/Spec/QU8Add.lean) | [QU8Add](lean/Salty/Results/QU8Add.lean) | Unsigned two-input quantized clamped addition |
| `x32-transposec` | [X32Transpose](lean/Salty/Spec/X32Transpose.lean) | [X32Transpose](lean/Salty/Results/X32Transpose.lean) | Original-input matrix copy, including zero-dimension behavior |
| `x32-packw-gemm-goi` | [X32Pack](lean/Salty/Spec/X32Pack.lean) | [X32Pack](lean/Salty/Results/X32Pack.lean) | Group/channel tile layout, optional bias, preserved holes and gaps |
| `qs8-rsum`, `qu8-rsum` | [Rsum](lean/Salty/Spec/Rsum.lean) | [Rsum](lean/Salty/Results/Rsum.lean) | Original-byte sum plus the old scalar output |
| `qs8-rdsum`, `qu8-rdsum` | [Rdsum](lean/Salty/Spec/Rdsum.lean) | [Rdsum](lean/Salty/Results/Rdsum.lean) | Per-column original-byte sum plus each old output word |

The `Model` directory contains the shared machine and operation semantics, with
**no dependencies on kernel specifications**. [IntegerOps](lean/Salty/Model/IntegerOps.lean)
defines width-parameterized saturation, rounding, extension, multiplication, and
selection; [SIMD](lean/Salty/Model/SIMD.lean) supplies fixed instruction adapters.
`ShiftISA`, `ReductionISA`, and `WideningISA` describe reusable instruction behavior.
The interpreter does not call a kernel's `neonLane` or `rvvLane` calculation.

`Spec/*Lane.lean` holds quantized parameter records and composed lane calculations;
`Spec/QuantizedShift.lean` holds the kernels' scalar count decoding and repaired
shift sequence. `Spec/NaNRepair.lean` defines the supporting floating-point merge
repair, and `Spec/QS8ConvertLane.lean` also holds the widening/clip composition.
The family `Spec` files use these definitions to state caller
contracts and reference memories. `Generated` contains complete extracted source
and target programs. `Proofs/Core` and `Proofs/<family>` contain lemmas, invariants,
and implementation proofs. `Results` exposes final guarantees; `Examples` contains
finite regressions. Public result statements retain their original names and types.

The layout check permits Model → Model and Spec → Model/Spec dependencies. Both
layers reject proof imports and theorem commands; Generated imports only Model.CByte.
Lean still checks proof fields and termination obligations used in definitions.
The specialization lemmas in `Proofs/Core/SIMDSpecialization.lean` establish that
shared operations reproduce the previous fixed-width arithmetic formulas for every
operand. These do not assert a complete ISA model: instruction adapters still admit
only the supported widths, operand forms, and rounding modes.

## Shared extraction frontend

[extraction/extract.py](extraction/extract.py) invokes Clang and writes the models;
[frontend.py](extraction/frontend.py) contains the single AST translator. The
[extraction guide](extraction/README.md) describes its supported fragment and trust
boundary. Kernel configuration is data: `profiles.json` selects admitted features,
entry signatures and files; `intrinsics.json` gives checked call signatures and
model primitives; `abi.json` gives scalar representations, sizes and parameter
layouts. All these inputs are hashed in each family's provenance. The old
`extract_*.py` commands are small compatibility delegates with no translation rules.

The refactor preserves all 22 generated program declarations exactly. The full
mutation suite runs against the shared engine, with additional checks for profile
and extraction-state isolation. This is regression evidence, not a proof that the
frontend preserves C semantics.

## Meaning and limits

The common `Salty.Equivalent` relation compares all returned/fault outcomes and
implies divergence agreement. It works for NEON–NEON, RVV–RVV, and NEON–RVV without
an ISA-specific equality definition. The registered theorems prove that both
complete extracted functions terminate on their common caller domain and return
**exactly the same entire memory, including permissions**. The reference-result
proofs also preserve bytes outside the output. Timing, read traces, intermediate
registers, FP exception flags, and saturation flags are outside the observation.

Caller contracts expose dimensions, padding, alignment, nonwrapping bounds,
parameter memory, and aliasing restrictions. Pointwise inputs need seven readable
padding bytes; scalar reductions need 15 and permit input/output overlap because
all reads precede the sole store. Row sums require 15 readable padding bytes per
input row, zero padding through `max(channels,40)`, and output separate from input
and zero storage. Their vector additions wrap in 32 bits; the signed final scalar
store for an odd channel count must not overflow. Input rows may overlap.

The row-sum proof covers the actual seven-row substitutions, 252-row batches,
signed 16-channel / unsigned 32-channel main strips, eight-channel tails and
4/2/1 stores. Unsigned main-path 16-byte loads retain their full 40-byte group
footprint even though only their low eight lanes contribute. All row and channel
loops are unbounded within the explicit LP64 domain. RVV choices may be any
positive bounded lengths; scalar sums and packing additionally require capacity
at least eight. The architecture mapping is documented in the report.

Clang, the strict AST translator, fixed LP64 little-endian ABI, intrinsic
interpretations, and live C object/lifetime assumptions form a **trusted frontend
bridge**. Real source/target files are also checked against architecture headers.
This is source-linked intrinsic verification, not a proof of compiler output or
native machine code. `Model/ByteISA.lean` supplies a separate assembly-like byte
subset, but no suite theorem claims binary correspondence through it.

## Reproduce

Lean is pinned to `4.21.0-rc3`; no Mathlib or external Lean package is needed.
From `verification/lean`:

```sh
lake build
lake env lean Audit.lean
lake env lean Regression.lean
lake exe rdsum_regression
```

From the repository root:

```sh
python3 verification/check_layout.py
python3 verification/extraction/extract.py --family all --check
python3 verification/audit.py
RISCV_CLANG=/path/to/llvm/bin/clang python3 verification/run_checks.py
python3 verification/report/build.py
```

The complete runner needs Python 3, an AArch64 host with FPCR=0, a native Clang
with NEON and sanitizers, and an LLVM installation with RVV headers and RISC-V
code generation. Set `EXTRACTION_CLANG` to the recorded extraction compiler if
needed. Set `CVC5_PREFIX` to a cvc5 1.3.2 SDK to include the concrete-mask adapter
regression. The legacy bitwuzla adapter is unchanged.

The gate regenerates source models and provenance, checks exact theorem types and
nonempty caller witnesses, and audits axioms. Registered results use only standard
`propext`, `Quot.sound`, and `Classical.choice`; no custom equivalence axioms,
`sorryAx`, or native Boolean-reduction axioms are admitted. The dependency gate
complements these checks: a human must still review the definitions and contracts.

`coverage.json` records all 40 sources, hashes, exclusions and theorem names.
`audit.py --require-complete` intentionally fails because 25 implemented pairs
remain unproved. `--refresh` resets registration rather than certifying new models.
Ordinary audit success means the recorded proofs are valid, not that all kernels
have been verified.

## Repairs and regression evidence

[REPAIRS.md](REPAIRS.md) documents all 17 changed targets, counterexamples, repair
details, and remaining limits. Four of these repaired targets have whole-function
proofs here: quantized conversion, transpose, and signed/unsigned quantized addition.
The other repairs have bounded regression evidence and supporting arithmetic
lemmas where stated; they do not count toward the 11 proved pairs.

The five sanitizer-backed C regression programs cover actual source/target C:
packed depthwise layout, sparse FMA/pointer carry, exponential reduction order,
quantization, NaN propagation, convolution access masks, transpose edge cases,
and all 256 effective quantized-add shift counts. They run NEON natively and an
RVV instruction interpreter at VLEN 128/256/512. They do not execute native RISC-V
binaries. Compiled Lean regressions additionally compare reductions, packing and
row sums to independent finite oracles at block/tail boundaries. Such finite
checks supplement the unbounded theorems and never promote pending coverage.
