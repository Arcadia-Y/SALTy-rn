# Translation repairs


The [report's repair section](report/report.tex) summarizes all 17 edited targets.
The following details are part of their correctness contract:

1. `qs8-vcvt`: remove the overflowing doubled product; round at shift 15 instead
   of shift 16 after doubling. The input -128 with zero point 128, multiplier
   32768, output zero point 0 distinguishes old (-128) and source/repaired (127).
2. `f32-dwconv-minmax`: each bias/filter block contains four packed weights.
   Tile at most four channels and advance weights by four even in a short tail.
3. `f32-spmm-minmax`: use FMA, preserving single rounding. Also preserve the
   source's 4/2/1 strips and carry the input pointer after sparse-map updates.
   A zero-sum map is no longer required merely to hide pointer divergence.
4. `f32-raddstoreexpminusmax`: retain four accumulator lanes, pairwise AArch64
   final addition, and the 2/1-element tail order. The sequence `[0,-17,...,-17]`
   with seven -17 values exposes the old reduction-order discrepancy.
5. Binary `f32-vadd/vsub/vmul/vdiv/vmin/vmax/vmulc` and unary `f32-vsqrt`: restore
   operand NaN payload/sign and quieting for AArch64 FPCR=0. Binary priority is
   first signaling NaN, then first quiet NaN. Exception flags are not matched.
6. `qs8-vmul-minmax-fp32`: follow bias-add/reinterpret/saturating-subtract from
   the source. Conversion plus wrapping addition fails at scale 2^31 and output
   zero point 1. Restore a NaN scale's sign/payload after RVV arithmetic.
7. `f32-conv-hwc2chw`: mask the strided memory access itself. Merging after an
   unconditional load still touches invalid padding addresses. A cvc5 adapter
   was added for concrete access masks so the new intrinsic is recognized.

8. `x32-transposec`: the source executes its do-loop at width zero, aliases the
   second output column to the first, and leaves input column zero in output.
   The old RVV while-loop skipped all writes. With input `[7,9]`, height 1,
   input/output strides 8/4 and zero-initialized output, source returns `[7]`
   while old RVV leaves `[0]`. Set effective RVV width to one for width zero.
   Also skip the outer loop at height zero: `(NULL,NULL,0,0,0,0)` and
   `(NULL,NULL,12,0,3,0)` must touch no memory or perform null-pointer arithmetic.
   A reviewer caught that empty-height edge in the first repair. Regression
   covers both null-pointer calls, zero dimensions, padding and both permitted
   strided-store orders.

9. `qs8-vadd-minmax` and `qu8-vadd-minmax`: NEON `SRSHL` interprets the signed low byte of the
   negated raw shift; RVV `VSSRA` masks to five bits and only shifts right.
   With one input byte 1, second input 0, multipliers 1/0, zero points 0,
   bounds -128/127, and raw shift 32, source gives 0 but the old target gives 1.
   Negative raw shifts also require left shifts (e.g. -1 gives 2 for that input).
   Decode the low byte using unsigned negation, select zero for counts outside
   (-32,32), rounded arithmetic right shift for negative counts, and wrapping
   left shift otherwise. Counts such as raw 256 must act as zero, not be rejected
   merely because they lie outside the usual quantizer range. Source negation of
   `INT32_MIN` remains undefined; this value cannot enter a source-equivalence
   caller domain. `Proofs/Core/ShiftISA.lean` proves the instruction-level repair for all
   accumulator and raw-count bit patterns; `Salty.Kernels.QS8Add.behavior_equivalent`
   proves both signed-add functions on the explicit defined caller domain.
   The unsigned-add witness uses the same inputs and shift with bounds 0/255:
   native source gives 0 while the old target gives 1. Its old direction branch
   also used the raw count rather than the signed low byte, so large positive
   and negative counts both require the same decoded-count repair. The unsigned
   kernel's whole-function theorem is `Salty.Kernels.QU8Add.behavior_equivalent`,
   with its own actual caller/parameter-load proof. The extended regression
   includes its actual source/target, unsigned widening subtraction, explicit
   16-bit signed reinterpretation, and signed-to-unsigned saturating narrow.
   The native sanitizer regression covers every effective count and overflow
   multipliers. The real RVV header/code-generation check covers the new branches.
   Instruction references: [Arm SRSHL reference](https://documentation-service.arm.com/static/6245c734b059dc5ff9a8bdab)
   and [RISC-V scaling shifts](https://docs.riscv.org/reference/isa/unpriv/v-st-ext).

These changes prioritize equivalence over throughput. Performance is unmeasured.
Other floating-point kernels remain outside the established whole-function proofs.
