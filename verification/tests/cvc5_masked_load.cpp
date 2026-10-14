#include <cassert>
#include <iostream>
#include "../../src/verification_cvc5/salt.hpp"
using namespace salt_cvc5;
int main() {
    VerificationContext context(128);
    g_ctx = &context;
    float input[2] = {1.0f, 2.0f};
    auto& buffer = context.registerBuffer("input", sizeof(input));
    buffer.bind(input);
    auto& tm = context.tm;
    const Term keep = tm.mkBitVector(32, 0x12345678);
    RVVVector old(tm, 32, {keep, keep, keep, keep});
    MaskVector mask(tm, {tm.mkBitVector(1, 0), tm.mkBitVector(1, 1)});
    const float* shifted = reinterpret_cast<const float*>(reinterpret_cast<uintptr_t>(input) - 4);
    auto result = __riscv_vlse32_v_f32m1_tumu(mask, old, shifted, 4, 2);
    assert(result.getVL() == 4);
    assert(result.getElement(0) == keep);
    assert(result.getElement(1) == buffer.loadScalar(0, 32));
    assert(result.getElement(2) == keep && result.getElement(3) == keep);
    bool rejected = false;
    try {
        MaskVector symbolic(tm, {tm.mkConst(tm.mkBitVectorSort(1), "mask")});
        (void)__riscv_vlse32_v_f32m1_tumu(symbolic, old, shifted, 4, 1);
    } catch (const std::runtime_error&) { rejected = true; }
    assert(rejected);
    g_ctx = nullptr;
    std::cout << "cvc5 masked load: skips invalid inactive address, preserves mask/tails, rejects symbolic mask\n";
}
