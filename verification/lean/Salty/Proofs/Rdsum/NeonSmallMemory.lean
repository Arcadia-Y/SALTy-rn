import Salty.Proofs.Rdsum.NeonLastMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def afterFour (s : State) (output : Address) (low high : List (BitVec 32)) : State :=
  neonSmallStored s output 4 "vo" low high

def smallStored (s : State) (output : Address) (low high : List (BitVec 32)) (n : Nat) : State :=
  if n < 4 then lastStored s output low n
  else lastStored (afterFour s output low high) (output+16) high (n-4)

theorem small_defined_low (kind : Interpretation) (s : State) (output : Address)
    (low high : List (BitVec 32)) (ll : low.length = 4) (n : Nat) (small : n < 4)
    (defined : LastOriginalDefined kind s.memory output (low++high) n) :
    LastOriginalDefined kind s.memory output low n := by
  obtain ⟨a,b,c,d,rfl⟩ := list_four low ll
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · simp [LastOriginalDefined]
  · simpa [LastOriginalDefined] using defined
  · simp [LastOriginalDefined]
  · simpa [LastOriginalDefined] using defined

theorem small_defined_high (kind : Interpretation) (s : State) (output : Address)
    (low high : List (BitVec 32)) (ll : low.length = 4) (hl : high.length = 4)
    (n : Nat) (large : 4 ≤ n) (small : n < 8)
    (defined : LastOriginalDefined kind s.memory output (low++high) n) :
    LastOriginalDefined kind (afterFour s output low high).memory (output+16) high (n-4) := by
  have frame (column : Nat) (hc : column < 4) := readWord32_after_prefix_at s.memory output 4 column
    (encodeWords32 (storedWords s.memory output 4 low)) (by simp [ll]) (by omega)
  obtain ⟨a,b,c,d,rfl⟩ := list_four low ll
  obtain ⟨e,f,g,h,rfl⟩ := list_four high hl
  have cases : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · simp [LastOriginalDefined]
  · intro _
    simp only [Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    change ScalarStoreDefined kind
      (readWord32 (writeBytes s.memory output (encodeWords32 (storedWords s.memory output 4 [a,b,c,d]))) (output+BitVec.ofNat 64 (4*4))) e
    have old := frame 0 (by decide)
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at old
    rw [old]
    exact defined rfl
  · simp [LastOriginalDefined]
  · intro _
    simp only [Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    change ScalarStoreDefined kind
      (readWord32 (writeBytes s.memory output (encodeWords32 (storedWords s.memory output 4 [a,b,c,d]))) (output+BitVec.ofNat 64 (4*4)+BitVec.ofNat 64 (4*2))) g
    have old := frame 2 (by decide)
    rw [old]
    simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat]
    have address : output+16#64+8#64 = output+24#64 := by simp [BitVec.add_assoc]
    rw [address]
    exact defined rfl

theorem smallStored_memory (s : State) (output : Address) (low high : List (BitVec 32))
    (ll : low.length = 4) (hl : high.length = 4) (n : Nat) (small : n < 8) :
    (smallStored s output low high n).memory =
      writeBytes s.memory output (encodeWords32 (storedWords s.memory output n ((low++high).take n))) := by
  unfold smallStored
  split
  next h =>
    rw [lastStored_memory s output low ll n h, List.take_append_of_le_length (by omega)]
  next h =>
    rw [lastStored_memory _ _ high hl (n-4) (by omega)]
    have rlen : (high.take (n-4)).length = n-4 := by simp [hl]; omega
    have total : 4+(n-4) = n := by omega
    have take : (low++high).take n = low++high.take (n-4) := by
      rw [List.take_append_eq_append_take, List.take_of_length_le (by omega), ll]
    rw [take]
    have join := storedWords_write_join_after s.memory output low (high.take (n-4)) (by omega)
    simpa only [ll, rlen, total] using join

@[simp] theorem smallStored_channels (s : State) (output : Address) (low high : List (BitVec 32)) (n : Nat) :
    (smallStored s output low high n).locals "channels" = some (.integer 0) := by
  unfold smallStored
  split <;> exact lastStored_channels ..

end Salty.Kernels.Rdsum
