import Salty.Proofs.Core.PackingMemory

namespace Salty.CByte

/-- Odd-channel writes occupy only the first word of each eight-byte slot. -/
theorem stride8_within (base p : Address) (n : Nat)
    (h : StridedFootprint base 8 n p) : Footprint base (8*n) p := by
  obtain ⟨lane, hi, byte, hb, address⟩ := h
  refine ⟨8*lane+byte, by omega, ?_⟩
  rw [address]
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

theorem writeStrided32_take (m : Memory) (base stride : Address) (bs : List Byte) (n : Nat) :
    writeStrided32 m base stride (bs.take (4*n)) n = writeStrided32 m base stride bs n := by
  induction n generalizing m base bs with
  | zero => rfl
  | succ n ih =>
    simp only [writeStrided32, List.take_take, List.drop_take]
    rw [show 4*(n+1)-4 = 4*n by omega, show min 4 (4*(n+1)) = 4 by omega, ih]

theorem writeStrided32_add (m : Memory) (base stride : Address) (bs : List Byte) (n k : Nat) :
    writeStrided32 m base stride bs (n+k) =
      writeStrided32 (writeStrided32 m base stride bs n)
        (base+stride*BitVec.ofNat 64 n) stride (bs.drop (4*n)) k := by
  induction n generalizing m base bs with
  | zero => simp [writeStrided32]
  | succ n ih =>
    simp only [Nat.succ_add, writeStrided32, ih, List.drop_drop]
    have address : base+stride+stride*BitVec.ofNat 64 n = base+stride*BitVec.ofNat 64 (n+1) := by
      rw [BitVec.ofNat_add, BitVec.mul_add]
      simp only [BitVec.ofNat_eq_ofNat, BitVec.mul_one]
      ac_rfl
    rw [address, show (0+4*n).succ.succ.succ.succ = 4*(n+1) by omega]

def singleResult (m : Memory) (input output : Address) (n : Nat) : Memory :=
  writeStrided32 m output 8 (readBytes m input (4*n)) n

@[simp] theorem singleResult_readable (m : Memory) (input output : Address) (n : Nat) :
    (singleResult m input output n).readable = m.readable := by simp [singleResult]

@[simp] theorem singleResult_writable (m : Memory) (input output : Address) (n : Nat) :
    (singleResult m input output n).writable = m.writable := by simp [singleResult]

theorem singleResult_frame (m : Memory) (input output p : Address) (n : Nat)
    (outside : ¬ StridedFootprint output 8 n p) : (singleResult m input output n).data p = m.data p :=
  writeStrided32_frame m output 8 p (readBytes m input (4*n)) n outside

theorem PairSafe.single_advance {m : Memory} {input output : Address} {n k : Nat}
    (safe : PairSafe m input input output n) (hk : k ≤ n) :
    PairSafe (singleResult m input output k) (input+BitVec.ofNat 64 (4*k))
      (input+BitVec.ofNat 64 (4*k)) (output+BitVec.ofNat 64 (8*k)) (n-k) := by
  constructor
  · intro p hp
    rw [singleResult_readable]
    exact safe.readA p (footprint_shift_within (by omega) hp)
  · intro p hp
    rw [singleResult_readable]
    exact safe.readA p (footprint_shift_within (by omega) hp)
  · intro p hp
    rw [singleResult_writable]
    exact safe.writable p (footprint_shift_within (by omega) hp)
  · intro p hi ho
    exact safe.separateA p (footprint_shift_within (by omega) hi) (footprint_shift_within (by omega) ho)
  · intro p hi ho
    exact safe.separateA p (footprint_shift_within (by omega) hi) (footprint_shift_within (by omega) ho)

theorem singleResult_split {m : Memory} {input output : Address} {n k : Nat}
    (safe : PairSafe m input input output n) (hk : k ≤ n) :
    singleResult m input output n =
      singleResult (singleResult m input output k) (input+BitVec.ofNat 64 (4*k))
        (output+BitVec.ofNat 64 (8*k)) (n-k) := by
  have reads : readBytes (singleResult m input output k) (input+BitVec.ofNat 64 (4*k)) (4*(n-k)) =
      readBytes m (input+BitVec.ofNat 64 (4*k)) (4*(n-k)) := by
    apply readBytes_writeStrided32_disjoint
    intro p hi ho
    exact safe.separateA p (footprint_shift_within (by omega) hi)
      (footprint_mono (by omega) (stride8_within output p k ho))
  have prefixPart := writeStrided32_take m output 8 (readBytes m input (4*n)) k
  rw [readBytes_take m input (4*k) (4*n) (by omega)] at prefixPart
  have suffixPart : (readBytes m input (4*n)).drop (4*k) =
      readBytes m (input+BitVec.ofNat 64 (4*k)) (4*(n-k)) := by
    have count : 4*n = 4*k+4*(n-k) := by omega
    rw [count, readBytes_add]
    simpa only [readBytes_length] using (List.drop_left (l₁ := readBytes m input (4*k))
      (l₂ := readBytes m (input+BitVec.ofNat 64 (4*k)) (4*(n-k))))
  change writeStrided32 m output 8 (readBytes m input (4*n)) n = _
  have partition := writeStrided32_add m output 8 (readBytes m input (4*n)) k (n-k)
  rw [show k+(n-k) = n by omega] at partition
  rw [partition, ← prefixPart, suffixPart]
  unfold singleResult
  change _ = writeStrided32 _ _ _ (readBytes (singleResult m input output k) _ _) _
  rw [reads]
  congr 1
  simp only [BitVec.ofNat_mul, BitVec.ofNat_eq_ofNat]

end Salty.CByte
