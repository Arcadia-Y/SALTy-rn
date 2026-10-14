import Salty.Proofs.Rdsum.NeonTail
import Salty.Proofs.Core.CByteBlocks

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def mainLoadWidth : Interpretation → Nat
  | .signed => 8
  | .unsigned => 16

def mainVin (kind : Interpretation) (chunk : Nat) : String :=
  match kind, chunk with
  | .signed, 0 => "vin0" | .signed, _ => "vin8"
  | .unsigned, 0 => "vin4" | .unsigned, 1 => "vin12"
  | .unsigned, 2 => "vin20" | .unsigned, _ => "vin28"

def mainRowCode (kind : Interpretation) (row : String) : Stmt :=
  match kind with
  | .signed =>
    .seq (.assign "vin0" (.call .load8 [.offset 1 (.var row) (.lit 0)]))
    (.seq (.assign "vin8" (.call .load8 [.offset 1 (.var row) (.lit 8)]))
    (.seq (.assign "vacc16_0" (.call .widenAddByte16S [.var "vacc16_0", .var "vin0"]))
    (.seq (.assign "vacc16_8" (.call .widenAddByte16S [.var "vacc16_8", .var "vin8"])) .skip)))
  | .unsigned =>
    .seq (.assign "vin4" (.call .load16 [.offset 1 (.var row) (.lit 0)]))
    (.seq (.assign "vin12" (.call .load16 [.offset 1 (.var row) (.lit 8)]))
    (.seq (.assign "vin20" (.call .load16 [.offset 1 (.var row) (.lit 16)]))
    (.seq (.assign "vin28" (.call .load16 [.offset 1 (.var row) (.lit 24)]))
    (.seq (.assign "vacc16_4" (.call .widenAddByte16U [.var "vacc16_4", .call .low8 [.var "vin4"]]))
    (.seq (.assign "vacc16_12" (.call .widenAddByte16U [.var "vacc16_12", .call .low8 [.var "vin12"]]))
    (.seq (.assign "vacc16_20" (.call .widenAddByte16U [.var "vacc16_20", .call .low8 [.var "vin20"]]))
    (.seq (.assign "vacc16_28" (.call .widenAddByte16U [.var "vacc16_28", .call .low8 [.var "vin28"]])) .skip)))))))

def mainRowAcc (kind : Interpretation) (m : Memory) (ptr : Address)
    (acc : Nat → List (BitVec 16)) (chunk : Nat) : List (BitVec 16) :=
  WideningISA.widenAdd16 kind (acc chunk) (readBytes m (ptr+BitVec.ofNat 64 (8*chunk)) 8)

def mainRowLoaded (kind : Interpretation) (s : State) (ptr : Address) : State :=
  let m := s.memory
  let s := update s (mainVin kind 0) (.vector 1 (readBytes m ptr (mainLoadWidth kind)))
  let s := update s (mainVin kind 1) (.vector 1 (readBytes m (ptr+8) (mainLoadWidth kind)))
  match kind with
  | .signed => s
  | .unsigned =>
    let s := update s "vin20" (.vector 1 (readBytes m (ptr+16) 16))
    update s "vin28" (.vector 1 (readBytes m (ptr+24) 16))

def mainRowAfter (kind : Interpretation) (s : State) (ptr : Address)
    (acc : Nat → List (BitVec 16)) : State :=
  let next := mainRowAcc kind s.memory ptr acc
  let s := mainRowLoaded kind s ptr
  let s := update s (neonHalfName kind true 0) (.halfwords (next 0))
  let s := update s (neonHalfName kind true 1) (.halfwords (next 1))
  match kind with
  | .signed => s
  | .unsigned =>
    let s := update s "vacc16_20" (.halfwords (next 2))
    update s "vacc16_28" (.halfwords (next 3))

/-- One source main-path row. Unsigned source loads are 16 bytes even though
only their low eight lanes contribute to each accumulator. -/
theorem main_row_exec (kind : Interpretation) (cfg : Config) (s : State) (row : String) (ptr : Address)
    (acc : Nat → List (BitVec 16))
    (distinct : row ∉ ["vin0", "vin8", "vin4", "vin12", "vin20", "vin28"])
    (hp : s.locals row = some (.pointer ptr))
    (ha : ∀ j, j < neonChunks kind true → (acc j).length = 8)
    (hv : ∀ j, j < neonChunks kind true → s.locals (neonHalfName kind true j) = some (.halfwords (acc j)))
    (safe : ∀ j, j < neonChunks kind true → ∀ a,
      Footprint (ptr+BitVec.ofNat 64 (8*j)) (mainLoadWidth kind) a → s.memory.readable a = true) :
    Exec cfg (mainRowCode kind row) s (mainRowAfter kind s ptr acc) := by
  have n0 : row ≠ "vin0" := by intro h; apply distinct; simp [h]
  have n8 : row ≠ "vin8" := by intro h; apply distinct; simp [h]
  have n4 : row ≠ "vin4" := by intro h; apply distinct; simp [h]
  have n12 : row ≠ "vin12" := by intro h; apply distinct; simp [h]
  have n20 : row ≠ "vin20" := by intro h; apply distinct; simp [h]
  have n28 : row ≠ "vin28" := by intro h; apply distinct; simp [h]
  cases kind with
  | signed =>
    have a0 := ha 0 (by decide); have a1 := ha 1 (by decide)
    have v0 := hv 0 (by decide); have v1 := hv 1 (by decide)
    have l0 := loadBytes_success s.memory (ptr+BitVec.ofNat 64 (8*0)) 8 (safe 0 (by decide))
    have l1 := loadBytes_success s.memory (ptr+BitVec.ofNat 64 (8*1)) 8 (safe 1 (by decide))
    simp only [neonHalfName, ↓reduceIte] at v0 v1
    simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at l0 l1
    apply run_sound (fuel := 7)
    simp [mainRowCode, mainRowAfter, mainRowLoaded, mainRowAcc, mainVin, mainLoadWidth, neonHalfName,
      run, eval, intrinsic, update, hp, n0,n8,n4,n12,n20,n28,a0,a1,v0,v1,l0,l1]
  | unsigned =>
    have a0 := ha 0 (by decide); have a1 := ha 1 (by decide)
    have a2 := ha 2 (by decide); have a3 := ha 3 (by decide)
    have v0 := hv 0 (by decide); have v1 := hv 1 (by decide)
    have v2 := hv 2 (by decide); have v3 := hv 3 (by decide)
    have l0 := loadBytes_success s.memory (ptr+BitVec.ofNat 64 (8*0)) 16 (safe 0 (by decide))
    have l1 := loadBytes_success s.memory (ptr+BitVec.ofNat 64 (8*1)) 16 (safe 1 (by decide))
    have l2 := loadBytes_success s.memory (ptr+BitVec.ofNat 64 (8*2)) 16 (safe 2 (by decide))
    have l3 := loadBytes_success s.memory (ptr+BitVec.ofNat 64 (8*3)) 16 (safe 3 (by decide))
    simp only [neonHalfName, ↓reduceIte] at v0 v1 v2 v3
    simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at l0 l1 l2 l3
    apply run_sound (fuel := 11)
    simp [mainRowCode, mainRowAfter, mainRowLoaded, mainRowAcc, mainVin, mainLoadWidth, neonHalfName,
      run, eval, intrinsic, update, hp, n0,n8,n4,n12,n20,n28,a0,a1,a2,a3,v0,v1,v2,v3,l0,l1,l2,l3,
      readBytes_take s.memory ptr 8 16 (by decide), readBytes_take s.memory (ptr+8#64) 8 16 (by decide),
      readBytes_take s.memory (ptr+16#64) 8 16 (by decide), readBytes_take s.memory (ptr+24#64) 8 16 (by decide)]

end Salty.Kernels.Rdsum
