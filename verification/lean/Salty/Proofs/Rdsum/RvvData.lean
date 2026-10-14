import Salty.Proofs.Rdsum.RvvInstructions

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

def rowAcc (kind : Interpretation) (rows : Nat → List Byte) (initial : List (BitVec 16)) : Nat → List (BitVec 16)
  | 0 => initial
  | n+1 => WideningISA.widenAdd16 kind (rowAcc kind rows initial n) (rows n)

theorem rowAcc_length (kind : Interpretation) (rows : Nat → List Byte) (initial : List (BitVec 16))
    (n : Nat) (hi : initial.length = n) (hr : ∀ i, (rows i).length = n) (count : Nat) :
    (rowAcc kind rows initial count).length = n := by
  induction count with
  | zero => exact hi
  | succ k ih =>
    change (WideningISA.widenAdd16 kind (rowAcc kind rows initial k) (rows k)).length = n
    rw [WideningISA.widenAdd16_length kind _ _ (ih.trans (hr k).symm), ih]

def rvvData (kind : Interpretation) : Stmt := takeStatements 14 (dropStatements 6 (rvvGroup kind))

def rvvDataAfter (kind : Interpretation) (s : State) (rows : Nat → List Byte)
    (initial : List (BitVec 16)) : State :=
  match kind with
  | .signed =>
    let s := update s "vin0" (.vector 1 (rows 0))
    let s := update s "vin1" (.vector 1 (rows 1))
    let s := update s "vin2" (.vector 1 (rows 2))
    let s := update s "vin3" (.vector 1 (rows 3))
    let s := update s "vin4" (.vector 1 (rows 4))
    let s := update s "vin5" (.vector 1 (rows 5))
    let s := update s "vin6" (.vector 1 (rows 6))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 1))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 2))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 3))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 4))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 5))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 6))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 7))
    s
  | .unsigned =>
    let s := update s "vin0" (.vector 1 (rows 0))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 1))
    let s := update s "vin1" (.vector 1 (rows 1))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 2))
    let s := update s "vin2" (.vector 1 (rows 2))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 3))
    let s := update s "vin3" (.vector 1 (rows 3))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 4))
    let s := update s "vin4" (.vector 1 (rows 4))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 5))
    let s := update s "vin5" (.vector 1 (rows 5))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 6))
    let s := update s "vin6" (.vector 1 (rows 6))
    let s := update s "vacc16" (.halfwords (rowAcc kind rows initial 7))
    s

theorem rvv_data_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (n : Nat) (acc : List (BitVec 16))
    (cap : n ≤ cfg.capacity) (ha : acc.length = n)
    (ptr : ∀ i, i < 7 → s.locals (rowName i) = some (.pointer (pointers i)))
    (vl : s.locals "vl" = some (.integer n))
    (vacc : s.locals "vacc16" = some (.halfwords acc))
    (safe : ∀ i, i < 7 → ∀ a, Footprint (pointers i) n a → s.memory.readable a = true) :
    Exec cfg (rvvData kind) s
      (rvvDataAfter kind s (fun i => readBytes s.memory (pointers i) n) acc) := by
  have loads (i : Nat) (hi : i < 7) := loadBytes_success s.memory (pointers i) n (safe i hi)
  have lengths (k : Nat) :
      (rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc k).length = n :=
    rowAcc_length kind _ acc n ha (fun i => readBytes_length ..) k
  have p0 := ptr 0 (by decide)
  have l0 := loads 0 (by decide)
  have p1 := ptr 1 (by decide)
  have l1 := loads 1 (by decide)
  have p2 := ptr 2 (by decide)
  have l2 := loads 2 (by decide)
  have p3 := ptr 3 (by decide)
  have l3 := loads 3 (by decide)
  have p4 := ptr 4 (by decide)
  have l4 := loads 4 (by decide)
  have p5 := ptr 5 (by decide)
  have l5 := loads 5 (by decide)
  have p6 := ptr 6 (by decide)
  have l6 := loads 6 (by decide)
  have t1 : (rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 1).take n =
      rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 1 :=
    List.take_of_length_le (by simp only [lengths, Nat.le_refl])
  have a1 := lengths 1
  simp only [rowAcc] at t1 a1
  have t2 : (rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 2).take n =
      rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 2 :=
    List.take_of_length_le (by simp only [lengths, Nat.le_refl])
  have a2 := lengths 2
  simp only [rowAcc] at t2 a2
  have t3 : (rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 3).take n =
      rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 3 :=
    List.take_of_length_le (by simp only [lengths, Nat.le_refl])
  have a3 := lengths 3
  simp only [rowAcc] at t3 a3
  have t4 : (rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 4).take n =
      rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 4 :=
    List.take_of_length_le (by simp only [lengths, Nat.le_refl])
  have a4 := lengths 4
  simp only [rowAcc] at t4 a4
  have t5 : (rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 5).take n =
      rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 5 :=
    List.take_of_length_le (by simp only [lengths, Nat.le_refl])
  have a5 := lengths 5
  simp only [rowAcc] at t5 a5
  have t6 : (rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 6).take n =
      rowAcc kind (fun i => readBytes s.memory (pointers i) n) acc 6 :=
    List.take_of_length_le (by simp only [lengths, Nat.le_refl])
  have a6 := lengths 6
  simp only [rowAcc] at t6 a6
  simp only [rowName] at p0 p1 p2 p3 p4 p5 p6
  cases kind <;> apply run_sound (fuel := 20) <;>
    simp [rvvData, rvvGroup, rvvBatches, rvvChannels, rvvProgram,
      Generated.QS8Rdsum.rvv, Generated.QU8Rdsum.rvv, dropStatements, firstStatement,
      takeStatements, loopBody, rvvDataAfter, run, eval, intrinsic, wideningIntrinsic,
      update_locals, update_memory, rowName, vl, vacc, cap, ha,
      p0,p1,p2,p3,p4,p5,p6,l0,l1,l2,l3,l4,l5,l6,
      rowAcc, WideningISA.widenAdd16_length, List.take_of_length_le, t1,t2,t3,t4,t5,t6,a1,a2,a3,a4,a5,a6]

@[simp] theorem rvvDataAfter_memory (kind : Interpretation) (s : State)
    (rows : Nat → List Byte) (initial : List (BitVec 16)) :
    (rvvDataAfter kind s rows initial).memory = s.memory := by
  cases kind <;> simp [rvvDataAfter, update_memory]

theorem rvvDataAfter_acc (kind : Interpretation) (s : State)
    (rows : Nat → List Byte) (initial : List (BitVec 16)) :
    (rvvDataAfter kind s rows initial).locals "vacc16" =
      some (.halfwords (rowAcc kind rows initial 7)) := by
  cases kind <;> simp [rvvDataAfter, update_locals]

theorem rvvDataAfter_row (kind : Interpretation) (s : State)
    (rows : Nat → List Byte) (initial : List (BitVec 16)) (i : Nat) (hi : i < 7) :
    (rvvDataAfter kind s rows initial).locals (rowName i) = s.locals (rowName i) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases kind <;> simp [rvvDataAfter, update_locals, rowName]

theorem rowAcc_fold (kind : Interpretation) (rows : Nat → List Byte)
    (initial : List (BitVec 16)) (n : Nat) :
    rowAcc kind rows initial n =
      (List.range n).foldl (fun acc i => WideningISA.widenAdd16 kind acc (rows i)) initial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rowAcc, List.range_succ, List.foldl_append, ih]

end Salty.Kernels.Rdsum
