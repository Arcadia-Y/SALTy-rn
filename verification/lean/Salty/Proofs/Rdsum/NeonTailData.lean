import Salty.Proofs.Rdsum.NeonZero

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

def neonTailVin (kind : Interpretation) (i : Nat) : String :=
  match kind, i with
  | .signed, 0 => "vin0_2" | .unsigned, 4 => "vin4_2"
  | _, 0 => "vin0" | _, 1 => "vin1" | _, 2 => "vin2" | _, 3 => "vin3"
  | _, 4 => "vin4" | _, 5 => "vin5" | _, _ => "vin6"

def neonTailLoaded (kind : Interpretation) (s : State) (rows : Nat → List Byte) : State :=
  let s := update s (neonTailVin kind 0) (.vector 1 (rows 0))
  let s := update s (neonTailVin kind 1) (.vector 1 (rows 1))
  let s := update s (neonTailVin kind 2) (.vector 1 (rows 2))
  let s := update s (neonTailVin kind 3) (.vector 1 (rows 3))
  let s := update s (neonTailVin kind 4) (.vector 1 (rows 4))
  let s := update s (neonTailVin kind 5) (.vector 1 (rows 5))
  let s := update s (neonTailVin kind 6) (.vector 1 (rows 6))
  s

def neonTailAdded (kind : Interpretation) (s : State) (rows : Nat → List Byte) (acc : List (BitVec 16)) : State :=
  let s := update s (neonHalfName kind false 0) (.halfwords (rowAcc kind rows acc 1))
  let s := update s (neonHalfName kind false 0) (.halfwords (rowAcc kind rows acc 2))
  let s := update s (neonHalfName kind false 0) (.halfwords (rowAcc kind rows acc 3))
  let s := update s (neonHalfName kind false 0) (.halfwords (rowAcc kind rows acc 4))
  let s := update s (neonHalfName kind false 0) (.halfwords (rowAcc kind rows acc 5))
  let s := update s (neonHalfName kind false 0) (.halfwords (rowAcc kind rows acc 6))
  let s := update s (neonHalfName kind false 0) (.halfwords (rowAcc kind rows acc 7))
  s

def neonPointersAfter (main : Bool) (s : State) (pointers : Nat → Address) (increment : Nat) : State :=
  let s := update s (neonRowName main 0) (.pointer (pointers 0+BitVec.ofNat 64 increment))
  let s := update s (neonRowName main 1) (.pointer (pointers 1+BitVec.ofNat 64 increment))
  let s := update s (neonRowName main 2) (.pointer (pointers 2+BitVec.ofNat 64 increment))
  let s := update s (neonRowName main 3) (.pointer (pointers 3+BitVec.ofNat 64 increment))
  let s := update s (neonRowName main 4) (.pointer (pointers 4+BitVec.ofNat 64 increment))
  let s := update s (neonRowName main 5) (.pointer (pointers 5+BitVec.ofNat 64 increment))
  let s := update s (neonRowName main 6) (.pointer (pointers 6+BitVec.ofNat 64 increment))
  s

def neonTailData (kind : Interpretation) : Stmt := dropStatements 6 (neonGroup kind false)

def neonTailDataAfter (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (increment : Nat) (rows : Nat → List Byte) (acc : List (BitVec 16)) : State :=
  let s := neonTailLoaded kind s rows
  match kind with
  | .signed => neonPointersAfter false (neonTailAdded kind s rows acc) pointers increment
  | .unsigned => neonTailAdded kind (neonPointersAfter false s pointers increment) rows acc

def neonTailLoadsCode (kind : Interpretation) : Stmt :=
  (.seq (.assign (neonTailVin kind 0) (.call .load8 [(.offset 1 (.var (neonRowName false 0)) (.lit 0))]))
  (.seq (.assign (neonTailVin kind 1) (.call .load8 [(.offset 1 (.var (neonRowName false 1)) (.lit 0))]))
  (.seq (.assign (neonTailVin kind 2) (.call .load8 [(.offset 1 (.var (neonRowName false 2)) (.lit 0))]))
  (.seq (.assign (neonTailVin kind 3) (.call .load8 [(.offset 1 (.var (neonRowName false 3)) (.lit 0))]))
  (.seq (.assign (neonTailVin kind 4) (.call .load8 [(.offset 1 (.var (neonRowName false 4)) (.lit 0))]))
  (.seq (.assign (neonTailVin kind 5) (.call .load8 [(.offset 1 (.var (neonRowName false 5)) (.lit 0))]))
  (.seq (.assign (neonTailVin kind 6) (.call .load8 [(.offset 1 (.var (neonRowName false 6)) (.lit 0))]))
  .skip)))))))

def neonTailAddsCode (kind : Interpretation) : Stmt :=
  (.seq (.assign (neonHalfName kind false 0) (.call (rowBytePrim kind) [.var (neonHalfName kind false 0), .var (neonTailVin kind 0)]))
  (.seq (.assign (neonHalfName kind false 0) (.call (rowBytePrim kind) [.var (neonHalfName kind false 0), .var (neonTailVin kind 1)]))
  (.seq (.assign (neonHalfName kind false 0) (.call (rowBytePrim kind) [.var (neonHalfName kind false 0), .var (neonTailVin kind 2)]))
  (.seq (.assign (neonHalfName kind false 0) (.call (rowBytePrim kind) [.var (neonHalfName kind false 0), .var (neonTailVin kind 3)]))
  (.seq (.assign (neonHalfName kind false 0) (.call (rowBytePrim kind) [.var (neonHalfName kind false 0), .var (neonTailVin kind 4)]))
  (.seq (.assign (neonHalfName kind false 0) (.call (rowBytePrim kind) [.var (neonHalfName kind false 0), .var (neonTailVin kind 5)]))
  (.seq (.assign (neonHalfName kind false 0) (.call (rowBytePrim kind) [.var (neonHalfName kind false 0), .var (neonTailVin kind 6)]))
  .skip)))))))

def neonPointersCode (main : Bool) : Stmt :=
  (.seq (.assign (neonRowName main 0) (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var (neonRowName main 0))) (.var "input_increment")))))
  (.seq (.assign (neonRowName main 1) (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var (neonRowName main 1))) (.var "input_increment")))))
  (.seq (.assign (neonRowName main 2) (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var (neonRowName main 2))) (.var "input_increment")))))
  (.seq (.assign (neonRowName main 3) (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var (neonRowName main 3))) (.var "input_increment")))))
  (.seq (.assign (neonRowName main 4) (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var (neonRowName main 4))) (.var "input_increment")))))
  (.seq (.assign (neonRowName main 5) (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var (neonRowName main 5))) (.var "input_increment")))))
  (.seq (.assign (neonRowName main 6) (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var (neonRowName main 6))) (.var "input_increment")))))
  .skip)))))))

theorem neon_tail_loads_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address)
    (ptr : ∀ i, i < 7 → s.locals (neonRowName false i) = some (.pointer (pointers i)))
    (safe : ∀ i, i < 7 → ∀ a, Footprint (pointers i) 8 a → s.memory.readable a = true) :
    Exec cfg (neonTailLoadsCode kind) s (neonTailLoaded kind s (fun i => readBytes s.memory (pointers i) 8)) := by
  have p0 := ptr 0 (by decide)
  have l0 := loadBytes_success s.memory (pointers 0) 8 (safe 0 (by decide))
  have p1 := ptr 1 (by decide)
  have l1 := loadBytes_success s.memory (pointers 1) 8 (safe 1 (by decide))
  have p2 := ptr 2 (by decide)
  have l2 := loadBytes_success s.memory (pointers 2) 8 (safe 2 (by decide))
  have p3 := ptr 3 (by decide)
  have l3 := loadBytes_success s.memory (pointers 3) 8 (safe 3 (by decide))
  have p4 := ptr 4 (by decide)
  have l4 := loadBytes_success s.memory (pointers 4) 8 (safe 4 (by decide))
  have p5 := ptr 5 (by decide)
  have l5 := loadBytes_success s.memory (pointers 5) 8 (safe 5 (by decide))
  have p6 := ptr 6 (by decide)
  have l6 := loadBytes_success s.memory (pointers 6) 8 (safe 6 (by decide))
  simp only [neonRowName, Bool.false_eq_true, ↓reduceIte] at p0 p1 p2 p3 p4 p5 p6
  cases kind <;> apply run_sound (fuel := 10) <;>
    simp [neonTailLoadsCode, neonTailLoaded, neonTailVin, neonRowName,
      run, eval, intrinsic, update_locals, update_memory,
      p0,p1,p2,p3,p4,p5,p6,l0,l1,l2,l3,l4,l5,l6]

 theorem neon_tail_adds_exec (kind : Interpretation) (cfg : Config) (s : State)
    (rows : Nat → List Byte) (acc : List (BitVec 16)) (ha : acc.length = 8)
    (hr : ∀ i, (rows i).length = 8)
    (vacc : s.locals (neonHalfName kind false 0) = some (.halfwords acc))
    (vin : ∀ i, i < 7 → s.locals (neonTailVin kind i) = some (.vector 1 (rows i))) :
    Exec cfg (neonTailAddsCode kind) s (neonTailAdded kind s rows acc) := by
  have v0 := vin 0 (by decide)
  have v1 := vin 1 (by decide)
  have v2 := vin 2 (by decide)
  have v3 := vin 3 (by decide)
  have v4 := vin 4 (by decide)
  have v5 := vin 5 (by decide)
  have v6 := vin 6 (by decide)
  have a1 := rowAcc_length kind rows acc 8 ha hr 1
  simp only [rowAcc] at a1
  have a2 := rowAcc_length kind rows acc 8 ha hr 2
  simp only [rowAcc] at a2
  have a3 := rowAcc_length kind rows acc 8 ha hr 3
  simp only [rowAcc] at a3
  have a4 := rowAcc_length kind rows acc 8 ha hr 4
  simp only [rowAcc] at a4
  have a5 := rowAcc_length kind rows acc 8 ha hr 5
  simp only [rowAcc] at a5
  have a6 := rowAcc_length kind rows acc 8 ha hr 6
  simp only [rowAcc] at a6
  cases kind <;> simp only [neonHalfName, neonTailVin, Bool.false_eq_true, ↓reduceIte] at vacc v0 v1 v2 v3 v4 v5 v6
  all_goals
    apply run_sound (fuel := 10)
    simp [neonTailAddsCode, neonTailAdded, neonHalfName, neonTailVin, rowBytePrim, rowAcc,
      run, eval, intrinsic, update_locals, update_memory, ha, hr, vacc,
      v0,v1,v2,v3,v4,v5,v6,a1,a2,a3,a4,a5,a6]

 theorem neon_pointers_exec (cfg : Config) (s : State) (main : Bool) (pointers : Nat → Address) (increment : Nat)
    (ptr : ∀ i, i < 7 → s.locals (neonRowName main i) = some (.pointer (pointers i)))
    (step : s.locals "input_increment" = some (.integer increment)) :
    Exec cfg (neonPointersCode main) s (neonPointersAfter main s pointers increment) := by
  have cast (a : Address) :
      BitVec.ofInt 64 (convert .u64 ((a.toNat : Int)+increment)) = a+BitVec.ofNat 64 increment := by
    simp only [convert, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast]
    simp
  have p0 := ptr 0 (by decide)
  have p1 := ptr 1 (by decide)
  have p2 := ptr 2 (by decide)
  have p3 := ptr 3 (by decide)
  have p4 := ptr 4 (by decide)
  have p5 := ptr 5 (by decide)
  have p6 := ptr 6 (by decide)
  cases main <;> simp only [neonRowName, rowName, Bool.false_eq_true, ↓reduceIte] at p0 p1 p2 p3 p4 p5 p6
  all_goals
    apply run_sound (fuel := 10)
    simp [neonPointersCode, neonPointersAfter, neonRowName, rowName,
      run, eval, binary, cast, update_locals, update_memory, step,p0,p1,p2,p3,p4,p5,p6]

theorem neon_tail_data_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (increment : Nat) (acc : List (BitVec 16)) (ha : acc.length = 8)
    (ptr : ∀ i, i < 7 → s.locals (neonRowName false i) = some (.pointer (pointers i)))
    (vacc : s.locals (neonHalfName kind false 0) = some (.halfwords acc))
    (step : s.locals "input_increment" = some (.integer increment))
    (safe : ∀ i, i < 7 → ∀ a, Footprint (pointers i) 8 a → s.memory.readable a = true) :
    Exec cfg (neonTailData kind) s (neonTailDataAfter kind s pointers increment
      (fun i => readBytes s.memory (pointers i) 8) acc) := by
  let rows := fun i => readBytes s.memory (pointers i) 8
  let l := neonTailLoaded kind s rows
  have load : Exec cfg (neonTailLoadsCode kind) s l := neon_tail_loads_exec kind cfg s pointers ptr safe
  have lp : ∀ i, i < 7 → l.locals (neonRowName false i) = some (.pointer (pointers i)) := by
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    exact (load.locals_frame _ (by rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;> rfl)).trans (ptr i hi)
  have la : l.locals (neonHalfName kind false 0) = some (.halfwords acc) :=
    (load.locals_frame _ (by cases kind <;> rfl)).trans vacc
  have ls : l.locals "input_increment" = some (.integer increment) := (load.locals_frame _ (by cases kind <;> rfl)).trans step
  have lv : ∀ i, i < 7 → l.locals (neonTailVin kind i) = some (.vector 1 (rows i)) := by
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;>
      simp [l, neonTailLoaded, neonTailVin, update_locals]
  apply exec_take_drop (t := l) 7
  · have shape : takeStatements 7 (neonTailData kind) = neonTailLoadsCode kind := by cases kind <;> rfl
    rw [shape]; exact load
  · cases kind with
    | signed =>
      let a := neonTailAdded .signed l rows acc
      have add : Exec cfg (neonTailAddsCode .signed) l a := neon_tail_adds_exec .signed cfg l rows acc ha (fun i => readBytes_length ..) la lv
      apply exec_take_drop (t := a) 7
      · exact add
      · apply neon_pointers_exec cfg a false pointers increment
        · intro i hi
          have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
          exact (add.locals_frame _ (by rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (lp i hi)
        · exact (add.locals_frame _ (by rfl)).trans ls
    | unsigned =>
      let p := neonPointersAfter false l pointers increment
      have advance : Exec cfg (neonPointersCode false) l p := neon_pointers_exec cfg l false pointers increment lp ls
      apply exec_take_drop (t := p) 7
      · exact advance
      · apply neon_tail_adds_exec .unsigned cfg p rows acc ha (fun i => readBytes_length ..)
        · exact (advance.locals_frame _ (by rfl)).trans la
        · intro i hi
          have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
          exact (advance.locals_frame _ (by rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (lv i hi)

@[simp] theorem neonTailDataAfter_memory (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (increment : Nat) (rows : Nat → List Byte) (acc : List (BitVec 16)) :
    (neonTailDataAfter kind s pointers increment rows acc).memory = s.memory := by cases kind <;> rfl

theorem neonTailDataAfter_acc (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (increment : Nat) (rows : Nat → List Byte) (acc : List (BitVec 16)) :
    (neonTailDataAfter kind s pointers increment rows acc).locals (neonHalfName kind false 0) =
      some (.halfwords (rowAcc kind rows acc 7)) := by
  cases kind <;> simp [neonTailDataAfter, neonTailAdded, neonPointersAfter, neonHalfName, neonRowName, update_locals]

theorem neonTailDataAfter_row (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (increment : Nat) (rows : Nat → List Byte) (acc : List (BitVec 16)) (i : Nat) (hi : i < 7) :
    (neonTailDataAfter kind s pointers increment rows acc).locals (neonRowName false i) =
      some (.pointer (pointers i+BitVec.ofNat 64 increment)) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;>
    simp [neonTailDataAfter, neonTailAdded, neonPointersAfter, neonHalfName, neonRowName, update_locals]

end Salty.Kernels.Rdsum
