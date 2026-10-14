import Salty.Proofs.QS8Convert.Execution

namespace Salty.Kernels.QS8Convert
open CByte

def neonTail : Stmt := firstStatement (dropStatements 8 Generated.QS8Convert.neon)
def neonTailBody : Stmt := match neonTail with
  | .branch _ body _ => body
  | _ => .skip

def neonTailStores : Stmt := dropStatements 8 neonTailBody

def tailStore4 : Stmt :=
  .branch (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1)))))
    (.seq (.effect .storeLane32 [.var "output", .call .reinterpret32 [.var "vy_2"], .lit 0])
      (.seq (.assign "output" (.offset 1 (.var "output") (.lit 4)))
        (.seq (.assign "vy_2" (.call .extract8 [.var "vy_2", .var "vy_2", .lit 4])) .skip))) .skip

def tailStore2 : Stmt :=
  .branch (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1)))))
    (.seq (.effect .storeLane16 [.var "output", .call .reinterpret16 [.var "vy_2"], .lit 0])
      (.seq (.assign "output" (.offset 1 (.var "output") (.lit 2)))
        (.seq (.assign "vy_2" (.call .extract8 [.var "vy_2", .var "vy_2", .lit 2])) .skip))) .skip

def tailStore1 : Stmt :=
  .branch (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1)))))
    (.seq (.effect .storeLane8 [.var "output", .var "vy_2", .lit 0]) .skip) .skip

/-- Kernel-checked syntactic projection of the extracted program. -/
theorem neonTailStores_shape : neonTailStores =
    .seq tailStore4 (.seq tailStore2 (.seq tailStore1 .skip)) := rfl

theorem neon_tail_zero (cfg : Config) (s : State)
    (batch : s.locals "batch" = some (.integer 0)) : Exec cfg neonTailStores s s := by
  have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 0) := by
    simp [eval, binary, convert, batch, Int.max_def]
  have e2 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 0) := by
    simp [eval, binary, convert, batch, Int.max_def]
  have e1 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 0) := by
    simp [eval, binary, convert, batch, Int.max_def]
  rw [neonTailStores_shape]
  exact .seq (.no e4 rfl .skip) (.seq (.no e2 rfl .skip) (.seq (.no e1 rfl .skip) .skip))

def branchBody : Stmt → Stmt
  | .branch _ body _ => body
  | _ => .skip

def rotate8 (bs : List Byte) (width : Nat) : List Byte := ((bs ++ bs).drop width).take 8

def tailAfter (s : State) (output : Address) (width : Nat) (bs : List Byte) (m : Memory) : State :=
  let t := { s with memory := m }
  let t := update t "output" (.pointer (output + BitVec.ofNat 64 width))
  update t "vy_2" (.vector 1 (rotate8 bs width))

theorem tail_store4_body (cfg : Config) (s : State) (output : Address) (bs : List Byte) (m : Memory)
    (len : bs.length = 8)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vy_2" = some (.vector 1 bs))
    (store : storeBytes s.memory output (bs.take 4) = some m) :
    Exec cfg (branchBody tailStore4) s (tailAfter s output 4 bs m) := by
  apply run_sound (fuel := 8)
  simp [branchBody, tailStore4, run, eval, intrinsic, effect, storeLane, update,
    ptr, vec, len, store, tailAfter, rotate8]

theorem tail_store2_body (cfg : Config) (s : State) (output : Address) (bs : List Byte) (m : Memory)
    (len : bs.length = 8)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vy_2" = some (.vector 1 bs))
    (store : storeBytes s.memory output (bs.take 2) = some m) :
    Exec cfg (branchBody tailStore2) s (tailAfter s output 2 bs m) := by
  apply run_sound (fuel := 8)
  simp [branchBody, tailStore2, run, eval, intrinsic, effect, storeLane, update,
    ptr, vec, len, store, tailAfter, rotate8]

theorem tail_store1_body (cfg : Config) (s : State) (output : Address) (bs : List Byte) (m : Memory)
    (len : bs.length = 8)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vy_2" = some (.vector 1 bs))
    (store : storeBytes s.memory output (bs.take 1) = some m) :
    Exec cfg (branchBody tailStore1) s { s with memory := m } := by
  apply run_sound (fuel := 4)
  simp [branchBody, tailStore1, run, eval, effect, storeLane, ptr, vec, len, store]

/-- Every legal residual length executes the extracted store suffix and
writes exactly its prefix, with the complete final memory specified. -/
theorem neon_tail_stores (cfg : Config) (s : State) (n : Nat) (output : Address)
    (bs : List Byte) (short : n < 8) (len : bs.length = 8)
    (batch : s.locals "batch" = some (.integer n))
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vy_2" = some (.vector 1 bs))
    (safe : ∀ a, Footprint output n a → s.memory.writable a = true) :
    ∃ t, Exec cfg neonTailStores s t ∧
      t.memory = writeBytes s.memory output (bs.take n) := by
  obtain ⟨b0, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  obtain ⟨b1, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  obtain ⟨b2, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  obtain ⟨b3, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  obtain ⟨b4, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  obtain ⟨b5, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  obtain ⟨b6, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  obtain ⟨b7, bs, rfl⟩ := List.exists_cons_of_length_pos (l := bs) (by (try simp only [List.length_cons] at len); omega)
  have last : bs = [] := List.length_eq_zero_iff.mp (by (try simp only [List.length_cons] at len); omega)
  subst bs
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨s, neon_tail_zero cfg s (by simpa using batch), rfl⟩
  · have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    have h4 : Exec cfg tailStore4 s s := .no e4 rfl .skip
    have e2 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    have h2 : Exec cfg tailStore2 s s := .no e2 rfl .skip
    have e1 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 1) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    let m1 := writeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 1)
    let t1 := { s with memory := m1 }
    have store1 : storeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 1) = some m1 := by
      apply storeBytes_success
      intro a ha
      exact safe a (footprint_mono (n := 1) (by decide) (by simpa using ha))
    have h1 : Exec cfg tailStore1 s t1 := by
      apply Exec.yes e1 (by rfl)
      apply tail_store1_body cfg s output ([b0,b1,b2,b3,b4,b5,b6,b7]) m1
      · rfl
      · simp [tailAfter, update, ptr, BitVec.add_assoc]
      · simp [tailAfter, update, vec, rotate8]
      · exact store1
    refine ⟨t1, ?_, ?_⟩
    · rw [neonTailStores_shape]
      exact .seq h4 (.seq h2 (.seq h1 .skip))
    · simp [m1, t1, tailAfter, update, rotate8, writeBytes, BitVec.add_assoc]
  · have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    have h4 : Exec cfg tailStore4 s s := .no e4 rfl .skip
    have e2 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 2) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    let m2 := writeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 2)
    let t2 := tailAfter s output 2 ([b0,b1,b2,b3,b4,b5,b6,b7]) m2
    have store2 : storeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 2) = some m2 := by
      apply storeBytes_success
      intro a ha
      exact safe a (footprint_mono (n := 2) (by decide) (by simpa using ha))
    have h2 : Exec cfg tailStore2 s t2 := by
      apply Exec.yes e2 (by rfl)
      apply tail_store2_body cfg s output ([b0,b1,b2,b3,b4,b5,b6,b7]) m2
      · rfl
      · simp [tailAfter, update, ptr, BitVec.add_assoc]
      · simp [tailAfter, update, vec, rotate8]
      · exact store2
    have e1 : eval cfg t2 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, m2, t2, tailAfter, update, batch]
    have h1 : Exec cfg tailStore1 t2 t2 := .no e1 rfl .skip
    refine ⟨t2, ?_, ?_⟩
    · rw [neonTailStores_shape]
      exact .seq h4 (.seq h2 (.seq h1 .skip))
    · simp [m2, t2, tailAfter, update, rotate8, writeBytes, BitVec.add_assoc]
  · have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    have h4 : Exec cfg tailStore4 s s := .no e4 rfl .skip
    have e2 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 2) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    let m2 := writeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 2)
    let t2 := tailAfter s output 2 ([b0,b1,b2,b3,b4,b5,b6,b7]) m2
    have store2 : storeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 2) = some m2 := by
      apply storeBytes_success
      intro a ha
      exact safe a (footprint_mono (n := 2) (by decide) (by simpa using ha))
    have h2 : Exec cfg tailStore2 s t2 := by
      apply Exec.yes e2 (by rfl)
      apply tail_store2_body cfg s output ([b0,b1,b2,b3,b4,b5,b6,b7]) m2
      · rfl
      · simp [tailAfter, update, ptr, BitVec.add_assoc]
      · simp [tailAfter, update, vec, rotate8]
      · exact store2
    have e1 : eval cfg t2 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 1) := by
      simp [eval, binary, convert, Int.max_def, m2, t2, tailAfter, update, batch]
    let m1 := writeBytes t2.memory (output + 2#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 2).take 1)
    let t1 := { t2 with memory := m1 }
    have store1 : storeBytes t2.memory (output + 2#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 2).take 1) = some m1 := by
      apply storeBytes_success
      intro a ha
      simp only [m2, t2, tailAfter, update, writeBytes_writable]
      apply safe a
      have hs := footprint_shift output a 1 2 (by simpa [rotate8] using ha)
      exact footprint_mono (by decide) hs
    have h1 : Exec cfg tailStore1 t2 t1 := by
      apply Exec.yes e1 (by rfl)
      apply tail_store1_body cfg t2 (output + 2#64) (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 2) m1
      · rfl
      · simp [m2, t2, tailAfter, update, ptr, BitVec.add_assoc]
      · simp [m2, t2, tailAfter, update, vec, rotate8]
      · exact store1
    refine ⟨t1, ?_, ?_⟩
    · rw [neonTailStores_shape]
      exact .seq h4 (.seq h2 (.seq h1 .skip))
    · simp [m2, t2, m1, t1, tailAfter, update, rotate8, writeBytes, BitVec.add_assoc]
  · have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 4) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    let m4 := writeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4)
    let t4 := tailAfter s output 4 ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
    have store4 : storeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4) = some m4 := by
      apply storeBytes_success
      intro a ha
      exact safe a (footprint_mono (n := 4) (by decide) (by simpa using ha))
    have h4 : Exec cfg tailStore4 s t4 := by
      apply Exec.yes e4 (by rfl)
      apply tail_store4_body cfg s output ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
      · rfl
      · simp [tailAfter, update, ptr, BitVec.add_assoc]
      · simp [tailAfter, update, vec, rotate8]
      · exact store4
    have e2 : eval cfg t4 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, tailAfter, update, batch]
    have h2 : Exec cfg tailStore2 t4 t4 := .no e2 rfl .skip
    have e1 : eval cfg t4 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, tailAfter, update, batch]
    have h1 : Exec cfg tailStore1 t4 t4 := .no e1 rfl .skip
    refine ⟨t4, ?_, ?_⟩
    · rw [neonTailStores_shape]
      exact .seq h4 (.seq h2 (.seq h1 .skip))
    · simp [m4, t4, tailAfter, update, rotate8, writeBytes, BitVec.add_assoc]
  · have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 4) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    let m4 := writeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4)
    let t4 := tailAfter s output 4 ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
    have store4 : storeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4) = some m4 := by
      apply storeBytes_success
      intro a ha
      exact safe a (footprint_mono (n := 4) (by decide) (by simpa using ha))
    have h4 : Exec cfg tailStore4 s t4 := by
      apply Exec.yes e4 (by rfl)
      apply tail_store4_body cfg s output ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
      · rfl
      · simp [tailAfter, update, ptr, BitVec.add_assoc]
      · simp [tailAfter, update, vec, rotate8]
      · exact store4
    have e2 : eval cfg t4 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, tailAfter, update, batch]
    have h2 : Exec cfg tailStore2 t4 t4 := .no e2 rfl .skip
    have e1 : eval cfg t4 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 1) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, tailAfter, update, batch]
    let m1 := writeBytes t4.memory (output + 4#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4).take 1)
    let t1 := { t4 with memory := m1 }
    have store1 : storeBytes t4.memory (output + 4#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4).take 1) = some m1 := by
      apply storeBytes_success
      intro a ha
      simp only [m4, t4, tailAfter, update, writeBytes_writable]
      apply safe a
      have hs := footprint_shift output a 1 4 (by simpa [rotate8] using ha)
      exact footprint_mono (by decide) hs
    have h1 : Exec cfg tailStore1 t4 t1 := by
      apply Exec.yes e1 (by rfl)
      apply tail_store1_body cfg t4 (output + 4#64) (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) m1
      · rfl
      · simp [m4, t4, tailAfter, update, ptr, BitVec.add_assoc]
      · simp [m4, t4, tailAfter, update, vec, rotate8]
      · exact store1
    refine ⟨t1, ?_, ?_⟩
    · rw [neonTailStores_shape]
      exact .seq h4 (.seq h2 (.seq h1 .skip))
    · simp [m4, t4, m1, t1, tailAfter, update, rotate8, writeBytes, BitVec.add_assoc]
  · have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 4) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    let m4 := writeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4)
    let t4 := tailAfter s output 4 ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
    have store4 : storeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4) = some m4 := by
      apply storeBytes_success
      intro a ha
      exact safe a (footprint_mono (n := 4) (by decide) (by simpa using ha))
    have h4 : Exec cfg tailStore4 s t4 := by
      apply Exec.yes e4 (by rfl)
      apply tail_store4_body cfg s output ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
      · rfl
      · simp [tailAfter, update, ptr, BitVec.add_assoc]
      · simp [tailAfter, update, vec, rotate8]
      · exact store4
    have e2 : eval cfg t4 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 2) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, tailAfter, update, batch]
    let m2 := writeBytes t4.memory (output + 4#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4).take 2)
    let t2 := tailAfter t4 (output + 4#64) 2 (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) m2
    have store2 : storeBytes t4.memory (output + 4#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4).take 2) = some m2 := by
      apply storeBytes_success
      intro a ha
      simp only [m4, t4, tailAfter, update, writeBytes_writable]
      apply safe a
      have hs := footprint_shift output a 2 4 (by simpa [rotate8] using ha)
      exact footprint_mono (by decide) hs
    have h2 : Exec cfg tailStore2 t4 t2 := by
      apply Exec.yes e2 (by rfl)
      apply tail_store2_body cfg t4 (output + 4#64) (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) m2
      · rfl
      · simp [m4, t4, tailAfter, update, ptr, BitVec.add_assoc]
      · simp [m4, t4, tailAfter, update, vec, rotate8]
      · exact store2
    have e1 : eval cfg t2 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 0) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, m2, t2, tailAfter, update, batch]
    have h1 : Exec cfg tailStore1 t2 t2 := .no e1 rfl .skip
    refine ⟨t2, ?_, ?_⟩
    · rw [neonTailStores_shape]
      exact .seq h4 (.seq h2 (.seq h1 .skip))
    · simp [m4, t4, m2, t2, tailAfter, update, rotate8, writeBytes, BitVec.add_assoc]
  · have e4 : eval cfg s (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1))))) = some (.integer 4) := by
      simp [eval, binary, convert, Int.max_def, tailAfter, update, batch]
    let m4 := writeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4)
    let t4 := tailAfter s output 4 ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
    have store4 : storeBytes s.memory output (([b0,b1,b2,b3,b4,b5,b6,b7]).take 4) = some m4 := by
      apply storeBytes_success
      intro a ha
      exact safe a (footprint_mono (n := 4) (by decide) (by simpa using ha))
    have h4 : Exec cfg tailStore4 s t4 := by
      apply Exec.yes e4 (by rfl)
      apply tail_store4_body cfg s output ([b0,b1,b2,b3,b4,b5,b6,b7]) m4
      · rfl
      · simp [tailAfter, update, ptr, BitVec.add_assoc]
      · simp [tailAfter, update, vec, rotate8]
      · exact store4
    have e2 : eval cfg t4 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1))))) = some (.integer 2) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, tailAfter, update, batch]
    let m2 := writeBytes t4.memory (output + 4#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4).take 2)
    let t2 := tailAfter t4 (output + 4#64) 2 (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) m2
    have store2 : storeBytes t4.memory (output + 4#64) ((rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4).take 2) = some m2 := by
      apply storeBytes_success
      intro a ha
      simp only [m4, t4, tailAfter, update, writeBytes_writable]
      apply safe a
      have hs := footprint_shift output a 2 4 (by simpa [rotate8] using ha)
      exact footprint_mono (by decide) hs
    have h2 : Exec cfg tailStore2 t4 t2 := by
      apply Exec.yes e2 (by rfl)
      apply tail_store2_body cfg t4 (output + 4#64) (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) m2
      · rfl
      · simp [m4, t4, tailAfter, update, ptr, BitVec.add_assoc]
      · simp [m4, t4, tailAfter, update, vec, rotate8]
      · exact store2
    have e1 : eval cfg t2 (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1))))) = some (.integer 1) := by
      simp [eval, binary, convert, Int.max_def, m4, t4, m2, t2, tailAfter, update, batch]
    let m1 := writeBytes t2.memory (output + 6#64) ((rotate8 (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) 2).take 1)
    let t1 := { t2 with memory := m1 }
    have store1 : storeBytes t2.memory (output + 6#64) ((rotate8 (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) 2).take 1) = some m1 := by
      apply storeBytes_success
      intro a ha
      simp only [m4, t4, m2, t2, tailAfter, update, writeBytes_writable]
      apply safe a
      have hs := footprint_shift output a 1 6 (by simpa [rotate8] using ha)
      exact footprint_mono (by decide) hs
    have h1 : Exec cfg tailStore1 t2 t1 := by
      apply Exec.yes e1 (by rfl)
      apply tail_store1_body cfg t2 (output + 6#64) (rotate8 (rotate8 ([b0,b1,b2,b3,b4,b5,b6,b7]) 4) 2) m1
      · rfl
      · simp [m4, t4, m2, t2, tailAfter, update, ptr, BitVec.add_assoc]
      · simp [m4, t4, m2, t2, tailAfter, update, vec, rotate8]
      · exact store1
    refine ⟨t1, ?_, ?_⟩
    · rw [neonTailStores_shape]
      exact .seq h4 (.seq h2 (.seq h1 .skip))
    · simp [m4, t4, m2, t2, m1, t1, tailAfter, update, rotate8, writeBytes, BitVec.add_assoc]

def neonTailPrep : Stmt := takeStatements 8 neonTailBody

def tailPrepAfter (s : State) (p : QuantizedISA.Params) (bs : List Byte) : State :=
  let t := update s "vx_2" (.vector 1 bs)
  let t := update t "vacc_2" (.halfwords (bs.map (neonAccumulator p)))
  update t "vy_2" (.vector 1 (bs.map (QuantizedISA.neonLane p)))

set_option maxHeartbeats 1000000 in
theorem neon_tail_prep (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : QuantizedISA.Params) (bs : List Byte) (locals : NeonLocals s n input output p)
    (pos : 0 < n) (short : n < 8)
    (len : bs.length = 8) (load : loadBytes s.memory input 8 = some bs) :
    Exec cfg neonTailPrep s (tailPrepAfter s p bs) := by
  have ht {α : Type} (f : Byte → α) : (bs.map f).take 8 = bs.map f := by
    apply List.take_of_length_le
    simp [len]
  have hb : bs.take 8 = bs := by simp [← len]
  have zr {α β γ : Type} (f : α → β → γ) (xs : List α) (x : β) :
      List.zipWith f xs [x,x,x,x,x,x,x,x] = (xs.take 8).map (fun b => f b x) :=
    zip_replicate_right f xs x 8
  have zl {α β γ : Type} (f : α → β → γ) (x : α) (xs : List β) :
      List.zipWith f [x,x,x,x,x,x,x,x] xs = (xs.take 8).map (f x) :=
    zip_replicate_left f x xs 8
  have c1 : convert .u64 1 = 1 := rfl
  have c7 : convert .u64 7 = 7 := rfl
  apply run_sound (fuel := 20)
  simp +contextual (maxSteps := 1000000) [neonTailPrep, neonTailBody, neonTail,
    firstStatement, dropStatements, takeStatements, Generated.QS8Convert.neon,
    run, eval, intrinsic, saturatingIntrinsic, effect, update, binary, truth,
    locals.batch, locals.inputPtr, locals.inputZero, locals.multiplier, locals.outputZero,
    len, load, zr, zl, ht, hb, tailPrepAfter, QuantizedISA.neonLane, neonAccumulator,
    List.map_map, Function.comp_def, c1, c7, show (1 : Int) ≤ n by omega,
    show (n : Int) ≤ 7 by omega]
  rfl

/-- Complete extracted source tail, with checked residual-length assertions,
padded vector load, all conversion instructions and 4/2/1 stores. -/
theorem neon_tail_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : QuantizedISA.Params) (locals : NeonLocals s n input output p) (short : n < 8)
    (readable : n ≠ 0 → ∀ a, Footprint input 8 a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output n a → s.memory.writable a = true) :
    ∃ t, Exec cfg neonTail s t ∧
      t.memory = writeBytes s.memory output ((readBytes s.memory input n).map (QuantizedISA.neonLane p)) := by
  by_cases zero : n = 0
  · subst n
    refine ⟨s, ?_, rfl⟩
    apply Exec.no (v := .integer 0)
    · simp [neonTail, firstStatement, dropStatements, Generated.QS8Convert.neon,
        eval, binary, convert, locals.batch]
    · rfl
    · exact .skip
  · let bs := readBytes s.memory input 8
    let prep := tailPrepAfter s p bs
    have hprep : Exec cfg neonTailPrep s prep := neon_tail_prep cfg s n input output p bs locals
      (by omega) short (readBytes_length ..) (loadBytes_success _ _ _ (readable zero))
    obtain ⟨t, hstores, hm⟩ := neon_tail_stores cfg prep n output (bs.map (QuantizedISA.neonLane p)) short
      (by simp [bs])
      (by simp [prep, tailPrepAfter, update, locals.batch])
      (by simp [prep, tailPrepAfter, update, locals.outputPtr])
      (by simp [prep, tailPrepAfter, update]) writable
    refine ⟨t, ?_, ?_⟩
    · apply Exec.yes (v := .integer 1)
      · simp [neonTail, firstStatement, dropStatements, Generated.QS8Convert.neon,
          eval, binary, convert, locals.batch, zero]
      · rfl
      · exact exec_take_drop 8 hprep hstores
    · rw [hm]
      change writeBytes s.memory output ((bs.map (QuantizedISA.neonLane p)).take n) = _
      rw [← List.map_take, readBytes_take _ _ _ _ (by omega)]

end Salty.Kernels.QS8Convert
