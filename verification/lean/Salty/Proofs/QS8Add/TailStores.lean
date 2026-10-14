import Salty.Proofs.QS8Add.NeonLanes

namespace Salty.Kernels.QS8Add
open CByte

def tailStore4 : Stmt :=
  .branch (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.lit 1)))))
    (.seq (.effect .storeLane32 [.var "output", .call .reinterpret32 [.var "vout01234567"], .lit 0])
      (.seq (.assign "output" (.offset 1 (.var "output") (.lit 4)))
        (.seq (.assign "vout01234567" (.call .extract8 [.var "vout01234567", .var "vout01234567", .lit 4])) .skip))) .skip

def tailStore2 : Stmt :=
  .branch (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 1)))))
    (.seq (.effect .storeLane16 [.var "output", .call .reinterpret16 [.var "vout01234567"], .lit 0])
      (.seq (.assign "output" (.offset 1 (.var "output") (.lit 2)))
        (.seq (.assign "vout01234567" (.call .extract8 [.var "vout01234567", .var "vout01234567", .lit 2])) .skip))) .skip

def tailStore1 : Stmt :=
  .branch (.cast .u64 (.bin .band (.var "batch") (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.lit 1)))))
    (.seq (.effect .storeLane8 [.var "output", .var "vout01234567", .lit 0]) .skip) .skip

def neonTailStores : Stmt := takeStatements 3 (match firstStatement (dropStatements 16 neonTailBody) with
  | .branch _ _ no => no
  | _ => .skip)

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
  update t "vout01234567" (.vector 1 (rotate8 bs width))

theorem tail_store4_body (cfg : Config) (s : State) (output : Address) (bs : List Byte) (m : Memory)
    (len : bs.length = 8)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout01234567" = some (.vector 1 bs))
    (store : storeBytes s.memory output (bs.take 4) = some m) :
    Exec cfg (branchBody tailStore4) s (tailAfter s output 4 bs m) := by
  apply run_sound (fuel := 8)
  simp [branchBody, tailStore4, run, eval, intrinsic, effect, storeLane, update,
    ptr, vec, len, store, tailAfter, rotate8]

theorem tail_store2_body (cfg : Config) (s : State) (output : Address) (bs : List Byte) (m : Memory)
    (len : bs.length = 8)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout01234567" = some (.vector 1 bs))
    (store : storeBytes s.memory output (bs.take 2) = some m) :
    Exec cfg (branchBody tailStore2) s (tailAfter s output 2 bs m) := by
  apply run_sound (fuel := 8)
  simp [branchBody, tailStore2, run, eval, intrinsic, effect, storeLane, update,
    ptr, vec, len, store, tailAfter, rotate8]

theorem tail_store1_body (cfg : Config) (s : State) (output : Address) (bs : List Byte) (m : Memory)
    (len : bs.length = 8)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout01234567" = some (.vector 1 bs))
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
    (vec : s.locals "vout01234567" = some (.vector 1 bs))
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


end Salty.Kernels.QS8Add
