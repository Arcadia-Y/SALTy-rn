import Salty.Proofs.Rdsum.NeonMainStore

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

theorem mainWordPrefix_values (values : Nat → BitVec 32) (count : Nat) :
    mainWordPrefix (wordValues values) count = (List.range (4*count)).map values := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [mainWordPrefix, ih, Nat.mul_add, Nat.mul_one, List.range_add, List.map_append, List.map_map]
    rfl

theorem mainOutputWords_values (m : Memory) (output : Address) (values : Nat → BitVec 32) :
    mainOutputWords m output (wordValues values) =
      wordValues (fun column => readWord32 m (output+BitVec.ofNat 64 (4*column))+values column) := by
  funext word
  unfold mainOutputWords wordValues
  rw [storedWords_columns]
  apply List.map_congr_left
  intro lane hl
  congr 2
  simp only [Nat.mul_add, ← Nat.mul_assoc, BitVec.ofNat_add, BitVec.add_assoc]

def neonMainOutput (kind : Interpretation) : Stmt :=
  takeStatements (1+5*(neonWidth kind true/4))
    (dropStatements (9+neonWidth kind true/4) (neonChannels kind true))

theorem neon_main_output_shape (kind : Interpretation) : neonMainOutput kind =
    appendStatements (neonMainLoadAdd kind) (mainStoreCode (neonWidth kind true/4)) := by
  cases kind <;> rfl

/-- All old output words are loaded before the first store. The complete fixed
width output block equals a single scalar-specification write to memory. -/
theorem neon_main_output_correct (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (values : Nat → BitVec 32)
    (out : s.locals "output" = some (.pointer output))
    (words : ∀ word, word < neonWidth kind true/4 → s.locals (neonWordName true word) = some (.words32 (wordValues values word)))
    (readable : ∀ a, Footprint output (4*neonWidth kind true) a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output (4*neonWidth kind true) a → s.memory.writable a = true) :
    ∃ t, Exec cfg (neonMainOutput kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 ((List.range (neonWidth kind true)).map
        (fun column => readWord32 s.memory (output+BitVec.ofNat 64 (4*column))+values column))) ∧
      t.locals "output" = some (.pointer (output+BitVec.ofNat 64 (4*neonWidth kind true))) := by
  let u := mainLoadAdded kind s output (wordValues values)
  let acc := mainOutputWords s.memory output (wordValues values)
  have load : Exec cfg (neonMainLoadAdd kind) s u := neon_main_load_add_exec kind cfg s output (wordValues values)
    out (by intros; simp [wordValues]) words readable
  have uout : u.locals "output" = some (.pointer output) :=
    (load.locals_frame "output" (by cases kind <;> rfl)).trans out
  have lengths : ∀ word, word < neonWidth kind true/4 → (acc word).length = 4 := by
    intros
    simp [acc,mainOutputWords,wordValues]
  have store := main_store_exec cfg u output acc (neonWidth kind true/4) uout lengths
    (mainLoadAdded_words kind s output (wordValues values))
    (by simpa only [u, mainLoadAdded_memory] using (show ∀ a, Footprint output (16*(neonWidth kind true/4)) a → s.memory.writable a = true from
      by cases kind <;> simpa [neonWidth] using writable))
  refine ⟨mainStored u output acc (neonWidth kind true/4),?_,?_,?_⟩
  · rw [neon_main_output_shape]
    exact appendStatements_exec load store
  · rw [mainStored_memory _ _ _ _ lengths]
    simp only [acc, mainOutputWords_values, mainWordPrefix_values]
    have count : 4*(neonWidth kind true/4) = neonWidth kind true := by cases kind <;> rfl
    rw [count]
    simp only [u,mainLoadAdded_memory]
  · have h := mainStored_output u output acc (neonWidth kind true/4) uout
    have count : 16*(neonWidth kind true/4) = 4*neonWidth kind true := by cases kind <;> rfl
    simpa only [count] using h

end Salty.Kernels.Rdsum
