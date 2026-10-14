import Salty.Proofs.Rdsum.NeonMainRowsCorrect

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def neonMainInit (kind : Interpretation) : Stmt :=
  takeStatements (8+neonWidth kind true/4) (neonChannels kind true)

def neonMainInitialized (kind : Interpretation) (s : State) (input : Address) (stride rows : Nat) : State :=
  update (mainWordsAfter (rowsInitialized s input stride) (fun _ => List.replicate 4 0)
    (neonWidth kind true/4)) "r" (.integer rows)

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

private theorem cast_word (n : Int) : BitVec.ofInt 64 (convert .u64 n) = BitVec.ofInt 64 n := by
  change BitVec.ofInt 64 ((BitVec.ofInt 64 n).toNat : Int) = BitVec.ofInt 64 n
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem neon_main_init_exec (kind : Interpretation) (cfg : Config) (s : State) (input : Address)
    (stride rows : Nat) (bound : rows < 2^31)
    (hi : s.locals "input" = some (.pointer input))
    (hs : s.locals "input_stride" = some (.integer stride))
    (hr : s.locals "rows" = some (.integer rows)) :
    Exec cfg (neonMainInit kind) s (neonMainInitialized kind s input stride rows) := by
  cases kind <;> apply run_sound (fuel := 19) <;>
    simp [neonMainInit, neonWidth, neonChannels, neonProgram, Generated.QS8Rdsum.neon, Generated.QU8Rdsum.neon,
      takeStatements, dropStatements, firstStatement, loopBody, run, eval, binary, intrinsic, saturatingIntrinsic,
      selectionIntrinsic, integerArithmeticIntrinsic, neonMainInitialized, mainWordsAfter, rowsInitialized, neonWordName,
      update_locals, hi, hs, hr, cast_i32_nat rows bound,
      cast_word, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.ofNat_mul, show convert .u32 0 = 0 from rfl,
      show convert .u64 1 = 1 from rfl, show convert .u64 2 = 2 from rfl,
      show convert .u64 3 = 3 from rfl, show convert .u64 4 = 4 from rfl,
      show convert .u64 5 = 5 from rfl, show convert .u64 6 = 6 from rfl]

@[simp] theorem neonMainInitialized_memory (kind : Interpretation) (s : State) (input : Address) (stride rows : Nat) :
    (neonMainInitialized kind s input stride rows).memory = s.memory := by
  simp [neonMainInitialized, update, rowsInitialized]

theorem neonMainInitialized_locals (kind : Interpretation) (s : State) (input zero : Address) (stride rows : Nat)
    (hz : s.locals "zero" = some (.pointer zero))
    (hs : s.locals "input_increment" = some (.integer (7*stride))) :
    NeonMainBatchLocals kind (neonMainInitialized kind s input stride rows)
      (fun i => input+BitVec.ofNat 64 (i*stride)) zero rows stride (fun _ => 0) := by
  constructor
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;>
      simp [neonMainInitialized, rowsInitialized, mainWordsAfter, neonWidth, neonWordName, update_locals, rowName]
  · cases kind <;> simpa [neonMainInitialized, rowsInitialized, mainWordsAfter, neonWidth, neonWordName, update_locals] using hz
  · simp [neonMainInitialized, update_locals]
  · cases kind <;> simpa [neonMainInitialized, rowsInitialized, mainWordsAfter, neonWidth, neonWordName, update_locals] using hs
  · intro word hw
    have words := mainWordsAfter_word (rowsInitialized s input stride) (fun _ => List.replicate 4 (0 : BitVec 32))
      (neonWidth kind true/4) word (by cases kind <;> decide) hw
    have ne : neonWordName true word ≠ "r" := by
      have all : ∀ i : Fin 8, neonWordName true i.val ≠ "r" := by decide
      exact all ⟨word,by cases kind <;> simp [neonWidth] at hw <;> omega⟩
    simpa [neonMainInitialized, update_locals, ne, wordValues, List.map_const'] using words

end Salty.Kernels.Rdsum
