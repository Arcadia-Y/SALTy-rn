import Salty.Proofs.S8Clamp.Execution

namespace Salty.Kernels.S8Clamp.Execution
open CByte

def neon64Main : Stmt := firstStatement neon64Body
def neon64Loads : Stmt := takeStatements 8 neon64Main
def neon64Clamps : Stmt := takeStatements 8 (dropStatements 8 neon64Main)
def neon64Stores : Stmt := dropStatements 16 neon64Main

structure FourVecs (s : State) (b0 b1 b2 b3 : List Byte) : Prop where
  v0 : s.locals "vacc0" = some (.vector 1 b0)
  v1 : s.locals "vacc1" = some (.vector 1 b1)
  v2 : s.locals "vacc2" = some (.vector 1 b2)
  v3 : s.locals "vacc3" = some (.vector 1 b3)

def load64After (s : State) (input : Address) (b0 b1 b2 b3 : List Byte) : State :=
  let t := update s "vacc0" (.vector 1 b0)
  let t := update t "input" (.pointer (input + 16))
  let t := update t "vacc1" (.vector 1 b1)
  let t := update t "input" (.pointer (input + 32))
  let t := update t "vacc2" (.vector 1 b2)
  let t := update t "input" (.pointer (input + 48))
  let t := update t "vacc3" (.vector 1 b3)
  let t := update t "input" (.pointer (input + 64))
  t

theorem neon64_loads_exec (cfg : Config) (s : State) (input : Address)
    (b0 b1 b2 b3 : List Byte)
    (ptr : s.locals "input" = some (.pointer input))
    (h0 : loadBytes s.memory input 16 = some b0)
    (h1 : loadBytes s.memory (input + 16#64) 16 = some b1)
    (h2 : loadBytes s.memory (input + 32#64) 16 = some b2)
    (h3 : loadBytes s.memory (input + 48#64) 16 = some b3)
    : Exec cfg neon64Loads s (load64After s input b0 b1 b2 b3) := by
  apply run_sound (fuel := 20)
  simp [neon64Loads, neon64Main, neon64Body, firstStatement, dropStatements, loopBody,
    takeStatements, Generated.S8Clamp.neon, run, eval, intrinsic, update, ptr,
    h0, h1, h2, h3, load64After, BitVec.add_assoc]

theorem load64After_vecs (s : State) (input : Address) (b0 b1 b2 b3 : List Byte) :
    FourVecs (load64After s input b0 b1 b2 b3) b0 b1 b2 b3 := by
  constructor <;> simp [load64After, update]

def clamp64After (s : State) (p : Params) (b0 b1 b2 b3 : List Byte) : State :=
  let t := update s "vacc0" (.vector 1 (b0.map (fun x => ByteISA.maxSigned x p.lo)))
  let t := update t "vacc1" (.vector 1 (b1.map (fun x => ByteISA.maxSigned x p.lo)))
  let t := update t "vacc2" (.vector 1 (b2.map (fun x => ByteISA.maxSigned x p.lo)))
  let t := update t "vacc3" (.vector 1 (b3.map (fun x => ByteISA.maxSigned x p.lo)))
  let t := update t "vacc0" (.vector 1 (b0.map (mainLane p)))
  let t := update t "vacc1" (.vector 1 (b1.map (mainLane p)))
  let t := update t "vacc2" (.vector 1 (b2.map (mainLane p)))
  let t := update t "vacc3" (.vector 1 (b3.map (mainLane p)))
  t

private theorem zip16 (f : Byte → Byte → Byte) (bs : List Byte) (x : Byte) :
    List.zipWith f bs [x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x] =
      (bs.take 16).map (fun b => f b x) := zip_replicate f bs x 16

theorem neon64_clamps_exec (cfg : Config) (s : State) (p : Params) (b0 b1 b2 b3 : List Byte)
    (min : s.locals "voutput_min" = some (.vector 1 (List.replicate 16 p.lo)))
    (max : s.locals "voutput_max" = some (.vector 1 (List.replicate 16 p.hi)))
    (vecs : FourVecs s b0 b1 b2 b3)
    (len0 : b0.length = 16)
    (len1 : b1.length = 16)
    (len2 : b2.length = 16)
    (len3 : b3.length = 16)
    : Exec cfg neon64Clamps s (clamp64After s p b0 b1 b2 b3) := by
  have ht0 (f : Byte → Byte) : (b0.map f).take 16 = b0.map f := by
    apply List.take_of_length_le
    simp [len0]
  have hb0 : b0.take 16 = b0 := by apply List.take_of_length_le; omega
  have ht1 (f : Byte → Byte) : (b1.map f).take 16 = b1.map f := by
    apply List.take_of_length_le
    simp [len1]
  have hb1 : b1.take 16 = b1 := by apply List.take_of_length_le; omega
  have ht2 (f : Byte → Byte) : (b2.map f).take 16 = b2.map f := by
    apply List.take_of_length_le
    simp [len2]
  have hb2 : b2.take 16 = b2 := by apply List.take_of_length_le; omega
  have ht3 (f : Byte → Byte) : (b3.map f).take 16 = b3.map f := by
    apply List.take_of_length_le
    simp [len3]
  have hb3 : b3.take 16 = b3 := by apply List.take_of_length_le; omega
  apply run_sound (fuel := 20)
  simp [neon64Clamps, neon64Main, neon64Body, firstStatement, dropStatements, loopBody,
    takeStatements, Generated.S8Clamp.neon, run, eval, intrinsic, zipLanes, update,
    min, max, vecs.v0, vecs.v1, vecs.v2, vecs.v3,
    len0, len1, len2, len3, ht0, ht1, ht2, ht3, hb0, hb1, hb2, hb3,
    zip_replicate, zip16, List.map_map, Function.comp_def, clamp64After]
  rfl

theorem clamp64After_vecs (s : State) (p : Params) (b0 b1 b2 b3 : List Byte) :
    FourVecs (clamp64After s p b0 b1 b2 b3)
      (b0.map (mainLane p)) (b1.map (mainLane p)) (b2.map (mainLane p)) (b3.map (mainLane p)) := by
  constructor <;> simp [clamp64After, update]

def store64After (s : State) (output : Address) (m1 m2 m3 m4 : Memory) : State :=
  let t := { s with memory := m1 }
  let t := update t "output" (.pointer (output + 16))
  let t := { t with memory := m2 }
  let t := update t "output" (.pointer (output + 32))
  let t := { t with memory := m3 }
  let t := update t "output" (.pointer (output + 48))
  let t := { t with memory := m4 }
  let t := update t "output" (.pointer (output + 64))
  t

theorem neon64_stores_exec (cfg : Config) (s : State) (output : Address)
    (c0 c1 c2 c3 : List Byte) (m1 m2 m3 m4 : Memory)
    (ptr : s.locals "output" = some (.pointer output))
    (vecs : FourVecs s c0 c1 c2 c3)
    (len0 : c0.length = 16)
    (h0 : storeBytes s.memory output c0 = some m1)
    (len1 : c1.length = 16)
    (h1 : storeBytes m1 (output + 16#64) c1 = some m2)
    (len2 : c2.length = 16)
    (h2 : storeBytes m2 (output + 32#64) c2 = some m3)
    (len3 : c3.length = 16)
    (h3 : storeBytes m3 (output + 48#64) c3 = some m4)
    : Exec cfg neon64Stores s (store64After s output m1 m2 m3 m4) := by
  apply run_sound (fuel := 20)
  simp [neon64Stores, neon64Main, neon64Body, firstStatement, dropStatements, loopBody,
    takeStatements, Generated.S8Clamp.neon, run, eval, effect, storeVector, update, ptr,
    vecs.v0, vecs.v1, vecs.v2, vecs.v3, len0, len1, len2, len3,
    h0, h1, h2, h3, store64After, BitVec.add_assoc]

def neon64After (s : State) (n : Nat) (input output : Address) (p : Params)
    (b0 b1 b2 b3 : List Byte) (m1 m2 m3 m4 : Memory) : State :=
  let l := load64After s input b0 b1 b2 b3
  let c := clamp64After l p b0 b1 b2 b3
  let t := store64After c output m1 m2 m3 m4
  update t "batch" (.integer (n - 64 : Nat))

/-- The composed proof checks every statement of the extracted 64-byte body.
The split is syntactic and discharged by exec_take_drop; no replacement loop
body is assumed equivalent. -/
theorem neon64_body_exec (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (b0 b1 b2 b3 : List Byte) (m1 m2 m3 m4 : Memory)
    (locals : NeonLocals s n input output p) (bound : n < 2^64) (large : 64 ≤ n)
    (len0 : b0.length = 16)
    (load0 : loadBytes s.memory input 16 = some b0)
    (len1 : b1.length = 16)
    (load1 : loadBytes s.memory (input + 16#64) 16 = some b1)
    (len2 : b2.length = 16)
    (load2 : loadBytes s.memory (input + 32#64) 16 = some b2)
    (len3 : b3.length = 16)
    (load3 : loadBytes s.memory (input + 48#64) 16 = some b3)
    (store0 : storeBytes s.memory output (b0.map (mainLane p)) = some m1)
    (store1 : storeBytes m1 (output + 16#64) (b1.map (mainLane p)) = some m2)
    (store2 : storeBytes m2 (output + 32#64) (b2.map (mainLane p)) = some m3)
    (store3 : storeBytes m3 (output + 48#64) (b3.map (mainLane p)) = some m4)
    : Exec cfg neon64Body s (neon64After s n input output p b0 b1 b2 b3 m1 m2 m3 m4) := by
  let l := load64After s input b0 b1 b2 b3
  let c := clamp64After l p b0 b1 b2 b3
  let t := store64After c output m1 m2 m3 m4
  have hload : Exec cfg neon64Loads s l :=
    neon64_loads_exec cfg s input b0 b1 b2 b3 locals.inputPtr load0 load1 load2 load3
  have hclamp : Exec cfg neon64Clamps l c :=
    neon64_clamps_exec cfg l p b0 b1 b2 b3
      (by simp [l, load64After, update, locals.min])
      (by simp [l, load64After, update, locals.max])
      (load64After_vecs ..) len0 len1 len2 len3
  have hstore : Exec cfg neon64Stores c t :=
    neon64_stores_exec cfg c output (b0.map (mainLane p)) (b1.map (mainLane p))
      (b2.map (mainLane p)) (b3.map (mainLane p)) m1 m2 m3 m4
      (by simp [c, l, clamp64After, load64After, update, locals.outputPtr])
      (clamp64After_vecs ..)
      (by simp [len0]) store0 (by simp [len1]) store1
      (by simp [len2]) store2 (by simp [len3]) store3
  have hmain : Exec cfg neon64Main s t := exec_take_drop 8 hload (exec_take_drop 8 hclamp hstore)
  apply Exec.seq hmain
  apply Exec.assign
  have hsub : convert .u64 ((n : Int) - 64) = (n - 64 : Nat) := by
    simpa using cast_sub n 64 large bound
  simp [eval, t, c, l, store64After, clamp64After, load64After, update, locals.batch,
    binary, show convert .u64 64 = 64 from cast_nat 64 (by decide), hsub]

theorem neon64After_locals (s : State) (n : Nat) (input output : Address) (p : Params)
    (b0 b1 b2 b3 : List Byte) (m1 m2 m3 m4 : Memory) (h : NeonLocals s n input output p) :
    NeonLocals (neon64After s n input output p b0 b1 b2 b3 m1 m2 m3 m4) (n - 64)
      (input + 64) (output + 64) p := by
  constructor <;> simp [neon64After, load64After, clamp64After, store64After, update, h.min, h.max]

end Salty.Kernels.S8Clamp.Execution
