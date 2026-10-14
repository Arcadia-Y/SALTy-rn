import Salty.Proofs.X32Pack.TileMemory
import Salty.Proofs.X32Pack.Init

namespace Salty.Kernels.X32Pack
open CByte

/-- The fixed-width source keeps a two-field vector object between tiles.
Only its shape is needed: each paired depth iteration replaces every used lane. -/
def TupleReady (rvv : Bool) (s : State) : Prop :=
  if rvv then True else ∃ x y, s.locals "v00" = some (.vectors 4 [x,y]) ∧ x.length = 8 ∧ y.length = 8

structure TileLocals (s : State) (n extra : Nat) (weights bias output : Address) : Prop where
  depth : s.locals "kc" = some (.integer n)
  extra : s.locals "extra_bytes" = some (.integer extra)
  weights : s.locals "w0" = some (.pointer weights)
  bias : s.locals "bias" = some (.pointer bias)
  output : s.locals "packed_weights" = some (.pointer output)

structure TileEnd (s : State) (weights bias output : Address) : Prop where
  weights : s.locals "w0" = some (.pointer weights)
  bias : s.locals "bias" = some (.pointer bias)
  output : s.locals "packed_weights" = some (.pointer output)

def pairChannelBody (rvv : Bool) : Stmt := if rvv then rvvChannelBody else neonChannelBody
def pairPrefix (rvv : Bool) : Stmt := takeStatements 3 (pairChannelBody rvv)
def pairDepth (rvv : Bool) : Stmt :=
  takeStatements (if rvv then 1 else 2) (dropStatements 3 (pairChannelBody rvv))
def pairSuffix (rvv : Bool) : Stmt := dropStatements (if rvv then 4 else 5) (pairChannelBody rvv)

theorem pair_prefix_shape (rvv : Bool) : pairPrefix rvv =
    .seq (pairHeader rvv)
      (.seq (.assign "w1" (.offset 4 (.var "w0") (.var "kc")))
      (.seq (.assign "k" (.var "kc")) .skip)) := by cases rvv <;> rfl

theorem pair_suffix_shape (rvv : Bool) : pairSuffix rvv =
    .seq (.assign "packed_weights" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "packed_weights")) (.var "extra_bytes")))))
      (.seq (.assign "w0" (.var "w1")) .skip) := by cases rvv <;> rfl

theorem pair_depth_total (rvv : Bool) (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (loc : PairLocals s n a b output) (tuple : TupleReady rvv s)
    (bound : 8*n ≤ 2^64) (safe : PairSafe s.memory a b output n) :
    ∃ t, Exec cfg (pairDepth rvv) s t ∧ t.memory = pairResult s.memory a b output n ∧
      PairLocals t 0 (a+BitVec.ofNat 64 (4*n)) (b+BitVec.ofNat 64 (4*n))
        (output+BitVec.ofNat 64 (8*n)) ∧ TupleReady rvv t := by
  cases rvv with
  | true =>
    obtain ⟨t, execution, memory, locals⟩ := rvv_pair_loop_total cfg s n a b output loc bound safe
    exact ⟨t, .seq execution .skip, memory, locals, trivial⟩
  | false =>
    obtain ⟨x, y, value, hx, hy⟩ := tuple
    have sourceLoc : NeonPairLocals s n a b output x y := ⟨loc.count, loc.left, loc.right, loc.output, value⟩
    obtain ⟨t, tx, ty, execution, memory, locals, htx, hty⟩ :=
      neon_pair_depth_total cfg s n a b output x y sourceLoc hx hy bound safe
    exact ⟨t, execution, memory, ⟨locals.count, locals.left, locals.right, locals.output⟩,
      tx, ty, locals.tuple, htx, hty⟩

theorem cast_pointer_add (a : Address) (n : Nat) :
    BitVec.ofInt 64 (convert .u64 ((a.toNat : Int)+n)) = a+BitVec.ofNat 64 n := by
  simp only [convert, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast]
  simp

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

theorem TupleReady.of_frame {rvv : Bool} {s t : State} (ready : TupleReady rvv s)
    (frame : t.locals "v00" = s.locals "v00") : TupleReady rvv t := by
  cases rvv with
  | true => trivial
  | false => obtain ⟨x,y,value,hx,hy⟩ := ready; exact ⟨x,y,frame.trans value,hx,hy⟩

end Salty.Kernels.X32Pack
