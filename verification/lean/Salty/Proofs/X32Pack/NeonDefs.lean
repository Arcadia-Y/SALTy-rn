import Salty.Proofs.Core.PackingMemory
import Salty.Proofs.Core.CByteSyntax
import Salty.Generated.X32PackNeon

namespace Salty.Kernels.X32Pack
open CByte

def neonGroups : Stmt := firstStatement (dropStatements 11 Generated.X32Pack.neon)
def neonGroup : Stmt := firstStatement (firstStatement neonGroups)
def neonChannelLoop : Stmt := firstStatement (dropStatements 2 neonGroup)
def neonChannelBody : Stmt := firstStatement (loopBody neonChannelLoop)
def neonPairLoop : Stmt := firstStatement (dropStatements 3 neonChannelBody)
def neonPairBody : Stmt := loopBody neonPairLoop
def neonPairTail : Stmt := firstStatement (dropStatements 4 neonChannelBody)
def neonPairTailBody : Stmt := loopBody neonPairTail

structure NeonPairLocals (s : State) (n : Nat) (a b output : Address) (x y : List Byte) : Prop where
  count : s.locals "k" = some (.integer n)
  left : s.locals "w0" = some (.pointer a)
  right : s.locals "w1" = some (.pointer b)
  output : s.locals "packed_weights" = some (.pointer output)
  tuple : s.locals "v00" = some (.vectors 4 [x,y])

theorem neon_pair_loop_shape : neonPairLoop =
    .loop (.bin .ge (.var "k") (.cast .u64 (.lit 2))) neonPairBody := rfl

theorem neon_pair_tail_shape : neonPairTail =
    .loop (.bin .ne (.var "k") (.cast .u64 (.lit 0))) neonPairTailBody := rfl

theorem neon_pair_body_shape : neonPairBody =
  .seq
    (.seq (.assign "v00" (.call .load2LaneU32x2 [.var "w0", .var "v00", .lit 0]))
    (.seq (.assign "w0" (.offset 4 (.var "w0") (.lit 2)))
    (.seq (.assign "v00" (.call .load2LaneU32x2 [.var "w1", .var "v00", .lit 1]))
    (.seq (.assign "w1" (.offset 4 (.var "w1") (.lit 2)))
    (.seq (.effect .storeU32x2 [.offset 4 (.var "packed_weights") (.lit 0), .vectorMember (.var "v00") 0])
    (.seq (.effect .storeU32x2 [.offset 4 (.var "packed_weights") (.lit 2), .vectorMember (.var "v00") 1])
    (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 4))) .skip)))))))
    (.assign "k" (.cast .u64 (.bin .sub (.var "k") (.cast .u64 (.lit 2))))) := rfl

/-- Two source structure-lane loads overwrite both old lanes in each field.
No property of the old vector contents is assumed beyond their sizes. -/
theorem load2_pair (cfg : Config) (m : Memory) (a b : Address) (x y xs ys : List Byte)
    (hx : x.length = 8) (hy : y.length = 8) (hxs : xs.length = 8)
    (leftLoad : loadBytes m a 8 = some xs) (rightLoad : loadBytes m b 8 = some ys) :
    (do
      let first ← intrinsic cfg m .load2LaneU32x2 [.pointer a, .vectors 4 [x,y], .integer 0]
      intrinsic cfg m .load2LaneU32x2 [.pointer b, first, .integer 1]) =
      some (.vectors 4 [xs.take 4 ++ ys.take 4, xs.drop 4 ++ ys.drop 4]) := by
  have xsLo : (xs.take 4).length = 4 := by simp [hxs]
  have xsHi : (xs.drop 4).length = 4 := by simp [hxs]
  have lenX := replaceWord_length x (xs.take 4) 0 hx xsLo (by decide)
  have lenY := replaceWord_length y (xs.drop 4) 0 hy xsHi (by decide)
  simp only [intrinsic, tupleMemoryIntrinsic, hx, hy, lenX, lenY, leftLoad, rightLoad]
  simp [lenX, lenY, rightLoad, replaceWord_pair x (xs.take 4) (ys.take 4) hx (by simp [hxs]),
    replaceWord_pair y (xs.drop 4) (ys.drop 4) hy (by simp [hxs])]

end Salty.Kernels.X32Pack
