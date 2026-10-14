import Salty.Model.ByteISA

namespace Salty.Kernels.S8Clamp
open ByteISA

structure Params where
  lo : Byte
  hi : Byte

def Valid (p : Params) : Prop := p.lo.toInt ≤ p.hi.toInt

def mainLane (p : Params) (x : Byte) : Byte := minSigned (maxSigned x p.lo) p.hi

def tailLane (p : Params) (x : Byte) : Byte := maxSigned (minSigned x p.hi) p.lo

end Salty.Kernels.S8Clamp
