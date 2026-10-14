import Salty.Model.CByteMemory

namespace Salty.CByte

def unsignedWord (bs : List Byte) : Nat := bs.foldr (fun b rest => b.toNat+256*rest) 0


/-- Read one original little-endian word, independently of signed interpretation. -/
def readWord32 (m : Memory) (a : Address) : BitVec 32 :=
  BitVec.ofNat 32 (unsignedWord (readBytes m a 4))

def readWords32 (m : Memory) (a : Address) : Nat → List (BitVec 32)
  | 0 => []
  | n+1 => readWord32 m a :: readWords32 m (a+4) n

end Salty.CByte
