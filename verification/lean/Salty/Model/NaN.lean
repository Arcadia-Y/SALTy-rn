import Std

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.NaN`. -/

namespace Salty.NaN
abbrev Word := BitVec 32

def magnitude (x : Word) : Word := x &&& 0x7fffffff
def isNaN (x : Word) : Bool := (0x7f800000#32).ult (magnitude x)
def isSignaling (x : Word) : Bool := isNaN x && (magnitude x).ult 0x7fc00000
def quiet (x : Word) : Word := x ||| 0x00400000

/-- AArch64 binary NaN-selection policy for FPCR.DN=0. No finite arithmetic
is defined here; this is only the NaN-propagation part of the instruction. -/
def armSelection (a b : Word) : Option Word :=
  if isSignaling a then some (quiet a)
  else if isSignaling b then some (quiet b)
  else if isNaN a then some (quiet a)
  else if isNaN b then some (quiet b)
  else none

end Salty.NaN
