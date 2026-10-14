import Std

namespace Salty.ReductionISA

inductive Interpretation where
  | signed | unsigned
  deriving DecidableEq, Repr

def value (kind : Interpretation) (x : BitVec w) : Int :=
  match kind with
  | .signed => x.toInt
  | .unsigned => x.toNat

def sumWords : List (BitVec 32) → BitVec 32
  | [] => 0
  | x :: xs => x + sumWords xs

def sumInts : List Int → Int
  | [] => 0
  | x :: xs => x + sumInts xs

/-- Pairwise addition before narrowing. The singleton case makes this helper
 total; SADALP/UADALP primitives require an even source lane count. -/
def pairSums : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: xs => (x + y) :: pairSums xs

/-- SADALP/UADALP's byte-to-halfword lane update, including modular16 addition. -/
def addPair16 (kind : Interpretation) (acc : BitVec 16) (x y : BitVec 8) : BitVec 16 :=
  acc + BitVec.ofInt 16 (value kind x + value kind y)

/-- Tail-undisturbed RVV addition. The caller checks the active length against
 both operands and the architectural capacity. -/
def addPrefix (old active : List (BitVec 32)) : List (BitVec 32) :=
  List.zipWith (· + ·) (old.take active.length) active ++ old.drop active.length

/-- Widening and reducing halfwords, as used by the second SADALP/UADALP stage. -/
def widen32 (kind : Interpretation) (xs : List (BitVec w)) : List (BitVec 32) :=
  xs.map (fun x => BitVec.ofInt 32 (value kind x))

/-- The fixed-width NEON instruction consumes two byte lanes per accumulator
lane. Its primitive requires exactly twice as many source lanes. -/
def pairAcc16 (kind : Interpretation) : List (BitVec 16) → List (BitVec 8) → List (BitVec 16)
  | a :: acc, x :: y :: xs => addPair16 kind a x y :: pairAcc16 kind acc xs
  | _, _ => []

/-- The second widening stage adds adjacent halfwords to modular32 lanes. -/
def pairAcc32 (kind : Interpretation) : List (BitVec 32) → List (BitVec 16) → List (BitVec 32)
  | a :: acc, x :: y :: xs =>
      (a + BitVec.ofInt 32 (value kind x + value kind y)) :: pairAcc32 kind acc xs
  | _, _ => []

end Salty.ReductionISA
