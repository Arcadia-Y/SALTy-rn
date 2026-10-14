import Salty.Model.ReductionISA

namespace Salty.WideningISA
open ReductionISA

def addByte16 (kind : Interpretation) (acc : BitVec 16) (x : BitVec 8) : BitVec 16 :=
  acc+BitVec.ofInt 16 (value kind x)

def addHalf32 (kind : Interpretation) (acc : BitVec 32) (x : BitVec 16) : BitVec 32 :=
  acc+BitVec.ofInt 32 (value kind x)

def widenAdd16 (kind : Interpretation) (acc : List (BitVec 16)) (xs : List (BitVec 8)) : List (BitVec 16) :=
  List.zipWith (addByte16 kind) acc xs

def widenAdd32 (kind : Interpretation) (acc : List (BitVec 32)) (xs : List (BitVec 16)) : List (BitVec 32) :=
  List.zipWith (addHalf32 kind) acc xs

end Salty.WideningISA
