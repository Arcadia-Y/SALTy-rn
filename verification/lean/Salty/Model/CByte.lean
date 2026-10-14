import Salty.Model.SIMD
import Salty.Model.Memory
import Salty.Model.ByteISA
import Salty.Model.ReductionISA
import Salty.Model.WideningISA

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.CByte`. -/

set_option maxHeartbeats 2000000

/-! A deliberately small, executable C/intrinsic model. This is not a C standard
semantics or a verified compiler frontend. The extractor's supported AST fragment
and intrinsic interface form a named, reviewable trusted bridge. Byte vectors
retain a lane-width tag so reinterpretation and little-endian lane stores are
explicit. Every byte access checks permissions. -/
namespace Salty.CByte

inductive Scalar where
  | i8 | u8 | i16 | u16 | i32 | u32 | i64 | u64
  deriving DecidableEq, Repr

inductive BinOp where
  | add | sub | mul | div | rem | band | eq | ne | ge | gt | lt | le
  deriving DecidableEq, Repr

inductive Prim where
  | dup16 | load16 | load8 | max16 | min16 | max8 | min8
  | store16 | store8 | low8 | reinterpret32 | reinterpret16
  | storeLane32 | storeLane16 | storeLane8 | extract8
  | setvl | loadRVV | maxRVV | minRVV | storeRVV | assertion
  | loadU32x2 | dupU32x2 | zipU32x2 | storeU32x2
  | loadU32RVV | storeStridedU32RVV | roundDown2 | differenceOrZero
  | dupI16x8 | subWideI8 | shiftI16x8 | sqrdmulhI16x8 | addSatI16x8 | narrowSatI8
  | extendI8RVV | reverseSubI16RVV | shiftI16RVV | wideningMulI16RVV
  | clipRNU15RVV | addSatI16RVV | clipRDN0RVV
  | lessI16x8 | bitSelectI16x8 | lessI16RVV | dupI16RVV | mergeI16RVV | wideningMulI16VectorRVV
  | dup8 | dupI32x4 | subWideBytes | lowI16x4 | highI16x4 | extendI16x4
  | mulI32x4 | mlaI32x4 | rshlI32x4 | narrowSatI16 | combineI16 | combineI8
  | subWideByteRVV | extendI16RVV | mulI32RVV | maccI32RVV
  | rightRNU32RVV | leftI32RVV | dupI32RVV | clipRDN0I16RVV
  | subWideUBytes | reinterpretI16 | narrowSatU8 | maxU8 | minU8
  | subWideUByteRVV | maxI16RVV | clipUnsignedRDN0RVV | maxU8RVV | minU8RVV
  | pairAcc16S | pairAcc16U
  | pairAcc32S | pairAcc32U
  | reduceI32x4S | reduceI32x4U
  | mulBytes16 | vlmax32M8 | vlmax32M1 | dupI32M1
  | extendByte32RVVS | extendByte32RVVU
  | addI32TURVV | reduceI32RVV
  | scalarI32RVVS | scalarI32RVVU
  | loadTable16 | storeI32 | storeU32
  | emptyTupleU32x2 | setTupleU32x2 | loadLaneU32x2 | load2LaneU32x2
  | createU32TupleRVV | dupU32PackM1 | loadU32PackM1
  | storeU32RVV | storeSegment2U32RVV
  | widenAddByte16S | widenAddByte16U | widenAddHalf32S | widenAddHalf32U
  | widenAddByte16RVVS | widenAddByte16RVVU | widenAddHalf32RVVS | widenAddHalf32RVVU
  | addWords32x4 | addWords32x2 | addWords32RVV
  | loadWords32x4 | loadWords32x2 | loadWords32RVV
  | storeWords32x4 | storeWords32x2 | storeWords32RVV
  | lowWords32x2 | extractWords32x4 | laneWords32S | laneWords32U
  | minimumU64 | floorU64I32
  deriving DecidableEq, Repr

inductive Expr where
  | lit (n : Int)
  | byteArray (bytes : List Byte)
  | var (name : String)
  | null
  | cast (ty : Scalar) (arg : Expr)
  | param (base : Expr) (offset : Nat)
  | param16 (base : Expr) (offset : Nat)
  | param8 (base : Expr) (offset : Nat)
  | paramU8 (base : Expr) (offset : Nat)
  | negSigned32 (arg : Expr)
  | checkedSigned32 (arg : Expr)
  | conditional (cond yes no : Expr)
  | bin (op : BinOp) (a b : Expr)
  | offset (bytes : Nat) (base count : Expr)
  | not (arg : Expr)
  | or (left right : Expr)
  | ptrToInt (arg : Expr)
  | intToPtr (arg : Expr)
  | vectorMember (arg : Expr) (index : Nat)
  | call (op : Prim) (args : List Expr)
  deriving Repr

inductive Stmt where
  | skip
  | assign (name : String) (rhs : Expr)
  | effect (op : Prim) (args : List Expr)
  | seq (first second : Stmt)
  | branch (cond : Expr) (yes no : Stmt)
  | loop (cond : Expr) (body : Stmt)
  deriving Repr

inductive Value where
  | integer (n : Int)
  | pointer (a : Address)
  | vector (laneBytes : Nat) (bytes : List Byte)
  | vectors (laneBytes : Nat) (members : List (List Byte))
  | halfwords (lanes : List (BitVec 16))
  | words32 (lanes : List (BitVec 32))
  | mask (lanes : List Bool)
  deriving DecidableEq, Repr

structure State where
  locals : String → Option Value
  memory : Memory

/-- Active lane capacity for the scalable vector configuration used by a
kernel (e8,m8: VLEN bits; e32,m8: VLEN/4). Every bounded, progressing choice
is admitted; a source bridge supplies the architectural capacity. -/
structure Config where
  capacity : Nat
  choose : Nat → Nat
  positive : ∀ n, 0 < n → 0 < choose n
  bounded : ∀ n, choose n ≤ min n capacity

/-- Canonical two's-complement conversions at the fixed ABI. -/
def convert : Scalar → Int → Int
  | .u8, n => (BitVec.ofInt 8 n).toNat
  | .i8, n => (BitVec.ofInt 8 n).toInt
  | .i16, n => (BitVec.ofInt 16 n).toInt
  | .u16, n => (BitVec.ofInt 16 n).toNat
  | .i32, n => (BitVec.ofInt 32 n).toInt
  | .i64, n => (BitVec.ofInt 64 n).toInt
  | .u32, n => (BitVec.ofInt 32 n).toNat
  | .u64, n => (BitVec.ofInt 64 n).toNat

def truth : Value → Option Bool
  | .integer n => some (n != 0)
  | .pointer a => some (a != 0)
  | _ => none

def loadBytes (m : Memory) (a : Address) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => do
    let b ← m.load a
    let bs ← loadBytes m (a + 1) n
    pure (b :: bs)

def storeBytes (m : Memory) (a : Address) : List Byte → Option Memory
  | [] => some m
  | b :: bs => do
    let next ← m.store a b
    storeBytes next (a + 1) bs

/-- Read a little-endian signed 32-bit parameter from actual memory. -/
def loadParam (m : Memory) (a : Address) : Option Value := do
  let bs ← loadBytes m a 4
  let n := bs.foldr (fun b rest => b.toNat + 256 * rest) 0
  pure (.integer (BitVec.ofNat 32 n).toInt)

/-- Signed 16-bit parameter access, including both byte permissions. -/
def loadParam16 (m : Memory) (a : Address) : Option Value := do
  let bs ← loadBytes m a 2
  let n := bs.foldr (fun b rest => b.toNat + 256 * rest) 0
  pure (.integer (BitVec.ofNat 16 n).toInt)

def binary (op : BinOp) : Value → Value → Option Value
  | .integer a, .integer b =>
    match op with
    | .add => some (.integer (a + b))
    | .sub => some (.integer (a - b))
    | .mul => some (.integer (a * b))
    | .div => if b = 0 then none else some (.integer (a.tdiv b))
    | .rem => if b = 0 then none else some (.integer (a % b))
    | .band => if a < 0 ∨ b < 0 then none else some (.integer (a.toNat &&& b.toNat))
    | .eq => some (.integer (if a = b then 1 else 0))
    | .ne => some (.integer (if a ≠ b then 1 else 0))
    | .ge => some (.integer (if a ≥ b then 1 else 0))
    | .gt => some (.integer (if a > b then 1 else 0))
    | .lt => some (.integer (if a < b then 1 else 0))
    | .le => some (.integer (if a ≤ b then 1 else 0))
  | .pointer a, .pointer b =>
    match op with
    | .eq => some (.integer (if a = b then 1 else 0))
    | .ne => some (.integer (if a ≠ b then 1 else 0))
    | _ => none
  | _, _ => none

def zipLanes (n : Nat) (f : Byte → Byte → Byte) : List Value → Option Value
  | [.vector 1 a, .vector 1 b] =>
    if a.length = n ∧ b.length = n then some (.vector 1 (List.zipWith f a b)) else none
  | _ => none

def scalarLanes (f : Byte → Byte → Byte) : List Value → Option Value
  | [.vector 1 a, .integer b, .integer vl] =>
    if 0 ≤ vl ∧ vl.toNat ≤ a.length then
      some (.vector 1 ((a.take vl.toNat).map (fun x => f x (BitVec.ofInt 8 b))))
    else none
  | _ => none

/-- Little-endian representation of a 32-bit lane. -/
def bytes32 (n : Int) : List Byte :=
  [BitVec.ofInt 8 n, BitVec.ofInt 8 (n / 256),
   BitVec.ofInt 8 (n / 65536), BitVec.ofInt 8 (n / 16777216)]

/-- Unsigned vectors share their raw halfword representation across explicit
reinterpretation. Signedness is applied by each consuming instruction. -/
def unsignedArithmeticIntrinsic (op : Prim) (args : List Value) : Option Value :=
  match op with
  | .subWideUBytes =>
    match args with
    | [.vector 1 a, .vector 1 b] =>
      if a.length = 8 ∧ b.length = 8 then
        some (.halfwords (List.zipWith SIMD.Unsigned.neonSubWide a b)) else none
    | _ => none
  | .reinterpretI16 =>
    match args with
    | [.halfwords a] => some (.halfwords a)
    | _ => none
  | .narrowSatU8 =>
    match args with
    | [.halfwords a] =>
      if a.length = 8 then some (.vector 1 (a.map SIMD.Unsigned.neonNarrowU8)) else none
    | _ => none
  | .maxU8 => zipLanes 8 SIMD.Unsigned.max8 args
  | .minU8 => zipLanes 8 SIMD.Unsigned.min8 args
  | .subWideUByteRVV =>
    match args with
    | [.vector 1 a, .integer b, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.halfwords
        ((a.take vl.toNat).map (fun x => SIMD.Unsigned.rvvSubWide x (BitVec.ofInt 8 b)))) else none
    | _ => none
  | .maxI16RVV =>
    match args with
    | [.halfwords a, .integer b, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.halfwords
        ((a.take vl.toNat).map (fun x => if x.toInt < (BitVec.ofInt 16 b).toInt then BitVec.ofInt 16 b else x))) else none
    | _ => none
  | .clipUnsignedRDN0RVV =>
    match args with
    | [.halfwords a, .integer shift, .integer mode, .integer vl] =>
      if shift = 0 ∧ mode = 2 ∧ 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.vector 1
        ((a.take vl.toNat).map (fun x => BitVec.ofNat 8 (min 255 x.toNat)))) else none
    | _ => none
  | .maxU8RVV => scalarLanes SIMD.Unsigned.max8 args
  | .minU8RVV => scalarLanes SIMD.Unsigned.min8 args
  | _ => none

def integerArithmeticIntrinsic (cfg : Config) (op : Prim) (args : List Value) : Option Value :=
  match op with
  | .dup8 =>
    match args with
    | [.integer n] =>
        if True then some (.vector 1 (List.replicate 8 (BitVec.ofInt 8 n))) else none
    | _ => none
  | .dupI32x4 =>
    match args with
    | [.integer n] =>
        if True then some (.words32 (List.replicate 4 (BitVec.ofInt 32 n))) else none
    | _ => none
  | .subWideBytes =>
    match args with
    | [.vector 1 a, .vector 1 b] =>
        if a.length = 8 ∧ b.length = 8 then some (.halfwords (List.zipWith SIMD.Arithmetic.neonSubWide a b)) else none
    | _ => none
  | .lowI16x4 =>
    match args with
    | [.halfwords a] =>
        if a.length = 8 then some (.halfwords (a.take 4)) else none
    | _ => none
  | .highI16x4 =>
    match args with
    | [.halfwords a] =>
        if a.length = 8 then some (.halfwords (a.drop 4)) else none
    | _ => none
  | .extendI16x4 =>
    match args with
    | [.halfwords a] =>
        if a.length = 4 then some (.words32 (a.map SIMD.Arithmetic.extend16)) else none
    | _ => none
  | .mulI32x4 =>
    match args with
    | [.words32 a, .words32 b] =>
        if a.length = 4 ∧ b.length = 4 then some (.words32 (List.zipWith SIMD.Arithmetic.multiply32 a b)) else none
    | _ => none
  | .mlaI32x4 =>
    match args with
    | [.words32 acc, .words32 a, .words32 b] =>
        if acc.length = 4 ∧ a.length = 4 ∧ b.length = 4 then some (.words32 (List.zipWith (fun p b => SIMD.Arithmetic.neonMla32 p.1 p.2 b) (acc.zip a) b)) else none
    | _ => none
  | .rshlI32x4 =>
    match args with
    | [.words32 a, .words32 b] =>
        if a.length = 4 ∧ b.length = 4 then some (.words32 (List.zipWith ShiftISA.neonSRSHL a b)) else none
    | _ => none
  | .narrowSatI16 =>
    match args with
    | [.words32 a] =>
        if a.length = 4 then some (.halfwords (a.map SIMD.Arithmetic.neonNarrow16)) else none
    | _ => none
  | .combineI16 =>
    match args with
    | [.halfwords a, .halfwords b] =>
        if a.length = 4 ∧ b.length = 4 then some (.halfwords (a ++ b)) else none
    | _ => none
  | .combineI8 =>
    match args with
    | [.vector 1 a, .vector 1 b] =>
        if a.length = 8 ∧ b.length = 8 then some (.vector 1 (a ++ b)) else none
    | _ => none
  | .subWideByteRVV =>
    match args with
    | [.vector 1 a, .integer b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.halfwords ((a.take vl.toNat).map (fun x => SIMD.Arithmetic.rvvSubWide x (BitVec.ofInt 8 b)))) else none
    | _ => none
  | .extendI16RVV =>
    match args with
    | [.halfwords a, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.words32 ((a.take vl.toNat).map SIMD.Arithmetic.extend16)) else none
    | _ => none
  | .mulI32RVV =>
    match args with
    | [.words32 a, .integer b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.words32 ((a.take vl.toNat).map (fun x => SIMD.Arithmetic.multiply32 x (BitVec.ofInt 32 b)))) else none
    | _ => none
  | .maccI32RVV =>
    match args with
    | [.words32 acc, .integer b, .words32 a, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ acc.length ∧ vl.toNat ≤ a.length then some (.words32 (List.zipWith (fun c x => SIMD.Arithmetic.rvvMacc32 c (BitVec.ofInt 32 b) x) (acc.take vl.toNat) (a.take vl.toNat))) else none
    | _ => none
  | .rightRNU32RVV =>
    match args with
    | [.words32 a, .integer shift, .integer mode, .integer vl] =>
        if mode = 0 ∧ 0 ≤ shift ∧ 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.words32 ((a.take vl.toNat).map (fun x => ShiftISA.rvvRight x shift.toNat))) else none
    | _ => none
  | .leftI32RVV =>
    match args with
    | [.words32 a, .integer shift, .integer vl] =>
        if 0 ≤ shift ∧ 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.words32 ((a.take vl.toNat).map (fun x => ShiftISA.rvvLeft x shift.toNat))) else none
    | _ => none
  | .dupI32RVV =>
    match args with
    | [.integer n, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity then some (.words32 (List.replicate vl.toNat (BitVec.ofInt 32 n))) else none
    | _ => none
  | .clipRDN0I16RVV =>
    match args with
    | [.words32 a, .integer shift, .integer mode, .integer vl] =>
        if shift = 0 ∧ mode = 2 ∧ 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.halfwords ((a.take vl.toNat).map SIMD.Arithmetic.rvvClip16RDN0)) else none
    | _ => none
  | _ => unsignedArithmeticIntrinsic op args

def selectionIntrinsic (cfg : Config) (op : Prim) (args : List Value) : Option Value :=
  match op with
  | .lessI16x8 =>
    match args with
    | [.halfwords a, .halfwords b] =>
        if a.length = 8 ∧ b.length = 8 then some (.halfwords
          (List.zipWith SIMD.Selection.signedLessMask a b)) else none
    | _ => none
  | .bitSelectI16x8 =>
    match args with
    | [.halfwords mask, .halfwords yes, .halfwords no] =>
        if mask.length = 8 ∧ yes.length = 8 ∧ no.length = 8 then some (.halfwords
          (List.zipWith (fun p n => SIMD.Selection.bitSelect p.1 p.2 n)
            (mask.zip yes) no)) else none
    | _ => none
  | .lessI16RVV =>
    match args with
    | [.halfwords a, .integer b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.mask
          ((a.take vl.toNat).map (fun x => SIMD.Selection.signedLess x (BitVec.ofInt 16 b)))) else none
    | _ => none
  | .dupI16RVV =>
    match args with
    | [.integer b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity then some (.halfwords (List.replicate vl.toNat (BitVec.ofInt 16 b))) else none
    | _ => none
  | .mergeI16RVV =>
    match args with
    | [.halfwords no, .integer yes, .mask mask, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ no.length ∧ vl.toNat ≤ mask.length then some (.halfwords
          (List.zipWith (fun n m => SIMD.Selection.merge n (BitVec.ofInt 16 yes) m)
            (no.take vl.toNat) (mask.take vl.toNat))) else none
    | _ => none
  | .wideningMulI16VectorRVV =>
    match args with
    | [.halfwords a, .halfwords b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length ∧ vl.toNat ≤ b.length then some (.words32
          (List.zipWith SIMD.Signed.wideningMul16 (a.take vl.toNat) (b.take vl.toNat))) else none
    | _ => none
  | _ => integerArithmeticIntrinsic cfg op args


/- Integer conversion primitives are factored out to keep simplification of
other instruction families small. -/
def saturatingIntrinsic (cfg : Config) (op : Prim) (args : List Value) : Option Value :=
  match op with
  | .dupI16x8 =>
    match args with
    | [.integer n] => some (.halfwords (List.replicate 8 (BitVec.ofInt 16 n)))
    | _ => none
  | .subWideI8 =>
    match args with
    | [.halfwords a, .vector 1 b] =>
        if a.length = 8 ∧ b.length = 8 then
          some (.halfwords (List.zipWith SIMD.Signed.subWide8 a b)) else none
    | _ => none
  | .shiftI16x8 =>
    match args with
    | [.halfwords a, .integer 7] =>
        if a.length = 8 then some (.halfwords (a.map (fun x => SIMD.Signed.shift16 x 7))) else none
    | _ => none
  | .sqrdmulhI16x8 =>
    match args with
    | [.halfwords a, .halfwords b] =>
        if a.length = 8 ∧ b.length = 8 then
          some (.halfwords (List.zipWith SIMD.Signed.sqrdmulh16 a b)) else none
    | _ => none
  | .addSatI16x8 =>
    match args with
    | [.halfwords a, .halfwords b] =>
        if a.length = 8 ∧ b.length = 8 then
          some (.halfwords (List.zipWith SIMD.Signed.addSat16 a b)) else none
    | _ => none
  | .narrowSatI8 =>
    match args with
    | [.halfwords a] =>
        if a.length = 8 then some (.vector 1 (a.map SIMD.Signed.narrowSat8)) else none
    | _ => none
  | .extendI8RVV =>
    match args with
    | [.vector 1 a, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then
          some (.halfwords ((a.take vl.toNat).map SIMD.Signed.signExtend8)) else none
    | _ => none
  | .reverseSubI16RVV =>
    match args with
    | [.halfwords a, .integer b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.halfwords
          ((a.take vl.toNat).map (fun x => SIMD.Signed.reverseSub16 x (BitVec.ofInt 16 b)))) else none
    | _ => none
  | .shiftI16RVV =>
    match args with
    | [.halfwords a, .integer 7, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then
          some (.halfwords ((a.take vl.toNat).map (fun x => SIMD.Signed.shift16 x 7))) else none
    | _ => none
  | .wideningMulI16RVV =>
    match args with
    | [.halfwords a, .integer b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.words32
          ((a.take vl.toNat).map (fun x => SIMD.Signed.wideningMul16 x (BitVec.ofInt 16 b)))) else none
    | _ => none
  | .clipRNU15RVV =>
    match args with
    | [.words32 a, .integer 15, .integer 0, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then
          some (.halfwords ((a.take vl.toNat).map SIMD.Signed.clipRNU15)) else none
    | _ => none
  | .addSatI16RVV =>
    match args with
    | [.halfwords a, .integer b, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then some (.halfwords
          ((a.take vl.toNat).map (fun x => SIMD.Signed.addSat16 x (BitVec.ofInt 16 b)))) else none
    | _ => none
  | .clipRDN0RVV =>
    match args with
    | [.halfwords a, .integer 0, .integer 2, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ a.length then
          some (.vector 1 ((a.take vl.toNat).map SIMD.Signed.clipRDN0)) else none
    | _ => none
  | _ => selectionIntrinsic cfg op args


/-- Reduction primitives retain the distinction between the destination tail,
active inputs, and the defined scalar reduction result. -/
def reductionIntrinsic (cfg : Config) (op : Prim) (args : List Value) : Option Value :=
  match op, args with
  | .pairAcc16S, [.halfwords acc, .vector 1 xs] =>
      if acc.length = 8 ∧ xs.length = 16 then
        some (.halfwords (ReductionISA.pairAcc16 .signed acc xs)) else none
  | .pairAcc16U, [.halfwords acc, .vector 1 xs] =>
      if acc.length = 8 ∧ xs.length = 16 then
        some (.halfwords (ReductionISA.pairAcc16 .unsigned acc xs)) else none
  | .pairAcc32S, [.words32 acc, .halfwords xs] =>
      if acc.length = 4 ∧ xs.length = 8 then
        some (.words32 (ReductionISA.pairAcc32 .signed acc xs)) else none
  | .pairAcc32U, [.words32 acc, .halfwords xs] =>
      if acc.length = 4 ∧ xs.length = 8 then
        some (.words32 (ReductionISA.pairAcc32 .unsigned acc xs)) else none
  | .reduceI32x4S, [.words32 xs] =>
      if xs.length = 4 then some (.integer (ReductionISA.value .signed (ReductionISA.sumWords xs))) else none
  | .reduceI32x4U, [.words32 xs] =>
      if xs.length = 4 then some (.integer (ReductionISA.value .unsigned (ReductionISA.sumWords xs))) else none
  | .loadTable16, [.vector 1 table, .integer offset] =>
      if 0 ≤ offset ∧ offset.toNat + 16 ≤ table.length then
        some (.vector 1 ((table.drop offset.toNat).take 16)) else none
  | .mulBytes16, xs => zipLanes 16 (· * ·) xs
  | .vlmax32M8, [] => some (.integer cfg.capacity)
  | .vlmax32M1, [] =>
      if 8 ≤ cfg.capacity then some (.integer (cfg.capacity / 8)) else none
  | .dupI32M1, [.integer n, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity / 8 then
        some (.words32 (List.replicate vl.toNat (BitVec.ofInt 32 n))) else none
  | .extendByte32RVVS, [.vector 1 xs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ xs.length ∧ vl.toNat ≤ cfg.capacity then
        some (.words32 (ReductionISA.widen32 .signed (xs.take vl.toNat))) else none
  | .extendByte32RVVU, [.vector 1 xs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ xs.length ∧ vl.toNat ≤ cfg.capacity then
        some (.words32 (ReductionISA.widen32 .unsigned (xs.take vl.toNat))) else none
  | .addI32TURVV, [.words32 dest, .words32 left, .words32 right, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ left.length ∧ vl.toNat ≤ right.length ∧
          dest.length = cfg.capacity ∧ vl.toNat ≤ cfg.capacity then
        some (.words32 (List.zipWith (· + ·) (left.take vl.toNat) (right.take vl.toNat) ++
          dest.drop vl.toNat)) else none
  | .reduceI32RVV, [.words32 xs, .words32 seed, .integer vl] =>
      -- The default (tail-agnostic) C intrinsic has no old-destination operand.
      -- For vl=0 even lane0 is unspecified, so that case is unsupported.
      if 0 < vl ∧ vl.toNat ≤ xs.length ∧ vl.toNat ≤ cfg.capacity ∧
          0 < seed.length ∧ seed.length ≤ cfg.capacity / 8 then
        some (.words32 [seed.head! + ReductionISA.sumWords (xs.take vl.toNat)])
      else none
  | .scalarI32RVVS, [.words32 xs] =>
      if 0 < xs.length then some (.integer (ReductionISA.value .signed xs.head!)) else none
  | .scalarI32RVVU, [.words32 xs] =>
      if 0 < xs.length then some (.integer (ReductionISA.value .unsigned xs.head!)) else none
  | _, _ => none

/-- Replace one 32-bit lane in the byte representation. Callers check lane
and vector sizes, so the untouched lane retains its original bytes. -/
def replaceWord (old word : List Byte) (lane : Nat) : List Byte :=
  old.take (4*lane) ++ word ++ old.drop (4*(lane+1))

/-- Little-endian 32-bit lanes decoded only after the caller has checked the
complete byte footprint. Short lists are total here but rejected by loads. -/
def decodeWords32 : Nat → List Byte → List (BitVec 32)
  | 0, _ => []
  | n+1, bs => BitVec.ofNat 32 ((bs.take 4).foldr (fun b rest => b.toNat+256*rest) 0) :: decodeWords32 n (bs.drop 4)

def encodeWords32 (xs : List (BitVec 32)) : List Byte :=
  (xs.map (fun x => bytes32 (x.toNat : Int))).flatten

/-- Row-sum instruction fragment. Fixed-width and scalable lane shapes are
checked separately; all 32-bit vector additions are modular. -/
@[simp] def wideningIntrinsic (cfg : Config) (m : Memory) (op : Prim) (args : List Value) : Option Value :=
  match op, args with
  | .widenAddByte16S, [.halfwords acc, .vector 1 xs] =>
      if acc.length = 8 ∧ xs.length = 8 then some (.halfwords (WideningISA.widenAdd16 .signed acc xs)) else none
  | .widenAddByte16U, [.halfwords acc, .vector 1 xs] =>
      if acc.length = 8 ∧ xs.length = 8 then some (.halfwords (WideningISA.widenAdd16 .unsigned acc xs)) else none
  | .widenAddHalf32S, [.words32 acc, .halfwords xs] =>
      if acc.length = 4 ∧ xs.length = 4 then some (.words32 (WideningISA.widenAdd32 .signed acc xs)) else none
  | .widenAddHalf32U, [.words32 acc, .halfwords xs] =>
      if acc.length = 4 ∧ xs.length = 4 then some (.words32 (WideningISA.widenAdd32 .unsigned acc xs)) else none
  | .widenAddByte16RVVS, [.halfwords acc, .vector 1 xs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ acc.length ∧ vl.toNat ≤ xs.length ∧ vl.toNat ≤ cfg.capacity then
        some (.halfwords (WideningISA.widenAdd16 .signed (acc.take vl.toNat) (xs.take vl.toNat))) else none
  | .widenAddByte16RVVU, [.halfwords acc, .vector 1 xs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ acc.length ∧ vl.toNat ≤ xs.length ∧ vl.toNat ≤ cfg.capacity then
        some (.halfwords (WideningISA.widenAdd16 .unsigned (acc.take vl.toNat) (xs.take vl.toNat))) else none
  | .widenAddHalf32RVVS, [.words32 acc, .halfwords xs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ acc.length ∧ vl.toNat ≤ xs.length ∧ vl.toNat ≤ cfg.capacity then
        some (.words32 (WideningISA.widenAdd32 .signed (acc.take vl.toNat) (xs.take vl.toNat))) else none
  | .widenAddHalf32RVVU, [.words32 acc, .halfwords xs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ acc.length ∧ vl.toNat ≤ xs.length ∧ vl.toNat ≤ cfg.capacity then
        some (.words32 (WideningISA.widenAdd32 .unsigned (acc.take vl.toNat) (xs.take vl.toNat))) else none
  | .addWords32x4, [.words32 a, .words32 b] =>
      if a.length = 4 ∧ b.length = 4 then some (.words32 (List.zipWith (· + ·) a b)) else none
  | .addWords32x2, [.words32 a, .words32 b] =>
      if a.length = 2 ∧ b.length = 2 then some (.words32 (List.zipWith (· + ·) a b)) else none
  | .addWords32RVV, [.words32 a, .words32 b, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ a.length ∧ vl.toNat ≤ b.length ∧ vl.toNat ≤ cfg.capacity then
        some (.words32 (List.zipWith (· + ·) (a.take vl.toNat) (b.take vl.toNat))) else none
  | .loadWords32x4, [.pointer p] => do
      pure (.words32 (decodeWords32 4 (← loadBytes m p 16)))
  | .loadWords32x2, [.pointer p] => do
      pure (.words32 (decodeWords32 2 (← loadBytes m p 8)))
  | .loadWords32RVV, [.pointer p, .integer vl] => do
      if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity then
        pure (.words32 (decodeWords32 vl.toNat (← loadBytes m p (4*vl.toNat)))) else none
  | .lowWords32x2, [.words32 xs] =>
      if xs.length = 4 then some (.words32 (xs.take 2)) else none
  | .extractWords32x4, [.words32 a, .words32 b, .integer lane] =>
      if a.length = 4 ∧ b.length = 4 ∧ 0 ≤ lane ∧ lane < 4 then
        some (.words32 (((a++b).drop lane.toNat).take 4)) else none
  | .laneWords32S, [.words32 xs, .integer lane] =>
      if xs.length = 4 ∧ 0 ≤ lane ∧ lane < 4 then
        some (.integer (ReductionISA.value .signed xs[lane.toNat]!)) else none
  | .laneWords32U, [.words32 xs, .integer lane] =>
      if xs.length = 4 ∧ 0 ≤ lane ∧ lane < 4 then
        some (.integer (ReductionISA.value .unsigned xs[lane.toNat]!)) else none
  | .minimumU64, [.integer a, .integer b] =>
      if 0 ≤ a ∧ a < 2^64 ∧ 0 ≤ b ∧ b < 2^64 then some (.integer (min a b)) else none
  | .floorU64I32, [.integer n] =>
      -- Supported composition: an exactly representable uint64→double, floor,
      -- then a defined double→int conversion. No arbitrary FP values admitted.
      if 0 ≤ n ∧ n ≤ 2^53 ∧ n < 2^31 then some (.integer n) else none
  | _, _ => saturatingIntrinsic cfg op args

/-- Packing intrinsics. The empty tuple is an internal declaration marker;
its empty members cannot pass any fixed-width vector read/use check. -/
def tupleMemoryIntrinsic (cfg : Config) (m : Memory) (op : Prim) (args : List Value) : Option Value :=
  match op, args with
  | .emptyTupleU32x2, [] => some (.vectors 4 [[], []])
  | .setTupleU32x2, [.vectors 4 [a, b], .integer lane, .vector 4 v] =>
      if v.length = 8 ∧ (a.length = 0 ∨ a.length = 8) ∧ (b.length = 0 ∨ b.length = 8) then
        if lane = 0 then some (.vectors 4 [v, b])
        else if lane = 1 then some (.vectors 4 [a, v]) else none
      else none
  | .loadLaneU32x2, [.pointer p, .vector 4 old, .integer lane] => do
      if old.length = 8 ∧ 0 ≤ lane ∧ lane < 2 then
        pure (.vector 4 (replaceWord old (← loadBytes m p 4) lane.toNat)) else none
  | .load2LaneU32x2, [.pointer p, .vectors 4 [a, b], .integer lane] => do
      if a.length = 8 ∧ b.length = 8 ∧ 0 ≤ lane ∧ lane < 2 then
        let words ← loadBytes m p 8
        pure (.vectors 4 [replaceWord a (words.take 4) lane.toNat,
                          replaceWord b (words.drop 4) lane.toNat]) else none
  | .createU32TupleRVV, [.vector 4 a, .vector 4 b] =>
      if a.length = b.length ∧ a.length % 4 = 0 ∧ a.length ≤ 4*cfg.capacity then
        some (.vectors 4 [a, b]) else none
  | .dupU32PackM1, [.integer n, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity / 4 then
        some (.vector 4 ((List.replicate vl.toNat (bytes32 n)).flatten)) else none
  | .loadU32PackM1, [.pointer p, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity / 4 then
        (.vector 4) <$> loadBytes m p (4*vl.toNat) else none
  | _, _ => none

/-- Unit-stride two-field segments: lane i stores the first vector's word,
then the second vector's word. The effect checks all fields are disjoint. -/
def interleaveWords (a b : List Byte) : Nat → List Byte
  | 0 => []
  | n+1 => a.take 4 ++ b.take 4 ++ interleaveWords (a.drop 4) (b.drop 4) n

/-- Pure/value-returning intrinsic calls. Unmodeled signatures fail closed.
RVV tail-agnostic lanes are absent: only the active prefix can be used later. -/
def intrinsic (cfg : Config) (m : Memory) (op : Prim) (args : List Value) : Option Value :=
  match op with
  | .emptyTupleU32x2 | .setTupleU32x2 | .loadLaneU32x2 | .load2LaneU32x2
  | .createU32TupleRVV | .dupU32PackM1 | .loadU32PackM1 => tupleMemoryIntrinsic cfg m op args
  | .pairAcc16S | .pairAcc16U | .pairAcc32S | .pairAcc32U | .reduceI32x4S | .reduceI32x4U
  | .mulBytes16 | .vlmax32M8 | .vlmax32M1 | .dupI32M1 | .extendByte32RVVS | .extendByte32RVVU
  | .loadTable16 | .addI32TURVV | .reduceI32RVV | .scalarI32RVVS | .scalarI32RVVU => reductionIntrinsic cfg op args
  | _ =>
    match op, args with
    | .dup16, [.integer b] => some (.vector 1 (List.replicate 16 (BitVec.ofInt 8 b)))
    | .load16, [.pointer a] => (.vector 1) <$> loadBytes m a 16
    | .load8, [.pointer a] => (.vector 1) <$> loadBytes m a 8
    | .max16, xs => zipLanes 16 ByteISA.maxSigned xs
    | .min16, xs => zipLanes 16 ByteISA.minSigned xs
    | .max8, xs => zipLanes 8 ByteISA.maxSigned xs
    | .min8, xs => zipLanes 8 ByteISA.minSigned xs
    | .low8, [.vector 1 a] => if a.length = 16 then some (.vector 1 (a.take 8)) else none
    | .reinterpret32, [.vector 1 a] => if a.length = 8 then some (.vector 4 a) else none
    | .reinterpret16, [.vector 1 a] => if a.length = 8 then some (.vector 2 a) else none
    | .extract8, [.vector 1 a, .vector 1 b, .integer n] =>
        if a.length = 8 ∧ b.length = 8 ∧ 0 ≤ n ∧ n < 8 then
          some (.vector 1 (((a ++ b).drop n.toNat).take 8)) else none
    | .setvl, [.integer n] => if 0 ≤ n then some (.integer (cfg.choose n.toNat)) else none
    | .loadRVV, [.pointer a, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity then (.vector 1) <$> loadBytes m a vl.toNat else none
    | .maxRVV, xs => scalarLanes ByteISA.maxSigned xs
    | .minRVV, xs => scalarLanes ByteISA.minSigned xs
    | .loadU32x2, [.pointer a] => (.vector 4) <$> loadBytes m a 8
    | .dupU32x2, [.integer n] => some (.vector 4 (bytes32 n ++ bytes32 n))
    | .zipU32x2, [.vector 4 a, .vector 4 b] =>
        if a.length = 8 ∧ b.length = 8 then
          some (.vectors 4 [a.take 4 ++ b.take 4, a.drop 4 ++ b.drop 4]) else none
    | .loadU32RVV, [.pointer a, .integer vl] =>
        if 0 ≤ vl ∧ vl.toNat ≤ cfg.capacity then
          (.vector 4) <$> loadBytes m a (4 * vl.toNat) else none
    | .roundDown2, [.integer n, .integer 2] =>
        if 0 ≤ n then some (.integer (n / 2 * 2)) else none
    | .differenceOrZero, [.integer a, .integer b] =>
        if 0 ≤ a ∧ 0 ≤ b then some (.integer (max (a - b) 0)) else none
    | _, _ => wideningIntrinsic cfg m op args

def eval (cfg : Config) (s : State) : Expr → Option Value
  | .lit n => some (.integer n)
  | .byteArray bs => some (.vector 1 bs)
  | .var name => s.locals name
  | .null => some (.pointer 0)
  | .cast ty e => do
    let .integer n ← eval cfg s e | none
    pure (.integer (convert ty n))
  | .param base offset => do
    let .pointer a ← eval cfg s base | none
    loadParam s.memory (a + BitVec.ofNat 64 offset)
  | .param16 base offset => do
    let .pointer a ← eval cfg s base | none
    loadParam16 s.memory (a + BitVec.ofNat 64 offset)
  | .param8 base offset => do
    let .pointer a ← eval cfg s base | none
    let b ← s.memory.load (a + BitVec.ofNat 64 offset)
    pure (.integer b.toInt)
  | .paramU8 base offset => do
    let .pointer a ← eval cfg s base | none
    let b ← s.memory.load (a + BitVec.ofNat 64 offset)
    pure (.integer b.toNat)
  | .negSigned32 e => do
    let .integer n ← eval cfg s e | none
    if -(2^31) < n ∧ n < 2^31 then pure (.integer (-n)) else none
  | .checkedSigned32 e => do
    let .integer n ← eval cfg s e | none
    if -(2^31) ≤ n ∧ n < 2^31 then pure (.integer n) else none
  | .conditional cond yes no => do
    let test ← truth (← eval cfg s cond)
    if test then eval cfg s yes else eval cfg s no
  | .bin op a b => do binary op (← eval cfg s a) (← eval cfg s b)
  | .offset bytes base count => do
    let .pointer a ← eval cfg s base | none
    let .integer n ← eval cfg s count | none
    pure (.pointer (a + BitVec.ofInt 64 (bytes * n)))
  | .not e => do
    let b ← truth (← eval cfg s e)
    pure (.integer (if b then 0 else 1))
  | .or a b => do
    let test ← truth (← eval cfg s a)
    if test then pure (.integer 1) else do
      let second ← truth (← eval cfg s b)
      pure (.integer (if second then 1 else 0))
  | .ptrToInt e => do
    let .pointer a ← eval cfg s e | none
    pure (.integer a.toNat)
  | .intToPtr e => do
    let .integer n ← eval cfg s e | none
    pure (.pointer (BitVec.ofInt 64 n))
  | .vectorMember e index => do
    let .vectors width members ← eval cfg s e | none
    pure (.vector width (← members[index]?))
  | .call op args => do intrinsic cfg s.memory op (← args.mapM (eval cfg s))

def update (s : State) (name : String) (v : Value) : State :=
  { s with locals := fun x => if x = name then some v else s.locals x }

def storeVector (m : Memory) (width count : Nat) : List Value → Option Memory
  | [.pointer a, .vector w bs] =>
    if w = width ∧ bs.length = count then storeBytes m a bs else none
  | _ => none

def storeLane (m : Memory) (width : Nat) : List Value → Option Memory
  | [.pointer a, .vector w bs, .integer lane] =>
    if w = width ∧ 0 ≤ lane ∧ (lane.toNat + 1) * width ≤ bs.length then
      storeBytes m a ((bs.drop (lane.toNat * width)).take width) else none
  | _ => none

/-- A sufficient geometry check for pairwise disjoint active 4-byte lane
stores, even with modular base addresses. RVV strided store element order is
unspecified; overlapping destinations are outside this supported primitive. -/
def DisjointStride32 (stride : Address) (lanes : Nat) : Prop :=
  lanes ≤ 1 ∨ (4 ≤ stride.toNat ∧ stride.toNat * (lanes - 1) + 4 ≤ 2^64)

instance (stride : Address) (lanes : Nat) : Decidable (DisjointStride32 stride lanes) :=
  inferInstanceAs (Decidable (lanes ≤ 1 ∨ (4 ≤ stride.toNat ∧ stride.toNat * (lanes - 1) + 4 ≤ 2^64)))

/-- Active 32-bit lanes stored at a byte stride; each lane access checks all
four byte permissions. A surrounding intrinsic checks the source vector length. -/
def storeStrided32 (m : Memory) (a stride : Address) (bs : List Byte) : Nat → Option Memory
  | 0 => some m
  | n + 1 => do
    let next ← storeBytes m a (bs.take 4)
    storeStrided32 next (a + stride) stride (bs.drop 4) n

/-- Effectful intrinsic calls. Option.none is a model fault (bad signature,
failed assertion, or forbidden memory access), never a successful void return.
C executions with invalid accesses are outside the intended defined domain. -/
def effect (m : Memory) (op : Prim) (args : List Value) : Option Memory :=
  match op, args with
  | .assertion, [.integer n] => if n ≠ 0 then some m else none
  | .storeI32, [.pointer a, .integer n] =>
      if -(2^31) ≤ n ∧ n < 2^31 then storeBytes m a (bytes32 n) else none
  | .storeU32, [.pointer a, .integer n] =>
      if 0 ≤ n ∧ n < 2^32 then storeBytes m a (bytes32 n) else none
  | .store16, xs => storeVector m 1 16 xs
  | .store8, xs => storeVector m 1 8 xs
  | .storeWords32x4, [.pointer p, .words32 xs] =>
      if xs.length = 4 then storeBytes m p (encodeWords32 xs) else none
  | .storeWords32x2, [.pointer p, .words32 xs] =>
      if xs.length = 2 then storeBytes m p (encodeWords32 xs) else none
  | .storeWords32RVV, [.pointer p, .words32 xs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ xs.length then storeBytes m p (encodeWords32 (xs.take vl.toNat)) else none
  | .storeU32x2, xs => storeVector m 4 8 xs
  | .storeU32RVV, [.pointer a, .vector 4 bs, .integer vl] =>
      if 0 ≤ vl ∧ 4*vl.toNat ≤ bs.length then storeBytes m a (bs.take (4*vl.toNat)) else none
  | .storeSegment2U32RVV, [.pointer a, .vectors 4 [left, right], .integer vl] =>
      if 0 ≤ vl ∧ 4*vl.toNat ≤ left.length ∧ 4*vl.toNat ≤ right.length ∧ 8*vl.toNat ≤ 2^64 then
        storeBytes m a (interleaveWords left right vl.toNat) else none
  | .storeLane32, xs => storeLane m 4 xs
  | .storeLane16, xs => storeLane m 2 xs
  | .storeLane8, xs => storeLane m 1 xs
  | .storeRVV, [.pointer a, .vector 1 bs, .integer vl] =>
      if 0 ≤ vl ∧ vl.toNat ≤ bs.length then storeBytes m a (bs.take vl.toNat) else none
  | .storeStridedU32RVV, [.pointer a, .integer stride, .vector 4 bs, .integer vl] =>
      if 0 ≤ vl ∧ 4 * vl.toNat ≤ bs.length ∧ DisjointStride32 (BitVec.ofInt 64 stride) vl.toNat then
        storeStrided32 m a (BitVec.ofInt 64 stride) bs vl.toNat else none
  | _, _ => none

/-- Terminating execution of the structured program. There is no loop bound or
fuel parameter in this relation; a correctness proof must construct a derivation
for every valid input length. Undefined/faulting executions have no derivation. -/
inductive Exec (cfg : Config) : Stmt → State → State → Prop where
  | skip : Exec cfg .skip s s
  | assign : eval cfg s e = some v → Exec cfg (.assign name e) s (update s name v)
  | effect : args.mapM (eval cfg s) = some vs → effect s.memory op vs = some m →
      Exec cfg (.effect op args) s { s with memory := m }
  | seq : Exec cfg a s t → Exec cfg b t u → Exec cfg (.seq a b) s u
  | yes : eval cfg s e = some v → truth v = some true → Exec cfg a s t →
      Exec cfg (.branch e a b) s t
  | no : eval cfg s e = some v → truth v = some false → Exec cfg b s t →
      Exec cfg (.branch e a b) s t
  | done : eval cfg s e = some v → truth v = some false → Exec cfg (.loop e body) s s
  | more : eval cfg s e = some v → truth v = some true → Exec cfg body s t →
      Exec cfg (.loop e body) t u → Exec cfg (.loop e body) s u

/-- Executable bounded evaluator, used only for reflection and regressions.
The unbounded specification remains Exec. A successful result yields an Exec
proof; a fuel exhaustion result never establishes equivalence. -/
def run (cfg : Config) : Nat → Stmt → State → Option State
  | 0, _, _ => none
  | fuel + 1, code, s =>
    match code with
    | .skip => some s
    | .assign name e => (update s name) <$> eval cfg s e
    | .effect op args => do
        let vs ← args.mapM (eval cfg s)
        let m ← effect s.memory op vs
        pure { s with memory := m }
    | .seq a b => do run cfg fuel b (← run cfg fuel a s)
    | .branch e a b => do
        let v ← eval cfg s e
        let test ← truth v
        run cfg fuel (if test then a else b) s
    | .loop e body => do
        let v ← eval cfg s e
        let test ← truth v
        if test then run cfg fuel (.loop e body) (← run cfg fuel body s) else pure s

/-- All caller-visible bytes and access permissions are observed; locals are not.
The extracted functions return void. Status flags (including FPSR.QC and RVV
vxsat), access traces and timing are excluded from this ABI-call observation.
Saturating instructions can change these flags; padded inactive source lanes
can make their final values differ even when the observed memories agree. -/
def Equivalent (cfg : Config) (a b : Stmt) (pre : State → Prop) : Prop :=
  ∀ s, pre s → ∃ sa sb, Exec cfg a s sa ∧ Exec cfg b s sb ∧ sa.memory = sb.memory

end Salty.CByte
