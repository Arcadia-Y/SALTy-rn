import Salty.Model.Behavior
import Salty.Model.Memory

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.ByteISA`. -/

/-! A small assembly-like instruction semantics for integer byte-vector programs.
This is an executable intermediate language, not an ISA-validated NEON/RVV subset or a decoder.
No floating-point instruction is accepted. Concrete source/binary lifting is
still required before a program in this syntax can certify a repository kernel.
-/
namespace Salty.ByteISA

abbrev Reg := Fin 32
abbrev GPR := Reg → BitVec 64
abbrev VPR := Reg → Nat → Byte

inductive Width where
  | fixed (lanes : Nat)
  | active
  deriving DecidableEq

inductive Instruction where
  | immediate (dst : Reg) (value : BitVec 64)
  | add (dst src : Reg) (value : BitVec 64)
  | sub (dst lhs rhs : Reg)
  | setvl (dst avl : Reg)
  | load (dst base : Reg) (width : Width)
  | store (src base : Reg) (width : Width)
  | signedMax (dst src bound : Reg) (width : Width)
  | signedMin (dst src bound : Reg) (width : Width)
  | branchNonzero (src : Reg) (target : Nat)
  | jump (target : Nat)
  | ret
  deriving DecidableEq

structure State where
  pc : Nat
  x : GPR
  v : VPR
  vl : Nat
  memory : Memory

structure Observation where
  result : BitVec 64
  bytes : Address → Byte

inductive FaultKind where
  | invalidPC | illegalWidth | unreadable | unwritable
  deriving DecidableEq

/-- A fault includes the memory at the point of failure. Sequential stores
retain their completed prefix, rather than pretending accesses are atomic. -/
structure Fault where
  kind : FaultKind
  address : Address
  bytes : Address → Byte

def update {A : Type} (f : Reg → A) (r : Reg) (value : A) : Reg → A :=
  fun q => if q = r then value else f q

def width (s : State) : Width → Nat
  | .fixed n => n
  | .active => s.vl

def maxSigned (a b : Byte) : Byte := if a.toInt < b.toInt then b else a
def minSigned (a b : Byte) : Byte := if a.toInt < b.toInt then a else b

def loadLanes (m : Memory) (base : Address) : Nat → Nat → Except Fault (List Byte)
  | 0, _ => .ok []
  | n + 1, offset =>
    let address := base + BitVec.ofNat 64 offset
    match m.load address with
    | none => .error ⟨.unreadable, address, m.data⟩
    | some byte => (loadLanes m base n (offset + 1)).map (byte :: ·)

def storeLanes (base : Address) (values : Nat → Byte) : Nat → Nat → Memory → Except Fault Memory
  | 0, _, m => .ok m
  | n + 1, offset, m =>
    let address := base + BitVec.ofNat 64 offset
    match m.store address (values offset) with
    | none => .error ⟨.unwritable, address, m.data⟩
    | some m' => storeLanes base values n (offset + 1) m'

/-- Capacity is the number of byte lanes in a register group. VSETVL here
chooses min(AVL,capacity); other legal choices require another instantiation.
Fixed-width operations are useful for decoded NEON byte operations. -/
def machine (program : List Instruction) (capacity : Nat) : Machine State Observation Fault where
  next s :=
    let next := { s with pc := s.pc + 1 }
    let illegal := Sum.inl (Outcome.fault ⟨.illegalWidth, 0, s.memory.data⟩)
    let vectorOp (dst src bound : Reg) (w : Width) (op : Byte → Byte → Byte) :=
      let n := width s w
      if n > capacity then illegal else
        let values := fun i => if i < n then op (s.v src i) (s.x bound |>.truncate 8) else s.v dst i
        Sum.inr { next with v := update s.v dst values }
    match program[s.pc]? with
    | none => .inl (.fault ⟨.invalidPC, 0, s.memory.data⟩)
    | some .ret => .inl (.returned ⟨s.x 0, s.memory.data⟩)
    | some (.immediate dst value) => .inr { next with x := update s.x dst value }
    | some (.add dst src value) => .inr { next with x := update s.x dst (s.x src + value) }
    | some (.sub dst lhs rhs) => .inr { next with x := update s.x dst (s.x lhs - s.x rhs) }
    | some (.branchNonzero src target) =>
      .inr (if s.x src = 0 then next else { s with pc := target })
    | some (.jump target) => .inr { s with pc := target }
    | some (.setvl dst avl) =>
      if capacity = 0 then illegal else
        let n := min (s.x avl).toNat capacity
        .inr { next with vl := n, x := update s.x dst (BitVec.ofNat 64 n) }
    | some (.signedMax dst src bound w) => vectorOp dst src bound w maxSigned
    | some (.signedMin dst src bound w) => vectorOp dst src bound w minSigned
    | some (.load dst base w) =>
      let n := width s w
      if n > capacity then illegal else
        match loadLanes s.memory (s.x base) n 0 with
        | .error fault => .inl (.fault fault)
        | .ok bytes =>
          .inr { next with v := update s.v dst (fun i => if i < n then bytes[i]! else s.v dst i) }
    | some (.store src base w) =>
      let n := width s w
      if n > capacity then illegal else
        match storeLanes (s.x base) (s.v src) n 0 s.memory with
        | .error fault => .inl (.fault fault)
        | .ok memory => .inr { next with memory := memory }

end Salty.ByteISA
