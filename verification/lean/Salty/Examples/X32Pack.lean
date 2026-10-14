import Salty.Generated.X32PackNeon
import Salty.Generated.X32PackRvv
import Salty.Examples.Rsum

/-! Finite executions against an independent packed-layout oracle. These are
regression checks of the bridge, not unbounded equivalence proofs. -/
namespace Salty.Kernels.X32PackExamples
open CByte

def weight (g c k : Nat) : Int := 2147483648 + 10000*g + 100*c + k

def bias (g c : Nat) : Int := 4294901760 + 100*g + c

def tileBytes (kc extra : Nat) : Nat := 8*(kc+1)+extra

def outputBytes (g nc kc extra : Nat) : Nat := g*((nc+1)/2)*tileBytes kc extra

def state (g nc kc extra : Nat) (withBias : Bool) : State :=
  ⟨fun name =>
    if name = "g" then some (.integer g)
    else if name = "nc" then some (.integer nc)
    else if name = "kc" then some (.integer kc)
    else if name = "nr" then some (.integer 2)
    else if name = "kr" ∨ name = "sr" then some (.integer 1)
    else if name = "weights" then some (.pointer 4096#64)
    else if name = "bias" then some (.pointer (if withBias then 32768#64 else 0#64))
    else if name = "packed_weights" then some (.pointer 65536#64)
    else if name = "extra_bytes" then some (.integer extra)
    else if name = "scale" ∨ name = "params" then some (.pointer 0#64)
    else none,
   ⟨fun a =>
      if 4096 ≤ a.toNat ∧ a.toNat < 4096+4*g*nc*kc then
        let word := (a.toNat-4096)/4
        (bytes32 (weight (word/(nc*kc)) (word/kc%nc) (word%kc)))[(a.toNat-4096)%4]!
      else if 32768 ≤ a.toNat ∧ a.toNat < 32768+4*g*nc then
        let word := (a.toNat-32768)/4
        (bytes32 (bias (word/nc) (word%nc)))[(a.toNat-32768)%4]!
      else 165,
    fun a => (4096 ≤ a.toNat ∧ a.toNat < 4096+4*g*nc*kc) ∨
      (withBias ∧ 32768 ≤ a.toNat ∧ a.toNat < 32768+4*g*nc),
    fun a => 65536 ≤ a.toNat ∧ a.toNat < 65536+outputBytes g nc kc extra⟩⟩

/-- Layout includes untouched odd-channel holes and extra-byte gaps. Without
bias the source zeroes both header words even in an odd final channel tile. -/
def expected (nc kc extra offset : Nat) (withBias : Bool) : Byte :=
  let tile := offset / tileBytes kc extra
  let group := tile / ((nc+1)/2)
  let channel := 2*(tile%((nc+1)/2))
  let within := offset % tileBytes kc extra
  if within < 8 then
    if withBias then
      if channel+within/4 < nc then (bytes32 (bias group (channel+within/4)))[within%4]! else 165
    else 0
  else if within < 8*(kc+1) then
    let field := (within-8)%8/4
    if channel+field < nc then
      (bytes32 (weight group (channel+field) ((within-8)/8)))[within%4]!
    else 165
  else 165

def check (cfg : Config) (code : Stmt) (g nc kc extra : Nat) (withBias : Bool) : Bool :=
  match run cfg 2048 code (state g nc kc extra withBias) with
  | none => false
  | some t =>
      (List.range (outputBytes g nc kc extra)).all (fun i =>
        t.memory.data (65536#64 + BitVec.ofNat 64 i) == expected nc kc extra i withBias) &&
      t.memory.data 65535#64 == 165 &&
      t.memory.data (65536#64 + BitVec.ofNat 64 (outputBytes g nc kc extra)) == 165

end Salty.Kernels.X32PackExamples
