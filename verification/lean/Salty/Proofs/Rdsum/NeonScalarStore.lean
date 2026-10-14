import Salty.Proofs.Rdsum.NeonSmallStores
import Salty.Proofs.Rdsum.ScalarWord

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def neonScalarStore (kind : Interpretation) : Stmt :=
  branchYes (firstStatement (dropStatements 2 (branchNo (neonTailOutput kind))))

def scalarStoreCode (kind : Interpretation) : Stmt :=
  .seq (.effect (match kind with | .signed => .storeI32 | .unsigned => .storeU32)
    [.var "output", match kind with
      | .signed => .checkedSigned32 (.bin .add (.param (.var "output") 0)
          (.call .laneWords32S [.var "vacc0_2", .lit 0]))
      | .unsigned => .cast .u32 (.bin .add (.cast .u32 (.param (.var "output") 0))
          (.call .laneWords32U [.var "vacc0_2", .lit 0]))]) .skip

theorem neon_scalar_store_shape (kind : Interpretation) : neonScalarStore kind = scalarStoreCode kind := by
  cases kind <;> rfl

/-- The vector additions wrap; the signed C scalar tail additionally requires a defined sum. -/
def ScalarStoreDefined (kind : Interpretation) (old acc : BitVec 32) : Prop :=
  match kind with
  | .signed => -(2^31) ≤ old.toInt+acc.toInt ∧ old.toInt+acc.toInt < 2^31
  | .unsigned => True

def neonScalarStored (s : State) (output : Address) (acc : BitVec 32) : State :=
  {s with memory := writeBytes s.memory output (bytes32 ((readWord32 s.memory output+acc).toNat : Int))}

theorem checked_add_eval (cfg : Config) (s : State) (a b : Expr) (x y : Int)
    (ha : eval cfg s a = some (.integer x)) (hb : eval cfg s b = some (.integer y))
    (bounds : -(2^31) ≤ x+y ∧ x+y < 2^31) :
    eval cfg s (.checkedSigned32 (.bin .add a b)) = some (.integer (x+y)) := by
  simp only [eval, ha, hb, Option.bind_some, binary, bounds, ↓reduceIte, pure, bind]
  rfl

theorem scalar_lane_eval (kind : Interpretation) (cfg : Config) (s : State)
    (acc : List (BitVec 32)) (len : acc.length = 4)
    (av : s.locals "vacc0_2" = some (.words32 acc)) :
    eval cfg s (.call (match kind with | .signed => .laneWords32S | .unsigned => .laneWords32U)
      [.var "vacc0_2", .lit 0]) = some (.integer (value kind acc[0]!)) := by
  cases kind <;> simp [eval, intrinsic, av, len, value]

theorem scalar_param_eval (cfg : Config) (s : State) (output : Address)
    (out : s.locals "output" = some (.pointer output))
    (readable : ∀ a, Footprint output 4 a → s.memory.readable a = true) :
    eval cfg s (.param (.var "output") 0) = some (.integer (readWord32 s.memory output).toInt) := by
  simp [eval, out, loadParam_readWord s.memory output readable]

theorem neon_scalar_store_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (acc : List (BitVec 32)) (len : acc.length = 4)
    (out : s.locals "output" = some (.pointer output))
    (av : s.locals "vacc0_2" = some (.words32 acc))
    (readable : ∀ a, Footprint output 4 a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output 4 a → s.memory.writable a = true)
    (defined : ScalarStoreDefined kind (readWord32 s.memory output) acc[0]!) :
    Exec cfg (neonScalarStore kind) s (neonScalarStored s output acc[0]!) := by
  have load := scalar_param_eval cfg s output out readable
  have lane := scalar_lane_eval kind cfg s acc len av
  have store := storeBytes_success s.memory output (bytes32 ((readWord32 s.memory output+acc[0]!).toNat : Int))
    (by simpa only [bytes32, List.length_cons, List.length_nil] using writable)
  rw [neon_scalar_store_shape]
  cases kind with
  | signed =>
    have sum := checked_add_eval cfg s _ _ _ _ load lane defined
    apply Exec.seq (Exec.effect (vs := [.pointer output, .integer ((readWord32 s.memory output).toInt+acc[0]!.toInt)]) ?_ ?_) .skip
    · simp only [scalarStoreCode, List.mapM_cons, List.mapM_nil, sum, eval, out,
        Option.bind_some, pure, bind, value]
    · change effect s.memory .storeI32 _ = _
      simp only [effect, ScalarStoreDefined] at defined ⊢
      rw [if_pos defined, bytes32_signed_add]
      exact store
  | unsigned =>
    have left := eval_cast_integer cfg s _ .u32 _ load
    rw [convert_word_unsigned] at left
    have add : eval cfg s (.bin .add (.cast .u32 (.param (.var "output") 0))
        (.call .laneWords32U [.var "vacc0_2", .lit 0])) =
        some (.integer ((readWord32 s.memory output).toNat+acc[0]!.toNat)) := by
      rw [eval]
      simp only [left, lane, value, pure, bind, Option.bind_some, binary]
    have sum := eval_cast_integer cfg s _ .u32 _ add
    have ub : (0 : Int) ≤ convert .u32 ((readWord32 s.memory output).toNat+acc[0]!.toNat) ∧
        convert .u32 ((readWord32 s.memory output).toNat+acc[0]!.toNat) < 2^32 := by
      simp only [convert]
      have h := (BitVec.ofInt 32 ((readWord32 s.memory output).toNat+acc[0]!.toNat)).isLt
      constructor <;> omega
    apply Exec.seq (Exec.effect (vs := [.pointer output, .integer (convert .u32 ((readWord32 s.memory output).toNat+acc[0]!.toNat))]) ?_ ?_) .skip
    · simp only [scalarStoreCode, List.mapM_cons, List.mapM_nil, sum, eval, out,
        Option.bind_some, pure, bind, value]
    · change effect s.memory .storeU32 _ = _
      simp only [effect]
      rw [if_pos ub, bytes32_unsigned_add]
      exact store

end Salty.Kernels.Rdsum
