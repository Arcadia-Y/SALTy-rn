import Salty.Model.Memory
import Std

namespace Salty

namespace Memory

theorem write_same (m : Memory) (a : Address) (b : Byte) :
    (m.write a b).data a = b := by simp [write]

/-- The elementary frame property: a store changes only its destination. -/
theorem write_other (m : Memory) (a p : Address) (b : Byte) (h : p ≠ a) :
    (m.write a b).data p = m.data p := by simp [write, h]

theorem load_write (m : Memory) (a : Address) (b : Byte) (h : m.readable a = true) :
    (m.write a b).load a = some b := by simp [load, write, h]
end Memory
end Salty
