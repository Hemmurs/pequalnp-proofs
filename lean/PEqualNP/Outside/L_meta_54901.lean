import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54901.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_54901.Helpers

theorem PEqualNP.Outside.L_meta_54901 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33957 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54901.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_54901.Helpers.witness]
