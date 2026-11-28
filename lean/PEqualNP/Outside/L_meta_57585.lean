import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57585

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.not, [16]⟩], output := 17 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_57585

theorem PEqualNP.Outside.L_meta_57585 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549414 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_57585.c1, PEqualNP.Outside.L_meta_57585.f1, by decide, by decide⟩
