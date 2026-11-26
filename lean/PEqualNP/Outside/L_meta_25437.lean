import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25437

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.or, [0, 7]⟩,
    ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.and, [10, 11]⟩,
    ⟨GateOp.or, [5, 12]⟩,
    ⟨GateOp.not, [13]⟩,
    ⟨GateOp.or, [8, 14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25437

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25437 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549433 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_25437.circuit, PEqualNP.Outside.L_meta_25437.shape, by decide, by decide +kernel⟩
