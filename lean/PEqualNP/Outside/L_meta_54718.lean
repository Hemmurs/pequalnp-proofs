import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54718

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩,
    ⟨GateOp.and, [8, 11]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.and, [13, 14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_54718

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_54718 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583730 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_54718.circuit, PEqualNP.Outside.L_meta_54718.shape, by decide, by decide +kernel⟩
