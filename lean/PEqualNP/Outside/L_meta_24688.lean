import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24688

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [3, 6]⟩,
    ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.not, [11]⟩,
    ⟨GateOp.or, [12, 13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24688

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24688 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_24688.circuit, PEqualNP.Outside.L_meta_24688.shape, by decide, by decide +kernel⟩
