import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55535

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.not, [5]⟩,
    ⟨GateOp.and, [6, 8]⟩,
    ⟨GateOp.and, [7, 9]⟩,
    ⟨GateOp.or, [0, 10]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [1, 11]⟩,
    ⟨GateOp.not, [13]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.not, [15]⟩]
  output := 16

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_55535

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_55535 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4312765 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_55535.circuit, PEqualNP.Outside.L_meta_55535.shape, by decide, by decide +kernel⟩
