import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55891_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩], 16⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 11 := by decide +kernel

end PEqualNP.Outside.L_meta_55891_aux

theorem PEqualNP.Outside.L_meta_55891 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583971 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_55891_aux.circ, PEqualNP.Outside.L_meta_55891_aux.h_ok, PEqualNP.Outside.L_meta_55891_aux.h_sz, by decide +kernel⟩
