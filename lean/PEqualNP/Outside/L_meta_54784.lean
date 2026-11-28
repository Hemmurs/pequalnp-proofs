import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54784_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩], 15⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 10 := by decide +kernel

end PEqualNP.Outside.L_meta_54784_aux

theorem PEqualNP.Outside.L_meta_54784 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274860991 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_54784_aux.circ, PEqualNP.Outside.L_meta_54784_aux.h_ok, PEqualNP.Outside.L_meta_54784_aux.h_sz, by decide +kernel⟩
