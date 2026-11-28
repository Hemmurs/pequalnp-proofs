import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56811

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
    ⟨GateOp.or, [5, 2]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [5, 8]⟩,
    ⟨GateOp.or, [0, 9]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.not, [10]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.and, [4, 1]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.or, [15, 14]⟩
  ], 17⟩

theorem witness_fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_eval : ∀ i j : Fin 6,
    witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2147756 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_56811

theorem PEqualNP.Outside.L_meta_56811 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147756 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_56811.witness, PEqualNP.Outside.L_meta_56811.witness_fan, by decide, PEqualNP.Outside.L_meta_56811.witness_eval⟩
