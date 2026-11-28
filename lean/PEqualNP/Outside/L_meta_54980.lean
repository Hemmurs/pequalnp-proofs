import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54980

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [7, 3]⟩,
    ⟨GateOp.or, [1, 10]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.and, [11, 4]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.or, [14, 13]⟩
  ], 16⟩

theorem witness_fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_eval : ∀ i j : Fin 6,
    witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2114597 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_54980

theorem PEqualNP.Outside.L_meta_54980 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114597 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_54980.witness, PEqualNP.Outside.L_meta_54980.witness_fan, by decide, PEqualNP.Outside.L_meta_54980.witness_eval⟩
