import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55682

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [1] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 0] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 2] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 8] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 5] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 3] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 2] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 14] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 10] }
  ],
  output := 16 }

end PEqualNP.Outside.L_meta_55682

theorem PEqualNP.Outside.L_meta_55682 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409528 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55682.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_55682.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
