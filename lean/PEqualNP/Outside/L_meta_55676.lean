import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55676

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [5] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 2] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 0] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 10] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 8] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 9] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [12] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }
  ],
  output := 16 }

end PEqualNP.Outside.L_meta_55676

theorem PEqualNP.Outside.L_meta_55676 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409141 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55676.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_55676.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
