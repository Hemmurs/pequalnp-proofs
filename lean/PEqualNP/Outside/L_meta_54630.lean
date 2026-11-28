import PEqualNP.Defs

-- Proof pattern of the merged L_meta_22289 (Arthur Ariel Sabintsev); circuit from the 4x6 class table of
-- notes/tools/improve/gen/rep46.py (annealing search over all 3250 row/column classes, relabelled to this mask).
theorem PEqualNP.Outside.L_meta_54630 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291582 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 20] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
