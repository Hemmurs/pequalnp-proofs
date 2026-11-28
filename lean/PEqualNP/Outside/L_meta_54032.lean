import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54032

open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  { gates :=
      [ { op := GateOp.and, inputs := [2, 4] }
      , { op := GateOp.or, inputs := [5, 4] }
      , { op := GateOp.or, inputs := [0, 6] }
      , { op := GateOp.or, inputs := [7, 2] }
      , { op := GateOp.or, inputs := [1, 8] }
      , { op := GateOp.or, inputs := [1, 7] }
      , { op := GateOp.not, inputs := [11] }
      , { op := GateOp.or, inputs := [9, 3] }
      , { op := GateOp.and, inputs := [10, 13] }
      , { op := GateOp.or, inputs := [12, 14] }
      ]
    output := 15 }

end PEqualNP.Outside.L_meta_54032

theorem PEqualNP.Outside.L_meta_54032 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215741 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54032.witnessCircuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54032.witnessCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
