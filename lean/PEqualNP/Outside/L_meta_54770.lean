import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54770

open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 2] }
      , { op := GateOp.and, inputs := [1, 6] }
      , { op := GateOp.or, inputs := [1, 6] }
      , { op := GateOp.not, inputs := [8] }
      , { op := GateOp.and, inputs := [5, 9] }
      , { op := GateOp.or, inputs := [2, 3] }
      , { op := GateOp.and, inputs := [4, 11] }
      , { op := GateOp.or, inputs := [7, 10] }
      , { op := GateOp.or, inputs := [13, 12] }
      , { op := GateOp.not, inputs := [14] }
      ]
    output := 15 }

end PEqualNP.Outside.L_meta_54770

theorem PEqualNP.Outside.L_meta_54770 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270716605 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54770.witnessCircuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54770.witnessCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
