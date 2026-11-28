import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55328 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2313403 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
