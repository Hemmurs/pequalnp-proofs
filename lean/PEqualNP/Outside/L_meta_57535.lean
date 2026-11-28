import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57535 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409533 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [0, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [9, 1]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [14, 15]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
