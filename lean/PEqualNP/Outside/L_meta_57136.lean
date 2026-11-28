import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57136 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182589 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 0]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [12, 11]⟩, ⟨.not, [13]⟩, ⟨.not, [10]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [16, 14]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
