import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57130 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182325 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [11, 9]⟩, ⟨.and, [10, 1]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [13, 12]⟩, ⟨.not, [15]⟩, ⟨.and, [16, 14]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
