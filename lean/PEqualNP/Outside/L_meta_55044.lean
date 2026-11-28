import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55044 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164518 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [1, 7]⟩, ⟨.not, [9]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
