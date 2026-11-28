import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54833 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (815975615 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
