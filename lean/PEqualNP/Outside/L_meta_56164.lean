import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56164 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274893755 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [8, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
