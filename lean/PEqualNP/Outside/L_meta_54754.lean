import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54754 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270650293 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
