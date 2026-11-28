import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54786 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274876583 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
