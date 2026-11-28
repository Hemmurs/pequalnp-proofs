import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54789 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274877099 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 6]⟩, ⟨.not, [5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [9, 11]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
