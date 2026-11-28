import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54895 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20029 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [0]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.not, [1]⟩, ⟨.not, [10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
