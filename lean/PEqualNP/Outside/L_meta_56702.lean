import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56702 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2116925 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [5, 0]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [14, 13]⟩, ⟨.not, [12]⟩, ⟨.or, [15, 16]⟩], 17⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
