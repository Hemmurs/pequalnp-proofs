import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54897 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20158 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.not, [2]⟩, ⟨.and, [1, 11]⟩, ⟨.not, [9]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [10, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
