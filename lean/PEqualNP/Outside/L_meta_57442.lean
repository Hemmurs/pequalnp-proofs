import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57442 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311467 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 0]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [5, 0]⟩, ⟨.not, [9]⟩, ⟨.not, [10]⟩, ⟨.and, [7, 3]⟩, ⟨.and, [12, 2]⟩, ⟨.and, [11, 6]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [16, 15]⟩], 17⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
