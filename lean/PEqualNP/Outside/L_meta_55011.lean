import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55011 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147484 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [4, 1]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
