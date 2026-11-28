import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53974 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113719 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.not, [0]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.not, [14]⟩], 15⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel
