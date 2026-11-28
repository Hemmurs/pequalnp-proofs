import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55892 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583975 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩,
      ⟨.not, [6]⟩,
      ⟨.or, [3, 7]⟩,
      ⟨.or, [4, 8]⟩,
      ⟨.or, [5, 6]⟩,
      ⟨.and, [9, 10]⟩,
      ⟨.or, [1, 4]⟩,
      ⟨.or, [2, 3]⟩,
      ⟨.and, [12, 13]⟩,
      ⟨.or, [11, 14]⟩,
      ⟨.not, [15]⟩], 16⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
