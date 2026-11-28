import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54846 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321315 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 5]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [2, 3]⟩,
      ⟨.and, [8, 9]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [11, 12]⟩,
      ⟨.or, [10, 13]⟩, ⟨.not, [14]⟩], 15⟩
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro gate member
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · dsimp only [witness]
    decide
  · dsimp only [witness]
    decide +kernel
