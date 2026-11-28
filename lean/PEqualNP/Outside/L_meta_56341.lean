import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56341 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321563 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [2, 3]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.or, [2, 5]⟩,
      ⟨.or, [3, 5]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.and, [7, 8]⟩,
      ⟨.and, [6, 10]⟩,
      ⟨.or, [1, 12]⟩,
      ⟨.and, [9, 13]⟩,
      ⟨.or, [11, 14]⟩,
      ⟨.not, [15]⟩], 16⟩
  exact ⟨C, by simp [C, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide⟩
