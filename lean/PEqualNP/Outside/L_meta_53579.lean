import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53579 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851451 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [4, 5]⟩,
      ⟨.or, [2, 9]⟩,
      ⟨.or, [8, 11]⟩,
      ⟨.or, [0, 6]⟩,
      ⟨.or, [1, 7]⟩,
      ⟨.and, [13, 14]⟩,
      ⟨.or, [13, 14]⟩,
      ⟨.or, [12, 15]⟩,
      ⟨.and, [16, 17]⟩,
      ⟨.or, [10, 18]⟩], 19⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
