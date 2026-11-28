import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54519 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907247 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [12, 4]⟩,
      ⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [15, 8]⟩, ⟨.and, [16, 14]⟩,
      ⟨.or, [17, 13]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [19, 0]⟩, ⟨.or, [20, 18]⟩], 21⟩
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro gate member
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · dsimp only [witness]
    decide
  · dsimp only [witness]
    decide +kernel
