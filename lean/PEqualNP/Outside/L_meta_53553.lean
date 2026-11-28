import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53553 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841583 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [0, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [15, 2]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [16, 12]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [19, 4]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
