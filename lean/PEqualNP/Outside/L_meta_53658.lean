import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53658 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1949305 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.and, [2, 14]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [4, 19]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
