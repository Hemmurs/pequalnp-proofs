import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54341 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288697 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [4, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 9]⟩, ⟨.and, [18, 19]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
