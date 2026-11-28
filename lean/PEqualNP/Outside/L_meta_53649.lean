import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53649 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940159 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [3, 7]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [17, 19]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
