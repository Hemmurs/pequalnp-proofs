import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53554 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841587 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [5, 1]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [19, 4]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
