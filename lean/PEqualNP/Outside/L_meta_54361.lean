import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54361 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291832 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [14, 10]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [19, 16]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
