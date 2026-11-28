import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53603 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1040319 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [0, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
