import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54349 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (290492 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨⟨[⟨.and, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [6, 17]⟩, ⟨.and, [16, 18]⟩, ⟨.or, [10, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
