import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54600 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1949565 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [2, 15]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 17]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [4, 20]⟩], 21⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
