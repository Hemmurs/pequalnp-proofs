import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54497 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (810558 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨⟨[⟨.or, [7, 9]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [17, 20]⟩], 21⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
