import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54473 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807857 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨⟨[⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 18]⟩, ⟨.and, [19, 0]⟩, ⟨.or, [17, 20]⟩], 21⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
