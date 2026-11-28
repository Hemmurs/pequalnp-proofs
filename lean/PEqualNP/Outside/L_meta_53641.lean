import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53641 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898227 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨⟨[⟨.or, [1, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [4, 19]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
