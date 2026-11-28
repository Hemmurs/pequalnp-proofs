import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54625

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 7]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.and, [2, 15]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [20, 16]⟩,
    ⟨.or, [21, 18]⟩], 22⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54625

theorem PEqualNP.Outside.L_meta_54625 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288509 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_54625.circuit, PEqualNP.Outside.L_meta_54625.monotone, by decide +kernel, by decide +kernel⟩
