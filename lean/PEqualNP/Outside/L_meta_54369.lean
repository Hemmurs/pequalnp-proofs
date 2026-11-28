import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54369

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [5, 6]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [1, 12]⟩,
    ⟨.and, [15, 17]⟩,
    ⟨.and, [13, 16]⟩,
    ⟨.or, [18, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54369

theorem PEqualNP.Outside.L_meta_54369 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292798 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_54369.circuit, PEqualNP.Outside.L_meta_54369.monotone, by decide, ?_⟩
  decide +kernel
