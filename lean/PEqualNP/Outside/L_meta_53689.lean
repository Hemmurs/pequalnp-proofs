import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53689

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 5]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [3, 16]⟩,
    ⟨.and, [10, 15]⟩,
    ⟨.and, [11, 17]⟩,
    ⟨.or, [18, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53689

theorem PEqualNP.Outside.L_meta_53689 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274877 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_53689.circuit, PEqualNP.Outside.L_meta_53689.monotone, by decide, ?_⟩
  decide +kernel
