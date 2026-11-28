import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [4, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54568

theorem PEqualNP.Outside.L_meta_54568 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883517 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54568.circuit, PEqualNP.Outside.L_meta_54568.monotone, by decide, ?_⟩
  decide +kernel
