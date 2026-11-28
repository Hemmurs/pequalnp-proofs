import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54437

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 9]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.and, [10, 15]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.and, [12, 18]⟩,
    ⟨.or, [16, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54437

theorem PEqualNP.Outside.L_meta_54437 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321006 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54437.circuit, PEqualNP.Outside.L_meta_54437.monotone, by decide, ?_⟩
  decide +kernel
