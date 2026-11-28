import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54459

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [6, 7]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.or, [5, 15]⟩,
    ⟨.or, [1, 16]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [8, 18]⟩,
    ⟨.and, [17, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54459

theorem PEqualNP.Outside.L_meta_54459 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (800622 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54459.circuit, PEqualNP.Outside.L_meta_54459.monotone, by decide, ?_⟩
  decide +kernel
