import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54399

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [5, 6]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.or, [11, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [12, 9]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [14, 15]⟩,
    ⟨.and, [2, 13]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [19, 16]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54399

theorem PEqualNP.Outside.L_meta_54399 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327094 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_54399.circuit, PEqualNP.Outside.L_meta_54399.monotone, by decide +kernel, by decide +kernel⟩
