import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54642

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [7, 8]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.or, [12, 6]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.and, [1, 15]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.or, [17, 16]⟩,
    ⟨.or, [20, 19]⟩,
    ⟨.or, [21, 18]⟩], 22⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54642

theorem PEqualNP.Outside.L_meta_54642 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292602 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_54642.circuit, PEqualNP.Outside.L_meta_54642.monotone, by decide +kernel, by decide +kernel⟩
