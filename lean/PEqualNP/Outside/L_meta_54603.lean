import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54603

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [7, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 14]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.and, [3, 15]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 0]⟩,
    ⟨.or, [20, 18]⟩], 21⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54603

theorem PEqualNP.Outside.L_meta_54603 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072255 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54603.circuit, PEqualNP.Outside.L_meta_54603.monotone, by decide +kernel, by decide +kernel⟩
