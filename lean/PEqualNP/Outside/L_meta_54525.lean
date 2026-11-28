import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54525

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [6, 8]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [12, 9]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [3, 15]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.and, [14, 13]⟩,
    ⟨.or, [18, 17]⟩,
    ⟨.or, [20, 19]⟩], 21⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54525

theorem PEqualNP.Outside.L_meta_54525 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (909246 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54525.circuit, PEqualNP.Outside.L_meta_54525.monotone, by decide +kernel, by decide +kernel⟩
