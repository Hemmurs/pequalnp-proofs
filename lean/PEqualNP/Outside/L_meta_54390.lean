import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54390

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [5, 6]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.or, [10, 7]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [16, 0]⟩,
    ⟨.or, [18, 17]⟩,
    ⟨.or, [19, 15]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54390

theorem PEqualNP.Outside.L_meta_54390 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323071 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_54390.circuit, PEqualNP.Outside.L_meta_54390.monotone, by decide +kernel, by decide +kernel⟩
