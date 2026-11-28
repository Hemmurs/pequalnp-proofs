import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53692

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [3, 14]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.and, [17, 18]⟩,
    ⟨.or, [16, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53692

theorem PEqualNP.Outside.L_meta_53692 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275326 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_53692.circuit, PEqualNP.Outside.L_meta_53692.monotone, by decide, ?_⟩
  decide +kernel
