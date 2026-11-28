import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53691

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 6]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.and, [11, 16]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.and, [15, 18]⟩,
    ⟨.or, [17, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53691

theorem PEqualNP.Outside.L_meta_53691 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275318 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_53691.circuit, PEqualNP.Outside.L_meta_53691.monotone, by decide, ?_⟩
  decide +kernel
