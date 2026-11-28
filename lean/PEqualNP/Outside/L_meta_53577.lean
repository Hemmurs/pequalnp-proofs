import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53577

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 9]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.or, [3, 14]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [18, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53577

theorem PEqualNP.Outside.L_meta_53577 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851196 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_53577.circuit, PEqualNP.Outside.L_meta_53577.monotone, by decide, ?_⟩
  decide +kernel
