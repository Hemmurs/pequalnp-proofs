import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54388

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [5, 6]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [8, 16]⟩,
    ⟨.and, [15, 17]⟩,
    ⟨.or, [14, 18]⟩,
    ⟨.or, [11, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_54388

theorem PEqualNP.Outside.L_meta_54388 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323006 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_54388.circuit, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_54388.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
