import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54324

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [1, 4]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [7, 16]⟩,
    ⟨.or, [2, 17]⟩,
    ⟨.and, [14, 18]⟩,
    ⟨.or, [12, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_54324

theorem PEqualNP.Outside.L_meta_54324 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287673 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_54324.circuit, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_54324.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
