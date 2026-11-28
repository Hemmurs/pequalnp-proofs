import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_54623_aux

def witness : Circuit :=
  ⟨[⟨.or, [4, 7]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [5, 13]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [20, 21]⟩], 22⟩

end PEqualNP.Outside.L_meta_54623_aux

theorem PEqualNP.Outside.L_meta_54623 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288495 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_54623_aux.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [PEqualNP.Outside.L_meta_54623_aux.witness] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
