import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54618

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [5, 7]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [10, 4]⟩,
    ⟨.or, [14, 6]⟩,
    ⟨.and, [1, 15]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [2, 17]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [20, 18]⟩,
    ⟨.or, [21, 19]⟩], 22⟩

lemma monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma represents : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (287738 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_54618

theorem PEqualNP.Outside.L_meta_54618 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287738 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_54618.witness, PEqualNP.Outside.L_meta_54618.monotone, by decide,
    PEqualNP.Outside.L_meta_54618.represents⟩
