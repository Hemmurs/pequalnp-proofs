import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54491

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [7, 8]⟩,
    ⟨.or, [10, 9]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [2, 15]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 17]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [19, 16]⟩,
    ⟨.or, [20, 18]⟩], 21⟩

lemma monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma represents : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (808632 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_54491

theorem PEqualNP.Outside.L_meta_54491 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808632 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54491.witness, PEqualNP.Outside.L_meta_54491.monotone, by decide,
    PEqualNP.Outside.L_meta_54491.represents⟩
