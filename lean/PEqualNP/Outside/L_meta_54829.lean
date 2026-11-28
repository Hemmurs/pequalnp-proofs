import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54829_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The ten gates found by exact synthesis: wires 0-5 are the points, gate `j` writes wire
`6 + j`, and the last gate writes the output wire 15. -/
def gs : List Gate := [
  ⟨.and, [3, 4]⟩,
  ⟨.and, [0, 3]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [0, 9]⟩,
  ⟨.and, [10, 11]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.not, [12]⟩,
  ⟨.and, [13, 14]⟩
]

def C : Circuit := ⟨gs, 15⟩

theorem fan : FanInTwo C := by
  intro g hg
  simp only [C, gs, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem small : C.size ≤ 10 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem sem : ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (815942055 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54829_aux

theorem PEqualNP.Outside.L_meta_54829 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (815942055 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_54829_aux.C,
    PEqualNP.Outside.L_meta_54829_aux.fan,
    PEqualNP.Outside.L_meta_54829_aux.small,
    PEqualNP.Outside.L_meta_54829_aux.sem⟩
