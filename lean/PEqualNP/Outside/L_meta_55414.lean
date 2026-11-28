import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55414

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [4, 3] }, { op := GateOp.or, inputs := [0, 6] },
      { op := GateOp.and, inputs := [5, 0] }, { op := GateOp.or, inputs := [2, 7] },
      { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.or, inputs := [8, 10] },
      { op := GateOp.or, inputs := [11, 0] }, { op := GateOp.not, inputs := [12] },
      { op := GateOp.and, inputs := [9, 11] }, { op := GateOp.and, inputs := [13, 1] },
      { op := GateOp.or, inputs := [14, 15] }],
    output := 16 }

theorem fan : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295096 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_55414

theorem PEqualNP.Outside.L_meta_55414 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295096 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_55414.C, PEqualNP.Outside.L_meta_55414.fan, by decide, PEqualNP.Outside.L_meta_55414.ev⟩
