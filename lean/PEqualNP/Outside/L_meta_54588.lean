import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54588

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (1947388 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [6, 12] },
      { op := GateOp.or, inputs := [13, 9] }, { op := GateOp.and, inputs := [0, 14] },
      { op := GateOp.or, inputs := [11, 12] }, { op := GateOp.and, inputs := [10, 16] },
      { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [3, 18] },
      { op := GateOp.or, inputs := [15, 17] }, { op := GateOp.or, inputs := [20, 19] }],
    output := 21 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_54588

theorem PEqualNP.Outside.L_meta_54588 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947388 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54588.upperC, PEqualNP.Outside.L_meta_54588.upper_mono, by decide, PEqualNP.Outside.L_meta_54588.upper_rep⟩
