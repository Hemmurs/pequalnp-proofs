import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53594_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (907199 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [3, 10] },
      { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.or, inputs := [6, 11] },
      { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.or, inputs := [12, 13] },
      { op := GateOp.or, inputs := [1, 4] }, { op := GateOp.or, inputs := [0, 14] },
      { op := GateOp.and, inputs := [15, 16] }, { op := GateOp.or, inputs := [17, 18] }],
    output := 19 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_53594_aux

theorem PEqualNP.Outside.L_meta_53594 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907199 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_53594_aux.upperC, PEqualNP.Outside.L_meta_53594_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_53594_aux.upper_rep⟩
