import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53645_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (1900024 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.or, inputs := [2, 10] }, { op := GateOp.or, inputs := [3, 12] },
      { op := GateOp.or, inputs := [0, 11] }, { op := GateOp.or, inputs := [6, 14] },
      { op := GateOp.and, inputs := [13, 15] }, { op := GateOp.or, inputs := [1, 7] },
      { op := GateOp.or, inputs := [12, 15] }, { op := GateOp.and, inputs := [17, 18] },
      { op := GateOp.or, inputs := [16, 19] }],
    output := 20 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_53645_aux

theorem PEqualNP.Outside.L_meta_53645 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900024 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_53645_aux.upperC, PEqualNP.Outside.L_meta_53645_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_53645_aux.upper_rep⟩
