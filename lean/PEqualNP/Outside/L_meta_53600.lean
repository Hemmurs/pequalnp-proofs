import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53600_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [0, 13]⟩,
    ⟨GateOp.and, [12, 14]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [3, 13]⟩,
    ⟨GateOp.and, [16, 17]⟩,
    ⟨GateOp.or, [10, 18]⟩,
    ⟨GateOp.or, [15, 19]⟩], 20⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

end PEqualNP.Outside.L_meta_53600_aux

theorem PEqualNP.Outside.L_meta_53600 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (915452 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_53600_aux.witness, PEqualNP.Outside.L_meta_53600_aux.witness_mono, by decide, ?_⟩
  decide +kernel
