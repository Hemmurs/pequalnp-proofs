import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_53637 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1897963 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  -- The gate list was synthesized on the 24 one-hot pairs and is checked below.
  -- Witness proof pattern: L_meta_23577.lean at 5a870a64d9d6817060329852222afa63b121ad91.
  refine ⟨⟨[⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [2, 9]⟩,
    ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [3, 11]⟩,
    ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [18, 19]⟩], 20⟩,
    ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
