import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53653 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947519 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [8, 7]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [5, 1]⟩,
      ⟨.or, [12, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [4, 0]⟩, ⟨.and, [12, 13]⟩,
      ⟨.or, [16, 17]⟩, ⟨.or, [15, 18]⟩], 19⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  intro gate membership
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
