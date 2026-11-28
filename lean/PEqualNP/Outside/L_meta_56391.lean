import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56391 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16574 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [5, 4]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.and, [2, 1]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [3, 12]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [9, 14]⟩,
    ⟨.or, [8, 15]⟩], 16⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
  · decide +kernel
