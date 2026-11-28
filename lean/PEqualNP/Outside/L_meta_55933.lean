import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55933 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270585661 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [3, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [8, 9]⟩,
    ⟨.or, [11, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
