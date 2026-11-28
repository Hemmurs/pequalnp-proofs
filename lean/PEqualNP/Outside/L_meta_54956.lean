import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54956 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52924 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [9, 7]⟩, ⟨.and, [8, 0]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [14, 10]⟩,
    ⟨.or, [15, 12]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
