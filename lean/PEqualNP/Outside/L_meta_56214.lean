import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56214 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (279104701 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 2]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [0, 7]⟩,
    ⟨.and, [9, 7]⟩, ⟨.or, [11, 5]⟩, ⟨.not, [12]⟩, ⟨.or, [10, 1]⟩, ⟨.and, [5, 14]⟩,
    ⟨.or, [13, 15]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
