import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54756 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270667711 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.and, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.not, [8]⟩,
    ⟨.and, [2, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [11, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
