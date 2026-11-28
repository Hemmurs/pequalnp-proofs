import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54775 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843821 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 8]⟩,
    ⟨.or, [4, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 12]⟩,
    ⟨.not, [11]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
