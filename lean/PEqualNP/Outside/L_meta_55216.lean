import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55216 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2213818 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 2]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [14, 12]⟩,
    ⟨.or, [15, 13]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
