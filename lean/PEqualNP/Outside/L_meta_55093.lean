import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55093

open CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩,
    ⟨.or, [6, 2]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.or, [5, 0]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [2, 12]⟩,
    ⟨.and, [9, 13]⟩,
    ⟨.not, [14]⟩,
    ⟨.and, [8, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_55093

theorem PEqualNP.Outside.L_meta_55093 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181815 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨L_meta_55093.witness, ?_, ?_, ?_⟩
  · simp [MetaComplexity.FanInTwo, L_meta_55093.witness]
  · decide +kernel
  · decide +kernel
