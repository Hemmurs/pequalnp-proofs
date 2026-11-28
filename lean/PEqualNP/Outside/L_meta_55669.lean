import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55669

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [8, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_55669

theorem PEqualNP.Outside.L_meta_55669 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408114 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55669.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_55669.witness]
