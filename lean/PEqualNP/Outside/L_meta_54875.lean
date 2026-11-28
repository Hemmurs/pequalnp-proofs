import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54875

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_54875

theorem PEqualNP.Outside.L_meta_54875 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17304 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54875.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_54875.witness]
