import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_55864

-- The forbidden pairs among inputs 0–4 are the cut {0,4} × {2,3}
-- and the two extra pairs {0,4} and {1,3}. Input 5 requires input 0.
private def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 7]⟩,
    ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [8, 9]⟩,
    ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.not, [5]⟩,
    ⟨.or, [0, 14]⟩, ⟨.and, [13, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_55864

-- Finite replay follows the pattern of lean/PEqualNP/Outside/L_meta_24157.lean
-- at d667e87931366d16a0380297f19024953d7b1db3, with this circuit's gates.
theorem PEqualNP.Outside.L_meta_55864 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583203 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55864.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55864.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
