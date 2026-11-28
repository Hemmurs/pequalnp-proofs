import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54847

open PEqualNP.CircuitLowerBounds

-- Wire six serves both the star at point five and the path through point three.
def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 8]⟩,
    ⟨.and, [5, 9]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩

end PEqualNP.Outside.L_meta_54847

-- Replay pattern from ec69bbe46ad50b855316a9f00effea48bc6257b6,
-- lean/PEqualNP/Outside/L_meta_24157.lean, with the new circuit and promise.
theorem PEqualNP.Outside.L_meta_54847 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321567 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_54847.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54847.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
