import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56095

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.and, [0, 2]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.not, [15]⟩], 16⟩

theorem shape : PEqualNP.MetaComplexity.FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_56095

theorem PEqualNP.Outside.L_meta_56095 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274876859 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_56095.witness, PEqualNP.Outside.L_meta_56095.shape, by decide, by decide +kernel⟩
