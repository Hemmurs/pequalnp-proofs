import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55096

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 5]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [9, 13]⟩,
    ⟨.not, [14]⟩,
    ⟨.and, [12, 15]⟩], 16⟩

theorem gates_ok : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_55096

theorem PEqualNP.Outside.L_meta_55096 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182069 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55096.circuit, PEqualNP.Outside.L_meta_55096.gates_ok, by decide, ?_⟩
  decide +kernel
