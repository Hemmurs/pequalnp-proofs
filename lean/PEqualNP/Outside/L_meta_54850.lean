import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54850
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [0, 1]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [4, 6]⟩,
  ⟨.or, [5, 7]⟩,
  ⟨.and, [8, 9]⟩,
  ⟨.and, [10, 11]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.not, [14]⟩], 15⟩

lemma fanin : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54850

open PEqualNP.Outside.L_meta_54850 in
theorem PEqualNP.Outside.L_meta_54850 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630322077 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fanin, by decide, by decide +kernel⟩
