import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.not, [7]⟩,
      ⟨GateOp.and, [5, 9]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.and, [8, 4]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [13, 12]⟩,
      ⟨GateOp.not, [14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270715833 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54768

theorem PEqualNP.Outside.L_meta_54768 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270715833 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54768.ckt, PEqualNP.Outside.L_meta_54768.fan, by decide, PEqualNP.Outside.L_meta_54768.ev⟩
