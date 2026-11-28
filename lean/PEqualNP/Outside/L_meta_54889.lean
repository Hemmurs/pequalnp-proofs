import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54889

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.or, [8, 5]⟩,
      ⟨GateOp.not, [6]⟩,
      ⟨GateOp.and, [0, 10]⟩,
      ⟨GateOp.not, [9]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.or, [15, 14]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18233 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54889

theorem PEqualNP.Outside.L_meta_54889 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18233 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54889.ckt, PEqualNP.Outside.L_meta_54889.fan, by decide, PEqualNP.Outside.L_meta_54889.ev⟩
