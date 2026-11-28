import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54038

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [6, 2]⟩,
      ⟨GateOp.or, [7, 3]⟩,
      ⟨GateOp.or, [7, 4]⟩,
      ⟨GateOp.or, [9, 5]⟩,
      ⟨GateOp.and, [6, 2]⟩,
      ⟨GateOp.and, [3, 10]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.and, [8, 14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2313395 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54038

theorem PEqualNP.Outside.L_meta_54038 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2313395 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54038.ckt, PEqualNP.Outside.L_meta_54038.fan, by decide, PEqualNP.Outside.L_meta_54038.ev⟩
