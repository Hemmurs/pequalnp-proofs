import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54874

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.and, [2, 8]⟩,
      ⟨GateOp.or, [3, 9]⟩,
      ⟨GateOp.or, [11, 10]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.and, [6, 13]⟩,
      ⟨GateOp.and, [3, 1]⟩,
      ⟨GateOp.or, [14, 15]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17201 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54874

theorem PEqualNP.Outside.L_meta_54874 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17201 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54874.ckt, PEqualNP.Outside.L_meta_54874.fan, by decide, PEqualNP.Outside.L_meta_54874.ev⟩
