import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55205

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [4, 6]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [0, 8]⟩,
      ⟨GateOp.and, [0, 2]⟩,
      ⟨GateOp.and, [3, 7]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.and, [9, 13]⟩,
      ⟨GateOp.and, [4, 2]⟩,
      ⟨GateOp.or, [14, 15]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198971 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_55205

theorem PEqualNP.Outside.L_meta_55205 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198971 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_55205.ckt, PEqualNP.Outside.L_meta_55205.fan, by decide, PEqualNP.Outside.L_meta_55205.ev⟩
