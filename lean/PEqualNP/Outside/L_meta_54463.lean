import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54463

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [13, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.and, [16, 10]⟩,
      ⟨GateOp.and, [11, 12]⟩,
      ⟨GateOp.and, [3, 13]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.or, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (807355 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54463

theorem PEqualNP.Outside.L_meta_54463 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807355 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54463.ckt, PEqualNP.Outside.L_meta_54463.mono, by decide, PEqualNP.Outside.L_meta_54463.rep⟩
