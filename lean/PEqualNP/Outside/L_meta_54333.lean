import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54333

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [6, 11]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [11, 3]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.and, [10, 17]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.or, [18, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (288362 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54333

theorem PEqualNP.Outside.L_meta_54333 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288362 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54333.ckt, PEqualNP.Outside.L_meta_54333.mono, by decide, PEqualNP.Outside.L_meta_54333.rep⟩
