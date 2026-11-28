import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54312

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [7, 11]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.or, [1, 6]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.and, [12, 17]⟩,
      ⟨GateOp.and, [10, 14]⟩,
      ⟨GateOp.or, [18, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (287413 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54312

theorem PEqualNP.Outside.L_meta_54312 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287413 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54312.ckt, PEqualNP.Outside.L_meta_54312.mono, by decide, PEqualNP.Outside.L_meta_54312.rep⟩
