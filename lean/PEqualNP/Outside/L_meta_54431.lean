import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54431

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [7, 12]⟩,
      ⟨GateOp.or, [12, 4]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.and, [0, 16]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.and, [11, 4]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.or, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (320503 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54431

theorem PEqualNP.Outside.L_meta_54431 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (320503 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54431.ckt, PEqualNP.Outside.L_meta_54431.mono, by decide, PEqualNP.Outside.L_meta_54431.rep⟩
