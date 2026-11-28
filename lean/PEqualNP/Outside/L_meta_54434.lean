import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54434

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 7]⟩,
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [3, 11]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.and, [13, 15]⟩,
      ⟨GateOp.and, [12, 4]⟩,
      ⟨GateOp.and, [10, 16]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.or, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (320953 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54434

theorem PEqualNP.Outside.L_meta_54434 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (320953 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54434.ckt, PEqualNP.Outside.L_meta_54434.mono, by decide, PEqualNP.Outside.L_meta_54434.rep⟩
