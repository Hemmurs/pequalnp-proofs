import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53681

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.or, [1, 8]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.and, [11, 10]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [17, 4]⟩,
      ⟨GateOp.or, [18, 5]⟩,
      ⟨GateOp.or, [19, 6]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (8256503 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53681

theorem PEqualNP.Outside.L_meta_53681 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (8256503 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53681.ckt, PEqualNP.Outside.L_meta_53681.mono, by decide, PEqualNP.Outside.L_meta_53681.rep⟩
