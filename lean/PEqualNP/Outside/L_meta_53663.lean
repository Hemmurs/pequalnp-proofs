import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53663

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.or, [1, 8]⟩,
      ⟨GateOp.and, [10, 11]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [2, 12]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.and, [13, 15]⟩,
      ⟨GateOp.or, [16, 4]⟩,
      ⟨GateOp.or, [17, 5]⟩,
      ⟨GateOp.or, [18, 6]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1965047 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53663

theorem PEqualNP.Outside.L_meta_53663 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965047 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_53663.ckt, PEqualNP.Outside.L_meta_53663.mono, by decide, PEqualNP.Outside.L_meta_53663.rep⟩
