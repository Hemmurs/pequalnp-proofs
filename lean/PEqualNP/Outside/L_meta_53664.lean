import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53664

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 6]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [2, 11]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [11, 15]⟩,
      ⟨GateOp.and, [12, 15]⟩,
      ⟨GateOp.and, [10, 16]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.or, [19, 4]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (2072317 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53664

theorem PEqualNP.Outside.L_meta_53664 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072317 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53664.ckt, PEqualNP.Outside.L_meta_53664.mono, by decide, PEqualNP.Outside.L_meta_53664.rep⟩
