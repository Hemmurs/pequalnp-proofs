import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54585

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 8]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [2, 11]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.and, [15, 13]⟩,
      ⟨GateOp.and, [10, 12]⟩,
      ⟨GateOp.and, [3, 11]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [19, 18]⟩,
      ⟨GateOp.or, [20, 4]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1940471 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54585

theorem PEqualNP.Outside.L_meta_54585 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940471 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54585.ckt, PEqualNP.Outside.L_meta_54585.mono, by decide, PEqualNP.Outside.L_meta_54585.rep⟩
