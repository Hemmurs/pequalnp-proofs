import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53570

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.and, [3, 5]⟩,
      ⟨GateOp.and, [10, 12]⟩,
      ⟨GateOp.and, [0, 14]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [18, 17]⟩,
      ⟨GateOp.or, [19, 4]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (848893 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53570

theorem PEqualNP.Outside.L_meta_53570 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (848893 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53570.ckt, PEqualNP.Outside.L_meta_53570.mono, by decide, PEqualNP.Outside.L_meta_53570.rep⟩
