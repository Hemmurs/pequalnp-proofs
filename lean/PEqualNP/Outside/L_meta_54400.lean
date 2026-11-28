import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54400

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [4, 7]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.and, [3, 4]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.and, [1, 14]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [18, 17]⟩,
      ⟨GateOp.or, [19, 0]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (327103 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54400

theorem PEqualNP.Outside.L_meta_54400 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327103 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54400.ckt, PEqualNP.Outside.L_meta_54400.mono, by decide, PEqualNP.Outside.L_meta_54400.rep⟩
