import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54365

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [1, 6]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [12, 8]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.and, [10, 15]⟩,
      ⟨GateOp.and, [11, 13]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [18, 4]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (292589 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54365

theorem PEqualNP.Outside.L_meta_54365 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292589 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_54365.ckt, PEqualNP.Outside.L_meta_54365.mono, by decide, PEqualNP.Outside.L_meta_54365.rep⟩
