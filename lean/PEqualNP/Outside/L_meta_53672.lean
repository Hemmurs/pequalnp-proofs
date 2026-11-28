import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53672

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [6, 11]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.and, [12, 15]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [18, 0]⟩,
      ⟨GateOp.or, [19, 4]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (4030079 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53672

theorem PEqualNP.Outside.L_meta_53672 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4030079 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53672.ckt, PEqualNP.Outside.L_meta_53672.mono, by decide, PEqualNP.Outside.L_meta_53672.rep⟩
