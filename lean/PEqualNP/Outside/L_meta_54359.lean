import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54359

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [1, 10]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [12, 16]⟩,
      ⟨GateOp.and, [11, 17]⟩,
      ⟨GateOp.and, [15, 13]⟩,
      ⟨GateOp.or, [18, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (291774 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54359

theorem PEqualNP.Outside.L_meta_54359 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291774 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54359.ckt, PEqualNP.Outside.L_meta_54359.mono, by decide, PEqualNP.Outside.L_meta_54359.rep⟩
