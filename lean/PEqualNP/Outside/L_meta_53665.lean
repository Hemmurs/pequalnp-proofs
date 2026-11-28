import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53665

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [6, 10]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [4, 12]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [13, 16]⟩,
      ⟨GateOp.and, [13, 16]⟩,
      ⟨GateOp.and, [11, 17]⟩,
      ⟨GateOp.or, [18, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (2072510 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53665

theorem PEqualNP.Outside.L_meta_53665 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072510 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53665.ckt, PEqualNP.Outside.L_meta_53665.mono, by decide, PEqualNP.Outside.L_meta_53665.rep⟩
