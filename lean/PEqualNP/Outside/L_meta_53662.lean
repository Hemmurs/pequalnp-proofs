import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53662

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [7, 8]⟩,
      ⟨GateOp.or, [6, 11]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.and, [3, 6]⟩,
      ⟨GateOp.and, [10, 12]⟩,
      ⟨GateOp.and, [0, 13]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [17, 16]⟩,
      ⟨GateOp.or, [18, 4]⟩,
      ⟨GateOp.or, [19, 5]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1964027 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53662

theorem PEqualNP.Outside.L_meta_53662 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1964027 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53662.ckt, PEqualNP.Outside.L_meta_53662.mono, by decide, PEqualNP.Outside.L_meta_53662.rep⟩
