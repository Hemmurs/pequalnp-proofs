import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53590

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [6, 12]⟩,
      ⟨GateOp.or, [0, 13]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [5, 16]⟩,
      ⟨GateOp.and, [17, 15]⟩,
      ⟨GateOp.and, [10, 14]⟩,
      ⟨GateOp.or, [18, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (905021 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53590

theorem PEqualNP.Outside.L_meta_53590 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (905021 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53590.ckt, PEqualNP.Outside.L_meta_53590.mono, by decide, PEqualNP.Outside.L_meta_53590.rep⟩
