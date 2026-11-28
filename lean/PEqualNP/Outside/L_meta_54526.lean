import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54526

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [4, 12]⟩,
      ⟨GateOp.or, [5, 9]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.and, [3, 10]⟩,
      ⟨GateOp.and, [2, 13]⟩,
      ⟨GateOp.and, [1, 15]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [19, 18]⟩,
      ⟨GateOp.or, [20, 0]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (909247 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54526

theorem PEqualNP.Outside.L_meta_54526 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (909247 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54526.ckt, PEqualNP.Outside.L_meta_54526.mono, by decide, PEqualNP.Outside.L_meta_54526.rep⟩
