import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54586

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [5, 2]⟩, ⟨GateOp.or, [8, 7]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [1, 17]⟩, ⟨GateOp.or, [19, 0]⟩, ⟨GateOp.and, [20, 18]⟩], 21⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54586

theorem PEqualNP.Outside.L_meta_54586 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1941438 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54586.C0, PEqualNP.Outside.L_meta_54586.ok0, by decide, by decide +kernel⟩
