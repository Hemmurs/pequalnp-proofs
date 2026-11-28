import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54644

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [13, 9]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [14, 0]⟩, ⟨GateOp.or, [1, 16]⟩, ⟨GateOp.or, [4, 19]⟩, ⟨GateOp.and, [17, 20]⟩, ⟨GateOp.or, [18, 21]⟩], 22⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54644

theorem PEqualNP.Outside.L_meta_54644 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292783 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54644.C0, PEqualNP.Outside.L_meta_54644.ok0, by decide, by decide +kernel⟩
