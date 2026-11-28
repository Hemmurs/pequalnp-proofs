import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54412

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witGates : List Gate :=
  [ ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [1, 10]⟩,
    ⟨GateOp.or, [2, 11]⟩,
    ⟨GateOp.and, [12, 13]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [3, 9]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [18, 17]⟩,
    ⟨GateOp.or, [14, 19]⟩ ]

def wit : Circuit := ⟨witGates, 20⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 12 := by
  decide

theorem wit_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (292478 : ℕ).testBit (6 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_54412

theorem PEqualNP.Outside.L_meta_54412 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292478 : ℕ).testBit (6 * u.val + v.val)) 12) :=
  ⟨PEqualNP.Outside.L_meta_54412.wit,
   PEqualNP.Outside.L_meta_54412.wit_mono,
   PEqualNP.Outside.L_meta_54412.wit_size,
   PEqualNP.Outside.L_meta_54412.wit_rep⟩
