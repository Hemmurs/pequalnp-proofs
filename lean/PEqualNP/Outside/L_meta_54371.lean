import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54371

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witGates : List Gate :=
  [ ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [10, 9]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [1, 12]⟩,
    ⟨GateOp.or, [2, 12]⟩,
    ⟨GateOp.or, [2, 11]⟩,
    ⟨GateOp.or, [13, 6]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.and, [14, 17]⟩,
    ⟨GateOp.and, [16, 15]⟩,
    ⟨GateOp.or, [19, 18]⟩ ]

def wit : Circuit := ⟨witGates, 20⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 11 := by
  decide

theorem wit_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (294458 : ℕ).testBit (6 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_54371

theorem PEqualNP.Outside.L_meta_54371 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294458 : ℕ).testBit (6 * u.val + v.val)) 11) :=
  ⟨PEqualNP.Outside.L_meta_54371.wit,
   PEqualNP.Outside.L_meta_54371.wit_mono,
   PEqualNP.Outside.L_meta_54371.wit_size,
   PEqualNP.Outside.L_meta_54371.wit_rep⟩
