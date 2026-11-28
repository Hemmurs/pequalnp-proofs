import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54523.Aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 through 3 select a row, and wires 4 through 9 select a column.
    Each subsequent wire is the output of the next gate in this list. -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
     ⟨.or, [0, 2]⟩,
     ⟨.or, [4, 5]⟩,
     ⟨.or, [6, 7]⟩,
     ⟨.or, [13, 8]⟩,
     ⟨.or, [14, 9]⟩,
     ⟨.or, [14, 4]⟩,
     ⟨.and, [10, 15]⟩,
     ⟨.and, [11, 16]⟩,
     ⟨.and, [3, 12]⟩,
     ⟨.or, [17, 18]⟩,
     ⟨.or, [20, 19]⟩], 21⟩

end PEqualNP.Outside.L_meta_54523.Aux

theorem PEqualNP.Outside.L_meta_54523 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (909117 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_54523.Aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_54523.Aux.witness, PEqualNP.MetaComplexity.Monotone2]
