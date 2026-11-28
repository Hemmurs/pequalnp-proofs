import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54499.Aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 through 3 select a row, and wires 4 through 9 select a column.
    Each subsequent wire is the output of the next gate in this list. -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩,
     ⟨.or, [0, 1]⟩,
     ⟨.or, [4, 5]⟩,
     ⟨.or, [4, 6]⟩,
     ⟨.or, [5, 7]⟩,
     ⟨.or, [14, 8]⟩,
     ⟨.or, [15, 9]⟩,
     ⟨.and, [11, 16]⟩,
     ⟨.and, [2, 13]⟩,
     ⟨.and, [10, 12]⟩,
     ⟨.or, [17, 18]⟩,
     ⟨.or, [20, 19]⟩], 21⟩

end PEqualNP.Outside.L_meta_54499.Aux

theorem PEqualNP.Outside.L_meta_54499 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (810683 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_54499.Aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_54499.Aux.witness, PEqualNP.MetaComplexity.Monotone2]
