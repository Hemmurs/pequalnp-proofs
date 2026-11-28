import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54442

open PEqualNP.CircuitLowerBounds

private def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [4, 12]⟩,
    ⟨.or, [2, 10]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [1, 7]⟩,
    ⟨.and, [12, 14]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [15, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_54442

theorem PEqualNP.Outside.L_meta_54442 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (322812 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_54442.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_54442.witness]
