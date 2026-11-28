import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54578

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 9]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [15, 12]⟩, ⟨GateOp.or, [17, 4]⟩, ⟨GateOp.or, [16, 3]⟩, ⟨GateOp.and, [14, 19]⟩, ⟨GateOp.or, [18, 20]⟩], 21⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898489 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨wit, wit_mono, by decide, by decide⟩

end PEqualNP.Outside.L_meta_54578

theorem PEqualNP.Outside.L_meta_54578 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898489 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_54578.main_aux
