import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57571
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.and, [1, 0]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [8, 2]⟩,
        ⟨GateOp.and, [3, 9]⟩,
        ⟨GateOp.or, [10, 1]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [6, 14]⟩,
        ⟨GateOp.and, [13, 15]⟩,
        ⟨GateOp.or, [12, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57571

theorem PEqualNP.Outside.L_meta_57571 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6524601 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57571.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57571.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
