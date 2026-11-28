import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57572
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 2]⟩,
        ⟨GateOp.or, [6, 5]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [9, 1]⟩,
        ⟨GateOp.or, [4, 7]⟩,
        ⟨GateOp.and, [8, 3]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.and, [11, 15]⟩,
        ⟨GateOp.or, [16, 13]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57572

theorem PEqualNP.Outside.L_meta_57572 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6524604 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57572.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57572.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
