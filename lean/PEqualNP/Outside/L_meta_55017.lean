import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55017 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147625 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.not, [0]⟩,
      ⟨.or, [2, 4]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.or, [4, 6]⟩,
      ⟨.and, [0, 7]⟩,
      ⟨.and, [1, 7]⟩,
      ⟨.and, [8, 9]⟩,
      ⟨.or, [1, 10]⟩,
      ⟨.or, [12, 13]⟩,
      ⟨.not, [14]⟩,
      ⟨.or, [11, 15]⟩], 16⟩
  exact ⟨C, by simp [C, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide⟩
