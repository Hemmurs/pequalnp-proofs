import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53654 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948403 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 7]⟩,
      ⟨.or, [1, 8]⟩,
      ⟨.or, [2, 9]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.and, [6, 3]⟩,
      ⟨.or, [13, 14]⟩,
      ⟨.and, [10, 11]⟩,
      ⟨.or, [16, 15]⟩,
      ⟨.or, [10, 11]⟩,
      ⟨.and, [18, 12]⟩,
      ⟨.or, [19, 17]⟩], 20⟩
  exact ⟨C, by simp [C, PEqualNP.MetaComplexity.Monotone2], by decide, by decide⟩
