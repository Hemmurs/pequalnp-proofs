import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57095
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W : List Gate := [⟨.or, [1, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [3, 10]⟩, ⟨.not, [10]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.not, [16]⟩]

theorem c1 : FanInTwo ⟨W, 17⟩ := by simp [FanInTwo, W]
theorem c2 : (⟨W, 17⟩ : Circuit).size ≤ 12 := by decide
theorem c3 : ∀ i j : Fin 6, (⟨W, 17⟩ : Circuit).eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181303 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_57095

open PEqualNP.Outside.L_meta_57095 in
theorem PEqualNP.Outside.L_meta_57095 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181303 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨⟨W, 17⟩, c1, c2, c3⟩
