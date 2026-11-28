import PEqualNP.Defs

-- The finite witness check follows the proof at d667e87931366d16a0380297f19024953d7b1db3,
-- lean/PEqualNP/Outside/L_meta_23684.lean, with the synthesized gate list below.
namespace PEqualNP.Outside.L_meta_54292
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def witness : Circuit := ⟨[
  ⟨.or, [4, 0]⟩,
  ⟨.or, [9, 2]⟩,
  ⟨.or, [6, 10]⟩,
  ⟨.and, [11, 12]⟩,
  ⟨.or, [8, 7]⟩,
  ⟨.or, [14, 3]⟩,
  ⟨.or, [5, 1]⟩,
  ⟨.or, [16, 10]⟩,
  ⟨.and, [15, 17]⟩,
  ⟨.or, [13, 18]⟩], 19⟩

private lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54292

open PEqualNP.Outside.L_meta_54292 in
theorem PEqualNP.Outside.L_meta_54292 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808504 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
