import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57422_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [2, 4]⟩,
     ⟨.and, [2, 4]⟩,
     ⟨.or, [1, 6]⟩,
     ⟨.or, [1, 7]⟩,
     ⟨.or, [3, 8]⟩,
     ⟨.not, [10]⟩,
     ⟨.or, [9, 11]⟩,
     ⟨.and, [0, 11]⟩,
     ⟨.and, [6, 12]⟩,
     ⟨.or, [3, 14]⟩,
     ⟨.and, [8, 15]⟩,
     ⟨.or, [13, 16]⟩], 17⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_57422_aux

open PEqualNP.Outside.L_meta_57422_aux in
theorem PEqualNP.Outside.L_meta_57422 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294433 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
