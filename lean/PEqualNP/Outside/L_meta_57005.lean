import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57005 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180910 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
