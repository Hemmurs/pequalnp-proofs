import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54857

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.not, [14]⟩], 15⟩

def fanInTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem fanInTwoB_sound (C : Circuit) (h : fanInTwoB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16536 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨wit, fanInTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54857

theorem PEqualNP.Outside.L_meta_54857 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16536 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_54857.main_aux
