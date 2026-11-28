import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56927

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.or, [14, 16]⟩], 17⟩

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

theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165561 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨wit, fanInTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_56927

theorem PEqualNP.Outside.L_meta_56927 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165561 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_56927.main_aux
