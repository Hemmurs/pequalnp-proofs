import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57517

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.and, [11, 15]⟩, ⟨GateOp.or, [14, 16]⟩], 17⟩

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

theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6377277 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨wit, fanInTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_57517

theorem PEqualNP.Outside.L_meta_57517 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6377277 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_57517.main_aux
