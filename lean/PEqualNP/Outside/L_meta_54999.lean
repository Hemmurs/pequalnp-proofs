import PEqualNP.Defs

-- Explicit circuit checked by the kernel on all promise inputs. Template: the merged two-lit files on
-- upstream main (L_meta_21449 by Leg0shii, L_meta_21605 by odinfree), Apache-2.0. Circuit found by SAT.

namespace PEqualNP.Outside.L_meta_54999_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit := ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [9, 15]⟩], 16⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) && Nat.ble g.inputs.length 2

theorem okB_sound (C : Circuit) (h : okB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_54999_aux

theorem PEqualNP.Outside.L_meta_54999 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2115005 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54999_aux.ckt, PEqualNP.Outside.L_meta_54999_aux.okB_sound _ (by decide +kernel), by decide +kernel, by decide +kernel⟩
