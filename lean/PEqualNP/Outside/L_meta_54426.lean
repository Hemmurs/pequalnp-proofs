import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54426

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [2, 12]⟩,
    ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [13, 15]⟩,
    ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.and, [16, 18]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [19, 20]⟩], 21⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294589 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54426

theorem PEqualNP.Outside.L_meta_54426 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294589 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_54426.main_aux
