import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54304

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [9, 12]⟩,
    ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.or, [10, 14]⟩,
    ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [4, 18]⟩], 19⟩

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

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276335 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54304

theorem PEqualNP.Outside.L_meta_54304 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276335 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_54304.main_aux
