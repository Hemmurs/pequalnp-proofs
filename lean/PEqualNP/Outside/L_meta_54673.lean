import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54673

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 20]⟩], 22⟩

def okOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.and => true
  | PEqualNP.CircuitLowerBounds.GateOp.or => true
  | _ => false

def shapeB (C : PEqualNP.CircuitLowerBounds.Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : PEqualNP.CircuitLowerBounds.Circuit} (h : shapeB C = true) : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have hp := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨?_, hp.2⟩
  have h1 := hp.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem wit_ok : PEqualNP.MetaComplexity.Monotone2 wit := shapeB_sound (by decide +kernel)

theorem wit_size : wit.size ≤ 13 := by decide +kernel

set_option maxRecDepth 200000 in
theorem wit_rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (392190 : ℕ).testBit (6 * u.val + v.val)) wit := by
  decide +kernel

end PEqualNP.Outside.L_meta_54673

theorem PEqualNP.Outside.L_meta_54673 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (392190 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54673.wit, PEqualNP.Outside.L_meta_54673.wit_ok, PEqualNP.Outside.L_meta_54673.wit_size,
    PEqualNP.Outside.L_meta_54673.wit_rep⟩
