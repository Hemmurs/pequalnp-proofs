import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54485_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 18]⟩], 21⟩

def okOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem okOpSound (g : Gate) (ok : okOp g = true) : g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [okOp, h] at ok ⊢

theorem witnessOk : Monotone2 witness := by
  have legal : witness.gates.all (fun g => okOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using okOpSound g passed.1, passed.2⟩

end PEqualNP.Outside.L_meta_54485_aux

theorem PEqualNP.Outside.L_meta_54485 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808507 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_54485_aux.witness, PEqualNP.Outside.L_meta_54485_aux.witnessOk, by decide, ?_⟩
  unfold PEqualNP.Represents.Represents
  decide +kernel
