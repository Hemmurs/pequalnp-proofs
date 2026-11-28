import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54505

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.or, [2, 9]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [8, 12]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [5, 14]⟩,
    ⟨GateOp.and, [13, 15]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.and, [17, 18]⟩,
    ⟨GateOp.or, [4, 19]⟩,
    ⟨GateOp.or, [16, 20]⟩], output := 21 }

def monoOk : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem mono_of (C : Circuit)
    (h : (C.gates.all fun g => monoOk g.op && decide (g.inputs.length ≤ 2)) = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> simp_all [monoOk]

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851321 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54505

theorem PEqualNP.Outside.L_meta_54505 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851321 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_54505.main
