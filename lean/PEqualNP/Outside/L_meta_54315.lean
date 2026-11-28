import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_54315
open PEqualNP.CircuitLowerBounds
def c1 : Circuit := { gates := [
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [6, 10]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.or, [13, 9]⟩,
    ⟨GateOp.or, [4, 7]⟩,
    ⟨GateOp.or, [15, 10]⟩,
    ⟨GateOp.or, [3, 12]⟩,
    ⟨GateOp.and, [17, 11]⟩,
    ⟨GateOp.and, [16, 14]⟩,
    ⟨GateOp.or, [18, 19]⟩], output := 20 }
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
theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287473 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩
end PEqualNP.Outside.L_meta_54315
theorem PEqualNP.Outside.L_meta_54315 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287473 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_54315.main
