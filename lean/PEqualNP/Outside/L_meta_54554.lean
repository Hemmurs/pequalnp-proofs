import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54554_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [1, 5] }
      , { op := GateOp.or, inputs := [2, 6] }
      , { op := GateOp.or, inputs := [3, 7] }
      , { op := GateOp.or, inputs := [10, 11] }
      , { op := GateOp.or, inputs := [11, 8] }
      , { op := GateOp.and, inputs := [10, 14] }
      , { op := GateOp.and, inputs := [12, 13] }
      , { op := GateOp.or, inputs := [8, 9] }
      , { op := GateOp.and, inputs := [0, 17] }
      , { op := GateOp.or, inputs := [15, 16] }
      , { op := GateOp.or, inputs := [18, 19] }
      , { op := GateOp.or, inputs := [4, 20] }
      ]
    output := 21 }

lemma wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

lemma wit_size : wit.size ≤ 12 := by
  decide

lemma wit_eval_eq (x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 : Bool) :
    wit.eval [x0, x1, x2, x3, y0, y1, y2, y3, y4, y5] =
      (y0 || ((x0 && (y4 || y5)) ||
        (((x1 || y1) && ((x2 || y2) || y4)) || ((x3 || y3) && ((x1 || y1) || (x2 || y2)))))) := by
  simp [Circuit.eval, Circuit.wires, wit, GateOp.eval]

lemma wit_rep :
    Represents (fun (u : Fin 4) (v : Fin 6) => (1881969 : ℕ).testBit (6 * u.val + v.val)) wit := by
  intro u v
  simp only [oneEach, List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
    wit_eval_eq]
  fin_cases u <;> fin_cases v <;> rfl

end PEqualNP.Outside.L_meta_54554_aux

theorem PEqualNP.Outside.L_meta_54554 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881969 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54554_aux.wit,
    PEqualNP.Outside.L_meta_54554_aux.wit_mono,
    PEqualNP.Outside.L_meta_54554_aux.wit_size,
    PEqualNP.Outside.L_meta_54554_aux.wit_rep⟩
