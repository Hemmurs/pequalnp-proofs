import PEqualNP.MetaComplexity.Helpers.Support

/-! Size and evaluation bounds for the reachable input set of a circuit wire. -/

namespace PEqualNP.SyntacticMultilinear

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Helpers

private theorem supportStep_eq {n : Nat} (L : List (Finset (Fin n))) (g : Gate) :
    supportStep L g = L ++ [gateSupp L g] := by
  have fold_eq (inputs : List Nat) :
      inputs.foldr (fun w acc => L.getD w ∅ ∪ acc) ∅ =
        (inputs.map (fun w => L.getD w ∅)).foldr (· ∪ ·) ∅ := by
    induction inputs with
    | nil => rfl
    | cons w rest ih => simp only [List.foldr_cons, List.map_cons, ih]
  exact congrArg (fun S => L ++ [S]) (fold_eq g.inputs)

private theorem supports_eq (n : Nat) (C : Circuit) :
    supports n C = suppsFrom C.gates (inputSupps n) := by
  have fold_eq (gs : List Gate) (L : List (Finset (Fin n))) :
      gs.foldl supportStep L = suppsFrom gs L := by
    induction gs generalizing L with
    | nil => rfl
    | cons g gs ih =>
      change gs.foldl supportStep (supportStep L g) = suppsFrom gs (L ++ [gateSupp L g])
      rw [supportStep_eq, ih]
  exact fold_eq _ _

/-- A wire can reach at most one more distinct input than the total number of gates. -/
theorem card_support_le_size_succ (n : Nat) (C : Circuit) (w : Nat)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (support n C w).card ≤ C.size + 1 := by
  have advance (gs : List Gate) (t : Nat) (L : List (Finset (Fin n)))
      (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) (hc : Cnt t L) :
      Cnt (t + gs.length) (suppsFrom gs L) := by
    induction gs generalizing t L with
    | nil => simpa [suppsFrom] using hc
    | cons g gs ih =>
      have tail := ih (t+1) (L ++ [gateSupp L g]) (fun a ha => hf a (List.mem_cons_of_mem _ ha))
        (cnt_step t L g (hf g List.mem_cons_self) hc)
      rw [List.length_cons, show t + (gs.length + 1) = (t + 1) + gs.length by omega]
      exact tail
  have bound := advance C.gates 0 (inputSupps n) fan cnt_inputs {w}
  simpa only [support, supports_eq, Finset.singleton_biUnion, Finset.card_singleton,
    Nat.zero_add, Circuit.size] using bound

/-- Two assignments agreeing on the reachable inputs give the same value at this wire. -/
theorem wire_eq_of_agree_on_support (n : Nat) (C : Circuit) (w : Nat) (x y : Fin n → Bool)
    (agree : ∀ i ∈ support n C w, x i = y i) :
    (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  apply (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 w
  simpa only [support, supports_eq] using agree

end PEqualNP.SyntacticMultilinear
