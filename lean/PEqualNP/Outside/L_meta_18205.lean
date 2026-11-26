import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18205

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.TopForm PEqualNP.ReadTwo

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ hi]

theorem fold_beyond (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply List.getD_eq_default
  rw [fold_len]; exact hi

def dflt : Gate := ⟨GateOp.or, []⟩

theorem fold_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dflt).inputs, i < w.length + k) :
    (gs.foldl step w).getD (w.length + k) false =
      (gs.getD k dflt).op.eval
        ((gs.getD k dflt).inputs.map fun i => (gs.foldl step w).getD i false) := by
  have hg' : gs.getD k dflt = gs[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  rw [hg'] at hr ⊢
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k+1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  generalize gs[k] = g at hr hsplit ⊢
  rw [hsplit, List.foldl_append, List.foldl_cons]
  have hl1 : ((gs.take k).foldl step w).length = w.length + k := by
    rw [fold_len, List.length_take]; omega
  generalize (gs.take k).foldl step w = w1 at hl1 ⊢
  rw [fold_pre _ _ _ (by simp [step, hl1])]
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  rw [show w.length + k - w1.length = 0 by omega]
  simp only [List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [fold_pre _ _ _ (by simp; have := hr i hi; omega),
    List.getD_append _ _ _ _ (by have := hr i hi; omega)]

theorem gateAt_eq (C : Circuit) (j : ℕ) : gateAt C j = C.gates.getD j dflt := rfl

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

theorem wv_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  unfold wval
  rw [wires_eq, gateAt_eq]
  have := fold_gate C.gates (List.ofFn x) j hj
    (by rw [List.length_ofFn]; exact hRB j hj)
  rw [List.length_ofFn] at this
  exact this

theorem wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval
  rw [wires_eq, fold_pre _ _ _ (by simp [hi]), ofFn_getD _ _ hi]

theorem wv_beyond (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : wval C x i = false := by
  unfold wval
  rw [wires_eq, fold_beyond _ _ _ (by simp [hi])]

theorem reach (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (a b : Fin n) : ∀ w : ℕ,
    wval C (indW n {a.val}) w = true → wval C (indW n {b.val}) w = false →
    Relation.ReflTransGen (fun u v : ℕ => n ≤ v ∧ u ∈ (gateAt C (v - n)).inputs ∧
      (wval C (indW n {a.val}) u = true ∧ wval C (indW n {b.val}) u = false) ∧
      (wval C (indW n {a.val}) v = true ∧ wval C (indW n {b.val}) v = false)) a.val w := by
  obtain ⟨hAO, hRB, _⟩ := hC
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro ht hf
  by_cases hw : w < n
  · rw [wv_input _ _ _ _ hw] at ht
    simp [indW] at ht
    subst ht
    exact Relation.ReflTransGen.refl
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    by_cases hj : j < C.gates.length
    · have ht0 := ht
      have hf0 := hf
      rw [wv_gate n C hRB _ j hj] at ht hf
      have hop := hAO _ (gateAt_mem C j hj)
      have key : ∃ u ∈ (gateAt C j).inputs,
          wval C (indW n {a.val}) u = true ∧ wval C (indW n {b.val}) u = false := by
        rcases hop with hop | hop <;> rw [hop] at ht hf <;> simp [GateOp.eval] at ht hf
        · obtain ⟨u, hu, hu'⟩ := hf
          exact ⟨u, hu, ht u hu, hu'⟩
        · obtain ⟨u, hu, hu'⟩ := ht
          exact ⟨u, hu, hu', hf u hu⟩
      obtain ⟨u, hu, hut, huf⟩ := key
      have hlt : u < n + j := hRB j hj u hu
      refine Relation.ReflTransGen.tail (ih u hlt hut huf) ?_
      refine ⟨by omega, ?_, ⟨hut, huf⟩, ⟨ht0, hf0⟩⟩
      rw [Nat.add_sub_cancel_left]
      exact hu
    · rw [wv_beyond _ _ _ _ (by omega)] at ht
      exact absurd ht (by simp)

end PEqualNP.Outside.L_meta_18205

open PEqualNP.Outside.L_meta_18205 in
theorem PEqualNP.Outside.L_meta_18205 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1) (x6 : ℕ),       PEqualNP.ReadTwo.isAnd x2 x6 →         have x8 : Fin x1 → ℕ → Bool := fun (x8 : Fin x1) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW x1 {↑x8});         have x9 : ℕ → Prop := fun (x9 : ℕ) => x8 x4 x9 = Bool.true ∧ x8 x5 x9 = Bool.false;         have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => x1 ≤ x11 ∧ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x11 - x1)).inputs ∧ x9 x10 ∧ x9 x11;         x8 x4 (x1 + x6) = Bool.true → (∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x8 x5 x12 = Bool.false) → ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x9 x13 ∧ Relation.ReflTransGen x10 (↑x4) x13 := by
  intro x1 x2 hC x4 x5 x6 hA
  dsimp only
  intro h1 h2 x13 hx13
  obtain ⟨hlen, hop⟩ := hA
  have hRB := hC.2.1
  rw [wv_gate x1 x2 hRB _ x6 hlen, hop] at h1
  simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at h1
  have ht : PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW x1 {x4.val}) x13 = true :=
    h1 x13 hx13
  have hf := h2 x13 hx13
  exact ⟨⟨ht, hf⟩, reach x1 x2 hC x4 x5 x13 ht hf⟩
