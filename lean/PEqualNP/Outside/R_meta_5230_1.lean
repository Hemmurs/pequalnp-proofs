import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5230_1
    (h1 : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), G = PEqualNP.EdgeOwnership.edgeGraph 11 (List.map (fun e : ℕ => (e / 11, e % 11)) [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]) → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → PEqualNP.TopForm.junk G C = {i, j} → PEqualNP.EdgeOwnership.InCone 11 C i j → PEqualNP.TopForm.centreless G C = ∅ → have U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G C; have R : Finset ℕ := PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C; have T : Finset ℕ := PEqualNP.TopForm.tops G C; (∀ a ∈ T, have S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side C a; (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) → (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, ∃ m ∈ R, PEqualNP.EdgeOwnership.gateVal 11 C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C a b) m ∧ 11 + h ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs ∧ PEqualNP.EdgeOwnership.gateVal 11 C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → C.size ≤ 21 → 4 ≤ U.card → ∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ T.card → T.card + R.card ≤ C.size + U.card - 17 → False)
    (h2 : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), G = PEqualNP.EdgeOwnership.edgeGraph 11 (List.map (fun e : ℕ => (e / 11, e % 11)) [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]) → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → PEqualNP.TopForm.junk G C = {i, j} → PEqualNP.EdgeOwnership.InCone 11 C i j → have V : Finset ℕ := PEqualNP.TopForm.centreless G C; V.Nonempty → have U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G C; have R : Finset ℕ := PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C; have T : Finset ℕ := PEqualNP.TopForm.tops G C; have S : ℕ → Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side C; (∀ a ∈ T, ∃ b : Fin 2, (S a b).card ≤ 1) → (∀ a ∈ V, ∃ b : Fin 2, ∃ k ∈ PEqualNP.TopForm.junk G C ∪ R, PEqualNP.TopForm.opnd C a b = 11 + k) → (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal 11 C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → C.size ≤ 21 → 4 ≤ U.card → ∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ V).card → (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card - 17 → False) : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;             have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             (∀ x15 ∈ x14,                 have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;                 (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →               (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) → x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 → (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card → (0 : ℕ) < (2 : ℕ) * x12.card + x13.card → (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False := by open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover in (
  intro G inst C i j hG hLeast hTop hJunk hCone
  dsimp only
  intro hStars hTrace hSize hU4 K hKMin hKU hKT hOff hBudget
  classical
  let U := Ustar G C
  let T := tops G C
  let V := centreless G C
  let R := orN G C \ lam G C
  let J := junk G C
  have hRoutes : (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true) := hTrace
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp -congrConsts only [id (@List.foldl_cons)]
      have hlt : i < (stepWire w g).length := by simp -congrConsts [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp -congrConsts [stepWire, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp -congrConsts [List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp -congrConsts at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp -congrConsts [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp -congrConsts only [id (@List.getElem_cons_zero)]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp -congrConsts [stepWire]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp -congrConsts [stepWire]; omega)]
          simp -congrConsts [stepWire, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa -congrConsts using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp -congrConsts [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp -congrConsts only [id (@List.getElem_cons_succ)]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    delta gateAt
    simp -congrConsts [hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    delta GateOp.eval
    simp -congrConsts only [id (@List.any_map), id (@List.any_eq_true), id (@Function.comp_apply), id (@id_eq)]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  let OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
    ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < n + k

  have coneStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl

  have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [coneStep_eq]
      omega

  have cones_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
        rw [cones_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp -congrConsts; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp -congrConsts
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_right (by omega)]
          simp -congrConsts [hlen]
        rw [e2, e1]
        simp -congrConsts only [id (@List.mem_flatMap), id (@List.mem_filter), id (@List.mem_cons), id (@decide_eq_true_eq)]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp -congrConsts, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - n) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · rintro ⟨h0, _⟩
          simp -congrConsts at h0
          omega

  have inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
      InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone n C i k) := by
    have h := cones_char n C.gates i j
    unfold InCone cones gateAt
    rw [h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - n, by omega, ?_, h3⟩
      have : n + (w - n) = w := by omega
      rw [this]
      exact hw
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
      have : n + k - n = k := by omega
      rw [this]
      exact h3

  letI : DecidableEq GateOp := gateOpDecEq
  have orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      orStep n cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else [])] := rfl

  have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [orStep_eq]
      omega

  have orSets_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by
        rw [orSets_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp -congrConsts; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp -congrConsts
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [id (@List.mem_cons), id (@List.mem_flatMap), id (@List.mem_filter), id (@decide_eq_true_eq)]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp -congrConsts, Or.inl h3⟩
            · refine ⟨by simp -congrConsts, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [id (@List.mem_singleton)]
          constructor
          · intro h3
            exact ⟨by simp -congrConsts, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · rintro ⟨h0, _⟩
          simp -congrConsts at h0
          omega

  have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    have h := orSets_char n C.gates g k
    unfold OrReaches orSets gateAt
    have e : n + k - n = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

  have reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) w w2) :
      ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg
      subst h1
      exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

  have orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
      ∀ w, OrReaches n C w g →
        Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      have hnw : n ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

  have mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
      Relation.ReflTransGen (OrStep n C) p u.val := by
    delta orIn at hu
    simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

  have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
      u ∈ PEqualNP.TopForm.orIn n C p := by
    delta orIn
    simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)]
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

  have two_inputs {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
      ∃ p q, (gateAt C k).inputs = [p, q] ∧ p < n + k ∧ q < n + k ∧ opnd C k 0 = p ∧
        opnd C k 1 = q := by
    obtain ⟨_, hRB, h2⟩ := hA
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
    exact ⟨p, q, hin, hRB k hk p (by rw [hin]; simp -congrConsts), hRB k hk q (by rw [hin]; simp -congrConsts),
      by delta opnd; simp -congrConsts [hin], by delta opnd; simp -congrConsts [hin]⟩

  have reach_gate {n : ℕ} {C : Circuit} {k w' : ℕ}
      (h : Relation.ReflTransGen (OrStep n C) (n + k) w') :
      w' = n + k ∨ (k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ Relation.ReflTransGen (OrStep n C) c w') := by
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, hr⟩
    · exact Or.inl h.symm
    · obtain ⟨k', hk', e, hop, hin, hlt⟩ := hstep
      have hkk : k' = k := by omega
      subst hkk
      exact Or.inr ⟨hk', hop, c, hin, hlt, hr⟩

  have orIn_gate {n : ℕ} {C : Circuit} {k : ℕ} (u : Fin n) (hu : u ∈ orIn n C (n + k)) :
      k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ u ∈ orIn n C c := by
    rcases reach_gate (mem_orIn_reach u hu) with h | ⟨hk, hop, c, hc, hlt, hr⟩
    · have := u.isLt
      omega
    · exact ⟨hk, hop, c, hc, hlt, reach_mem_orIn u hr⟩

  have coneStrict : ∀ k h, InCone 11 C h k → h < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro h hh
      obtain ⟨_, p, hp, _, hpath⟩ := (inCone_iff 11 C h k).mp hh
      rcases hpath with rfl | hpath
      · exact hp
      · exact (ih p hp h hpath).trans hp
  have hOrder : i < j := coneStrict j i hCone
  let path := Relation.ReflTransGen (OrStep 11 C)
  have andEmpty (k : ℕ) (hk : (gateAt C k).op = GateOp.and) :
      orIn 11 C (11 + k) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    have hor := (orIn_gate u hu).2.1
    rw [hk] at hor
    cases hor
  have charge (k w : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.or) (hw : w ∈ (gateAt C k).inputs)
      (he : orIn 11 C w = ∅) (x : Fin 11 → Bool)
      (hd : val C (List.ofFn x) (11 + k) = true) (hx : graphFun G ∅ x = false) :
      k ∈ R := by
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · delta orN gatesWhere
      simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_range)]
      exact ⟨hk, hop, fun hbelow => Bool.false_ne_true (hx ▸ hbelow x hd)⟩
    · intro hlam
      have hnon := (Finset.mem_filter.mp hlam).2
      obtain ⟨p, q, hpq, _, _, hp, hq⟩ := two_inputs hLeast.1 hk
      rw [hpq] at hw
      simp -congrConsts only [id (@List.mem_cons), id (@List.not_mem_nil), id (@or_false)] at hw
      rcases hw with rfl | rfl
      · exact (Finset.not_nonempty_iff_eq_empty.mpr (hp.symm ▸ he)) hnon.1
      · exact (Finset.not_nonempty_iff_eq_empty.mpr (hq.symm ▸ he)) hnon.2.1
  have nonemptySide (a : ℕ) (ha : a ∈ T) (b : Fin 2) (hn : a ∉ V) :
      (orIn 11 C (opnd C a b)).Nonempty := by
    have hside : side (n := 11) C a b ≠ ∅ := by
      intro he
      apply hn
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    exact Finset.nonempty_iff_ne_empty.mpr hside
  have findCharge (w h : ℕ) (hn : (orIn 11 C w).Nonempty) (hh : h ∈ J)
      (hr : OrReaches 11 C w h) :
      ∃ m ∈ R, path w (11 + m) ∧ 11 + h ∈ (gateAt C m).inputs := by
    obtain ⟨hop, _, x, hval, hx⟩ := (Finset.mem_filter.mp hh).2
    rcases Relation.ReflTransGen.cases_tail (orReaches_reach h w hr).1 with he | ⟨r, hp, hs⟩
    · rw [← he, andEmpty h hop] at hn
      exact (Finset.not_nonempty_empty hn).elim
    · obtain ⟨m, hm, rfl, hor, hread, hlt⟩ := hs
      have hd : val C (List.ofFn x) (11 + m) = true := by
        exact (val_or (by simp -congrConsts) hm hor).mpr ⟨11 + h, hread, hlt, hval⟩
      exact ⟨m, charge m _ hm hor hread (andEmpty h hop) x hd hx, hp, hread⟩
  have orInSub (k c : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
      (hc : c ∈ (gateAt C k).inputs) (hlt : c < 11 + k) (he : orIn 11 C (11 + k) = ∅) :
      orIn 11 C c = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    have hp : path (11 + k) u.val :=
      Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hc, hlt⟩ (mem_orIn_reach u hu)
    have hm := reach_mem_orIn u hp
    rw [he] at hm
    exact Finset.notMem_empty u hm
  have inputGate (c : ℕ) (he : orIn 11 C c = ∅) : 11 ≤ c := by
    by_contra hlt
    have hc : c < 11 := by omega
    have hm : (⟨c, hc⟩ : Fin 11) ∈ orIn 11 C c := by
      delta orIn
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have andOf (k : ℕ) (hk : k < C.gates.length) (hop : ¬ (gateAt C k).op = GateOp.or) :
      (gateAt C k).op = GateOp.and := by
    rcases hLeast.1.1 _ (gateAt_mem hk) with h | h
    · exact h
    · exact (hop h).elim
  have dirtyOrTop : ∀ k, k < C.gates.length → orIn 11 C (11 + k) = ∅ →
      (∃ x : Fin 11 → Bool, val C (List.ofFn x) (11 + k) = true ∧ graphFun G ∅ x = false) ∨
      (∃ t ∈ T, t = k ∨ InCone 11 C t k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk he
      by_cases hop : (gateAt C k).op = GateOp.or
      · obtain ⟨p, q, hpq, hp, _, _, _⟩ := two_inputs hLeast.1 hk
        have hpm : p ∈ (gateAt C k).inputs := by rw [hpq]; exact List.mem_cons_self
        have hpe := orInSub k p hk hop hpm hp he
        have hge := inputGate p hpe
        obtain ⟨k', rfl⟩ : ∃ k', p = 11 + k' := ⟨p - 11, by omega⟩
        have hk' : k' < k := by omega
        rcases ih k' hk' (by omega) hpe with ⟨x, hx, hf⟩ | ⟨t, ht, htk⟩
        · exact Or.inl ⟨x, (val_or (by simp -congrConsts) hk hop).mpr ⟨11 + k', hpm, hp, hx⟩, hf⟩
        · exact Or.inr ⟨t, ht, Or.inr ((inCone_iff 11 C t k).mpr ⟨hk, k', hk', hpm, htk⟩)⟩
      · have hand := andOf k hk hop
        by_cases hb : BelowF G C k
        · exact Or.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hand, hb⟩, Or.inl rfl⟩
        · left
          by_contra hne
          apply hb
          intro x hx
          by_contra hf
          exact hne ⟨x, hx, (Bool.not_eq_true _).mp hf⟩
  have centrelessOperand : ∀ a ∈ V, ∃ (b : Fin 2) (k : ℕ), (side C a b : Finset (Fin 11)) = ∅ ∧
      opnd C a b = 11 + k ∧ (k ∈ junk G C ∨ k ∈ R) := by
    intro a haV
    obtain ⟨haT, hside⟩ := Finset.mem_filter.mp haV
    obtain ⟨harange, haand, _⟩ := Finset.mem_filter.mp haT
    have halen := Finset.mem_range.mp harange
    obtain ⟨p, q, hpq, hp, hq, hp0, hq1⟩ := two_inputs hLeast.1 halen
    have key : ∀ (b : Fin 2), (side C a b : Finset (Fin 11)) = ∅ →
        opnd C a b ∈ (gateAt C a).inputs → opnd C a b < 11 + a →
        ∃ k, opnd C a b = 11 + k ∧ (k ∈ junk G C ∨ k ∈ R) := by
      intro b he hmem hlt
      have he' : orIn 11 C (opnd C a b) = ∅ := he
      have hge := inputGate _ he'
      obtain ⟨k, hkeq⟩ : ∃ k, opnd C a b = 11 + k := ⟨opnd C a b - 11, by omega⟩
      rw [hkeq] at he' hmem hlt
      have hk : k < C.gates.length := by omega
      refine ⟨k, hkeq, ?_⟩
      rcases dirtyOrTop k hk he' with ⟨x, hx, hf⟩ | ⟨t, ht, htk⟩
      · by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨p', q', hpq', hp', _, _, _⟩ := two_inputs hLeast.1 hk
          have hpm : p' ∈ (gateAt C k).inputs := by rw [hpq']; exact List.mem_cons_self
          exact Or.inr (charge k p' hk hop hpm (orInSub k p' hk hop hpm hp' he') x hx hf)
        · exact Or.inl (Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hk, andOf k hk hop, hk, x, hx, hf⟩)
      · exfalso
        obtain ⟨htr, htand, htb⟩ := Finset.mem_filter.mp ht
        exact hTop t (Finset.mem_range.mp htr) a halen htand htb haand
          ((inCone_iff 11 C t a).mpr ⟨halen, k, by omega, hmem, htk⟩)
    rcases hside with h0 | h1
    · obtain ⟨k, hk1, hk2⟩ := key 0 h0 (by rw [hp0, hpq]; exact List.mem_cons_self) (by rw [hp0]; exact hp)
      exact ⟨0, k, h0, hk1, hk2⟩
    · obtain ⟨k, hk1, hk2⟩ := key 1 h1 (by rw [hq1, hpq]; exact List.mem_cons_of_mem _ List.mem_cons_self) (by rw [hq1]; exact hq)
      exact ⟨1, k, h1, hk1, hk2⟩
  by_cases hv : V.Nonempty
  · refine h2 G C i j hG hLeast hTop hJunk hCone hv (fun a ha => (hStars a ha).2.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)) ?_ hTrace hSize hU4 K hKMin hKT hBudget
    intro a ha
    obtain ⟨b, k, _, e, hk⟩ := centrelessOperand a ha
    exact ⟨b, k, Finset.mem_union.mpr hk, e⟩
  · have hv0 : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
    have hTV : T \ V = T := by rw [hv0]; exact Finset.sdiff_empty
    have hKT2 : K.card ≤ T.card := by
      have h0 : K.card ≤ (T \ V).card := hKT
      rwa [hTV] at h0
    have hV0 : V.card = 0 := by rw [hv0]; rfl
    have hB2 : T.card + R.card ≤ C.size + U.card - 17 := by
      have h0 : (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card - 17 := hBudget
      rw [hTV] at h0
      omega
    refine h1 G C i j hG hLeast hTop hJunk hCone hv0 hStars ?_ hSize hU4 K hKMin hKT2 hB2
    intro u v he
    obtain ⟨a, ha, b, h, hh, hval, hr, hhval⟩ := hRoutes u v he
    obtain ⟨m, hm, hpath, hread⟩ :=
      findCharge _ h (nonemptySide a ha b (by rw [hv0]; exact Finset.notMem_empty a)) hh hr
    have hlen : m < C.gates.length := by
      have ho := (Finset.mem_sdiff.mp hm).1
      change m ∈ orN G C at ho
      delta orN gatesWhere at ho
      exact Finset.mem_range.mp (Finset.mem_filter.mp ho).1
    exact ⟨a, ha, b, h, hh, m, hm, hval, reach_orReaches hpath m rfl hlen, hread, hhval⟩
  )
