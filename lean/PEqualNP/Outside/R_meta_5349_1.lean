import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5349_1
    (h1 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → PEqualNP.TopForm.IsAO2 x1 x4 → {x7 ∈ x2.edgeFinset | ∃ (x8 : Fin x1) (x9 : Fin x1), x7 = s(x8, x9) ∧ ∃ x10 ∈ PEqualNP.TopForm.tops x2 x4, ∃ (x11 : Fin (2 : ℕ)), ∃ x12 ∈ PEqualNP.TopForm.junk x2 x4, x8 ∈ PEqualNP.TopForm.side x4 x10 x11 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x10 ((1 : Fin (2 : ℕ)) - x11)) x12 ∧ (x8 ∈ PEqualNP.TopForm.side x4 x12 (0 : Fin (2 : ℕ)) ∨ x9 ∈ PEqualNP.TopForm.side x4 x12 (0 : Fin (2 : ℕ))) ∧ (x8 ∈ PEqualNP.TopForm.side x4 x12 (1 : Fin (2 : ℕ)) ∨ x9 ∈ PEqualNP.TopForm.side x4 x12 (1 : Fin (2 : ℕ)))}.card ≤ (27 : ℕ) * x4.size)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → x2.support.ncard ≤ x4.size + (1 : ℕ))
    (h3 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∀ (x9 : Finset (Sym2 (Fin x2))) (x10 x11 : Sym2 (Fin x2) → Fin x2) (x12 x13 : Sym2 (Fin x2) → ℕ) (x14 : Sym2 (Fin x2) → Fin (2 : ℕ)), (∀ x15 ∈ x9, x15 ∈ PEqualNP.TopForm.Ustar x3 x5 ∧ x15 = s(x10 x15, x11 x15) ∧ x12 x15 ∈ PEqualNP.TopForm.tops x3 x5 ∧ x13 x15 ∈ PEqualNP.TopForm.junk x3 x5 ∧ x10 x15 ∈ PEqualNP.TopForm.side x5 (x12 x15) (x14 x15) ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 (x12 x15) ((1 : Fin (2 : ℕ)) - x14 x15)) (x13 x15) ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 (x13 x15) (PEqualNP.EdgeOwnership.pairInput (x10 x15) (x11 x15)) = Bool.true) → (∀ x16 ∈ x9, ∀ x18 ∈ [fun (x19 : Sym2 (Fin x2)) => ↑(x10 x19), fun (x19 : Sym2 (Fin x2)) => ↑(x11 x19), fun (x19 : Sym2 (Fin x2)) => (2 : ℕ) * x12 x19 + ↑(x14 x19), x13], (3 : ℕ) ≤ {x20 ∈ x9 | x18 x20 = x18 x16}.card) → (∀ (x17 : Fin x2), ∀ x18 ∈ x9, ∀ x20 ∈ x9, x11 x18 = x11 x20 → x17 ∈ PEqualNP.TopForm.side x5 (x12 x18) ((1 : Fin (2 : ℕ)) - x14 x18) → x17 ∈ PEqualNP.TopForm.side x5 (x12 x20) ((1 : Fin (2 : ℕ)) - x14 x20) → x18 = x20) → (∀ x21 ∈ x9, ¬∃ (x22 : Fin x2) (x23 : Fin x2), x21 = s(x22, x23) ∧ ∃ x24 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x25 : Fin (2 : ℕ)), ∃ x26 ∈ PEqualNP.TopForm.junk x3 x5, x22 ∈ PEqualNP.TopForm.side x5 x24 x25 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x24 ((1 : Fin (2 : ℕ)) - x25)) x26 ∧ (x22 ∈ PEqualNP.TopForm.side x5 x26 (0 : Fin (2 : ℕ)) ∨ x23 ∈ PEqualNP.TopForm.side x5 x26 (0 : Fin (2 : ℕ))) ∧ (x22 ∈ PEqualNP.TopForm.side x5 x26 (1 : Fin (2 : ℕ)) ∨ x23 ∈ PEqualNP.TopForm.side x5 x26 (1 : Fin (2 : ℕ)))) → x9.card ≤ x1 * (x5.size + (1 : ℕ))) : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∀ (x9 : Finset (Sym2 (Fin x2))) (x10 x11 : Sym2 (Fin x2) → Fin x2) (x12 x13 : Sym2 (Fin x2) → ℕ) (x14 : Sym2 (Fin x2) → Fin (2 : ℕ)), (∀ x15 ∈ x9, x15 ∈ PEqualNP.TopForm.Ustar x3 x5 ∧ x15 = s(x10 x15, x11 x15) ∧ x12 x15 ∈ PEqualNP.TopForm.tops x3 x5 ∧ x13 x15 ∈ PEqualNP.TopForm.junk x3 x5 ∧ x10 x15 ∈ PEqualNP.TopForm.side x5 (x12 x15) (x14 x15) ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 (x12 x15) ((1 : Fin (2 : ℕ)) - x14 x15)) (x13 x15) ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 (x13 x15) (PEqualNP.EdgeOwnership.pairInput (x10 x15) (x11 x15)) = Bool.true) → (∀ x16 ∈ x9, ∀ x18 ∈ [fun (x19 : Sym2 (Fin x2)) => ↑(x10 x19), fun (x19 : Sym2 (Fin x2)) => ↑(x11 x19), fun (x19 : Sym2 (Fin x2)) => (2 : ℕ) * x12 x19 + ↑(x14 x19), x13], (3 : ℕ) ≤ {x20 ∈ x9 | x18 x20 = x18 x16}.card) → (∀ (x17 : Fin x2), ∀ x18 ∈ x9, ∀ x20 ∈ x9, x11 x18 = x11 x20 → x17 ∈ PEqualNP.TopForm.side x5 (x12 x18) ((1 : Fin (2 : ℕ)) - x14 x18) → x17 ∈ PEqualNP.TopForm.side x5 (x12 x20) ((1 : Fin (2 : ℕ)) - x14 x20) → x18 = x20) → x9.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  obtain ⟨k, hk⟩ := h3
  refine ⟨k + 37, ?_⟩
  intro n G inst C hcy hleast htop M u v a g b hw _ hsep
  let ex : Sym2 (Fin n) → Prop := fun e => ∃ (p : Fin n) (q : Fin n), e = s(p, q) ∧
    ∃ t ∈ PEqualNP.TopForm.tops G C, ∃ (c : Fin 2), ∃ j ∈ PEqualNP.TopForm.junk G C,
      p ∈ PEqualNP.TopForm.side C t c ∧
      PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t ((1 : Fin 2) - c)) j ∧
      (p ∈ PEqualNP.TopForm.side C j (0 : Fin 2) ∨ q ∈ PEqualNP.TopForm.side C j (0 : Fin 2)) ∧
      (p ∈ PEqualNP.TopForm.side C j (1 : Fin 2) ∨ q ∈ PEqualNP.TopForm.side C j (1 : Fin 2))
  have hedge : ∀ e ∈ M, e ∈ G.edgeFinset := fun e he => (Finset.mem_sdiff.mp (hw e he).1).1
  have hA : (M.filter ex).card ≤ 27 * C.size := by
    refine (Finset.card_le_card ?_).trans (h1 n G C hcy hleast.1)
    intro e he
    obtain ⟨heM, hex⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hedge e heM, hex⟩
  have hsplit : M.card = (M.filter ex).card + (M.filter fun e => ¬ ex e).card :=
    (Finset.card_filter_add_card_filter_not (s := M) ex).symm
  have hBM : ∀ e ∈ M.filter (fun e => ¬ ex e), e ∈ M := fun e he => (Finset.mem_filter.mp he).1
  let label : Fin 4 → Sym2 (Fin n) → ℕ :=
    ![fun e => (u e).val, fun e => (v e).val, fun e => 2 * a e + (b e).val, g]
  let V := G.support.toFinset.image Fin.val
  let ranges : Fin 4 → Finset ℕ := ![V, V, Finset.range (2 * C.size), Finset.range C.size]
  let R := (Finset.univ : Finset (Fin 4)).sigma ranges
  have cap : R.card ≤ 5 * (C.size + 1) := by
    have hV : V.card ≤ C.size + 1 := by
      apply Finset.card_image_le.trans
      have he := (Set.ncard_eq_toFinset_card' G.support).symm
      rw [he]
      exact h2 n G C hleast
    change ((Finset.univ : Finset (Fin 4)).sigma ranges).card ≤ _
    rw [Finset.card_sigma, Fin.sum_univ_four]
    change V.card + V.card + (Finset.range (2 * C.size)).card + (Finset.range C.size).card ≤ _
    simp only [Finset.card_range]
    omega
  have allowed (e) (he : e ∈ M.filter (fun e => ¬ ex e)) (j : Fin 4) :
      (⟨j, label j e⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ R := by
    obtain ⟨_, heq, ht, hj, _, _, _⟩ := hw e (hBM e he)
    have hAdj : G.Adj (u e) (v e) := by
      have hm := hedge e (hBM e he)
      rw [heq] at hm
      exact G.mem_edgeFinset.mp hm
    have hU : (u e).val ∈ V :=
      Finset.mem_image.mpr ⟨u e, by simpa using (show u e ∈ G.support from ⟨_, hAdj⟩), rfl⟩
    have hV : (v e).val ∈ V :=
      Finset.mem_image.mpr ⟨v e, by simpa using (show v e ∈ G.support from ⟨_, hAdj.symm⟩), rfl⟩
    have index {P : ℕ → Prop} {dec : DecidablePred P} {i : ℕ}
        (h : i ∈ @PEqualNP.TopForm.gatesWhere C P dec) : i < C.size := by
      exact Finset.mem_range.mp
        (Finset.mem_filter.mp (show i ∈ (Finset.range C.size).filter P from h)).1
    have hA' : a e < C.size := index ht
    have hG : g e < C.size := index hj
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    fin_cases j
    · exact hU
    · exact hV
    · apply Finset.mem_range.mpr
      change 2 * a e + (b e).val < 2 * C.size
      have := (b e).isLt
      omega
    · exact Finset.mem_range.mpr hG
  have peel (m : ℕ) : ∀ (P : Finset (Sigma (fun _ : Fin 4 => ℕ))) (A : Finset (Sym2 (Fin n))),
      P.card = m → (∀ e ∈ A, ∀ j, (⟨j, label j e⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ P) →
      ∃ T ⊆ A, (∀ e ∈ T, ∀ j, 3 ≤ (T.filter fun z => label j z = label j e).card) ∧
        A.card ≤ T.card + 2 * P.card := by
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro P A hm hp
      by_cases h : ∀ e ∈ A, ∀ j, 3 ≤ (A.filter fun z => label j z = label j e).card
      · exact ⟨A, Finset.Subset.rfl, h, by omega⟩
      · rw [not_forall] at h
        obtain ⟨e, h⟩ := h
        rw [Classical.not_imp] at h
        obtain ⟨he, h⟩ := h
        rw [not_forall] at h
        obtain ⟨j, hfew⟩ := h
        rw [not_le] at hfew
        let B := A.filter fun z => label j z = label j e
        let r : Sigma (fun _ : Fin 4 => ℕ) := ⟨j, label j e⟩
        have hr : r ∈ P := hp e he j
        have hlt : (P.erase r).card < m := hm ▸ Finset.card_erase_lt_of_mem hr
        have rem (z) (hz : z ∈ A \ B) (i) :
            (⟨i, label i z⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ P.erase r := by
          obtain ⟨hza, hzb⟩ := Finset.mem_sdiff.mp hz
          apply Finset.mem_erase.mpr
          refine ⟨?_, hp z hza i⟩
          intro eq
          have ij : i = j := congrArg Sigma.fst eq
          subst i
          have same : label j z = label j e :=
            congrArg (fun p : Sigma (fun _ : Fin 4 => ℕ) => p.2) eq
          exact hzb (Finset.mem_filter.mpr ⟨hza, same⟩)
        obtain ⟨T, hTA, hT, hsize⟩ := ih _ hlt _ _ rfl rem
        refine ⟨T, hTA.trans Finset.sdiff_subset, hT, ?_⟩
        have hsum := Finset.card_sdiff_add_card_eq_card
          (Finset.filter_subset (fun z => label j z = label j e) A)
        change (A \ B).card + B.card = A.card at hsum
        change B.card < 3 at hfew
        have hle : (P.erase r).card ≤ P.card := Finset.card_le_card (Finset.erase_subset _ _)
        have hlt' : (P.erase r).card < P.card := Finset.card_erase_lt_of_mem hr
        omega
  obtain ⟨T, hT, hRich, hpay⟩ := peel R.card R (M.filter fun e => ¬ ex e) rfl allowed
  have hBound := hk n G C hcy hleast htop T u v a g b
    (fun e he => hw e (hBM e (hT he))) (by
    intro e he f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact hRich e he 0
    · exact hRich e he 1
    · exact hRich e he 2
    · exact hRich e he 3)
    (fun w e he d hd => hsep w e (hBM e (hT he)) d (hBM d (hT hd)))
    (fun e he => (Finset.mem_filter.mp (hT he)).2)
  rw [Nat.add_mul]
  omega
