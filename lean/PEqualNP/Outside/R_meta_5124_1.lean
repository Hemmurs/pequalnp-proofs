import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5124_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 n C → ∀ t ∈ PEqualNP.TopForm.tops G C, ∀ (b : Fin 2) (g : ℕ), PEqualNP.TopForm.opnd C t (1 - b) = n + g →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ q ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t b), ∀ a ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0), ∀ d ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1),
        G.Adj q a ∨ G.Adj q d ∨ G.Adj a d)
    (h2 : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ H : Finset (Sym2 (Fin n)), H ⊆ PEqualNP.TopForm.Ustar G C →
      (∀ u v : Fin n, s(u,v) ∈ H → ∀ w < n + C.gates.length, v ∈ PEqualNP.TopForm.orIn n C w →
        (2 ≤ (PEqualNP.TopForm.orIn n C w).card → ∃ a ∈ PEqualNP.TopForm.orIn n C w, ¬G.Adj u a) ∧
        (3 ≤ (PEqualNP.TopForm.orIn n C w).card → 2 ≤ ((PEqualNP.TopForm.orIn n C w).filter fun a => ¬G.Adj u a).card)) →
      (∀ u v : Fin n, s(u,v) ∈ H → ¬ ∃ t ∈ PEqualNP.TopForm.tops G C, ∃ (b : Fin 2) (g : ℕ),
        PEqualNP.TopForm.opnd C t (1 - b) = n + g ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t b) ∧
        (u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) ∨ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0)) ∧
        (u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1) ∨ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1))) →
      H.card ≤ k * (C.size + 1)) : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ (x12 x13 : Fin x2), s(x12, x13) ∈ x10 → ∀ x15 < x2 + x7.gates.length, x13 ∈ PEqualNP.TopForm.orIn x2 x7 x15 → ((2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → ∃ x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15, ¬x3.Adj x12 x19) ∧ ((3 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → (2 : ℕ) ≤ {x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15 | ¬x3.Adj x12 x19}.card)) → x10.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k, hk⟩ := h2
  refine ⟨k + 6, ?_⟩
  intro n G _ hg hne C hL hT M hM hc
  have hfil : ∀ (p : ℕ → Prop) (inst : DecidablePred p) (s : Finset ℕ) (t : ℕ),
      t ∈ @Finset.filter ℕ p inst s → t ∈ s :=
    fun p inst s t h => ((@Finset.mem_filter _ p inst s t).mp h).1
  have hAO : PEqualNP.TopForm.IsAO2 n C := hL.1
  have hsize : C.size = C.gates.length := rfl
  have no4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d →
      False := by
    intro a b c d hab hbc hcd hda hac hbd
    have e1 := G.ne_of_adj hab
    have e2 := G.ne_of_adj hbc
    have e3 := G.ne_of_adj hcd
    have e4 := G.ne_of_adj hda
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
      · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    have h5 := hg a _ hcyc
    simp at h5
  have hmemg : ∀ j, j < C.gates.length → PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
    intro j hj
    show C.gates.getD j _ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hop_lt : ∀ j, j < C.gates.length → ∀ b : Fin 2, PEqualNP.TopForm.opnd C j b < n + j := by
    intro j hj b
    have hl : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 := hAO.2.2 _ (hmemg j hj)
    have hb : (b : ℕ) < (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length := by rw [hl]; exact b.isLt
    have hm : PEqualNP.TopForm.opnd C j b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
      show (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD (b : ℕ) 0 ∈ _
      rw [List.getD_eq_getElem _ _ hb]
      exact List.getElem_mem hb
    exact hAO.2.1 j hj _ hm
  have big : ∀ (c x x' : Fin n) (S : Finset (Fin n)), x ≠ x' → G.Adj c x → G.Adj c x' →
      x ∈ S → x' ∈ S →
      ((2 ≤ S.card → ∃ a ∈ S, ¬G.Adj c a) ∧
        (3 ≤ S.card → 2 ≤ (S.filter fun a => ¬G.Adj c a).card)) →
      ∃ y1 ∈ S, ∃ y2 ∈ S, y1 ≠ y2 ∧ ¬G.Adj c y1 ∧ ¬G.Adj c y2 := by
    intro c x x' S hne hx hx' h1 h2 hcS
    have h2c : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨x, h1, x', h2, hne⟩
    obtain ⟨y, hy, hny⟩ := hcS.1 h2c
    have hyu : x ≠ y := fun h => hny (h ▸ hx)
    have hyu' : x' ≠ y := fun h => hny (h ▸ hx')
    have h3c : 3 ≤ S.card := Finset.two_lt_card.mpr ⟨x, h1, x', h2, y, hy, hne, hyu, hyu'⟩
    obtain ⟨y1, hy1, y2, hy2, h12⟩ := Finset.one_lt_card.mp (hcS.2 h3c)
    rw [Finset.mem_filter] at hy1 hy2
    exact ⟨y1, hy1.1, y2, hy2.1, h12, hy1.2, hy2.2⟩
  have key1 : ∀ (Q A : Finset (Fin n)) (v u u' : Fin n),
      (∀ q ∈ Q, ∀ a ∈ A, G.Adj q a ∨ G.Adj q v ∨ G.Adj a v) →
      u ∈ Q → u ∈ A → u' ∈ Q → u' ∈ A → G.Adj u v → G.Adj u' v →
      ((2 ≤ Q.card → ∃ a ∈ Q, ¬G.Adj v a) ∧
        (3 ≤ Q.card → 2 ≤ (Q.filter fun a => ¬G.Adj v a).card)) →
      ((2 ≤ A.card → ∃ a ∈ A, ¬G.Adj v a) ∧
        (3 ≤ A.card → 2 ≤ (A.filter fun a => ¬G.Adj v a).card)) →
      u = u' := by
    intro Q A v u u' hst huQ huA hu'Q hu'A huv hu'v hcQ hcA
    by_contra hne
    obtain ⟨y1, hy1, y2, hy2, hy12, hn1, hn2⟩ := big v u u' Q hne huv.symm hu'v.symm huQ hu'Q hcQ
    obtain ⟨z1, hz1, z2, hz2, hz12, hm1, hm2⟩ := big v u u' A hne huv.symm hu'v.symm huA hu'A hcA
    have adj : ∀ y ∈ Q, ∀ z ∈ A, ¬G.Adj v y → ¬G.Adj v z → G.Adj y z := by
      intro y hy z hz h1 h2
      rcases hst y hy z hz with h | h | h
      · exact h
      · exact (h1 h.symm).elim
      · exact (h2 h.symm).elim
    exact no4 y1 z1 y2 z2 (adj y1 hy1 z1 hz1 hn1 hm1) (adj y2 hy2 z1 hz1 hn2 hm1).symm
      (adj y2 hy2 z2 hz2 hn2 hm2) (adj y1 hy1 z2 hz2 hn1 hm2).symm hy12 hz12
  have key3 : ∀ (A B : Finset (Fin n)) (u v v' : Fin n),
      (∀ a ∈ A, ∀ d ∈ B, G.Adj u a ∨ G.Adj u d ∨ G.Adj a d) →
      v ∈ A → v ∈ B → v' ∈ A → v' ∈ B →
      ((2 ≤ A.card → ∃ a ∈ A, ¬G.Adj u a) ∧
        (3 ≤ A.card → 2 ≤ (A.filter fun a => ¬G.Adj u a).card)) →
      ((2 ≤ B.card → ∃ a ∈ B, ¬G.Adj u a) ∧
        (3 ≤ B.card → 2 ≤ (B.filter fun a => ¬G.Adj u a).card)) →
      v = v' := by
    intro A B u v v' hst hvA hvB hv'A hv'B hcA hcB
    by_contra hne
    have hx : ∀ x ∈ A, x ∈ B → G.Adj u x := by
      intro x hxA hxB
      rcases hst x hxA x hxB with h | h | h
      · exact h
      · exact h
      · exact (G.ne_of_adj h rfl).elim
    obtain ⟨y1, hy1, y2, hy2, hy12, hn1, hn2⟩ :=
      big u v v' A hne (hx v hvA hvB) (hx v' hv'A hv'B) hvA hv'A hcA
    obtain ⟨z1, hz1, z2, hz2, hz12, hm1, hm2⟩ :=
      big u v v' B hne (hx v hvA hvB) (hx v' hv'A hv'B) hvB hv'B hcB
    have adj : ∀ y ∈ A, ∀ z ∈ B, ¬G.Adj u y → ¬G.Adj u z → G.Adj y z := by
      intro y hy z hz h1 h2
      rcases hst y hy z hz with h | h | h
      · exact (h1 h).elim
      · exact (h2 h).elim
      · exact h
    exact no4 y1 z1 y2 z2 (adj y1 hy1 z1 hz1 hn1 hm1) (adj y2 hy2 z1 hz1 hn2 hm1).symm
      (adj y2 hy2 z2 hz2 hn2 hm2) (adj y1 hy1 z2 hz2 hn1 hm2).symm hy12 hz12
  obtain ⟨D, hD⟩ : ∃ D : Sym2 (Fin n) → Prop, ∀ e, D e ↔ ∃ u v : Fin n, e = s(u,v) ∧
      ∃ t ∈ PEqualNP.TopForm.tops G C, ∃ (b : Fin 2) (g : ℕ),
        PEqualNP.TopForm.opnd C t (1 - b) = n + g ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t b) ∧
        (u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) ∨ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0)) ∧
        (u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1) ∨ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1)) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : ℕ → Fin 2 → ℕ → Sym2 (Fin n) → Prop, ∀ t b c e, T t b c e ↔
      ∃ (u v : Fin n) (g : ℕ), e = s(u,v) ∧ s(u,v) ∈ M ∧ G.Adj u v ∧ t ∈ PEqualNP.TopForm.tops G C ∧
        PEqualNP.TopForm.opnd C t (1 - b) = n + g ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t b) ∧
        ((c = 0 ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1) = {v}) ∨
         (c = 1 ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) = {v}) ∨
         (c = 2 ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t b) = {u} ∧ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) ∧
           v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1))) := ⟨_, fun _ _ _ _ => Iff.rfl⟩
  have hrest : (M.filter fun e => ¬D e).card ≤ k * (C.size + 1) :=
    hk n G hg hne C hL hT _ ((Finset.filter_subset _ _).trans hM)
      (fun u v h => hc u v (Finset.mem_filter.mp h).1)
      (fun u v h hP => (Finset.mem_filter.mp h).2 ((hD _).mpr ⟨u, v, rfl, hP⟩))
  have cover : ∀ e ∈ M.filter D, ∃ tag ∈ (Finset.range C.gates.length ×ˢ
      (Finset.univ : Finset (Fin 2))) ×ˢ Finset.range 3, T tag.1.1 tag.1.2 tag.2 e := by
    intro e he
    obtain ⟨heM, hDe⟩ := Finset.mem_filter.mp he
    obtain ⟨u, v, rfl, t, ht, b, g, hopnd, hop, huQ, hA, hB⟩ := (hD e).mp hDe
    have htl : t < C.gates.length := Finset.mem_range.mp (hfil _ _ _ t ht)
    have hQl := hop_lt t htl b
    have hgl : g < C.gates.length := by
      have := hop_lt t htl (1 - b)
      rw [hopnd] at this
      omega
    have hA0l := hop_lt g hgl 0
    have hA1l := hop_lt g hgl 1
    have huv : G.Adj u v := by
      have := (Finset.mem_sdiff.mp (hM heM)).1
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    have hst := h1 n G C hAO t ht b g hopnd hop
    have heM' : s(v, u) ∈ M := by rw [Sym2.eq_swap]; exact heM
    have hmem : ∀ c, c < 3 → ((t, b), c) ∈ (Finset.range C.gates.length ×ˢ
        (Finset.univ : Finset (Fin 2))) ×ˢ Finset.range 3 := fun c hc3 =>
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr htl,
        Finset.mem_univ _⟩, Finset.mem_range.mpr hc3⟩
    by_cases h0 : u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0)
    · have hBn : ∀ d ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1), G.Adj u d := by
        intro d hd
        rcases hst u huQ u h0 d hd with h | h | h
        · exact (G.ne_of_adj h rfl).elim
        · exact h
        · exact h
      have hv1 : v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1) := by
        rcases hB with h | h
        · exact (G.ne_of_adj (hBn u h) rfl).elim
        · exact h
      have hsing : PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1) = {v} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hv1, fun x hx => ?_⟩
        by_contra hxv
        obtain ⟨y, hy, hny⟩ := (hc u v heM _ (by omega) hv1).1
          (Finset.one_lt_card.mpr ⟨x, hx, v, hv1, hxv⟩)
        exact hny (hBn y hy)
      exact ⟨((t, b), 0), hmem 0 (by norm_num), (hTd _ _ _ _).mpr
        ⟨u, v, g, rfl, heM, huv, ht, hopnd, hop, huQ, Or.inl ⟨rfl, h0, hsing⟩⟩⟩
    · by_cases h1' : u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1)
      · have hAn : ∀ a ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0), G.Adj u a := by
          intro a ha
          rcases hst u huQ a ha u h1' with h | h | h
          · exact h
          · exact (G.ne_of_adj h rfl).elim
          · exact h.symm
        have hv0 : v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) := hA.resolve_left h0
        have hsing : PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) = {v} := by
          rw [Finset.eq_singleton_iff_unique_mem]
          refine ⟨hv0, fun x hx => ?_⟩
          by_contra hxv
          obtain ⟨y, hy, hny⟩ := (hc u v heM _ (by omega) hv0).1
            (Finset.one_lt_card.mpr ⟨x, hx, v, hv0, hxv⟩)
          exact hny (hAn y hy)
        exact ⟨((t, b), 1), hmem 1 (by norm_num), (hTd _ _ _ _).mpr
          ⟨u, v, g, rfl, heM, huv, ht, hopnd, hop, huQ, Or.inr (Or.inl ⟨rfl, h1', hsing⟩)⟩⟩
      · have hv0 : v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 0) := hA.resolve_left h0
        have hv1 : v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C g 1) := hB.resolve_left h1'
        have hQn : ∀ q ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t b), G.Adj q v := by
          intro q hq
          rcases hst q hq v hv0 v hv1 with h | h | h
          · exact h
          · exact h
          · exact (G.ne_of_adj h rfl).elim
        have hsing : PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t b) = {u} := by
          rw [Finset.eq_singleton_iff_unique_mem]
          refine ⟨huQ, fun x hx => ?_⟩
          by_contra hxu
          obtain ⟨y, hy, hny⟩ := (hc v u heM' _ (by omega) huQ).1
            (Finset.one_lt_card.mpr ⟨x, hx, u, huQ, hxu⟩)
          exact hny (hQn y hy).symm
        exact ⟨((t, b), 2), hmem 2 (by norm_num), (hTd _ _ _ _).mpr
          ⟨u, v, g, rfl, heM, huv, ht, hopnd, hop, huQ, Or.inr (Or.inr ⟨rfl, hsing, hv0, hv1⟩)⟩⟩
  have uniq : ∀ t b c e e', T t b c e → T t b c e' → e = e' := by
    intro t b c e e' h h'
    obtain ⟨u, v, g, rfl, heM, huv, ht, hopnd, hop, huQ, hcase⟩ := (hTd _ _ _ _).mp h
    obtain ⟨u', v', g', rfl, heM', huv', -, hopnd', -, huQ', hcase'⟩ := (hTd _ _ _ _).mp h'
    have hgg : g' = g := by omega
    subst hgg
    have htl : t < C.gates.length := Finset.mem_range.mp (hfil _ _ _ t ht)
    have hQl := hop_lt t htl b
    have hgl : g' < C.gates.length := by
      have := hop_lt t htl (1 - b)
      rw [hopnd] at this
      omega
    have hA0l := hop_lt g' hgl 0
    have hA1l := hop_lt g' hgl 1
    have hst := h1 n G C hAO t ht b g' hopnd hop
    have hsw : s(v, u) ∈ M := by rw [Sym2.eq_swap]; exact heM
    rcases hcase with ⟨hc0, huA, hs⟩ | ⟨hc0, huA, hs⟩ | ⟨hc0, hs, hvA, hvB⟩ <;>
      rcases hcase' with ⟨hc0', huA', hs'⟩ | ⟨hc0', huA', hs'⟩ | ⟨hc0', hs', hvA', hvB'⟩ <;>
      first
        | (exfalso; omega)
        | skip
    · have hvv : v' = v := Finset.singleton_injective (hs'.symm.trans hs)
      subst hvv
      have huu : u = u' := key1 _ _ v' u u'
        (fun q hq a ha => hst q hq a ha v' (by rw [hs]; exact Finset.mem_singleton_self _))
        huQ huA huQ' huA' huv huv'
        (hc v' u hsw _ (by omega) huQ) (hc v' u hsw _ (by omega) huA)
      subst huu
      rfl
    · have hvv : v' = v := Finset.singleton_injective (hs'.symm.trans hs)
      subst hvv
      have huu : u = u' := key1 _ _ v' u u'
        (fun q hq a ha => by
          rcases hst q hq v' (by rw [hs]; exact Finset.mem_singleton_self _) a ha with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h.symm))
        huQ huA huQ' huA' huv huv'
        (hc v' u hsw _ (by omega) huQ) (hc v' u hsw _ (by omega) huA)
      subst huu
      rfl
    · have huu : u' = u := Finset.singleton_injective (hs'.symm.trans hs)
      subst huu
      have hvv : v = v' := key3 _ _ u' v v' (hst u' huQ) hvA hvB hvA' hvB'
        (hc u' v heM _ (by omega) hvA) (hc u' v heM _ (by omega) hvB)
      subst hvv
      rfl
  have hfirst : (M.filter D).card ≤ 6 * C.gates.length := by
    have hsub : M.filter D ⊆ ((Finset.range C.gates.length ×ˢ
        (Finset.univ : Finset (Fin 2))) ×ˢ Finset.range 3).biUnion
        (fun tag => (M.filter D).filter (fun e => T tag.1.1 tag.1.2 tag.2 e)) := by
      intro e he
      obtain ⟨tag, htag, hTe⟩ := cover e he
      exact Finset.mem_biUnion.mpr ⟨tag, htag, Finset.mem_filter.mpr ⟨he, hTe⟩⟩
    have hle := le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le_card_mul _ _ 1
      (fun tag _ => Finset.card_le_one.mpr (fun e he e' he' =>
        uniq _ _ _ e e' (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp he').2)))
    simp only [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := M) D
  have hexp : (k + 6) * (C.size + 1) = k * (C.size + 1) + 6 * (C.size + 1) := by ring
  rw [hexp]
  omega
