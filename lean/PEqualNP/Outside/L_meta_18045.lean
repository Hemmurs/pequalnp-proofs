import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18045 : ∀ (x1 x2 : Finset (Finset ℕ)), (∀ x3 ∈ x1 \ x2, ∃ x5 ∈ x1, ∃ x6 ∈ x1, x5 ⊂ x3 ∧ x6 ⊂ x3 ∧ x3 = x5 ∪ x6) → ∀ x4 ∈ x1, {x6 ∈ x1 ∩ x2 | x6 ⊆ x4}.biUnion id = x4 := by
  intro x1 x2 h x4 hx4
  have key : ∀ n : ℕ, ∀ s ∈ x1, s.card = n → ∀ a ∈ s, ∃ t ∈ x1 ∩ x2, t ⊆ s ∧ a ∈ t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs hn a ha
      by_cases hs2 : s ∈ x2
      · exact ⟨s, Finset.mem_inter.mpr ⟨hs, hs2⟩, Finset.Subset.refl _, ha⟩
      · obtain ⟨u, hu, v, hv, huv, hvv, heq⟩ := h s (Finset.mem_sdiff.mpr ⟨hs, hs2⟩)
        have ha' : a ∈ u ∪ v := heq ▸ ha
        rcases Finset.mem_union.mp ha' with hau | hav
        · obtain ⟨t, ht, hts, hat⟩ := ih u.card (hn ▸ Finset.card_lt_card huv) u hu rfl a hau
          exact ⟨t, ht, Finset.Subset.trans hts huv.subset, hat⟩
        · obtain ⟨t, ht, hts, hat⟩ := ih v.card (hn ▸ Finset.card_lt_card hvv) v hv rfl a hav
          exact ⟨t, ht, Finset.Subset.trans hts hvv.subset, hat⟩
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨t, ⟨_, hts⟩, hat⟩
    exact hts hat
  · intro ha
    obtain ⟨t, ht, hts, hat⟩ := key _ x4 hx4 rfl a ha
    exact ⟨t, ⟨ht, hts⟩, hat⟩
