import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hAO hF
  set R := F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset) with hR
  have hRc : R.card ≤ 2 * F.card := by
    calc R.card ≤ ∑ g ∈ F, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ F, 2 := by
          apply Finset.sum_le_sum
          intro g hg
          have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
            unfold PEqualNP.MetaComplexity.NestedCover.gateAt
            rw [List.getD_eq_getElem _ _ (hF g hg)]
            exact List.getElem_mem _
          have h2 := hAO.2.2 _ hmem
          calc ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card
              ≤ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length := List.toFinset_card_le _
            _ = 2 := h2
      _ = 2 * F.card := by simp [mul_comm]
  have hD : (F.filter (fun g => n + g ∈ R)).card
      = ((F.filter (fun g => n + g ∈ R)).image (fun g => n + g)).card := by
    rw [Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)]
  have h1 := Finset.card_filter_add_card_filter_not (s := R) (fun w => w < n)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := R.filter (fun w => ¬ w < n)) (fun w => w - n ∉ F)
  have hB : R.filter (fun w => n ≤ w ∧ w - n ∉ F)
      = (R.filter (fun w => ¬ w < n)).filter (fun w => w - n ∉ F) := by
    ext w
    simp only [Finset.mem_filter, not_lt]
    tauto
  have hDs : (F.filter (fun g => n + g ∈ R)).image (fun g => n + g)
      ⊆ (R.filter (fun w => ¬ w < n)).filter (fun w => ¬ (w - n ∉ F)) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    rw [Finset.mem_filter] at hg
    simp only [Finset.mem_filter, not_lt, not_not]
    refine ⟨⟨hg.2, Nat.le_add_right _ _⟩, ?_⟩
    simpa using hg.1
  have hDc := Finset.card_le_card hDs
  rw [hD, hB]
  omega
