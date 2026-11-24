import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1539 : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (P : Finset (K × K)) (a m : K) (T : Finset K), 2 * P.card < Fintype.card K → 2 * T.card ≤ Fintype.card K → ∃ b : K, (∀ pt ∈ P, pt.2 ≠ m * pt.1 + b) ∧ m * a + b ∉ T := by
  intro K _ _ _ P a m T hP hT
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset K) ⊆
      P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a) := by
    intro b _
    by_cases hb : ∀ pt ∈ P, pt.2 ≠ m * pt.1 + b
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m * a + b, h b hb, by ring⟩)
    · push_neg at hb
      obtain ⟨pt, hpt, e⟩ := hb
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨pt, hpt, by rw [e]; ring⟩)
  have c := Finset.card_le_card hsub
  have c1 := Finset.card_union_le (P.image fun pt => pt.2 - m * pt.1) (T.image fun t => t - m * a)
  have c2 := Finset.card_image_le (s := P) (f := fun pt => pt.2 - m * pt.1)
  have c3 := Finset.card_image_le (s := T) (f := fun t => t - m * a)
  rw [Finset.card_univ] at c
  omega
