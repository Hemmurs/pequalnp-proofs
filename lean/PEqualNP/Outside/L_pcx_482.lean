import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Embedding.Basic

namespace PEqualNP.Outside.L_pcx_482

open Finset

def rel {k q : Nat} (x : Fin k → Fin q) : (Fin k ⊕ Fin t) → (Fin k ⊕ Fin t) → Prop
  | Sum.inl i, Sum.inl j => x i ≠ x j
  | _, _ => True

def gr {k q t : Nat} (x : Fin k → Fin q) : SimpleGraph (Fin k ⊕ Fin t) :=
  SimpleGraph.fromRel (rel x)

lemma fwd (q k t s : Nat) (hq : 1 ≤ q) (x y : Fin k → Fin q)
    (hy : ∀ i j, y i = y j → x i = x j)
    (hu : (univ.image y).card ≤ max (univ.image x).card (q - s)) (ht : t ≤ s)
    (G : SimpleGraph (Fin k ⊕ Fin t)) (c : (Fin k ⊕ Fin t) → Fin q)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) (hcx : ∀ i, c (Sum.inl i) = x i) :
    ∃ c' : (Fin k ⊕ Fin t) → Fin q,
      (∀ u v, G.Adj u v → c' u ≠ c' v) ∧ ∀ i, c' (Sum.inl i) = y i := by
  classical
  set S : Finset (Fin q) :=
    (univ.image (fun w : Fin t => c (Sum.inr w))).filter (fun a => a ∉ univ.image x) with hS
  set T : Finset (Fin q) := (univ.image y)ᶜ with hT
  have hS1 : S.card ≤ t := by
    calc S.card ≤ (univ.image (fun w : Fin t => c (Sum.inr w))).card := card_filter_le _ _
      _ ≤ univ.card := card_image_le
      _ = t := by simp
  have hS2 : S.card ≤ q - (univ.image x).card := by
    have : S ⊆ (univ.image x)ᶜ := by
      intro a ha
      simp only [hS, mem_filter] at ha
      simpa using ha.2
    have := card_le_card this
    rw [card_compl] at this
    simpa using this
  have hTc : T.card = q - (univ.image y).card := by
    rw [hT, card_compl]; simp
  have hxq : (univ.image x).card ≤ q := by
    have := card_le_univ (univ.image x); simpa using this
  have hle : Fintype.card S ≤ Fintype.card T := by
    rw [Fintype.card_coe, Fintype.card_coe]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  let g : Fin q → Fin q := fun a =>
    if h : a ∈ univ.image x then y (Classical.choose (mem_image.mp h))
    else if h2 : a ∈ S then (e ⟨a, h2⟩).1 else ⟨0, hq⟩
  have gx : ∀ a (h : a ∈ univ.image x), ∃ i, x i = a ∧ g a = y i := by
    intro a h
    refine ⟨Classical.choose (mem_image.mp h), (Classical.choose_spec (mem_image.mp h)).2, ?_⟩
    simp only [g, dif_pos h]
  have gS : ∀ a, a ∉ univ.image x → ∀ h2 : a ∈ S, g a = (e ⟨a, h2⟩).1 := by
    intro a h h2
    simp only [g, dif_neg h, dif_pos h2]
  have gT : ∀ a, a ∉ univ.image x → a ∈ S → g a ∉ univ.image y := by
    intro a h h2
    rw [gS a h h2]
    exact mem_compl.mp (e ⟨a, h2⟩).2
  have memS : ∀ w, c (Sum.inr w) ∉ univ.image x → c (Sum.inr w) ∈ S := by
    intro w h
    simp only [hS, mem_filter, mem_image]
    exact ⟨⟨w, mem_univ _, rfl⟩, fun hh => h (mem_image.mpr hh)⟩
  refine ⟨fun u => Sum.elim y (fun w => g (c (Sum.inr w))) u, ?_, fun i => rfl⟩
  have key : ∀ i w, G.Adj (Sum.inl i) (Sum.inr w) → y i ≠ g (c (Sum.inr w)) := by
    intro i w hadj heq
    have hne := hc _ _ hadj
    rw [hcx] at hne
    by_cases h : c (Sum.inr w) ∈ univ.image x
    · obtain ⟨j, hj, hg⟩ := gx _ h
      rw [hg] at heq
      exact hne (by rw [hy i j heq, hj])
    · exact gT _ h (memS w h) (by rw [← heq]; simp)
  intro u v hadj
  rcases u with i | w <;> rcases v with j | w'
  · intro heq
    have hne := hc _ _ hadj
    rw [hcx, hcx] at hne
    exact hne (hy i j heq)
  · exact key i w' hadj
  · intro heq
    exact key j w hadj.symm heq.symm
  · intro heq
    have hne := hc _ _ hadj
    simp only [Sum.elim_inr] at heq
    by_cases h1 : c (Sum.inr w) ∈ univ.image x <;> by_cases h2 : c (Sum.inr w') ∈ univ.image x
    · obtain ⟨i, hi, hg⟩ := gx _ h1
      obtain ⟨j, hj, hg'⟩ := gx _ h2
      rw [hg, hg'] at heq
      exact hne (by rw [← hi, ← hj, hy i j heq])
    · obtain ⟨i, hi, hg⟩ := gx _ h1
      exact gT _ h2 (memS w' h2) (by rw [← heq, hg]; simp)
    · obtain ⟨j, hj, hg'⟩ := gx _ h2
      exact gT _ h1 (memS w h1) (by rw [heq, hg']; simp)
    · rw [gS _ h1 (memS w h1), gS _ h2 (memS w' h2)] at heq
      have := e.injective (Subtype.ext heq)
      exact hne (congrArg Subtype.val this)

lemma bwd (q k s : Nat) (x y : Fin k → Fin q)
    (c : (Fin k ⊕ Fin (min s (q - (univ.image x).card))) → Fin q)
    (hc : ∀ u v, (gr x).Adj u v → c u ≠ c v) (hcx : ∀ i, c (Sum.inl i) = y i) :
    (∀ i j, y i = y j → x i = x j) ∧
      (univ.image y).card ≤ max (univ.image x).card (q - s) := by
  classical
  constructor
  · intro i j heq
    by_contra hne
    have hij : (Sum.inl i : Fin k ⊕ Fin (min s (q - (univ.image x).card))) ≠ Sum.inl j := by
      intro h; apply hne; cases h; rfl
    have hadj : (gr x).Adj (Sum.inl i) (Sum.inl j) :=
      ⟨hij, Or.inl hne⟩
    exact hc _ _ hadj (by rw [hcx, hcx, heq])
  · have hinj : Function.Injective (fun w : Fin (min s (q - (univ.image x).card)) => c (Sum.inr w)) := by
      intro w w' heq
      by_contra hne
      have hadj : (gr x).Adj (Sum.inr w) (Sum.inr w') :=
        ⟨by intro h; apply hne; cases h; rfl, Or.inl trivial⟩
      exact hc _ _ hadj heq
    have hsub : univ.image (fun w : Fin (min s (q - (univ.image x).card)) => c (Sum.inr w)) ⊆ (univ.image y)ᶜ := by
      intro a ha
      simp only [mem_image, mem_univ, true_and] at ha
      obtain ⟨w, rfl⟩ := ha
      simp only [mem_compl, mem_image, mem_univ, true_and, not_exists]
      intro i heq
      have hadj : (gr x).Adj (Sum.inl i) (Sum.inr w) :=
        ⟨by simp, Or.inl trivial⟩
      exact hc _ _ hadj (by rw [hcx, heq])
    have h1 := card_le_card hsub
    rw [card_compl, card_image_of_injective _ hinj] at h1
    simp only [card_univ, Fintype.card_fin] at h1
    have hxq : (univ.image x).card ≤ q := by
      have := card_le_univ (univ.image x); simpa using this
    have hyq : (univ.image y).card ≤ q := by
      have := card_le_univ (univ.image y); simpa using this
    omega

lemma acc (q k s : Nat) (x : Fin k → Fin q) :
    ∃ c : (Fin k ⊕ Fin (min s (q - (univ.image x).card))) → Fin q,
      (∀ u v, (gr x).Adj u v → c u ≠ c v) ∧ ∀ i, c (Sum.inl i) = x i := by
  classical
  set t := min s (q - (univ.image x).card) with ht
  have hle : Fintype.card (Fin t) ≤ Fintype.card ((univ.image x)ᶜ : Finset (Fin q)) := by
    rw [Fintype.card_coe, card_compl]; simp; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  refine ⟨fun u => Sum.elim x (fun w => (e w).1) u, ?_, fun i => rfl⟩
  have key : ∀ i w, x i ≠ (e w).1 := by
    intro i w heq
    have := (e w).2
    simp only [mem_compl, mem_image, mem_univ, true_and, not_exists] at this
    exact this i heq
  intro u v hadj
  obtain ⟨hne, hr⟩ := hadj
  rcases u with i | w <;> rcases v with j | w'
  · rcases hr with h | h
    · exact h
    · exact fun e' => h e'.symm
  · exact key i w'
  · exact fun h => key j w h.symm
  · intro heq
    apply hne
    have := e.injective (Subtype.ext heq)
    rw [this]

end PEqualNP.Outside.L_pcx_482

theorem PEqualNP.Outside.L_pcx_482 : ∀ (q k s : Nat), 1 ≤ q →
  ∀ A B : Finset (Fin k → Fin q),
    let used := fun (x : Fin k → Fin q) => (Finset.univ.image x).card
    let accepts := fun (t : Nat) (G : SimpleGraph (Fin k ⊕ Fin t))
        (R : Finset (Fin k → Fin q)) =>
      ∃ x ∈ R, ∃ c : (Fin k ⊕ Fin t) → Fin q,
        (∀ u v, G.Adj u v → c u ≠ c v) ∧ ∀ i, c (Sum.inl i) = x i
    (∀ (t : Nat), t ≤ s → ∀ G : SimpleGraph (Fin k ⊕ Fin t),
      accepts t G A → accepts t G B) ↔
    ∀ x ∈ A, ∃ y ∈ B, (∀ i j, y i = y j → x i = x j) ∧
      used y ≤ max (used x) (q - s) := by
  intro q k s hq A B used accepts
  constructor
  · intro H x hx
    obtain ⟨y, hy, c, hc, hcx⟩ := H _ (min_le_left _ _) (PEqualNP.Outside.L_pcx_482.gr x)
      (by
        obtain ⟨c, hc, hcx⟩ := PEqualNP.Outside.L_pcx_482.acc q k s x
        exact ⟨x, hx, c, hc, hcx⟩)
    exact ⟨y, hy, PEqualNP.Outside.L_pcx_482.bwd q k s x y c hc hcx⟩
  · intro H t ht G ⟨x, hx, c, hc, hcx⟩
    obtain ⟨y, hy, hr, hu⟩ := H x hx
    obtain ⟨c', hc', hcy⟩ := PEqualNP.Outside.L_pcx_482.fwd q k t s hq x y hr hu ht G c hc hcx
    exact ⟨y, hy, c', hc', hcy⟩
