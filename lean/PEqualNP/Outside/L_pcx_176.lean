import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_176

open PEqualNP.ProofComplexity

section gen

variable {V : Type} [DecidableEq V]

def Ent (A : Finset (LinClause V)) (C : LinClause V) : Prop :=
  ∀ a : V → Bool, (∀ X ∈ A, LinClauseSat a X) → LinClauseSat a C

def Tree (C : LinClause V) (A : Finset (LinClause V)) : Prop :=
  ∃ K : Finset (Finset V), K.card + 1 = A.card ∧ (∀ f ∈ K, (f, true) ∉ C) ∧
    (∀ f ∈ K, ∃ X ∈ A, (f, true) ∈ X) ∧ (∀ f, (f, true) ∈ C → ∃ X ∈ A, (f, true) ∈ X)

def Good (C : LinClause V) (p : Finset (LinClause V) × ℕ) : Prop :=
  ∃ A, A ⊆ p.1 ∧ Ent A C ∧ (p.2 + 1 = 2 * p.1.card → Tree C A)

def Inv (F : Set (LinClause V)) (π : List (LinClause V)) : Prop :=
  ∃ P : List (Finset (LinClause V) × ℕ),
    (∀ p ∈ P, (∀ X ∈ p.1, X ∈ F) ∧ 2 * p.1.card ≤ p.2 + 1) ∧
    (P.map Prod.snd).sum ≤ π.length ∧ ∀ C ∈ π, ∃ p ∈ P, Good C p

omit [DecidableEq V] in
theorem good_mono {C : LinClause V} {S S' : Finset (LinClause V)} {w w' : ℕ}
    (h : Good C (S, w)) (hs : S ⊆ S') (ht : w' + 1 = 2 * S'.card → w + 1 = 2 * S.card) :
    Good C (S', w') := by
  obtain ⟨A, hA, hE, hT⟩ := h
  exact ⟨A, hA.trans hs, hE, fun h => hT (ht h)⟩

theorem res_sound {A1 A2 : Finset (LinClause V)} {C D R : LinClause V} (h1 : Ent A1 C)
    (h2 : Ent A2 D) (hR : IsLinResolvent C D R) : Ent (A1 ∪ A2) R := by
  intro a ha
  obtain ⟨f, hfC, hfD, rfl⟩ := hR
  obtain ⟨q1, hq1, hs1⟩ := h1 a (fun X hX => ha X (Finset.mem_union_left _ hX))
  obtain ⟨q2, hq2, hs2⟩ := h2 a (fun X hX => ha X (Finset.mem_union_right _ hX))
  by_cases e1 : q1 = (f, false)
  · by_cases e2 : q2 = (f, true)
    · subst e1
      subst e2
      exact (Bool.false_ne_true (hs1.mp (hs2.mpr rfl))).elim
    · exact ⟨q2, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e2, hq2⟩), hs2⟩
  · exact ⟨q1, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e1, hq1⟩), hs1⟩

theorem tree_node {F : Set (LinClause V)}
    (hF : ∀ X ∈ F, ∀ Y ∈ F, ∀ f : Finset V, (f, true) ∈ X → (f, true) ∈ Y → X = Y)
    {A1 A2 : Finset (LinClause V)} {C D R : LinClause V}
    (hA1 : ∀ X ∈ A1, X ∈ F) (hA2 : ∀ X ∈ A2, X ∈ F) (hd : Disjoint A1 A2)
    (h1 : Tree C A1) (h2 : Tree D A2) (hR : IsLinResolvent C D R) : Tree R (A1 ∪ A2) := by
  obtain ⟨f, hfC, hfD, rfl⟩ := hR
  obtain ⟨K1, hc1, hn1, hs1, hp1⟩ := h1
  obtain ⟨K2, hc2, hn2, hs2, hp2⟩ := h2
  have clash : ∀ X ∈ A1, ∀ Y ∈ A2, ∀ g : Finset V, (g, true) ∈ X → (g, true) ∈ Y → False := by
    intro X hX Y hY g hgX hgY
    have := hF X (hA1 X hX) Y (hA2 Y hY) g hgX hgY
    subst this
    exact Finset.disjoint_left.mp hd hX hY
  have clash' : ∀ g : Finset V, (∃ X ∈ A1, (g, true) ∈ X) → (∃ Y ∈ A2, (g, true) ∈ Y) → False := by
    rintro g ⟨X, hX, hgX⟩ ⟨Y, hY, hgY⟩
    exact clash X hX Y hY g hgX hgY
  have hfD' := hp2 f hfD
  have hf1 : f ∉ K1 := fun h => clash' f (hs1 f h) hfD'
  have hf2 : f ∉ K2 := fun h => hn2 f h hfD
  have hK : Disjoint K1 K2 := Finset.disjoint_left.mpr (fun g h1 h2 => clash' g (hs1 g h1) (hs2 g h2))
  refine ⟨insert f (K1 ∪ K2), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hf1, hf2]), Finset.card_union_of_disjoint hK,
      Finset.card_union_of_disjoint hd]
    omega
  · intro g hg hgR
    rcases Finset.mem_union.mp hgR with hgC | hgD
    · have hgC' := (Finset.mem_erase.mp hgC).2
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact clash' g (hp1 g hgC') hfD'
      · rcases Finset.mem_union.mp hg with hg | hg
        · exact hn1 g hg hgC'
        · exact clash' g (hp1 g hgC') (hs2 g hg)
    · have hgD' := Finset.mem_erase.mp hgD
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hgD'.1 rfl
      · rcases Finset.mem_union.mp hg with hg | hg
        · exact clash' g (hs1 g hg) (hp2 g hgD'.2)
        · exact hn2 g hg hgD'.2
  · intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · obtain ⟨Y, hY, h⟩ := hfD'
      exact ⟨Y, Finset.mem_union_right _ hY, h⟩
    · rcases Finset.mem_union.mp hg with hg | hg
      · obtain ⟨Y, hY, h⟩ := hs1 g hg
        exact ⟨Y, Finset.mem_union_left _ hY, h⟩
      · obtain ⟨Y, hY, h⟩ := hs2 g hg
        exact ⟨Y, Finset.mem_union_right _ hY, h⟩
  · intro g hgR
    rcases Finset.mem_union.mp hgR with hgC | hgD
    · obtain ⟨Y, hY, h⟩ := hp1 g (Finset.mem_erase.mp hgC).2
      exact ⟨Y, Finset.mem_union_left _ hY, h⟩
    · obtain ⟨Y, hY, h⟩ := hp2 g (Finset.mem_erase.mp hgD).2
      exact ⟨Y, Finset.mem_union_right _ hY, h⟩

theorem inv_of_deriv {F : Set (LinClause V)}
    (hF : ∀ X ∈ F, ∀ Y ∈ F, ∀ f : Finset V, (f, true) ∈ X → (f, true) ∈ Y → X = Y)
    {π : List (LinClause V)} (h : IsLinDerivation F π) : Inv F π := by
  induction h with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | @ax π C _ hC ih =>
    obtain ⟨P, hP, hsum, hall⟩ := ih
    refine ⟨(({C} : Finset (LinClause V)), 1) :: P, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨by intro X hX; rw [Finset.mem_singleton.mp hX]; exact hC, by simp⟩
      · exact hP p hp
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · exact ⟨_, List.mem_cons_self, {X}, subset_rfl,
          fun a ha => ha X (Finset.mem_singleton_self X),
          fun _ => ⟨∅, by simp, by simp, by simp,
            fun f hf => ⟨X, Finset.mem_singleton_self X, hf⟩⟩⟩
      · obtain ⟨p, hp, hg⟩ := hall X hX
        exact ⟨p, List.mem_cons_of_mem _ hp, hg⟩
  | @weak π C D _ hC himp ih =>
    obtain ⟨P, hP, hsum, hall⟩ := ih
    obtain ⟨⟨S, w⟩, hp, A, hAS, hE, hT⟩ := hall C hC
    have hb := (hP _ hp).2
    have hs := List.sum_map_erase Prod.snd hp
    simp only at hb hs
    refine ⟨(S, w + 1) :: P.erase (S, w), ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨(hP _ hp).1, by simp only; omega⟩
      · exact hP q (List.mem_of_mem_erase hq)
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · exact ⟨_, List.mem_cons_self, A, hAS, fun a ha => himp a (hE a ha),
          fun h => by simp only at h; omega⟩
      · obtain ⟨q, hq, hg⟩ := hall X hX
        by_cases e : q = (S, w)
        · subst e
          exact ⟨_, List.mem_cons_self, good_mono hg subset_rfl (fun h => by omega)⟩
        · exact ⟨q, List.mem_cons_of_mem _ ((List.mem_erase_of_ne e).mpr hq), hg⟩
  | @res π C D R _ hC hD hR ih =>
    obtain ⟨P, hP, hsum, hall⟩ := ih
    obtain ⟨⟨S1, w1⟩, hp1, A1, hAS1, hE1, hT1⟩ := hall C hC
    obtain ⟨⟨S2, w2⟩, hp2, A2, hAS2, hE2, hT2⟩ := hall D hD
    have hb1 := (hP _ hp1).2
    have hb2 := (hP _ hp2).2
    have hs1 := List.sum_map_erase Prod.snd hp1
    simp only at hb1 hb2 hs1 hT1 hT2 hAS1 hAS2
    by_cases e12 : (S2, w2) = (S1, w1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e12
      refine ⟨(S2, w2 + 1) :: P.erase (S2, w2), ?_, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨(hP _ hp1).1, by simp only; omega⟩
        · exact hP q (List.mem_of_mem_erase hq)
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · exact ⟨_, List.mem_cons_self, A1 ∪ A2, Finset.union_subset hAS1 hAS2,
            res_sound hE1 hE2 hR, fun h => by simp only at h; omega⟩
        · obtain ⟨q, hq, hg⟩ := hall X hX
          by_cases e : q = (S2, w2)
          · subst e
            exact ⟨_, List.mem_cons_self, good_mono hg subset_rfl (fun h => by omega)⟩
          · exact ⟨q, List.mem_cons_of_mem _ ((List.mem_erase_of_ne e).mpr hq), hg⟩
    · have hp2' : (S2, w2) ∈ P.erase (S1, w1) := (List.mem_erase_of_ne e12).mpr hp2
      have hs2 := List.sum_map_erase Prod.snd hp2'
      simp only at hs2
      have hcu := Finset.card_union_le S1 S2
      refine ⟨(S1 ∪ S2, w1 + w2 + 1) :: (P.erase (S1, w1)).erase (S2, w2), ?_, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · refine ⟨?_, by simp only; omega⟩
          intro X hX
          rcases Finset.mem_union.mp hX with h | h
          · exact (hP _ hp1).1 X h
          · exact (hP _ hp2).1 X h
        · exact hP q (List.mem_of_mem_erase (List.mem_of_mem_erase hq))
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · refine ⟨_, List.mem_cons_self, A1 ∪ A2, Finset.union_subset_union hAS1 hAS2,
            res_sound hE1 hE2 hR, ?_⟩
          intro h
          simp only at h
          have hdS : Disjoint S1 S2 := Finset.card_union_eq_card_add_card.mp (by omega)
          exact tree_node hF (fun Y hY => (hP _ hp1).1 Y (hAS1 hY))
            (fun Y hY => (hP _ hp2).1 Y (hAS2 hY)) (Finset.disjoint_of_subset_left hAS1
              (Finset.disjoint_of_subset_right hAS2 hdS)) (hT1 (by omega)) (hT2 (by omega)) hR
        · obtain ⟨q, hq, hg⟩ := hall X hX
          by_cases e : q = (S1, w1)
          · subst e
            exact ⟨_, List.mem_cons_self,
              good_mono hg Finset.subset_union_left (fun h => by omega)⟩
          · by_cases e' : q = (S2, w2)
            · subst e'
              exact ⟨_, List.mem_cons_self,
                good_mono hg Finset.subset_union_right (fun h => by omega)⟩
            · exact ⟨q, List.mem_cons_of_mem _ ((List.mem_erase_of_ne e').mpr
                ((List.mem_erase_of_ne e).mpr hq)), hg⟩

omit [DecidableEq V] in
theorem eq_sat (a : V → Bool) (v : V) (b : Bool) : LinEqSat a (({v} : Finset V), b) ↔ a v = b := by
  unfold LinEqSat
  cases h : a v <;> cases b <;> simp [Finset.filter_singleton, h]

theorem lin_sat (a : V → Bool) (C : Clause V) : LinClauseSat a (linOfClause C) ↔ ClauseSat a C := by
  unfold LinClauseSat linOfClause ClauseSat
  constructor
  · rintro ⟨q, hq, hs⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨l, hl, (eq_sat a l.1 l.2).mp hs⟩
  · rintro ⟨l, hl, hs⟩
    exact ⟨_, Finset.mem_image_of_mem _ hl, (eq_sat a l.1 l.2).mpr hs⟩

end gen

abbrev J2 : Type := {t : Fin 5 × Fin 5 × Fin 4 // t.1 < t.2.1}

abbrev J : Type := Fin 5 ⊕ J2

def cl : J → Clause (Fin 5 × Fin 4)
  | Sum.inl i => Finset.univ.image (fun j : Fin 4 => ((i, j), true))
  | Sum.inr t => {((t.1.1, t.1.2.2), false), ((t.1.2.1, t.1.2.2), false)}

def asg : J → Fin 5 × Fin 4 → Bool
  | Sum.inl i0 => fun x =>
      decide (x.1 ≠ i0 ∧ x.2.val = if x.1.val < i0.val then x.1.val else x.1.val - 1)
  | Sum.inr t => fun x =>
      if x.1 = t.1.1 ∨ x.1 = t.1.2.1 then decide (x.2 = t.1.2.2)
      else decide (x.2.val =
        if x.1.val - (if t.1.1 < x.1 then 1 else 0) - (if t.1.2.1 < x.1 then 1 else 0) < t.1.2.2.val
        then x.1.val - (if t.1.1 < x.1 then 1 else 0) - (if t.1.2.1 < x.1 then 1 else 0)
        else x.1.val - (if t.1.1 < x.1 then 1 else 0) - (if t.1.2.1 < x.1 then 1 else 0) + 1)

instance (a : Fin 5 × Fin 4 → Bool) (C : Clause (Fin 5 × Fin 4)) : Decidable (ClauseSat a C) := by
  unfold ClauseSat
  infer_instance

theorem key : ∀ k k' : J, k ≠ k' → ClauseSat (asg k) (cl k') := by
  decide +kernel

theorem cardJ : Fintype.card J = 45 := by
  decide +kernel

theorem ax_form {X : LinClause (Fin 5 × Fin 4)}
    (hX : X ∈ (fun C => linOfClause C) '' PHP 5 4) : ∃ k : J, X = linOfClause (cl k) := by
  obtain ⟨C, hC, rfl⟩ := hX
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩
  · exact ⟨Sum.inl i, rfl⟩
  · rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨Sum.inr ⟨(i, i', j), h⟩, rfl⟩
    · exact ⟨Sum.inr ⟨(i', i, j), h⟩, congrArg linOfClause (Finset.pair_comm _ _)⟩

theorem need_all {A : Finset (LinClause (Fin 5 × Fin 4))}
    (hA : ∀ X ∈ A, X ∈ (fun C => linOfClause C) '' PHP 5 4) (hE : Ent A ∅) : 45 ≤ A.card := by
  have hmem : ∀ k : J, linOfClause (cl k) ∈ A ∧ ¬ ClauseSat (asg k) (cl k) := by
    intro k
    have hex : ∃ X ∈ A, ¬ LinClauseSat (asg k) X := by
      by_contra hcon
      push Not at hcon
      obtain ⟨q, hq, _⟩ := hE (asg k) hcon
      simp at hq
    obtain ⟨X, hXA, hX⟩ := hex
    obtain ⟨k', rfl⟩ := ax_form (hA X hXA)
    rw [lin_sat] at hX
    have hk : k = k' := by
      by_contra hne
      exact hX (key k k' hne)
    subst hk
    exact ⟨hXA, hX⟩
  have hinj : Function.Injective (fun k : J => linOfClause (cl k)) := by
    intro k k' h
    by_contra hne
    have h1 := (hmem k).2
    rw [← lin_sat] at h1
    have h' : linOfClause (cl k) = linOfClause (cl k') := h
    rw [h', lin_sat] at h1
    exact h1 (key k k' hne)
  have hsub : Finset.univ.image (fun k : J => linOfClause (cl k)) ⊆ A := by
    intro X hX
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hX
    exact (hmem k).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, cardJ] at hc
  exact hc

theorem pos_form {X : LinClause (Fin 5 × Fin 4)}
    (hX : X ∈ (fun C => linOfClause C) '' PHP 5 4) {f : Finset (Fin 5 × Fin 4)}
    (hf : (f, true) ∈ X) :
    ∃ i : Fin 5, ∃ j : Fin 4, f = {(i, j)} ∧
      X = linOfClause (Finset.univ.image (fun j : Fin 4 => ((i, j), true))) := by
  obtain ⟨C, hC, rfl⟩ := hX
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩
  · simp only [linOfClause, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq,
      exists_exists_eq_and, and_true] at hf
    obtain ⟨j, hj⟩ := hf
    exact ⟨i, j, hj.symm, rfl⟩
  · simp [linOfClause] at hf

theorem pos_unique : ∀ X ∈ (fun C => linOfClause C) '' PHP 5 4,
    ∀ Y ∈ (fun C => linOfClause C) '' PHP 5 4, ∀ f : Finset (Fin 5 × Fin 4),
    (f, true) ∈ X → (f, true) ∈ Y → X = Y := by
  intro X hX Y hY f hfX hfY
  obtain ⟨i, j, h1, rfl⟩ := pos_form hX hfX
  obtain ⟨i', j', h2, rfl⟩ := pos_form hY hfY
  rw [h1] at h2
  have := Finset.singleton_injective h2
  simp only [Prod.mk.injEq] at this
  rw [this.1]

theorem main : ¬ (∃ π : List (LinClause (Fin 5 × Fin 4)),
    IsLinRefutation (PHP 5 4) π ∧ π.length ≤ 89) := by
  rintro ⟨π, ⟨hd, he⟩, hlen⟩
  obtain ⟨P, hP, hsum, hall⟩ := inv_of_deriv pos_unique hd
  obtain ⟨p, hp, A, hAS, hE, hT⟩ := hall ∅ he
  have h1 := need_all (fun X hX => (hP p hp).1 X (hAS hX)) hE
  have h2 := Finset.card_le_card hAS
  have h3 := (hP p hp).2
  have h4 : p.2 ≤ (P.map Prod.snd).sum := List.single_le_sum (fun _ _ => Nat.zero_le _) p.2
    (List.mem_map_of_mem hp)
  obtain ⟨K, hK, _, hK2, _⟩ := hT (by omega)
  have hsub : K ⊆ Finset.univ.image (fun v : Fin 5 × Fin 4 => ({v} : Finset (Fin 5 × Fin 4))) := by
    intro f hf
    obtain ⟨X, hXA, hfX⟩ := hK2 f hf
    obtain ⟨i, j, h, _⟩ := pos_form ((hP p hp).1 X (hAS hXA)) hfX
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, h.symm⟩
  have h5 := Finset.card_le_card hsub
  have h6 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 5 × Fin 4)))
    (f := fun v : Fin 5 × Fin 4 => ({v} : Finset (Fin 5 × Fin 4)))
  have h7 : (Finset.univ : Finset (Fin 5 × Fin 4)).card = 20 := by
    simp
  omega

end PEqualNP.Outside.L_pcx_176

theorem PEqualNP.Outside.L_pcx_176 : ¬ (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 89) :=
  PEqualNP.Outside.L_pcx_176.main
