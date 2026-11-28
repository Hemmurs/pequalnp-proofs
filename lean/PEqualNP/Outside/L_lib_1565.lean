import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1565

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_ext : ∀ (gs : List Gate) (x : List Bool),
    ∃ t, gs.foldl step x = x ++ t ∧ t.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro x; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro x
    obtain ⟨t, h1, h2⟩ := ih (step x g)
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: t, ?_, by simp [h2]⟩
    rw [List.foldl_cons, h1]
    simp [step]

lemma fold_len (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  obtain ⟨t, h1, h2⟩ := fold_ext gs x
  rw [h1, List.length_append, h2]

lemma fold_low (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  obtain ⟨t, h1, h2⟩ := fold_ext gs x
  rw [h1, List.getD_append _ _ _ _ hi]

lemma step_eq (w : List Bool) (g : Gate) :
    step w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

lemma or_eval (w : List Bool) (l : List ℕ) :
    (GateOp.or.eval (l.map fun i => w.getD i false) = true) ↔
      ∃ i ∈ l, w.getD i false = true := by
  simp [GateOp.eval, List.any_eq_true]

lemma ana (p : ℕ) : ∀ gs : List Gate,
    (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) →
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < p + j) →
    ∃ sup : ℕ → Finset ℕ, (∀ w, ∀ i ∈ sup w, i < p) ∧
      (∀ W : Finset ℕ, (∀ w ∈ W, w < p + gs.length) →
        (W.biUnion sup).card ≤ gs.length + W.card) ∧
      ∀ x : List Bool, x.length = p → ∀ w < p + gs.length,
        ((gs.foldl step x).getD w false = true ↔ ∃ i ∈ sup w, x.getD i false = true) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _
    refine ⟨fun w => if w < p then {w} else ∅, ?_, ?_, ?_⟩
    · intro w i hi
      dsimp only at hi
      split_ifs at hi with h
      · rw [Finset.mem_singleton] at hi; omega
      · simp at hi
    · intro W _
      refine (Finset.card_biUnion_le_card_mul W _ 1 ?_).trans (by simp)
      intro w _
      split_ifs <;> simp
    · intro x hx w hw
      have hw' : w < p := by simpa using hw
      simp [hw']
  | append_singleton gs g ih =>
    intro hop hrb
    have hop' : ∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2 :=
      fun g' hg' => hop g' (by simp [hg'])
    have hrb' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < p + j := by
      intro j hj i hi
      refine hrb j (by simp; omega) i ?_
      rwa [List.getD_append _ _ _ _ hj]
    obtain ⟨sup, h1, h2, h3⟩ := ih hop' hrb'
    have hg : ∀ i ∈ g.inputs, i < p + gs.length := by
      intro i hi
      refine hrb gs.length (by simp) i ?_
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simpa using hi
    obtain ⟨hgo, hgl⟩ := hop g (by simp)
    refine ⟨fun w => if w = p + gs.length then g.inputs.toFinset.biUnion sup else sup w,
      ?_, ?_, ?_⟩
    · intro w i hi
      dsimp only at hi
      split_ifs at hi with h
      · obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hi
        exact h1 v i hv
      · exact h1 w i hi
    · intro W hW
      by_cases hn : p + gs.length ∈ W
      · have hsub : (W.biUnion fun w =>
            if w = p + gs.length then g.inputs.toFinset.biUnion sup else sup w) ⊆
            ((W.erase (p + gs.length)) ∪ g.inputs.toFinset).biUnion sup := by
          intro i hi
          obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
          split_ifs at hiw with h
          · obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp hiw
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hiv⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hiw⟩
        have hb := h2 ((W.erase (p + gs.length)) ∪ g.inputs.toFinset) (by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · have := hW w (Finset.mem_of_mem_erase hw)
            have hne := Finset.ne_of_mem_erase hw
            simp at this; omega
          · exact hg w (List.mem_toFinset.mp hw))
        have hc1 : (W.erase (p + gs.length) ∪ g.inputs.toFinset).card ≤ W.card - 1 + 2 := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_erase_of_mem hn]
          have := List.toFinset_card_le g.inputs
          omega
        have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hn⟩
        have := Finset.card_le_card hsub
        simp only [List.length_append, List.length_singleton]
        omega
      · have heq : (W.biUnion fun w =>
            if w = p + gs.length then g.inputs.toFinset.biUnion sup else sup w) =
            W.biUnion sup := by
          refine Finset.biUnion_congr rfl ?_
          intro w hw
          have : w ≠ p + gs.length := fun h => hn (h ▸ hw)
          simp [this]
        rw [heq]
        have := h2 W (by
          intro w hw
          have := hW w hw
          have hne : w ≠ p + gs.length := fun h => hn (h ▸ hw)
          simp at this; omega)
        simp only [List.length_append, List.length_singleton]
        omega
    · intro x hx w hw
      have hlen : (gs.foldl step x).length = p + gs.length := by rw [fold_len, hx]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hwn : w = p + gs.length
      · subst hwn
        simp only [ite_true]
        rw [step_eq, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
        simp only [List.getD_cons_zero, hgo]
        rw [or_eval]
        constructor
        · rintro ⟨i, hi, hv⟩
          obtain ⟨k, hk, hkv⟩ := (h3 x hx i (hg i hi)).mp hv
          exact ⟨k, Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, hk⟩, hkv⟩
        · rintro ⟨k, hk, hkv⟩
          obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp hk
          have hi' := List.mem_toFinset.mp hi
          exact ⟨i, hi', (h3 x hx i (hg i hi')).mpr ⟨k, hki, hkv⟩⟩
      · have hw' : w < p + gs.length := by simp at hw; omega
        simp only [hwn, ite_false]
        rw [step_eq, List.getD_append _ _ _ _ (by omega)]
        exact h3 x hx w hw'


lemma syn (p a : ℕ) (ha : a < p) : ∀ l : List ℕ, (∀ i ∈ l, i < p) →
    ∃ C : Circuit, (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack p C ∧ C.output < p + C.size ∧
      C.size = l.length ∧
      ∀ x : List Bool, x.length = p →
        (C.eval x = true ↔ (x.getD a false = true ∨ ∃ i ∈ l, x.getD i false = true)) := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨⟨[], a⟩, by simp, ?_, by simpa [Circuit.size] using ha, rfl, ?_⟩
    · intro j hj
      simp at hj
    · intro x hx
      simp [Circuit.eval, Circuit.wires]
  | cons b l ih =>
    intro hl
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := ih (fun i hi => hl i (by simp [hi]))
    have hb : b < p := hl b (by simp)
    unfold Circuit.size at h3 h4
    refine ⟨⟨C.gates ++ [⟨GateOp.or, [C.output, b]⟩], p + C.gates.length⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h1 g hg
      · rw [List.mem_singleton] at hg
        subst hg
        simp
    · intro j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
      by_cases hjl : j < C.gates.length
      · rw [List.getD_append _ _ _ _ hjl] at hi
        exact h2 j hjl i hi
      · have hje : j = C.gates.length := by omega
        subst hje
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        simp at hi
        rcases hi with rfl | rfl <;> omega
    · simp [Circuit.size]
    · simp [Circuit.size, h4]
    · intro x hx
      have hlen : (C.gates.foldl step x).length = p + C.gates.length := by rw [fold_len, hx]
      have hev : (C.gates.foldl step x).getD C.output false = C.eval x := rfl
      have hlow : (C.gates.foldl step x).getD b false = x.getD b false :=
        fold_low _ _ _ (by omega)
      show ((C.gates ++ [(⟨GateOp.or, [C.output, b]⟩ : Gate)]).foldl step x).getD
        (p + C.gates.length) false = true ↔ _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, step_eq,
        List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [or_eval]
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
        hev, hlow, h5 x hx]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)

lemma getD_inputs {k : ℕ} (L : List (Finset (Fin k))) (f : Finset (Fin k) → Bool) (j : ℕ) :
    ((L.map f).getD j false = true) ↔ ∃ A, L[j]? = some A ∧ f A = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : L[j]? <;> simp

lemma tapA {k : ℕ} (F : Finset (Finset (Fin k))) (f : Fin k → Finset (Fin k) → Bool)
    (C : Circuit) (h1 : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (h2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack F.card C)
    (_h3 : C.output < F.card + C.size) :
    ∃ T : Finset (Finset (Fin k)), T ⊆ F ∧ T.card ≤ C.size + 1 ∧
      ∀ i : Fin k, (C.eval (F.toList.map (f i)) = true ↔ ∃ A ∈ T, f i A = true) := by
  classical
  obtain ⟨sup, s1, s2, s3⟩ := ana F.card C.gates h1 h2
  refine ⟨(sup C.output).biUnion (fun j => (F.toList[j]?).toFinset), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hA
    rw [Option.mem_toFinset] at hj
    exact Finset.mem_toList.mp (List.mem_of_getElem? hj)
  · refine (Finset.card_biUnion_le_card_mul _ _ 1 ?_).trans ?_
    · intro j _
      rw [Option.card_toFinset]
      cases F.toList[j]? <;> simp
    · have := s2 {C.output} (by simpa [Circuit.size] using _h3)
      rw [Finset.singleton_biUnion] at this
      simpa [Circuit.size, Nat.add_comm] using this
  · intro i
    have hx : (F.toList.map (f i)).length = F.card := by simp
    have := s3 _ hx C.output _h3
    rw [show C.eval (F.toList.map (f i)) = (C.gates.foldl step (F.toList.map (f i))).getD
      C.output false from rfl, this]
    constructor
    · rintro ⟨j, hj, hv⟩
      obtain ⟨A, hA, hfA⟩ := (getD_inputs _ _ _).mp hv
      exact ⟨A, Finset.mem_biUnion.mpr ⟨j, hj, Option.mem_toFinset.mpr hA⟩, hfA⟩
    · rintro ⟨A, hA, hfA⟩
      obtain ⟨j, hj, hjA⟩ := Finset.mem_biUnion.mp hA
      exact ⟨j, hj, (getD_inputs _ _ _).mpr ⟨A, Option.mem_toFinset.mp hjA, hfA⟩⟩

lemma tapB {k : ℕ} (F T : Finset (Finset (Fin k))) (f : Fin k → Finset (Fin k) → Bool)
    (hT : T ⊆ F) (hne : T.Nonempty) :
    ∃ C : Circuit, ((∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack F.card C ∧ C.output < F.card + C.size) ∧
      C.size + 1 ≤ T.card ∧
      ∀ i : Fin k, (C.eval (F.toList.map (f i)) = true ↔ ∃ A ∈ T, f i A = true) := by
  classical
  have hmem : ∀ A, A ∈ T.toList ↔ A ∈ T := fun A => Finset.mem_toList
  have hlenT : T.toList.length = T.card := Finset.length_toList T
  obtain ⟨A0, hA0⟩ := hne
  cases hl : T.toList with
  | nil =>
    rw [← hmem, hl] at hA0
    simp at hA0
  | cons B l =>
    rw [hl] at hlenT
    have hmem' : ∀ A, A ∈ T ↔ A = B ∨ A ∈ l := by
      intro A
      rw [← hmem, hl, List.mem_cons]
    have hF : ∀ A ∈ T, A ∈ F.toList := fun A hA => Finset.mem_toList.mpr (hT hA)
    have hidx : ∀ A ∈ T, F.toList.idxOf A < F.card := by
      intro A hA
      have := List.idxOf_lt_length_of_mem (hF A hA)
      simpa using this
    have hget : ∀ A ∈ T, F.toList[F.toList.idxOf A]? = some A :=
      fun A hA => List.getElem?_idxOf (hF A hA)
    obtain ⟨C, c1, c2, c3, c4, c5⟩ := syn F.card (F.toList.idxOf B)
      (hidx B ((hmem' B).mpr (Or.inl rfl))) (l.map (fun A => F.toList.idxOf A)) (by
        intro i hi
        obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hi
        exact hidx A ((hmem' A).mpr (Or.inr hA)))
    refine ⟨C, ⟨c1, c2, c3⟩, ?_, ?_⟩
    · rw [c4, ← hlenT]
      simp
    · intro i
      rw [c5 _ (by simp)]
      have hval : ∀ A ∈ T, ((F.toList.map (f i)).getD (F.toList.idxOf A) false = true ↔
          f i A = true) := by
        intro A hA
        rw [getD_inputs]
        constructor
        · rintro ⟨A', hA', hf⟩
          rw [hget A hA] at hA'
          cases hA'
          exact hf
        · intro hf
          exact ⟨A, hget A hA, hf⟩
      constructor
      · rintro (h | ⟨j, hj, hv⟩)
        · have hB := (hmem' B).mpr (Or.inl rfl)
          exact ⟨B, hB, (hval B hB).mp h⟩
        · obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hj
          have hA' := (hmem' A).mpr (Or.inr hA)
          exact ⟨A, hA', (hval A hA').mp hv⟩
      · rintro ⟨A, hA, hf⟩
        rcases (hmem' A).mp hA with rfl | hAl
        · exact Or.inl ((hval _ hA).mpr hf)
        · exact Or.inr ⟨_, List.mem_map.mpr ⟨A, hAl, rfl⟩, (hval A hA).mpr hf⟩


lemma costUp {k : ℕ} (F X T : Finset (Finset (Fin k)))
    (d1 : DecidablePred fun A : Finset (Fin k) => ¬ ∃ B ∈ F, A ⊂ B)
    (d2 : DecidableEq (Finset (Fin k)))
    (d3 : DecidablePred fun p : Finset (Fin k) × Finset (Fin k) =>
      p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2)
    (hne : ∀ A ∈ F, A.Nonempty)
    (lam : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hX : X ⊆ F) (hd : ∀ A ∈ F, ∀ B ∈ X, A ⊆ B → A ∈ X) (hTX : T ⊆ X)
    (hcov : ∀ A ∈ X, ∀ i ∈ A, ∃ B ∈ T, i ∈ B) :
    (@Finset.filter _ (fun A => ¬ ∃ B ∈ F, A ⊂ B) d1 X).card +
      (@Finset.filter _ (fun p : Finset (Fin k) × Finset (Fin k) =>
        p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2) d3
        (X.product (@SDiff.sdiff _ (@Finset.instSDiff _ d2) F X))).card ≤ T.card := by
  classical
  let M : Finset (Finset (Fin k)) := X.filter (fun A => ∀ B ∈ X, A ⊆ B → B ⊆ A)
  have hRM : (@Finset.filter _ (fun A => ¬ ∃ B ∈ F, A ⊂ B) d1 X) ⊆ M := by
    intro A hA
    obtain ⟨hAX, hAr⟩ := Finset.mem_filter.mp hA
    refine Finset.mem_filter.mpr ⟨hAX, ?_⟩
    intro B hB hAB
    by_contra hBA
    exact hAr ⟨B, hX hB, hAB, hBA⟩
  have hPM : (@Finset.filter _ (fun p : Finset (Fin k) × Finset (Fin k) =>
        p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2) d3
        (X.product (@SDiff.sdiff _ (@Finset.instSDiff _ d2) F X))).card ≤
      (M \ (@Finset.filter _ (fun A => ¬ ∃ B ∈ F, A ⊂ B) d1 X)).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · rintro ⟨A, C⟩ hp
      obtain ⟨hprod, hAC, hbet⟩ := Finset.mem_filter.mp hp
      obtain ⟨hAX, hC⟩ := Finset.mem_product.mp hprod
      obtain ⟨hCF, hCX⟩ := Finset.mem_sdiff.mp hC
      simp only at hAX hCF hCX hAC hbet
      refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hAX, ?_⟩, ?_⟩)
      · intro B hB hAB
        by_contra hBA
        have hABs : A ⊂ B := ⟨hAB, hBA⟩
        rcases lam B (hX hB) C hCF with h | h | h
        · by_cases hBC : B = C
          · exact hCX (hBC ▸ hB)
          · exact hbet ⟨B, hX hB, hABs, lt_of_le_of_ne h hBC⟩
        · exact hCX (hd C hCF B hB h)
        · obtain ⟨i, hi⟩ := hne A (hX hAX)
          exact Finset.disjoint_left.mp h (hAB hi) (hAC.1 hi)
      · intro hA
        exact (Finset.mem_filter.mp hA).2 ⟨C, hCF, hAC⟩
    · rintro ⟨A, C⟩ hp ⟨A', C'⟩ hp' heq
      simp only at heq
      subst heq
      obtain ⟨hprod, hAC, hbet⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      obtain ⟨hAX, hC⟩ := Finset.mem_product.mp hprod
      obtain ⟨hCF, hCX⟩ := Finset.mem_sdiff.mp hC
      obtain ⟨hprod', hAC', hbet'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp')
      obtain ⟨_, hC'⟩ := Finset.mem_product.mp hprod'
      obtain ⟨hCF', hCX'⟩ := Finset.mem_sdiff.mp hC'
      simp only at hAX hCF hCX hAC hbet hCF' hCX' hAC' hbet'
      have hCC : C = C' := by
        by_contra hne'
        rcases lam C hCF C' hCF' with h | h | h
        · exact hbet' ⟨C, hCF, hAC, lt_of_le_of_ne h hne'⟩
        · exact hbet ⟨C', hCF', hAC', lt_of_le_of_ne h (Ne.symm hne')⟩
        · obtain ⟨i, hi⟩ := hne A (hX hAX)
          exact Finset.disjoint_left.mp h (hAC.1 hi) (hAC'.1 hi)
      rw [hCC]
  have hex : ∀ A ∈ M, ∃ B ∈ T, B ⊆ A ∧ B.Nonempty := by
    intro A hA
    obtain ⟨hAX, hAm⟩ := Finset.mem_filter.mp hA
    obtain ⟨i, hi⟩ := hne A (hX hAX)
    obtain ⟨B, hBT, hiB⟩ := hcov A hAX i hi
    refine ⟨B, hBT, ?_, ⟨i, hiB⟩⟩
    rcases lam A (hX hAX) B (hX (hTX hBT)) with h | h | h
    · exact hAm B (hTX hBT) h
    · exact h
    · exact absurd hiB (Finset.disjoint_left.mp h hi)
  choose! φ hφ using hex
  have hMT : M.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro A hA
      exact Finset.mem_coe.mpr (hφ A (Finset.mem_coe.mp hA)).1
    · intro A hA A' hA' heq
      have hA1 := Finset.mem_coe.mp hA
      have hA2 := Finset.mem_coe.mp hA'
      obtain ⟨_, hs1, i, hi⟩ := hφ A hA1
      obtain ⟨_, hs2, _⟩ := hφ A' hA2
      obtain ⟨hAX, hAm⟩ := Finset.mem_filter.mp hA1
      obtain ⟨hAX', hAm'⟩ := Finset.mem_filter.mp hA2
      rcases lam A (hX hAX) A' (hX hAX') with h | h | h
      · exact Finset.Subset.antisymm h (hAm A' hAX' h)
      · exact Finset.Subset.antisymm (hAm' A hAX h) h
      · exact absurd (hs2 (heq ▸ hi)) (Finset.disjoint_left.mp h (hs1 hi))
  have := Finset.card_sdiff_add_card_eq_card hRM
  omega

lemma costLow {k : ℕ} (F X : Finset (Finset (Fin k)))
    (d1 : DecidablePred fun A : Finset (Fin k) => ¬ ∃ B ∈ F, A ⊂ B)
    (d2 : DecidableEq (Finset (Fin k)))
    (d3 : DecidablePred fun p : Finset (Fin k) × Finset (Fin k) =>
      p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2)
    (_hX : X ⊆ F) :
    ∃ T : Finset (Finset (Fin k)), T ⊆ X ∧ T.card ≤
      (@Finset.filter _ (fun A => ¬ ∃ B ∈ F, A ⊂ B) d1 X).card +
      (@Finset.filter _ (fun p : Finset (Fin k) × Finset (Fin k) =>
        p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2) d3
        (X.product (@SDiff.sdiff _ (@Finset.instSDiff _ d2) F X))).card ∧
      ∀ A ∈ X, ∃ B ∈ T, A ⊆ B := by
  classical
  refine ⟨(@Finset.filter _ (fun A => ¬ ∃ B ∈ F, A ⊂ B) d1 X) ∪
    (@Finset.filter _ (fun p : Finset (Fin k) × Finset (Fin k) =>
        p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2) d3
        (X.product (@SDiff.sdiff _ (@Finset.instSDiff _ d2) F X))).image Prod.fst, ?_, ?_, ?_⟩
  · intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact (Finset.mem_filter.mp hA).1
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  · intro A hA
    obtain ⟨B, hB, hBmax⟩ := Finset.exists_max_image (X.filter (fun B => A ⊆ B))
      Finset.card ⟨A, Finset.mem_filter.mpr ⟨hA, subset_refl _⟩⟩
    obtain ⟨hBX, hAB⟩ := Finset.mem_filter.mp hB
    refine ⟨B, ?_, hAB⟩
    by_cases hroot : ∃ C ∈ F, B ⊂ C
    · obtain ⟨C0, hC0F, hBC0⟩ := hroot
      obtain ⟨C, hC, hCmin⟩ := Finset.exists_min_image (F.filter (fun C => B ⊂ C))
        Finset.card ⟨C0, Finset.mem_filter.mpr ⟨hC0F, hBC0⟩⟩
      obtain ⟨hCF, hBC⟩ := Finset.mem_filter.mp hC
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(B, C), ?_, rfl⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hBX, Finset.mem_sdiff.mpr
        ⟨hCF, ?_⟩⟩, hBC, ?_⟩
      · intro hCX
        have h1 := hBmax C (Finset.mem_filter.mpr ⟨hCX, hAB.trans hBC.1⟩)
        have h2 := Finset.card_lt_card hBC
        omega
      · rintro ⟨B', hB'F, hBB', hB'C⟩
        have h1 := hCmin B' (Finset.mem_filter.mpr ⟨hB'F, hBB'⟩)
        have h2 := Finset.card_lt_card (show B' ⊂ C from hB'C)
        omega
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hBX, hroot⟩)

lemma tf : (true ≤ false) = False :=
  eq_false (fun h => Bool.noConfusion (h rfl))

lemma boolL (h : Bool → Bool → Bool) (t a b : Bool) (va : Bool → Bool → Fin 4 → Bool)
    (hva : ∀ u v, va u v 0 = true ∧ va u v 1 = u ∧ va u v 2 = (!v) ∧ va u v 3 = false)
    (hm : ∀ a a' b b' : Bool, a ≤ a' → b ≤ b' → h a b ≤ h a' b')
    (R : ∀ i j : Fin 4, (∀ u v : Bool, h u v = t → va u v i ≤ va u v j) →
      va a b i ≤ va a b j) : h a b = t := by
  have v0 := fun u v => (hva u v).1
  have v1 := fun u v => (hva u v).2.1
  have v2 := fun u v => (hva u v).2.2.1
  have v3 := fun u v => (hva u v).2.2.2
  have r01 := R 0 1
  have r13 := R 1 3
  have r02 := R 0 2
  have r23 := R 2 3
  have r12 := R 1 2
  have r21 := R 2 1
  have r03 := R 0 3
  simp only [v0, v1, v2, v3, Bool.forall_bool] at r01 r13 r02 r23 r12 r21 r03
  have m1 := hm false false false true (by decide) (by decide)
  have m2 := hm false true false false (by decide) (by decide)
  have m3 := hm false true true true (by decide) (by decide)
  have m4 := hm true true false true (by decide) (by decide)
  clear R hm hva v0 v1 v2 v3
  rcases a with _ | _ <;> rcases b with _ | _ <;>
    generalize h false false = p00 at * <;>
    generalize h false true = p01 at * <;>
    generalize h true false = p10 at * <;>
    generalize h true true = p11 at * <;>
    clear h va <;>
    rcases t with _ | _ <;> rcases p00 with _ | _ <;> rcases p01 with _ | _ <;>
    rcases p10 with _ | _ <;> rcases p11 with _ | _ <;>
    simp_all [tf]


lemma sideA {k : ℕ} (F : Finset (Finset (Fin k)))
    (d1 : DecidablePred fun A : Finset (Fin k) => ¬ ∃ B ∈ F, A ⊂ B)
    (d2 : DecidableEq (Finset (Fin k)))
    (d3 : DecidablePred fun p : Finset (Fin k) × Finset (Fin k) =>
      p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2)
    (d4 : ∀ (i : Fin k) (A : Finset (Fin k)), Decidable (i ∈ A))
    (hne : ∀ A ∈ F, A.Nonempty) (hsing : ∀ i : Fin k, {i} ∈ F)
    (lam : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (C : Circuit) (h1 : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (h2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack F.card C)
    (h3 : C.output < F.card + C.size) :
    ∃ X : Finset (Finset (Fin k)), X ⊆ F ∧ (∀ A ∈ F, ∀ B ∈ X, A ⊆ B → A ∈ X) ∧
      (@Finset.filter _ (fun A => ¬ ∃ B ∈ F, A ⊂ B) d1 X).card +
      (@Finset.filter _ (fun p : Finset (Fin k) × Finset (Fin k) =>
        p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2) d3
        (X.product (@SDiff.sdiff _ (@Finset.instSDiff _ d2) F X))).card ≤ C.size + 1 ∧
      ∀ i : Fin k, (C.eval (F.toList.map (fun A => @decide (i ∈ A) (d4 i A))) = true ↔
        {i} ∈ X) := by
  classical
  obtain ⟨T, hTF, hTc, hTe⟩ := tapA F (fun i A => @decide (i ∈ A) (d4 i A)) C h1 h2 h3
  have hmemX : ∀ A, A ∈ F.filter (fun A => ∀ i ∈ A, ∃ B ∈ T, i ∈ B) ↔
      A ∈ F ∧ ∀ i ∈ A, ∃ B ∈ T, i ∈ B := fun A => Finset.mem_filter
  refine ⟨F.filter (fun A => ∀ i ∈ A, ∃ B ∈ T, i ∈ B), Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · intro A hA B hB hAB
    exact (hmemX A).mpr ⟨hA, fun i hi => ((hmemX B).mp hB).2 i (hAB hi)⟩
  · refine (costUp F _ T d1 d2 d3 hne lam (Finset.filter_subset _ _) ?_ ?_ ?_).trans hTc
    · intro A hA B hB hAB
      exact (hmemX A).mpr ⟨hA, fun i hi => ((hmemX B).mp hB).2 i (hAB hi)⟩
    · intro B hB
      exact (hmemX B).mpr ⟨hTF hB, fun i hi => ⟨B, hB, hi⟩⟩
    · intro A hA
      exact ((hmemX A).mp hA).2
  · intro i
    rw [hTe i, hmemX]
    constructor
    · rintro ⟨A, hA, hi⟩
      refine ⟨hsing i, ?_⟩
      intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact ⟨A, hA, of_decide_eq_true hi⟩
    · rintro ⟨_, hi⟩
      obtain ⟨B, hB, hiB⟩ := hi i (Finset.mem_singleton_self i)
      exact ⟨B, hB, decide_eq_true hiB⟩

lemma sideB {k : ℕ} (F X : Finset (Finset (Fin k)))
    (d1 : DecidablePred fun A : Finset (Fin k) => ¬ ∃ B ∈ F, A ⊂ B)
    (d2 : DecidableEq (Finset (Fin k)))
    (d3 : DecidablePred fun p : Finset (Fin k) × Finset (Fin k) =>
      p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2)
    (d4 : ∀ (i : Fin k) (A : Finset (Fin k)), Decidable (i ∈ A))
    (hsing : ∀ i : Fin k, {i} ∈ F)
    (hX : X ⊆ F) (hd : ∀ A ∈ F, ∀ B ∈ X, A ⊆ B → A ∈ X) (r : Fin k) (hr : {r} ∈ X) :
    ∃ C : Circuit, ((∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack F.card C ∧ C.output < F.card + C.size) ∧
      C.size + 1 ≤ (@Finset.filter _ (fun A => ¬ ∃ B ∈ F, A ⊂ B) d1 X).card +
      (@Finset.filter _ (fun p : Finset (Fin k) × Finset (Fin k) =>
        p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2) d3
        (X.product (@SDiff.sdiff _ (@Finset.instSDiff _ d2) F X))).card ∧
      ∀ i : Fin k, (C.eval (F.toList.map (fun A => @decide (i ∈ A) (d4 i A))) = true ↔
        {i} ∈ X) := by
  obtain ⟨T, hTX, hTc, hTcov⟩ := costLow F X d1 d2 d3 hX
  obtain ⟨B0, hB0, _⟩ := hTcov _ hr
  obtain ⟨C, hleg, hsz, hev⟩ := tapB F T (fun i A => @decide (i ∈ A) (d4 i A))
    (hTX.trans hX) ⟨B0, hB0⟩
  refine ⟨C, hleg, hsz.trans hTc, ?_⟩
  intro i
  rw [hev i]
  constructor
  · rintro ⟨A, hA, hi⟩
    exact hd _ (hsing i) A (hTX hA) (Finset.singleton_subset_iff.mpr (of_decide_eq_true hi))
  · intro hi
    obtain ⟨B, hB, hiB⟩ := hTcov _ hi
    exact ⟨B, hB, decide_eq_true (Finset.singleton_subset_iff.mp hiB)⟩

end PEqualNP.Outside.L_lib_1565

theorem PEqualNP.Outside.L_lib_1565 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
let bank := fun {k : Nat} (F : Finset (Finset (Fin k))) =>
  (∀ A ∈ F, A.Nonempty) ∧ (∀ i : Fin k, {i} ∈ F) ∧
    ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
let inputs := fun {k : Nat} (F : Finset (Finset (Fin k))) (i : Fin k) =>
  F.toList.map (fun A => decide (i ∈ A))
let legal := fun (p : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack p C ∧ C.output < p + C.size
let down := fun {k : Nat} (F X : Finset (Finset (Fin k))) =>
  ∀ A ∈ F, ∀ B ∈ X, A ⊆ B → A ∈ X
let cost := fun {k : Nat} (F X : Finset (Finset (Fin k))) =>
  (X.filter (fun A => ¬ ∃ B ∈ F, A ⊂ B)).card +
  ((X.product (F \ X)).filter (fun p =>
    p.1 ⊂ p.2 ∧ ¬ ∃ B ∈ F, p.1 ⊂ B ∧ B ⊂ p.2)).card
let valAt := fun (a b : Bool) (i : Fin 4) =>
  if i.val = 0 then true else if i.val = 1 then a else if i.val = 2 then !b else false
let respects := fun (h : Bool → Bool → Bool) (t a b : Bool) =>
  ∀ i j : Fin 4, (∀ u v : Bool, h u v = t → valAt u v i ≤ valAt u v j) →
    valAt a b i ≤ valAt a b j
∀ (m n s : Nat) (F : Finset (Finset (Fin m))) (G : Finset (Finset (Fin n)))
  (r : Fin m) (c : Fin n) (h : Fin m × Fin n → Bool → Bool → Bool)
  (t : Fin m × Fin n → Bool) (D : Finset (Fin m × Fin n)),
  bank F → bank G →
  (∀ (e : Fin m × Fin n) (a a' b b' : Bool),
    a ≤ a' → b ≤ b' → h e a b ≤ h e a' b') →
  ((∃ P Q : PEqualNP.CircuitLowerBounds.Circuit,
    legal F.card P ∧ legal G.card Q ∧ P.size + Q.size ≤ s ∧
    P.eval (inputs F r) = true ∧ Q.eval (inputs G c) = true ∧
    ∀ e ∈ D, h e (P.eval (inputs F e.1)) (Q.eval (inputs G e.2)) = t e) ↔
  ∃ X ⊆ F, ∃ Y ⊆ G, down F X ∧ down G Y ∧ {r} ∈ X ∧ {c} ∈ Y ∧
    cost F X + cost G Y ≤ s + 2 ∧ ∀ e ∈ D,
      respects (h e) (t e) (decide ({e.1} ∈ X)) (decide ({e.2} ∈ Y)))) := by
  dsimp only
  intro m n s F G r c h t D hF hG hmono
  have hva : ∀ u v : Bool,
      (@ite Bool ((0 : Fin 4).val = 0) (Classical.propDecidable _) true
        (@ite Bool ((0 : Fin 4).val = 1) (Classical.propDecidable _) u
          (@ite Bool ((0 : Fin 4).val = 2) (Classical.propDecidable _) (!v) false)) = true) ∧
      (@ite Bool ((1 : Fin 4).val = 0) (Classical.propDecidable _) true
        (@ite Bool ((1 : Fin 4).val = 1) (Classical.propDecidable _) u
          (@ite Bool ((1 : Fin 4).val = 2) (Classical.propDecidable _) (!v) false)) = u) ∧
      (@ite Bool ((2 : Fin 4).val = 0) (Classical.propDecidable _) true
        (@ite Bool ((2 : Fin 4).val = 1) (Classical.propDecidable _) u
          (@ite Bool ((2 : Fin 4).val = 2) (Classical.propDecidable _) (!v) false)) = (!v)) ∧
      (@ite Bool ((3 : Fin 4).val = 0) (Classical.propDecidable _) true
        (@ite Bool ((3 : Fin 4).val = 1) (Classical.propDecidable _) u
          (@ite Bool ((3 : Fin 4).val = 2) (Classical.propDecidable _) (!v) false)) = false) := by
    intro u v
    simp
  constructor
  · rintro ⟨P, Q, hP, hQ, hs, hPr, hQc, hD⟩
    obtain ⟨X, hXF, hXd, hXc, hXe⟩ := PEqualNP.Outside.L_lib_1565.sideA F
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      hF.1 hF.2.1 hF.2.2 P hP.1 hP.2.1 hP.2.2
    obtain ⟨Y, hYG, hYd, hYc, hYe⟩ := PEqualNP.Outside.L_lib_1565.sideA G
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      hG.1 hG.2.1 hG.2.2 Q hQ.1 hQ.2.1 hQ.2.2
    refine ⟨X, hXF, Y, hYG, hXd, hYd, (hXe r).mp hPr, (hYe c).mp hQc, ?_, ?_⟩
    · have := Nat.add_le_add hXc hYc
      omega
    · intro e he i j H
      have e1 : @decide ({e.1} ∈ X) (Classical.propDecidable _) =
          P.eval (F.toList.map (fun A => @decide (e.1 ∈ A) (Classical.propDecidable _))) := by
        rw [Bool.eq_iff_iff, hXe e.1]
        simp
      have e2 : @decide ({e.2} ∈ Y) (Classical.propDecidable _) =
          Q.eval (G.toList.map (fun A => @decide (e.2 ∈ A) (Classical.propDecidable _))) := by
        rw [Bool.eq_iff_iff, hYe e.2]
        simp
      rw [e1, e2]
      exact H _ _ (hD e he)
  · rintro ⟨X, hXF, Y, hYG, hXd, hYd, hrX, hcY, hcost, hresp⟩
    obtain ⟨P, hP, hPs, hPe⟩ := PEqualNP.Outside.L_lib_1565.sideB F X
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      hF.2.1 hXF hXd r hrX
    obtain ⟨Q, hQ, hQs, hQe⟩ := PEqualNP.Outside.L_lib_1565.sideB G Y
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _) (fun _ _ => Classical.propDecidable _)
      hG.2.1 hYG hYd c hcY
    refine ⟨P, Q, hP, hQ, ?_, (hPe r).mpr hrX, (hQe c).mpr hcY, ?_⟩
    · have := Nat.add_le_add hPs hQs
      omega
    · intro e he
      have e1 : P.eval (F.toList.map (fun A => @decide (e.1 ∈ A) (Classical.propDecidable _)))
          = @decide ({e.1} ∈ X) (Classical.propDecidable _) := by
        rw [Bool.eq_iff_iff, hPe e.1]
        simp
      have e2 : Q.eval (G.toList.map (fun A => @decide (e.2 ∈ A) (Classical.propDecidable _)))
          = @decide ({e.2} ∈ Y) (Classical.propDecidable _) := by
        rw [Bool.eq_iff_iff, hQe e.2]
        simp
      rw [e1, e2]
      exact PEqualNP.Outside.L_lib_1565.boolL (h e) (t e) _ _ _ hva (hmono e) (hresp e he)
