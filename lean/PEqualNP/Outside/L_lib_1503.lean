import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1503

open Classical

abbrev V (q : Nat) := Finset (Fin q)

noncomputable def patL {q : Nat} (F : Finset (V q × V q)) (a : Fin q) : Finset (V q × V q) :=
  F.filter (fun x => a ∈ x.1)

noncomputable def patR {q : Nat} (F : Finset (V q × V q)) (b : Fin q) : Finset (V q × V q) :=
  F.filter (fun x => b ∈ x.2)

noncomputable def supL {q : Nat} (F : Finset (V q × V q)) (S : Finset (V q × V q)) : Finset (Fin q) :=
  Finset.univ.filter (fun a => S ⊆ patL F a)

noncomputable def supR {q : Nat} (F : Finset (V q × V q)) (S : Finset (V q × V q)) : Finset (Fin q) :=
  Finset.univ.filter (fun b => S ⊆ patR F b)

noncomputable def exactL {q : Nat} (F : Finset (V q × V q)) (S : Finset (V q × V q)) : Finset (Fin q) :=
  Finset.univ.filter (fun a => patL F a = S)

noncomputable def exactR {q : Nat} (F : Finset (V q × V q)) (S : Finset (V q × V q)) : Finset (Fin q) :=
  Finset.univ.filter (fun b => patR F b = S)

lemma mem_supL_iff {q : Nat} {F S : Finset (V q × V q)} (hSF : S ⊆ F) (a : Fin q) :
    a ∈ supL F S ↔ ∀ x ∈ S, a ∈ x.1 := by
  simp only [supL, patL, Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff]
  constructor
  · intro h x hx
    exact (h hx).2
  · intro h x hx
    exact ⟨hSF hx, h x hx⟩

lemma mem_supR_iff {q : Nat} {F S : Finset (V q × V q)} (hSF : S ⊆ F) (b : Fin q) :
    b ∈ supR F S ↔ ∀ x ∈ S, b ∈ x.2 := by
  simp only [supR, patR, Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff]
  constructor
  · intro h x hx
    exact (h hx).2
  · intro h x hx
    exact ⟨hSF hx, h x hx⟩

lemma sup_inter_mem {q : Nat} {F : Finset (V q × V q)}
    (hS : ∀ x ∈ F, ∀ y ∈ F, (x.1 ∩ y.1, x.2 ∩ y.2) ∈ F) :
    ∀ S : Finset (V q × V q), S ⊆ F → S.Nonempty → (supL F S, supR F S) ∈ F := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ hne
    exact False.elim (Finset.not_nonempty_empty hne)
  | insert x T hxT ih =>
    intro hsub _
    have hxF : x ∈ F := hsub (Finset.mem_insert_self x T)
    have hTF : T ⊆ F := fun y hy => hsub (Finset.mem_insert_of_mem hy)
    by_cases hT : T.Nonempty
    · have hih := ih hTF hT
      have h1 : supL F (insert x T) = x.1 ∩ supL F T := by
        ext a
        rw [mem_supL_iff hsub, Finset.mem_inter, mem_supL_iff hTF]
        constructor
        · intro h
          exact ⟨h x (Finset.mem_insert_self x T), fun y hy => h y (Finset.mem_insert_of_mem hy)⟩
        · intro ⟨h1, h2⟩ y hy
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · exact h1
          · exact h2 y hyT
      have h2 : supR F (insert x T) = x.2 ∩ supR F T := by
        ext b
        rw [mem_supR_iff hsub, Finset.mem_inter, mem_supR_iff hTF]
        constructor
        · intro h
          exact ⟨h x (Finset.mem_insert_self x T), fun y hy => h y (Finset.mem_insert_of_mem hy)⟩
        · intro ⟨h1, h2⟩ y hy
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · exact h1
          · exact h2 y hyT
      rw [h1, h2]
      exact hS x hxF (supL F T, supR F T) hih
    · rw [Finset.not_nonempty_iff_eq_empty] at hT
      subst hT
      have h1 : supL F (insert x ∅) = x.1 := by
        ext a
        rw [mem_supL_iff hsub]
        simp
      have h2 : supR F (insert x ∅) = x.2 := by
        ext b
        rw [mem_supR_iff hsub]
        simp
      rw [h1, h2]
      exact hxF

lemma sup_card_eq {q : Nat} {F : Finset (V q × V q)}
    (hS : ∀ x ∈ F, ∀ y ∈ F, (x.1 ∩ y.1, x.2 ∩ y.2) ∈ F)
    (hR : ∀ x ∈ F, x.1.card = x.2.card)
    (S : Finset (V q × V q)) (hSF : S ⊆ F) :
    (supL F S).card = (supR F S).card := by
  by_cases hne : S.Nonempty
  · exact hR (supL F S, supR F S) (sup_inter_mem hS S hSF hne)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have h1 : supL F ∅ = Finset.univ := by
      ext a
      simp [supL]
    have h2 : supR F ∅ = Finset.univ := by
      ext b
      simp [supR]
    rw [h1, h2]

lemma supL_card_decomp {q : Nat} (F S : Finset (V q × V q)) (hSF : S ⊆ F) :
    (supL F S).card = (exactL F S).card +
      ∑ T ∈ F.powerset.filter (fun T => S ⊂ T), (exactL F T).card := by
  have hmaps : ∀ a ∈ supL F S, patL F a ∈ F.powerset.filter (fun T => S ⊆ T) := by
    intro a ha
    rw [supL, Finset.mem_filter] at ha
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, ha.2⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := patL F) hmaps
  have hterm : ∀ T ∈ F.powerset.filter (fun T => S ⊆ T),
      ((supL F S).filter (fun a => patL F a = T)).card = (exactL F T).card := by
    intro T hT
    rw [Finset.mem_filter] at hT
    congr 1
    ext a
    simp only [supL, exactL, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by rw [h]; exact hT.2, h⟩
  rw [hfib, Finset.sum_congr rfl hterm]
  have hSmem : S ∈ F.powerset.filter (fun T => S ⊆ T) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSF, Finset.Subset.refl S⟩
  rw [← Finset.add_sum_erase _ _ hSmem]
  congr 1
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset, Finset.ssubset_iff_subset_ne]
    constructor
    · intro ⟨hne, hTF, hST⟩
      exact ⟨hTF, hST, Ne.symm hne⟩
    · intro ⟨hTF, hST, hne⟩
      exact ⟨Ne.symm hne, hTF, hST⟩
  · intro _ _; rfl

lemma supR_card_decomp {q : Nat} (F S : Finset (V q × V q)) (hSF : S ⊆ F) :
    (supR F S).card = (exactR F S).card +
      ∑ T ∈ F.powerset.filter (fun T => S ⊂ T), (exactR F T).card := by
  have hmaps : ∀ b ∈ supR F S, patR F b ∈ F.powerset.filter (fun T => S ⊆ T) := by
    intro b hb
    rw [supR, Finset.mem_filter] at hb
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, hb.2⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := patR F) hmaps
  have hterm : ∀ T ∈ F.powerset.filter (fun T => S ⊆ T),
      ((supR F S).filter (fun b => patR F b = T)).card = (exactR F T).card := by
    intro T hT
    rw [Finset.mem_filter] at hT
    congr 1
    ext b
    simp only [supR, exactR, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by rw [h]; exact hT.2, h⟩
  rw [hfib, Finset.sum_congr rfl hterm]
  have hSmem : S ∈ F.powerset.filter (fun T => S ⊆ T) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSF, Finset.Subset.refl S⟩
  rw [← Finset.add_sum_erase _ _ hSmem]
  congr 1
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset, Finset.ssubset_iff_subset_ne]
    constructor
    · intro ⟨hne, hTF, hST⟩
      exact ⟨hTF, hST, Ne.symm hne⟩
    · intro ⟨hTF, hST, hne⟩
      exact ⟨Ne.symm hne, hTF, hST⟩
  · intro _ _; rfl

lemma exact_card_eq_aux {q : Nat} {F : Finset (V q × V q)}
    (hS : ∀ x ∈ F, ∀ y ∈ F, (x.1 ∩ y.1, x.2 ∩ y.2) ∈ F)
    (hR : ∀ x ∈ F, x.1.card = x.2.card) :
    ∀ k : Nat, ∀ S : Finset (V q × V q), S ⊆ F → F.card - S.card = k →
      (exactL F S).card = (exactR F S).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro S hSF hk
    have hsup := sup_card_eq hS hR S hSF
    rw [supL_card_decomp F S hSF, supR_card_decomp F S hSF] at hsup
    have hsum :
        ∑ T ∈ F.powerset.filter (fun T => S ⊂ T), (exactL F T).card =
        ∑ T ∈ F.powerset.filter (fun T => S ⊂ T), (exactR F T).card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      have hlt : S.card < T.card := Finset.card_lt_card hT.2
      have hle : T.card ≤ F.card := Finset.card_le_card hT.1
      have hdk : F.card - T.card < k := by omega
      exact ih (F.card - T.card) hdk T hT.1 rfl
    omega

lemma exact_card_eq {q : Nat} {F : Finset (V q × V q)}
    (hS : ∀ x ∈ F, ∀ y ∈ F, (x.1 ∩ y.1, x.2 ∩ y.2) ∈ F)
    (hR : ∀ x ∈ F, x.1.card = x.2.card)
    (S : Finset (V q × V q)) :
    (exactL F S).card = (exactR F S).card := by
  by_cases hSF : S ⊆ F
  · exact exact_card_eq_aux hS hR (F.card - S.card) S hSF rfl
  · have h1 : exactL F S = ∅ := by
      ext a
      simp only [exactL, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro heq
      apply hSF
      rw [← heq]
      exact Finset.filter_subset _ _
    have h2 : exactR F S = ∅ := by
      ext b
      simp only [exactR, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro heq
      apply hSF
      rw [← heq]
      exact Finset.filter_subset _ _
    rw [h1, h2]

lemma fiber_equiv_left_inv {α β : Type*} {p : α → β} {q : α → β}
    (φ : ∀ s : β, {a : α // p a = s} ≃ {b : α // q b = s})
    (a : α) :
    ((φ (q (φ (p a) ⟨a, rfl⟩).val)).symm ⟨(φ (p a) ⟨a, rfl⟩).val, rfl⟩).val = a := by
  have hcast : ∀ (y : α) (s₁ s₂ : β) (hs : s₁ = s₂) (h1 : q y = s₁) (h2 : q y = s₂),
      ((φ s₁).symm ⟨y, h1⟩).val = ((φ s₂).symm ⟨y, h2⟩).val := by
    intro y s₁ s₂ hs h1 h2
    subst hs
    rfl
  let y := φ (p a) ⟨a, rfl⟩
  have h1 := hcast y.val (q y.val) (p a) y.property rfl y.property
  rw [h1]
  exact congrArg Subtype.val ((φ (p a)).symm_apply_apply ⟨a, rfl⟩)

lemma fiber_equiv_right_inv {α β : Type*} {p : α → β} {q : α → β}
    (φ : ∀ s : β, {a : α // p a = s} ≃ {b : α // q b = s})
    (b : α) :
    (φ (p ((φ (q b)).symm ⟨b, rfl⟩).val) ⟨((φ (q b)).symm ⟨b, rfl⟩).val, rfl⟩).val = b := by
  have hcast : ∀ (x : α) (s₁ s₂ : β) (hs : s₁ = s₂) (h1 : p x = s₁) (h2 : p x = s₂),
      (φ s₁ ⟨x, h1⟩).val = (φ s₂ ⟨x, h2⟩).val := by
    intro x s₁ s₂ hs h1 h2
    subst hs
    rfl
  let x := (φ (q b)).symm ⟨b, rfl⟩
  have h1 := hcast x.val (p x.val) (q b) x.property rfl x.property
  rw [h1]
  exact congrArg Subtype.val ((φ (q b)).apply_symm_apply ⟨b, rfl⟩)

lemma part1 {q : Nat} (F : Finset (V q × V q))
    (hS : ∀ x ∈ F, ∀ y ∈ F, (x.1 ∩ y.1, x.2 ∩ y.2) ∈ F)
    (hR : ∀ x ∈ F, x.1.card = x.2.card) :
    ∃ e : Equiv.Perm (Fin q), ∀ x ∈ F, x.1.image e = x.2 := by
  have hcard : ∀ S : Finset (V q × V q),
      Fintype.card {a : Fin q // patL F a = S} = Fintype.card {b : Fin q // patR F b = S} := by
    intro S
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact exact_card_eq hS hR S
  let φ : ∀ S : Finset (V q × V q),
      {a : Fin q // patL F a = S} ≃ {b : Fin q // patR F b = S} :=
    fun S => Fintype.equivOfCardEq (hcard S)
  let e : Equiv.Perm (Fin q) :=
    { toFun := fun a => (φ (patL F a) ⟨a, rfl⟩).val
      invFun := fun b => ((φ (patR F b)).symm ⟨b, rfl⟩).val
      left_inv := fiber_equiv_left_inv φ
      right_inv := fiber_equiv_right_inv φ }
  refine ⟨e, ?_⟩
  intro x hx
  ext b
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hpat : patR F (e a) = patL F a := (φ (patL F a) ⟨a, rfl⟩).property
    have hxL : x ∈ patL F a := by
      rw [patL, Finset.mem_filter]
      exact ⟨hx, ha⟩
    rw [← hpat, patR, Finset.mem_filter] at hxL
    exact hxL.2
  · intro hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    have hpat : patL F (e.symm b) = patR F b := ((φ (patR F b)).symm ⟨b, rfl⟩).property
    have hxR : x ∈ patR F b := by
      rw [patR, Finset.mem_filter]
      exact ⟨hx, hb⟩
    rw [← hpat, patL, Finset.mem_filter] at hxR
    exact hxR.2

lemma part1_any {q : Nat} (inst : DecidableEq (Fin q))
    (F : Finset (V q × V q))
    (hS : ∀ x ∈ F, ∀ y ∈ F,
      (@min (V q) (@Finset.instMin (Fin q) inst) x.1 y.1,
       @min (V q) (@Finset.instMin (Fin q) inst) x.2 y.2) ∈ F)
    (hR : ∀ x ∈ F, x.1.card = x.2.card) :
    ∃ e : Equiv.Perm (Fin q), ∀ x ∈ F, @Finset.image (Fin q) (Fin q) inst e x.1 = x.2 := by
  have hS' : ∀ x ∈ F, ∀ y ∈ F,
      (@min (V q) (@Finset.instMin (Fin q) (instDecidableEqFin q)) x.1 y.1,
       @min (V q) (@Finset.instMin (Fin q) (instDecidableEqFin q)) x.2 y.2) ∈ F := by
    intro x hx y hy
    have hxy := hS x hx y hy
    have h1 : @min (V q) (@Finset.instMin (Fin q) (instDecidableEqFin q)) x.1 y.1 =
        @min (V q) (@Finset.instMin (Fin q) inst) x.1 y.1 := by
      ext z; simp only [Finset.mem_inter]
    have h2 : @min (V q) (@Finset.instMin (Fin q) (instDecidableEqFin q)) x.2 y.2 =
        @min (V q) (@Finset.instMin (Fin q) inst) x.2 y.2 := by
      ext z; simp only [Finset.mem_inter]
    rw [h1, h2]
    exact hxy
  rcases part1 F hS' hR with ⟨e, he⟩
  refine ⟨e, fun x hx => ?_⟩
  have hxe := he x hx
  ext b
  have hb := Finset.ext_iff.mp hxe b
  simpa only [Finset.mem_image] using hb

end PEqualNP.Outside.L_lib_1503

theorem PEqualNP.Outside.L_lib_1503 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ q : Nat,
let V := Finset (Fin q)
let stable := fun (F : Finset (V × V)) =>
  ∀ x ∈ F, ∀ y ∈ F, (x.1 ∩ y.1,x.2 ∩ y.2) ∈ F
let ranked := fun (F : Finset (V × V)) => ∀ x ∈ F, x.1.card=x.2.card
(∀ F : Finset (V × V), stable F → ranked F →
  ∃ e : Equiv.Perm (Fin q), ∀ x ∈ F, x.1.image e=x.2) ∧
∀ M : Nat,
(∃ U : Fin M → Finset (V × V), (∀ i, stable (U i) ∧ ranked (U i)) ∧
  ∀ A B : V, A.card=B.card → ∃ i, (A,B) ∈ U i) ↔
∃ e : Fin M → Equiv.Perm (Fin q), ∀ A B : V, A.card=B.card → ∃ i, A.image (e i)=B) := by
  dsimp only
  intro q
  refine ⟨?_, fun M => ⟨?_, ?_⟩⟩
  · intro F hS hR
    exact PEqualNP.Outside.L_lib_1503.part1_any (fun a b => Classical.propDecidable (a = b)) F hS hR
  · rintro ⟨U, hU, hcov⟩
    choose e he using fun i =>
      PEqualNP.Outside.L_lib_1503.part1_any (fun a b => Classical.propDecidable (a = b)) (U i) (hU i).1 (hU i).2
    refine ⟨e, fun A B hAB => ?_⟩
    rcases hcov A B hAB with ⟨i, hi⟩
    exact ⟨i, he i (A, B) hi⟩
  · rintro ⟨e, he⟩
    refine ⟨fun i => Finset.univ.image (fun A : Finset (Fin q) => (A, A.image (e i))), ?_, ?_⟩
    · intro i
      refine ⟨?_, ?_⟩
      · intro x hx y hy
        rw [Finset.mem_image] at hx hy ⊢
        rcases hx with ⟨A, _, rfl⟩
        rcases hy with ⟨B, _, rfl⟩
        refine ⟨A ∩ B, Finset.mem_univ _, ?_⟩
        apply Prod.ext
        · ext z; simp only [Finset.mem_inter]
        · ext z; simp only [Finset.mem_image, Finset.mem_inter]
          constructor
          · rintro ⟨a, ⟨haA, haB⟩, rfl⟩
            exact ⟨⟨a, haA, rfl⟩, ⟨a, haB, rfl⟩⟩
          · rintro ⟨⟨a, haA, h1⟩, ⟨b, hbB, h2⟩⟩
            have hab : a = b := (e i).injective (h1.trans h2.symm)
            subst hab
            exact ⟨a, ⟨haA, hbB⟩, h1⟩
      · intro x hx
        rw [Finset.mem_image] at hx
        rcases hx with ⟨A, _, rfl⟩
        exact (Finset.card_image_of_injective A (e i).injective).symm
    · intro A B hAB
      rcases he A B hAB with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [Finset.mem_image]
      refine ⟨A, Finset.mem_univ _, Prod.ext rfl ?_⟩
      ext z
      have hz := Finset.ext_iff.mp hi z
      simpa only [Finset.mem_image] using hz
