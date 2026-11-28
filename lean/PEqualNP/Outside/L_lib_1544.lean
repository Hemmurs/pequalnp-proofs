import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1544

theorem count (n : Nat) (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    (P : Finset (Fin n))
    (h3 : ∀ v, v ∉ P → (∃ w, G.Adj v w) → 3 ≤ (G.neighborSet v).ncard)
    [DecidablePred fun v => v ∉ P ∧ ∃ w, G.Adj v w] :
    (Finset.univ.filter (fun v => v ∉ P ∧ ∃ w, G.Adj v w)).card ≤ P.card := by
  classical
  let W : Set (Fin n) := {v | ∃ w, G.Adj v w}
  by_cases hW : Nonempty W
  swap
  · have : (Finset.univ.filter (fun v => v ∉ P ∧ ∃ w, G.Adj v w)) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨_, hw⟩
      exact hW ⟨⟨v, hw⟩⟩
    rw [this]
    simp
  let H := G.induce W
  have hH : H.IsAcyclic := hG.induce W
  have hE := hH.ncard_edgeSet_add_one_le_card
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hEc : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have hdeg : ∀ w : W, (G.neighborSet w.val).ncard = H.degree w := by
    intro w
    have : G.neighborSet w.val = Subtype.val '' (H.neighborSet w) := by
      ext a
      simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
      constructor
      · intro ha
        exact ⟨⟨a, ⟨w.val, ha.symm⟩⟩, ha, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact hb
    rw [this, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_eq_toFinset_card']
    rfl
  have hlow : ∀ w : W, (if w.val ∈ P then 1 else 3) ≤ H.degree w := by
    intro w
    rw [← hdeg w]
    split_ifs with hp
    · obtain ⟨a, ha⟩ := w.2
      exact Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite _)).2 ⟨a, ha⟩)
    · exact h3 w.val hp w.2
  have hs : ∑ w : W, (if w.val ∈ P then 1 else 3) ≤ ∑ w : W, H.degree w :=
    Finset.sum_le_sum (fun w _ => hlow w)
  have hsplit : ∑ w : W, (if w.val ∈ P then 1 else 3) =
      Fintype.card W + 2 * (Finset.univ.filter (fun w : W => w.val ∉ P)).card := by
    have h1 : ∀ w : W, (if w.val ∈ P then 1 else 3) = 1 + 2 * (if w.val ∉ P then 1 else 0) := by
      intro w
      by_cases hp : w.val ∈ P <;> simp [hp]
    simp_rw [h1]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp
  have hWle : Fintype.card W ≤ (Finset.univ.filter (fun w : W => w.val ∉ P)).card + P.card := by
    have h1 : (Finset.univ.filter (fun w : W => w.val ∈ P)).card ≤ P.card := by
      apply Finset.card_le_card_of_injOn (fun w => w.val)
      · intro w hw
        simpa using hw
      · intro a _ b _ h
        exact Subtype.ext h
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset W))
      (fun w : W => w.val ∈ P)
    rw [Finset.card_univ] at h2
    omega
  have hQ : (Finset.univ.filter (fun v => v ∉ P ∧ ∃ w, G.Adj v w)).card =
      (Finset.univ.filter (fun w : W => w.val ∉ P)).card := by
    symm
    apply Finset.card_bij (fun w _ => w.val)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨hw, w.2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact ⟨⟨v, hv.2⟩, by simpa using hv.1, rfl⟩
  rw [Nat.card_eq_fintype_card] at hE
  omega

theorem red (n k : Nat) (port : Fin k ↪ Fin n) :
    ∀ (m : Nat) (G : SimpleGraph (Fin n)), G.IsAcyclic →
    ({v | ∃ w, G.Adj v w} : Set (Fin n)).ncard ≤ m →
    ∃ S : Finset (Fin n), (∀ i, port i ∈ S) ∧ S.card ≤ 2*k ∧
    ∀ x : Fin k → Fin 3,
      (∃ d : Fin n → Fin 3, (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → d u ≠ d v) ∧ ∀ i, d (port i) = x i) →
      ∃ c : Fin n → Fin 3, (∀ u v, G.Adj u v → c u ≠ c v) ∧ ∀ i, c (port i) = x i := by
  classical
  intro m
  induction m with
  | zero =>
    intro G hG hm
    have hno : ∀ v w, ¬ G.Adj v w := by
      intro v w h
      have he : ({v | ∃ w, G.Adj v w} : Set (Fin n)) = ∅ := by
        have h0 := Nat.le_zero.mp hm
        exact (Set.ncard_eq_zero (Set.toFinite _)).mp h0
      have hv : v ∈ ({v | ∃ w, G.Adj v w} : Set (Fin n)) := ⟨w, h⟩
      rw [he] at hv
      exact hv
    refine ⟨Finset.univ.map port, ?_, ?_, ?_⟩
    · intro i
      simp
    · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
      omega
    · rintro x ⟨d, _, hd⟩
      exact ⟨d, fun u v h => absurd h (hno u v), hd⟩
  | succ m ih =>
    intro G hG hm
    by_cases hc : ∃ v, (∀ i, port i ≠ v) ∧ (∃ w, G.Adj v w) ∧ (G.neighborSet v).ncard ≤ 2
    · obtain ⟨v, hvp, ⟨w0, hw0⟩, hv2⟩ := hc
      let G' : SimpleGraph (Fin n) :=
        { Adj := fun a b => G.Adj a b ∧ a ≠ v ∧ b ≠ v
          symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
          loopless := ⟨fun a h => G.irrefl h.1⟩ }
      have hle : G' ≤ G := fun a b h => h.1
      have hG' : G'.IsAcyclic := SimpleGraph.IsAcyclic.anti hle hG
      have hm' : ({u | ∃ w, G'.Adj u w} : Set (Fin n)).ncard ≤ m := by
        have hss : ({u | ∃ w, G'.Adj u w} : Set (Fin n)) ⊂ {u | ∃ w, G.Adj u w} := by
          refine ⟨fun u ⟨w, h⟩ => ⟨w, h.1⟩, fun hsub => ?_⟩
          obtain ⟨w, h⟩ := hsub ⟨w0, hw0⟩
          exact h.2.1 rfl
        have := Set.ncard_lt_ncard hss (Set.toFinite _)
        omega
      obtain ⟨S, hS1, hS2, hS3⟩ := ih G' hG' hm'
      refine ⟨S, hS1, hS2, ?_⟩
      rintro x ⟨d, hd, hdx⟩
      obtain ⟨c', hc', hc'x⟩ := hS3 x ⟨d, fun a ha b hb h => hd a ha b hb h.1, hdx⟩
      have ht : ∃ t : Fin 3, ∀ w, G.Adj v w → c' w ≠ t := by
        by_contra hcon
        have himg : c' '' (G.neighborSet v) = Set.univ := by
          ext t
          simp only [Set.mem_image, SimpleGraph.mem_neighborSet, Set.mem_univ, iff_true]
          by_contra h2
          exact hcon ⟨t, fun w hw e => h2 ⟨w, hw, e⟩⟩
        have h1 : (c' '' (G.neighborSet v)).ncard ≤ (G.neighborSet v).ncard :=
          Set.ncard_image_le (Set.toFinite _)
        rw [himg, Set.ncard_univ, Nat.card_fin] at h1
        omega
      obtain ⟨t, ht⟩ := ht
      refine ⟨Function.update c' v t, ?_, ?_⟩
      · intro a b hab
        by_cases ha : a = v
        · have hab' : G.Adj v b := by
            rw [← ha]
            exact hab
          have hb : b ≠ v := by
            intro e
            rw [e] at hab'
            exact G.irrefl hab'
          rw [ha, Function.update_self, Function.update_of_ne hb]
          exact fun e => ht b hab' e.symm
        · by_cases hb : b = v
          · have hab' : G.Adj v a := by
              rw [← hb]
              exact hab.symm
            rw [hb, Function.update_self, Function.update_of_ne ha]
            exact ht a hab'
          · rw [Function.update_of_ne ha, Function.update_of_ne hb]
            exact hc' a b ⟨hab, ha, hb⟩
      · intro i
        rw [Function.update_of_ne (hvp i)]
        exact hc'x i
    · have hc3 : ∀ v, v ∉ Finset.univ.map port → (∃ w, G.Adj v w) → 3 ≤ (G.neighborSet v).ncard := by
        intro v hv hw
        by_contra h
        refine hc ⟨v, ?_, hw, by omega⟩
        intro i e
        exact hv (by rw [← e]; simp)
      have hcount := count n G hG (Finset.univ.map port) hc3
      refine ⟨Finset.univ.map port ∪
        Finset.univ.filter (fun v => v ∉ Finset.univ.map port ∧ ∃ w, G.Adj v w), ?_, ?_, ?_⟩
      · intro i
        simp
      · have h1 := Finset.card_union_le (Finset.univ.map port)
          (Finset.univ.filter (fun v => v ∉ Finset.univ.map port ∧ ∃ w, G.Adj v w))
        have hP : (Finset.univ.map port).card = k := by simp
        omega
      · rintro x ⟨d, hd, hdx⟩
        have hin : ∀ a b, G.Adj a b → a ∈ Finset.univ.map port ∪
            Finset.univ.filter (fun v => v ∉ Finset.univ.map port ∧ ∃ w, G.Adj v w) := by
          intro a b hab
          by_cases ha : a ∈ Finset.univ.map port
          · exact Finset.mem_union_left _ ha
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, b, hab⟩)
        exact ⟨d, fun a b hab => hd a (hin a b hab) b (hin b a hab.symm) hab, hdx⟩

end PEqualNP.Outside.L_lib_1544

theorem PEqualNP.Outside.L_lib_1544 : (∀ (n k : Nat) (G : SimpleGraph (Fin n)), G.IsAcyclic →
  ∀ port : Fin k ↪ Fin n, ∃ S : Finset (Fin n),
    (∀ i, port i ∈ S) ∧ S.card ≤ 2*k ∧
    ∀ x : Fin k → Fin 3,
      (∃ c : Fin n → Fin 3,
        (∀ u v, G.Adj u v → c u ≠ c v) ∧ ∀ i, c (port i) = x i) ↔
      ∃ d : Fin n → Fin 3,
        (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → d u ≠ d v) ∧ ∀ i, d (port i) = x i) := by
  intro n k G hG port
  obtain ⟨S, h1, h2, h3⟩ := PEqualNP.Outside.L_lib_1544.red n k port _ G hG le_rfl
  refine ⟨S, h1, h2, fun x => ⟨?_, h3 x⟩⟩
  rintro ⟨c, hc, hx⟩
  exact ⟨c, fun u _ v _ h => hc u v h, hx⟩
