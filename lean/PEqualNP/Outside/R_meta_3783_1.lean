import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3783_1
  (h1 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (1 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (x23 : Fin x2) => Bool.false) else (fun (x23 : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 Bool.true (x13 + x21) ∧ x24 ∈ x20 Bool.true (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 Bool.true (x13 + x21) = x20 Bool.true x25 ∪ x20 Bool.true x26) →                           x2 * x1 ≤ (100 : ℕ) * x10)
  (h2 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (1 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (x23 : Fin x2) => Bool.false) else (fun (x23 : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 Bool.false (x13 + x21) ∧ x24 ∈ x20 Bool.false (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 Bool.false (x13 + x21) = x20 Bool.false x25 ∪ x20 Bool.false x26) →                           x2 * x1 ≤ (100 : ℕ) * x10) : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (1 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (x23 : Fin x2) => Bool.false) else (fun (x23 : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x22 : Bool) (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 x22 (x13 + x21) ∧ x24 ∈ x20 x22 (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 x22 (x13 + x21) = x20 x22 x25 ∪ x20 x22 x26) →                           x2 * x1 ≤ (100 : ℕ) * x10 := by
  dsimp only
  intro q N I inst hq hN hdeg hline hodd s o W hout hin hgates hpos hneg hwit
  by_cases large : 200 ≤ q
  · obtain ⟨g, hg, d, p, r, rest⟩ := hwit
    cases d
    · exact h2 q N I large hN hdeg hline hodd s o W hout hin hgates hpos hneg ⟨g, hg, p, r, rest⟩
    · exact h1 q N I large hN hdeg hline hodd s o W hout hin hgates hpos hneg ⟨g, hg, p, r, rest⟩
  have mono : ∀ w < N + N + s, ∀ a b : (Fin N → Bool) × (Fin N → Bool),
      ((∀ i, a.1 i = true → b.1 i = true) ∧ (∀ i, a.2 i = true → b.2 i = true)) →
      a ∈ W w → b ∈ W w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw a b le ha
      by_cases left : w < N
      · have eq : W w = {z | z.1 ⟨w, left⟩ = true} := (hin ⟨w, left⟩).1
        rw [eq] at ha ⊢
        exact le.1 _ ha
      · by_cases right : w < N + N
        · have eq : w = N + (⟨w - N, by omega⟩ : Fin N).val := by simp only []; omega
          rw [eq, (hin ⟨w - N, by omega⟩).2] at ha ⊢
          exact le.2 _ ha
        · have eq : w = N + N + (w - (N + N)) := by omega
          obtain ⟨u, v, lower, law⟩ := hgates (w - (N + N)) (by omega)
          have mx : max u v < w := by omega
          have hu : u < w := lt_of_le_of_lt (le_max_left _ _) mx
          have hv : v < w := lt_of_le_of_lt (le_max_right _ _) mx
          have um := ih u hu (by omega) a b le
          have vm := ih v hv (by omega) a b le
          rw [eq] at ha ⊢
          simp only [List.mem_cons, List.not_mem_nil, or_false] at law
          rcases law with union | copy | zero | inter
          · rw [union] at ha ⊢
            exact ha.elim (fun h => Or.inl (um h)) (fun h => Or.inr (vm h))
          · rw [copy] at ha ⊢
            exact um ha
          · rw [zero] at ha
            exact False.elim ha
          · rw [inter] at ha ⊢
            exact ⟨um ha.1, vm ha.2⟩
  have reach : ∀ k ≤ s, ∀ U : Finset ℕ, (∀ w ∈ U, w < N + N + k) →
      ∃ S : Finset ℕ, S.card ≤ U.card + k ∧ (∀ v ∈ S, v < N + N) ∧
        ∀ z z' : (Fin N → Bool) × (Fin N → Bool),
          (∀ v ∈ S, (z ∈ W v ↔ z' ∈ W v)) → ∀ w ∈ U, (z ∈ W w ↔ z' ∈ W w) := by
    intro k
    induction k with
    | zero =>
      intro _ U hU
      exact ⟨U, by omega, fun v hv => by simpa using hU v hv, fun z z' h w hw => h w hw⟩
    | succ k ih =>
      intro hk U hU
      by_cases use : N + N + k ∈ U
      · obtain ⟨a, b, lower, law⟩ := hgates k (by omega)
        have ha : a < N + N + k := lt_of_le_of_lt (le_max_left _ _) lower
        have hb : b < N + N + k := lt_of_le_of_lt (le_max_right _ _) lower
        have bounds : ∀ u ∈ insert a (insert b (U.erase (N + N + k))), u < N + N + k := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | h
          · exact ha
          rcases Finset.mem_insert.mp h with rfl | h
          · exact hb
          obtain ⟨ne, inc⟩ := Finset.mem_erase.mp h
          have := hU u inc
          omega
        obtain ⟨S, c, inS, dep⟩ := ih (by omega) _ bounds
        have uc : (insert a (insert b (U.erase (N + N + k)))).card ≤ U.card + 1 := by
          have c1 := Finset.card_insert_le a (insert b (U.erase (N + N + k)))
          have c2 := Finset.card_insert_le b (U.erase (N + N + k))
          rw [Finset.card_erase_of_mem use] at c2
          have := Finset.card_pos.mpr ⟨_, use⟩
          omega
        refine ⟨S, by omega, inS, ?_⟩
        intro z z' agree u hu
        have da := dep z z' agree a (by simp)
        have db := dep z z' agree b (by simp)
        by_cases eq : u = N + N + k
        · subst eq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at law
          rcases law with union | copy | zero | inter
          · rw [union]
            exact or_congr da db
          · rw [copy]
            exact da
          · rw [zero]
            exact Iff.rfl
          · rw [inter]
            exact and_congr da db
        · exact dep z z' agree u (by simp [eq, hu])
      · have bounds : ∀ u ∈ U, u < N + N + k := by
          intro u hu
          have ne : u ≠ N + N + k := fun eq => use (eq ▸ hu)
          have := hU u hu
          omega
        obtain ⟨S, c, h⟩ := ih (by omega) U bounds
        exact ⟨S, by omega, h⟩
  obtain ⟨S, card, inS, dep⟩ := reach s le_rfl {o} (by simpa using hout)
  have nbig : 100 ≤ N := by
    have := Nat.zero_le (q ^ 2)
    omega
  have allBits : Finset.range (N + N) ⊆ S := by
    intro v hv
    have bound := Finset.mem_range.mp hv
    by_contra miss
    by_cases point : v < N
    · have ne : (⟨v, point⟩ : Fin N) ≠ (if v = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩ : Fin N) := by
        intro e
        have eq := congrArg Fin.val e
        split at eq
        · simp only [] at eq; omega
        · simp only [] at eq; omega
      obtain ⟨l, hl, _⟩ := hline _ _ ne
      have small : Fintype.card {k : Fin N // decide (k = l) = true} ≤ q := by
        simp [Fintype.card_subtype]
        omega
      have rej := hneg (fun k => decide (k = l)) small
      have acc := mono o hout (fun a => decide (a = (⟨v, point⟩ : Fin N)), fun k => decide (k = l))
        (fun a => decide (a = (⟨v, point⟩ : Fin N)) || decide (¬∃ m, I a m ∧ decide (m = l) = true),
          fun k => decide (k = l)) ⟨fun i h => by simp only [Bool.or_eq_true]; exact Or.inl h, fun i h => h⟩
        (hpos _ l hl.1)
      apply rej
      refine (dep _ _ ?_ o (by simp)).mp acc
      intro u hu
      by_cases up : u < N
      · rw [(hin ⟨u, up⟩).1]
        have ne' : (⟨u, up⟩ : Fin N) ≠ ⟨v, point⟩ := by
          intro e
          have := congrArg Fin.val e
          simp only [] at this
          exact miss (this ▸ hu)
        simp only [Set.mem_setOf_eq, decide_eq_false ne', Bool.false_or]
      · by_cases uq : u < N + N
        · have e : u = N + (⟨u - N, by omega⟩ : Fin N).val := by simp only []; omega
          rw [e, (hin ⟨u - N, by omega⟩).2]
          exact Iff.rfl
        · exact absurd (inS u hu) uq
    · have lk : v - N < N := by omega
      have pos : 0 < Fintype.card {p : Fin N // I p ⟨v - N, lk⟩} := by
        rw [hdeg]
        omega
      obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp pos
      have rej := hneg (fun _ => false) (by simp)
      have acc := mono o hout (fun a => decide (a = p), fun k => decide (k = (⟨v - N, lk⟩ : Fin N)))
        (fun a => decide (¬∃ m, I a m ∧ (fun _ : Fin N => false) m = true),
          fun k => decide (k = (⟨v - N, lk⟩ : Fin N))) ⟨fun i h => by simp, fun i h => h⟩
        (hpos p _ hp)
      apply rej
      refine (dep _ _ ?_ o (by simp)).mp acc
      intro u hu
      by_cases up : u < N
      · rw [(hin ⟨u, up⟩).1]
        exact Iff.rfl
      · have uq : u < N + N := inS u hu
        have e : u = N + (⟨u - N, by omega⟩ : Fin N).val := by simp only []; omega
        rw [e, (hin ⟨u - N, by omega⟩).2]
        have ne' : (⟨u - N, by omega⟩ : Fin N) ≠ ⟨v - N, lk⟩ := by
          intro e2
          have := congrArg Fin.val e2
          simp only [] at this
          have : u = v := by omega
          exact miss (this ▸ hu)
        simp only [Set.mem_setOf_eq, decide_eq_false ne']
  have count := Finset.card_le_card allBits
  simp only [Finset.card_range, Finset.card_singleton] at count card
  have qmax : q ≤ 199 := by omega
  have := Nat.mul_le_mul_left N qmax
  omega
