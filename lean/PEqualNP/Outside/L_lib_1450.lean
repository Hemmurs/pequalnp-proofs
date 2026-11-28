import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1450_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wireAt (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨value,pre,len⟩ := foldl_snoc_split readGate C.gates x j hj false
  rw [show (C.wires x).getD (x.length + j) false = _ from value]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · exact (getD_of_initial pre (by omega) false).symm
  · apply List.getD_eq_default
    unfold readGate at len
    omega

theorem wire_input' (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_of_initial (foldl_snoc_keeps readGate C.gates x) hi false

theorem wire_gate (C : Circuit) (x : List Bool) (hB : ReadsBack x.length C) (j : ℕ)
    (hj : j < C.size) :
    (C.wires x).getD (x.length + j) false = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have he := wireAt C x j hj
  have hat : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [he, ← hat]
  congr 1
  exact List.map_congr_left fun i hi => by simp only [ite_eq_left (hB j hj i hi)]



def reachStep (Ls : List (Finset ℕ)) (g : Gate) : Finset ℕ :=
  insert Ls.length (g.inputs.foldr (fun i acc => Ls.getD i ∅ ∪ acc) ∅)

def reachList (C : Circuit) (N : ℕ) : List (Finset ℕ) :=
  C.gates.foldl (fun Ls g => Ls ++ [reachStep Ls g]) ((List.range N).map fun i => {i})

def reach (C : Circuit) (N w : ℕ) : Finset ℕ := (reachList C N).getD w ∅

theorem mem_foldr_union (S : ℕ → Finset ℕ) (l : List ℕ) (x : ℕ) :
    x ∈ l.foldr (fun i acc => S i ∪ acc) ∅ ↔ ∃ i ∈ l, x ∈ S i := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem reach_input (C : Circuit) (N i : ℕ) (hi : i < N) : reach C N i = {i} := by
  have hp := foldl_snoc_keeps reachStep C.gates ((List.range N).map fun i => ({i} : Finset ℕ))
  unfold reach reachList
  rw [getD_of_initial hp (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem reach_gate (C : Circuit) (N : ℕ) (hB : ReadsBack N C) (j : ℕ) (hj : j < C.size)
    (x : ℕ) : x ∈ reach C N (N + j) ↔
      x = N + j ∨ ∃ i ∈ (gateAt C j).inputs, x ∈ reach C N i := by
  have hl : ((List.range N).map fun i => ({i} : Finset ℕ)).length = N := by simp
  obtain ⟨value, pre, len⟩ :=
    foldl_snoc_split reachStep C.gates ((List.range N).map fun i => ({i} : Finset ℕ)) j hj ∅
  rw [hl] at value len
  have hat : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  unfold reach reachList
  rw [value, reachStep, Finset.mem_insert, mem_foldr_union, len, ← hat]
  apply or_congr Iff.rfl
  apply exists_congr
  intro i
  constructor
  · rintro ⟨hi, hx⟩
    refine ⟨hi, ?_⟩
    rw [getD_of_initial pre (len ▸ hB j hj i hi)]
    exact hx
  · rintro ⟨hi, hx⟩
    refine ⟨hi, ?_⟩
    rw [getD_of_initial pre (len ▸ hB j hj i hi)] at hx
    exact hx

theorem reach_le (C : Circuit) (N : ℕ) (hB : ReadsBack N C) :
    ∀ w, w < N + C.size → ∀ x ∈ reach C N w, x ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw x hx
    by_cases hN : w < N
    · rw [reach_input C N w hN] at hx
      simp at hx; omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      rcases (reach_gate C N hB j (by omega) x).mp hx with h | ⟨i, hi, hx⟩
      · omega
      · have := hB j (by unfold Circuit.size at hw; omega) i hi
        have := ih i (by omega) (by omega) x hx
        omega

theorem reach_sub (C : Circuit) (N : ℕ) (hB : ReadsBack N C) (j : ℕ) (hj : j < C.size)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) : reach C N i ⊆ reach C N (N + j) :=
  fun x hx => (reach_gate C N hB j hj x).mpr (Or.inr ⟨i, hi, hx⟩)

theorem reach_up (C : Circuit) (N : ℕ) (hB : ReadsBack N C) :
    ∀ w, w < N + C.size → ∀ x ∈ reach C N w, x ≠ w →
      ∃ j < C.size, x ∈ (gateAt C j).inputs ∧ N + j ∈ reach C N w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw x hx hxw
    by_cases hN : w < N
    · rw [reach_input C N w hN] at hx
      simp at hx; omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < C.size := by omega
      rcases (reach_gate C N hB j hj x).mp hx with h | ⟨i, hi, hx⟩
      · omega
      · have hib := hB j hj i hi
        by_cases e : x = i
        · subst e
          exact ⟨j, hj, hi, (reach_gate C N hB j hj _).mpr (Or.inl rfl)⟩
        · obtain ⟨j', hj', h1, h2⟩ := ih i (by omega) (by omega) x hx e
          exact ⟨j', hj', h1, reach_sub C N hB j hj i hi h2⟩

theorem count_le_reads (C : Circuit) (j : ℕ) (hj : j < C.size) (x : ℕ) :
    (gateAt C j).inputs.count x ≤ readsIn C (Finset.range C.size) x := by
  unfold readsIn
  exact Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count x)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)

theorem reader_unique (C : Circuit) (x j1 j2 : ℕ) (h1 : j1 < C.size) (h2 : j2 < C.size)
    (hx1 : x ∈ (gateAt C j1).inputs) (hx2 : x ∈ (gateAt C j2).inputs)
    (hr : readsIn C (Finset.range C.size) x ≤ 1) : j1 = j2 := by
  by_contra hne
  have c1 := List.count_pos_iff.mpr hx1
  have c2 := List.count_pos_iff.mpr hx2
  have hs : ({j1, j2} : Finset ℕ) ⊆ Finset.range C.size := by
    intro z hz
    simp at hz
    rcases hz with rfl | rfl <;> simpa
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => (gateAt C j).inputs.count x) hs
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hne] at this
  unfold readsIn at hr
  omega

theorem reach_disjoint (C : Circuit) (N : ℕ) (hB : ReadsBack N C)
    (hr : ∀ x < N + C.size, readsIn C (Finset.range C.size) x ≤ 1)
    (j : ℕ) (hj : j < C.size) (u v : ℕ) (hu : u ∈ (gateAt C j).inputs)
    (hv : v ∈ (gateAt C j).inputs) (huv : u ≠ v) :
    ∀ x, x ∈ reach C N u → x ∈ reach C N v → False := by
  have hub := hB j hj u hu
  have hvb := hB j hj v hv
  have key : ∀ m x, N + C.size - x ≤ m → x ∈ reach C N u → x ∈ reach C N v → False := by
    intro m
    induction m with
    | zero =>
      intro x hm h1 _
      have := reach_le C N hB u (by omega) x h1
      omega
    | succ m ih =>
      intro x hm h1 h2
      have xu := reach_le C N hB u (by omega) x h1
      have xv := reach_le C N hB v (by omega) x h2
      by_cases eu : x = u
      · subst eu
        obtain ⟨j', hj', r1, r2⟩ := reach_up C N hB v (by omega) x h2 huv
        have := reach_le C N hB v (by omega) _ r2
        have := reader_unique C x j j' hj hj' hu r1 (hr x (by omega))
        omega
      by_cases ev : x = v
      · subst ev
        obtain ⟨j', hj', r1, r2⟩ := reach_up C N hB u (by omega) x h1 (Ne.symm huv)
        have := reach_le C N hB u (by omega) _ r2
        have := reader_unique C x j j' hj hj' hv r1 (hr x (by omega))
        omega
      obtain ⟨j1, hj1, r1, s1⟩ := reach_up C N hB u (by omega) x h1 eu
      obtain ⟨j2, hj2, r2, s2⟩ := reach_up C N hB v (by omega) x h2 ev
      have e := reader_unique C x j1 j2 hj1 hj2 r1 r2 (hr x (by omega))
      subst e
      have := hB j1 hj1 x r1
      exact ih (N + j1) (by omega) s1 s2
  intro x h1 h2
  exact key _ x le_rfl h1 h2


section Counts
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def oc (b : Bool) (F : Finset α → Bool) (L : Finset α) : ℕ∞ :=
  (Finset.univ.filter (fun y => F y = b)).inf (fun y => ((y ∩ L).card : ℕ∞))

noncomputable def zc (b : Bool) (F : Finset α → Bool) (L : Finset α) : ℕ∞ :=
  (Finset.univ.filter (fun y => F y = b)).inf (fun y => ((L \ y).card : ℕ∞))

def Inv (F : Finset α → Bool) (L : Finset α) : Prop :=
  oc true F L * zc false F L ≤ L.card ∧ oc false F L * zc true F L ≤ L.card

def Dep (F : Finset α → Bool) (L : Finset α) : Prop :=
  ∀ y y', y ∩ L = y' ∩ L → F y = F y'

theorem oc_le {b : Bool} {F : Finset α → Bool} {L : Finset α} {y : Finset α} (h : F y = b) :
    oc b F L ≤ (y ∩ L).card :=
  Finset.inf_le (by simp [h])

theorem zc_le {b : Bool} {F : Finset α → Bool} {L : Finset α} {y : Finset α} (h : F y = b) :
    zc b F L ≤ (L \ y).card :=
  Finset.inf_le (by simp [h])

theorem oc_wit {b : Bool} {F : Finset α → Bool} {L : Finset α} (h : oc b F L ≠ ⊤) :
    ∃ y, F y = b ∧ oc b F L = (y ∩ L).card := by
  have hne : (Finset.univ.filter (fun y => F y = b)).Nonempty := by
    by_contra e
    rw [Finset.not_nonempty_iff_eq_empty] at e
    exact h (by unfold oc; rw [e]; rfl)
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf _ hne (fun y => ((y ∩ L).card : ℕ∞))
  exact ⟨y, (Finset.mem_filter.mp hy).2, he⟩

theorem zc_wit {b : Bool} {F : Finset α → Bool} {L : Finset α} (h : zc b F L ≠ ⊤) :
    ∃ y, F y = b ∧ zc b F L = (L \ y).card := by
  have hne : (Finset.univ.filter (fun y => F y = b)).Nonempty := by
    by_contra e
    rw [Finset.not_nonempty_iff_eq_empty] at e
    exact h (by unfold zc; rw [e]; rfl)
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf _ hne (fun y => ((L \ y).card : ℕ∞))
  exact ⟨y, (Finset.mem_filter.mp hy).2, he⟩

theorem oc_pair {F G K : Finset α → Bool} {L1 L2 : Finset α} {b1 b2 c : Bool}
    (hF : Dep F L1) (hG : Dep G L2) (hd : Disjoint L1 L2)
    (h : ∀ y, F y = b1 → G y = b2 → K y = c) :
    oc c K (L1 ∪ L2) ≤ oc b1 F L1 + oc b2 G L2 := by
  by_cases t1 : oc b1 F L1 = ⊤
  · rw [t1, top_add]; exact le_top
  by_cases t2 : oc b2 G L2 = ⊤
  · rw [t2, add_top]; exact le_top
  obtain ⟨y1, f1, e1⟩ := oc_wit t1
  obtain ⟨y2, f2, e2⟩ := oc_wit t2
  have s1 : (y1 ∩ L1 ∪ y2 ∩ L2) ∩ L1 = y1 ∩ L1 := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact h
      · exact absurd h.2 (Finset.disjoint_left.mp hd hx)
    · intro hx; exact ⟨Or.inl hx, hx.2⟩
  have s2 : (y1 ∩ L1 ∪ y2 ∩ L2) ∩ L2 = y2 ∩ L2 := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact absurd hx (Finset.disjoint_left.mp hd h.2)
      · exact h
    · intro hx; exact ⟨Or.inr hx, hx.2⟩
  have hK := h _ ((hF _ _ s1).trans f1) ((hG _ _ s2).trans f2)
  refine (oc_le hK).trans ?_
  rw [e1, e2]
  have : (y1 ∩ L1 ∪ y2 ∩ L2) ∩ (L1 ∪ L2) = y1 ∩ L1 ∪ y2 ∩ L2 :=
    Finset.inter_eq_left.mpr (Finset.union_subset_union Finset.inter_subset_right
      Finset.inter_subset_right)
  rw [this, Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left
    Finset.inter_subset_right (Finset.disjoint_of_subset_right Finset.inter_subset_right hd))]
  push_cast; exact le_rfl

theorem zc_pair {F G K : Finset α → Bool} {L1 L2 : Finset α} {b1 b2 c : Bool}
    (hF : Dep F L1) (hG : Dep G L2) (hd : Disjoint L1 L2)
    (h : ∀ y, F y = b1 → G y = b2 → K y = c) :
    zc c K (L1 ∪ L2) ≤ zc b1 F L1 + zc b2 G L2 := by
  by_cases t1 : zc b1 F L1 = ⊤
  · rw [t1, top_add]; exact le_top
  by_cases t2 : zc b2 G L2 = ⊤
  · rw [t2, add_top]; exact le_top
  obtain ⟨y1, f1, e1⟩ := zc_wit t1
  obtain ⟨y2, f2, e2⟩ := zc_wit t2
  have s1 : (y1 ∩ L1 ∪ y2 ∩ L2) ∩ L1 = y1 ∩ L1 := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact h
      · exact absurd h.2 (Finset.disjoint_left.mp hd hx)
    · intro hx; exact ⟨Or.inl hx, hx.2⟩
  have s2 : (y1 ∩ L1 ∪ y2 ∩ L2) ∩ L2 = y2 ∩ L2 := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact absurd hx (Finset.disjoint_left.mp hd h.2)
      · exact h
    · intro hx; exact ⟨Or.inr hx, hx.2⟩
  have hK := h _ ((hF _ _ s1).trans f1) ((hG _ _ s2).trans f2)
  refine (zc_le hK).trans ?_
  rw [e1, e2]
  have : (L1 ∪ L2) \ (y1 ∩ L1 ∪ y2 ∩ L2) = (L1 \ y1) ∪ (L2 \ y2) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact Or.inl ⟨h, fun hy => hn (Or.inl ⟨hy, h⟩)⟩
      · exact Or.inr ⟨h, fun hy => hn (Or.inr ⟨hy, h⟩)⟩
    · rintro (⟨h, hn⟩ | ⟨h, hn⟩)
      · refine ⟨Or.inl h, ?_⟩
        rintro (⟨hy, _⟩ | ⟨_, h2⟩)
        · exact hn hy
        · exact Finset.disjoint_left.mp hd h h2
      · refine ⟨Or.inr h, ?_⟩
        rintro (⟨_, h1⟩ | ⟨hy, _⟩)
        · exact Finset.disjoint_left.mp hd h1 h
        · exact hn hy
  rw [this, Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left
    Finset.sdiff_subset (Finset.disjoint_of_subset_right Finset.sdiff_subset hd))]
  push_cast; exact le_rfl

theorem oc_single {F K : Finset α → Bool} {L1 L : Finset α} {b c : Bool}
    (hF : Dep F L1) (hs : L1 ⊆ L) (h : ∀ y, F y = b → K y = c) :
    oc c K L ≤ oc b F L1 := by
  apply Finset.le_inf
  intro y hy
  have fy := (Finset.mem_filter.mp hy).2
  have s : (y ∩ L1) ∩ L1 = y ∩ L1 := by rw [Finset.inter_assoc, Finset.inter_self]
  refine (oc_le (h _ ((hF _ _ s).trans fy))).trans ?_
  rw [Finset.inter_assoc, Finset.inter_eq_left.mpr hs]

theorem zc_single {F K : Finset α → Bool} {L1 L : Finset α} {b c : Bool}
    (hF : Dep F L1) (hs : L1 ⊆ L) (h : ∀ y, F y = b → K y = c) :
    zc c K L ≤ zc b F L1 := by
  apply Finset.le_inf
  intro y hy
  have fy := (Finset.mem_filter.mp hy).2
  have s : (y ∩ L1 ∪ (L \ L1)) ∩ L1 = y ∩ L1 := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
  refine (zc_le (h _ ((hF _ _ s).trans fy))).trans ?_
  have : L \ (y ∩ L1 ∪ (L \ L1)) = L1 \ y := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; tauto
    · rintro ⟨h1, h2⟩; exact ⟨hs h1, by tauto⟩
  rw [this]

theorem arith1 {p p1 p2 q q1 q2 c1 c2 : ℕ∞} (hp : p ≤ p1 + p2) (hq1 : q ≤ q1) (hq2 : q ≤ q2)
    (h1 : p1 * q1 ≤ c1) (h2 : p2 * q2 ≤ c2) : p * q ≤ c1 + c2 :=
  calc p * q ≤ (p1 + p2) * q := mul_le_mul' hp le_rfl
  _ = p1 * q + p2 * q := add_mul _ _ _
  _ ≤ p1 * q1 + p2 * q2 := add_le_add (mul_le_mul' le_rfl hq1) (mul_le_mul' le_rfl hq2)
  _ ≤ c1 + c2 := add_le_add h1 h2

theorem arith2 {p p1 p2 q q1 q2 c1 c2 : ℕ∞} (hp1 : p ≤ p1) (hp2 : p ≤ p2) (hq : q ≤ q1 + q2)
    (h1 : p1 * q1 ≤ c1) (h2 : p2 * q2 ≤ c2) : p * q ≤ c1 + c2 := by
  rw [mul_comm] at h1 h2 ⊢
  exact arith1 hq hp1 hp2 h1 h2

theorem card_union_enat {L1 L2 : Finset α} (hd : Disjoint L1 L2) :
    (((L1 ∪ L2).card : ℕ) : ℕ∞) = (L1.card : ℕ∞) + L2.card := by
  rw [Finset.card_union_of_disjoint hd]; push_cast; rfl

theorem inv_and {F G : Finset α → Bool} {L1 L2 : Finset α} (iF : Inv F L1) (iG : Inv G L2)
    (hF : Dep F L1) (hG : Dep G L2) (hd : Disjoint L1 L2) :
    Inv (fun y => F y && G y) (L1 ∪ L2) := by
  unfold Inv
  rw [card_union_enat hd]
  constructor
  · exact arith1 (oc_pair hF hG hd (fun y h1 h2 => by simp [h1, h2]))
      (zc_single hF Finset.subset_union_left (fun y h1 => by simp [h1]))
      (zc_single hG Finset.subset_union_right (fun y h1 => by simp [h1])) iF.1 iG.1
  · exact arith2 (oc_single hF Finset.subset_union_left (fun y h1 => by simp [h1]))
      (oc_single hG Finset.subset_union_right (fun y h1 => by simp [h1]))
      (zc_pair hF hG hd (fun y h1 h2 => by simp [h1, h2])) iF.2 iG.2

theorem inv_or {F G : Finset α → Bool} {L1 L2 : Finset α} (iF : Inv F L1) (iG : Inv G L2)
    (hF : Dep F L1) (hG : Dep G L2) (hd : Disjoint L1 L2) :
    Inv (fun y => F y || G y) (L1 ∪ L2) := by
  unfold Inv
  rw [card_union_enat hd]
  constructor
  · exact arith2 (oc_single hF Finset.subset_union_left (fun y h1 => by simp [h1]))
      (oc_single hG Finset.subset_union_right (fun y h1 => by simp [h1]))
      (zc_pair hF hG hd (fun y h1 h2 => by simp [h1, h2])) iF.1 iG.1
  · exact arith1 (oc_pair hF hG hd (fun y h1 h2 => by simp [h1, h2]))
      (zc_single hF Finset.subset_union_left (fun y h1 => by simp [h1]))
      (zc_single hG Finset.subset_union_right (fun y h1 => by simp [h1])) iF.2 iG.2

theorem inv_not {F : Finset α → Bool} {L : Finset α} (iF : Inv F L) :
    Inv (fun y => !F y) L := by
  have e : ∀ b, (Finset.univ.filter (fun y => (!F y) = b)) =
      Finset.univ.filter (fun y => F y = !b) := by
    intro b; apply Finset.filter_congr; intro y _; cases F y <;> cases b <;> simp
  have eo : ∀ b, oc b (fun y => !F y) L = oc (!b) F L := by intro b; unfold oc; rw [e]
  have ez : ∀ b, zc b (fun y => !F y) L = zc (!b) F L := by intro b; unfold zc; rw [e]
  unfold Inv
  rw [eo, eo, ez, ez]
  exact ⟨iF.2, iF.1⟩

theorem inv_mono {F : Finset α → Bool} {L L' : Finset α} (iF : Inv F L) (hF : Dep F L)
    (hs : L ⊆ L') : Inv F L' := by
  have h1 : ∀ b, oc b F L' ≤ oc b F L := fun b => oc_single hF hs (fun y h => h)
  have h2 : ∀ b, zc b F L' ≤ zc b F L := fun b => zc_single hF hs (fun y h => h)
  have hc : (L.card : ℕ∞) ≤ L'.card := by exact_mod_cast Finset.card_le_card hs
  exact ⟨(mul_le_mul' (h1 _) (h2 _)).trans (iF.1.trans hc),
    (mul_le_mul' (h1 _) (h2 _)).trans (iF.2.trans hc)⟩

theorem inv_const {F : Finset α → Bool} {L : Finset α} (c : Bool) (hc : ∀ y, F y = c) :
    Inv F L := by
  have o0 : oc c F L = 0 := le_antisymm ((oc_le (hc ∅)).trans (by simp)) (zero_le)
  have z0 : zc c F L = 0 := le_antisymm ((zc_le (L := L) (hc Finset.univ)).trans (by simp))
    (zero_le)
  cases c
  · exact ⟨by rw [z0, mul_zero]; exact zero_le, by rw [o0, zero_mul]; exact zero_le⟩
  · exact ⟨by rw [o0, zero_mul]; exact zero_le, by rw [z0, mul_zero]; exact zero_le⟩

theorem dep_const {F : Finset α → Bool} {L : Finset α} (c : Bool) (hc : ∀ y, F y = c) :
    Dep F L := fun y y' _ => (hc y).trans (hc y').symm

theorem dep_mono {F : Finset α → Bool} {L L' : Finset α} (hF : Dep F L) (hs : L ⊆ L') :
    Dep F L' := by
  intro y y' e
  apply hF
  rw [← Finset.inter_eq_right.mpr hs, ← Finset.inter_assoc, ← Finset.inter_assoc, e]

theorem inv_leaf (x : α) : Inv (fun y => decide (x ∈ y)) {x} := by
  have o1 : oc true (fun y => decide (x ∈ y)) {x} ≤ 1 :=
    (oc_le (y := {x}) (by simp)).trans (by simp)
  have z0 : zc false (fun y => decide (x ∈ y)) {x} ≤ 1 :=
    (zc_le (y := ∅) (by simp)).trans (by simp)
  have o0 : oc false (fun y => decide (x ∈ y)) {x} = 0 :=
    le_antisymm ((oc_le (y := ∅) (by simp)).trans (by simp)) (zero_le)
  refine ⟨?_, by rw [o0, zero_mul]; exact zero_le⟩
  simp only [Finset.card_singleton, Nat.cast_one]
  calc _ ≤ (1 : ℕ∞) * 1 := mul_le_mul' o1 z0
    _ = 1 := one_mul 1

theorem dep_leaf (x : α) : Dep (fun y => decide (x ∈ y)) {x} := by
  intro y y' e
  have : x ∈ y ∩ {x} ↔ x ∈ y' ∩ {x} := by rw [e]
  simp at this
  simp [this]

end Counts

theorem dep_comb {α : Type} [DecidableEq α] {F G : Finset α → Bool} {L1 L2 : Finset α}
    (φ : Bool → Bool → Bool) (hF : Dep F L1) (hG : Dep G L2) :
    Dep (fun y => φ (F y) (G y)) (L1 ∪ L2) := by
  intro y y' e
  have e1 : y ∩ L1 = y' ∩ L1 := by
    have := congrArg (· ∩ L1) e
    simp only [Finset.inter_assoc, Finset.union_inter_cancel_left] at this
    exact this
  have e2 : y ∩ L2 = y' ∩ L2 := by
    have := congrArg (· ∩ L2) e
    simp only [Finset.inter_assoc, Finset.union_inter_cancel_right] at this
    exact this
  simp only [hF y y' e1, hG y y' e2]

theorem dep_not {α : Type} [DecidableEq α] {F : Finset α → Bool} {L : Finset α}
    (hF : Dep F L) : Dep (fun y => !F y) L := by
  intro y y' e
  simp only [hF y y' e]

def Vw {k : ℕ} (C : Circuit) (bitsOf : Finset (Fin k) → List Bool) (P H : Finset (Fin k))
    (w : ℕ) (y : Finset (Fin k)) : Bool :=
  (C.wires (bitsOf (P ∪ (y ∩ H)))).getD w false

def Lw {k : ℕ} (C : Circuit) (H : Finset (Fin k)) (w : ℕ) : Finset (Fin k) :=
  H.filter (fun x => x.val ∈ reach C (k + 2) w)

theorem wire_inv {k : ℕ} (C : Circuit) (bitsOf : Finset (Fin k) → List Bool)
    (hlen : ∀ Y, (bitsOf Y).length = k + 2)
    (hbit : ∀ Y (x : Fin k), (bitsOf Y).getD x.val false = decide (x ∈ Y))
    (hk0 : ∀ Y, (bitsOf Y).getD k false = false)
    (hk1 : ∀ Y, (bitsOf Y).getD (k + 1) false = true)
    (P H : Finset (Fin k)) (hd : Disjoint P H)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) (hB : ReadsBack (k + 2) C)
    (hr : ∀ x < k + 2 + C.size, readsIn C (Finset.range C.size) x ≤ 1) :
    ∀ w < k + 2 + C.size, Dep (Vw C bitsOf P H w) (Lw C H w) ∧
      Inv (Vw C bitsOf P H w) (Lw C H w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases hN : w < k + 2
  · have hin : ∀ y, Vw C bitsOf P H w y = (bitsOf (P ∪ (y ∩ H))).getD w false := by
      intro y
      exact wire_input' C _ w (by rw [hlen]; exact hN)
    by_cases hk : w < k
    · let x : Fin k := ⟨w, hk⟩
      by_cases xH : x ∈ H
      · have hxP : x ∉ P := fun h => Finset.disjoint_left.mp hd h xH
        have e1 : Vw C bitsOf P H w = fun y => decide (x ∈ y) := by
          funext y
          rw [hin, show w = x.val from rfl, hbit]
          simp [hxP, xH]
        have e2 : Lw C H w = {x} := by
          ext z
          simp only [Lw, Finset.mem_filter, reach_input C (k + 2) w hN, Finset.mem_singleton,
            Fin.ext_iff]
          constructor
          · rintro ⟨_, h⟩; exact h
          · intro h; refine ⟨?_, h⟩
            have : z = x := Fin.ext h
            rw [this]; exact xH
        rw [e1, e2]
        exact ⟨dep_leaf x, inv_leaf x⟩
      · have e1 : ∀ y, Vw C bitsOf P H w y = decide (x ∈ P) := by
          intro y
          rw [hin, show w = x.val from rfl, hbit]
          simp [xH]
        exact ⟨dep_const _ e1, inv_const _ e1⟩
    · by_cases hk' : w = k
      · have e1 : ∀ y, Vw C bitsOf P H w y = false := by
          intro y; rw [hin, hk', hk0]
        exact ⟨dep_const _ e1, inv_const _ e1⟩
      · have e1 : ∀ y, Vw C bitsOf P H w y = true := by
          intro y; rw [hin, show w = k + 1 by omega, hk1]
        exact ⟨dep_const _ e1, inv_const _ e1⟩
  · obtain ⟨j, rfl⟩ : ∃ j, w = k + 2 + j := ⟨w - (k + 2), by omega⟩
    have hj : j < C.size := by omega
    have hval : ∀ y, Vw C bitsOf P H (k + 2 + j) y = (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => Vw C bitsOf P H i y) := by
      intro y
      have h := wire_gate C (bitsOf (P ∪ (y ∩ H))) (by rw [hlen]; exact hB) j hj
      rw [hlen] at h
      exact h
    have hsub : ∀ i ∈ (gateAt C j).inputs, Lw C H i ⊆ Lw C H (k + 2 + j) := by
      intro i hi z hz
      simp only [Lw, Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, reach_sub C (k + 2) hB j hj i hi hz.2⟩
    have hcov : ∀ z ∈ Lw C H (k + 2 + j), ∃ i ∈ (gateAt C j).inputs, z ∈ Lw C H i := by
      intro z hz
      simp only [Lw, Finset.mem_filter] at hz
      rcases (reach_gate C (k + 2) hB j hj z.val).mp hz.2 with h | ⟨i, hi, h⟩
      · have := z.isLt; omega
      · exact ⟨i, hi, by simp only [Lw, Finset.mem_filter]; exact ⟨hz.1, h⟩⟩
    have IH : ∀ i ∈ (gateAt C j).inputs, Dep (Vw C bitsOf P H i) (Lw C H i) ∧
        Inv (Vw C bitsOf P H i) (Lw C H i) := by
      intro i hi
      have := hB j hj i hi
      exact ih i (by omega) (by omega)
    have hmem : gateAt C j ∈ C.gates := by
      rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem _
    obtain ⟨hop, hl2⟩ := hF _ hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    generalize hI : (gateAt C j).inputs = I at hval hsub hcov IH hl2
    generalize hO : (gateAt C j).op = O at hval hop
    match I, hval, hsub, hcov, IH, hl2 with
    | [], hval, _, _, _, _ =>
      simp only [List.map_nil] at hval
      exact ⟨dep_const _ hval, inv_const _ hval⟩
    | [u], hval, hsub, _, IH, _ =>
      obtain ⟨du, iu⟩ := IH u (by simp)
      have su := hsub u (by simp)
      rcases hop with rfl | rfl | rfl
      · have e : Vw C bitsOf P H (k + 2 + j) = Vw C bitsOf P H u := by
          funext y; rw [hval]; simp [GateOp.eval]
        rw [e]; exact ⟨dep_mono du su, inv_mono iu du su⟩
      · have e : Vw C bitsOf P H (k + 2 + j) = Vw C bitsOf P H u := by
          funext y; rw [hval]; simp [GateOp.eval]
        rw [e]; exact ⟨dep_mono du su, inv_mono iu du su⟩
      · have e : Vw C bitsOf P H (k + 2 + j) = fun y => !Vw C bitsOf P H u y := by
          funext y; rw [hval]; simp [GateOp.eval]
        rw [e]
        exact ⟨dep_mono (dep_not du) su, inv_mono (inv_not iu) (dep_not du) su⟩
    | [u, v], hval, hsub, hcov, IH, _ =>
      obtain ⟨du, iu⟩ := IH u (by simp)
      obtain ⟨dv, iv⟩ := IH v (by simp)
      have su := hsub u (by simp)
      have sv := hsub v (by simp)
      have huv : u ≠ v := by
        intro e
        have c := count_le_reads C j hj u
        rw [hI, e] at c
        have := hr v (by have := hB j hj v (by rw [hI]; simp); omega)
        simp at c
        omega
      have hdis : Disjoint (Lw C H u) (Lw C H v) := by
        rw [Finset.disjoint_left]
        intro z h1 h2
        simp only [Lw, Finset.mem_filter] at h1 h2
        exact reach_disjoint C (k + 2) hB hr j hj u v (by rw [hI]; simp) (by rw [hI]; simp)
          huv z.val h1.2 h2.2
      have hU : Lw C H (k + 2 + j) = Lw C H u ∪ Lw C H v := by
        apply Finset.Subset.antisymm
        · intro z hz
          obtain ⟨i, hi, hz'⟩ := hcov z hz
          simp at hi
          rcases hi with rfl | rfl
          · exact Finset.mem_union_left _ hz'
          · exact Finset.mem_union_right _ hz'
        · exact Finset.union_subset su sv
      rcases hop with rfl | rfl | rfl
      · have e : Vw C bitsOf P H (k + 2 + j) =
            fun y => Vw C bitsOf P H u y && Vw C bitsOf P H v y := by
          funext y; rw [hval]; simp [GateOp.eval]
        rw [e, hU]
        exact ⟨dep_comb (· && ·) du dv, inv_and iu iv du dv hdis⟩
      · have e : Vw C bitsOf P H (k + 2 + j) =
            fun y => Vw C bitsOf P H u y || Vw C bitsOf P H v y := by
          funext y; rw [hval]; simp [GateOp.eval]
        rw [e, hU]
        exact ⟨dep_comb (· || ·) du dv, inv_or iu iv du dv hdis⟩
      · have e : Vw C bitsOf P H (k + 2 + j) = fun y => !Vw C bitsOf P H u y := by
          funext y; rw [hval]; simp [GateOp.eval]
        rw [e]
        exact ⟨dep_mono (dep_not du) su, inv_mono (inv_not iu) (dep_not du) su⟩
    | _ :: _ :: _ :: _, _, _, _, _, hl2 => simp at hl2

theorem tree_bound {k : ℕ} (C : Circuit) (bitsOf : Finset (Fin k) → List Bool)
    (hlen : ∀ Y, (bitsOf Y).length = k + 2)
    (hbit : ∀ Y (x : Fin k), (bitsOf Y).getD x.val false = decide (x ∈ Y))
    (hk0 : ∀ Y, (bitsOf Y).getD k false = false)
    (hk1 : ∀ Y, (bitsOf Y).getD (k + 1) false = true)
    (P H : Finset (Fin k)) (hd : Disjoint P H)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) (hB : ReadsBack (k + 2) C)
    (hr : ∀ x < k + 2 + C.size, readsIn C (Finset.range C.size) x ≤ 1)
    (hout : C.output < k + 2 + C.size) (a f : ℕ)
    (h0 : ∀ y ⊆ H, y.card ≤ f → (C.wires (bitsOf (P ∪ y))).getD C.output false = false)
    (h1 : ∀ y ⊆ H, (H \ y).card ≤ a → (C.wires (bitsOf (P ∪ y))).getD C.output false = true) :
    (a + 1) * (f + 1) ≤ H.card := by
  obtain ⟨dep, inv⟩ := wire_inv C bitsOf hlen hbit hk0 hk1 P H hd hF hB hr C.output hout
  set F := Vw C bitsOf P H C.output with hFdef
  set L := Lw C H C.output with hLdef
  have hLH : L ⊆ H := Finset.filter_subset _ _
  have hFv : ∀ y, y ⊆ H → F y = (C.wires (bitsOf (P ∪ y))).getD C.output false := by
    intro y hy
    rw [hFdef, Vw, Finset.inter_eq_left.mpr hy]
  have ho : ((f + 1 : ℕ) : ℕ∞) ≤ oc true F L := by
    apply Finset.le_inf
    intro y hy
    have fy := (Finset.mem_filter.mp hy).2
    by_contra hlt
    have hlt' : (y ∩ L).card ≤ f := by
      have : ((y ∩ L).card : ℕ∞) < ((f + 1 : ℕ) : ℕ∞) := not_le.mp hlt
      have := (Nat.cast_lt (α := ℕ∞)).mp this
      omega
    have s : y ∩ L ⊆ H := Finset.inter_subset_right.trans hLH
    have e : F (y ∩ L) = F y := dep _ _ (by rw [Finset.inter_assoc, Finset.inter_self])
    have := h0 _ s hlt'
    rw [← hFv _ s, e, fy] at this
    exact Bool.noConfusion this
  have hz : ((a + 1 : ℕ) : ℕ∞) ≤ zc false F L := by
    apply Finset.le_inf
    intro y hy
    have fy := (Finset.mem_filter.mp hy).2
    by_contra hlt
    have hlt' : (L \ y).card ≤ a := by
      have : ((L \ y).card : ℕ∞) < ((a + 1 : ℕ) : ℕ∞) := not_le.mp hlt
      have := (Nat.cast_lt (α := ℕ∞)).mp this
      omega
    set y' := y ∩ L ∪ (H \ L) with hy'
    have s : y' ⊆ H := Finset.union_subset (Finset.inter_subset_right.trans hLH)
      Finset.sdiff_subset
    have e : F y' = F y := dep _ _ (by
      ext z; simp only [hy', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto)
    have hc : H \ y' = L \ y := by
      ext z; simp only [hy', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩; tauto
      · rintro ⟨h1, h2⟩; exact ⟨hLH h1, by tauto⟩
    have := h1 _ s (by rw [hc]; exact hlt')
    rw [← hFv _ s, e, fy] at this
    exact Bool.noConfusion this
  have hm : (((a + 1) * (f + 1) : ℕ) : ℕ∞) ≤ L.card := by
    calc (((a + 1) * (f + 1) : ℕ) : ℕ∞) = ((f + 1 : ℕ) : ℕ∞) * ((a + 1 : ℕ) : ℕ∞) := by
          push_cast; ring
      _ ≤ oc true F L * zc false F L := mul_le_mul' ho hz
      _ ≤ L.card := inv.1
  have := (Nat.cast_le (α := ℕ∞)).mp hm
  exact this.trans (Finset.card_le_card hLH)

theorem divmod (f r c : ℕ) (hc : c < f) : (f * r + c) / f = r ∧ (f * r + c) % f = c := by
  have hf : 0 < f := by omega
  constructor
  · rw [Nat.mul_add_div hf, Nat.div_eq_of_lt hc]; simp
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

theorem forall_le_succ (P : ℕ → Prop) (n : ℕ) :
    (∀ c ≤ n + 1, P c) ↔ (∀ c ≤ n, P c) ∧ P (n + 1) := by
  constructor
  · intro h; exact ⟨fun c hc => h c (by omega), h _ le_rfl⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases Nat.lt_or_ge c (n + 1) with h | h
    · exact h1 c (by omega)
    · rwa [show c = n + 1 by omega]

theorem exists_le_succ (P : ℕ → Prop) (n : ℕ) :
    (∃ c ≤ n + 1, P c) ↔ (∃ c ≤ n, P c) ∨ P (n + 1) := by
  constructor
  · rintro ⟨c, hc, h⟩
    rcases Nat.lt_or_ge c (n + 1) with h' | h'
    · exact Or.inl ⟨c, by omega, h⟩
    · rw [show c = n + 1 by omega] at h; exact Or.inr h
  · rintro (⟨c, hc, h⟩ | h)
    · exact ⟨c, by omega, h⟩
    · exact ⟨n + 1, le_rfl, h⟩

def mkC (m : ℕ) (G : ℕ → Gate) (out : ℕ) : Circuit := ⟨(List.range m).map G, out⟩

theorem mkC_size (m : ℕ) (G : ℕ → Gate) (out : ℕ) : (mkC m G out).size = m := by
  simp [mkC, Circuit.size]

theorem mkC_gateAt (m : ℕ) (G : ℕ → Gate) (out : ℕ) (j : ℕ) (hj : j < m) :
    gateAt (mkC m G out) j = G j := by
  simp [gateAt, mkC, List.getD_eq_getElem?_getD, hj]

theorem mkC_fan (m : ℕ) (G : ℕ → Gate) (out : ℕ)
    (h : ∀ j < m, ((G j).op = GateOp.and ∨ (G j).op = GateOp.or) ∧ (G j).inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.FanInTwo (mkC m G out) := by
  intro g hg
  simp only [mkC, List.mem_map, List.mem_range] at hg
  obtain ⟨j, hj, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := h j hj
  refine ⟨?_, h2⟩
  rcases h1 with h1 | h1 <;> simp [h1]

theorem mkC_back (N m : ℕ) (G : ℕ → Gate) (out : ℕ)
    (h : ∀ j < m, ∀ i ∈ (G j).inputs, i < N + j) : ReadsBack N (mkC m G out) := by
  intro j hj i hi
  have hj' : j < m := by simpa [mkC] using hj
  rw [mkC_gateAt m G out j hj'] at hi
  exact h j hj' i hi

theorem mkC_not (m : ℕ) (G : ℕ → Gate) (out : ℕ)
    (h : ∀ j < m, (G j).op = GateOp.and ∨ (G j).op = GateOp.or) :
    PEqualNP.NotBracket.notCount (mkC m G out) = 0 := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp only [mkC, List.mem_map, List.mem_range] at hg
  obtain ⟨j, hj, rfl⟩ := hg
  rcases h j hj with h1 | h1 <;> simp [h1]

theorem mkC_wire (N m : ℕ) (G : ℕ → Gate) (out : ℕ) (x : List Bool) (hx : x.length = N)
    (h : ∀ j < m, ∀ i ∈ (G j).inputs, i < N + j) (j : ℕ) (hj : j < m) :
    ((mkC m G out).wires x).getD (N + j) false = (G j).op.eval
      ((G j).inputs.map fun i => ((mkC m G out).wires x).getD i false) := by
  have := wire_gate (mkC m G out) x (by rw [hx]; exact mkC_back N m G out h) j
    (by rw [mkC_size]; exact hj)
  rw [hx, mkC_gateAt m G out j hj] at this
  exact this

theorem list_count_sum (l : List ℕ) (R : ℕ) (h : ∀ x ∈ l, x < R) :
    ∑ w ∈ Finset.range R, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    congr 1
    have hx := h x List.mem_cons_self
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hn; exact absurd (Finset.mem_range.mpr hx) hn

theorem tree_count (C : Circuit) (N : ℕ) (hl : ∀ j < C.size, (gateAt C j).inputs.length = 2)
    (hB : ReadsBack N C) (hout : C.output < N + C.size) (T : Finset ℕ)
    (hT : T ⊆ Finset.range (N + C.size)) (hcard : T.card = 2 * C.size + 1)
    (hcov : ∀ w ∈ T, 1 ≤ readsIn C (Finset.range C.size) w + (if C.output = w then 1 else 0)) :
    ∀ w < N + C.size, readsIn C (Finset.range C.size) w + (if C.output = w then 1 else 0) ≤ 1 := by
  set v := fun w => readsIn C (Finset.range C.size) w + (if C.output = w then 1 else 0) with hv
  have total : ∑ w ∈ Finset.range (N + C.size), v w = 2 * C.size + 1 := by
    simp only [hv, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hout)]
    unfold readsIn
    rw [Finset.sum_comm]
    have : ∀ j ∈ Finset.range C.size,
        ∑ w ∈ Finset.range (N + C.size), (gateAt C j).inputs.count w = 2 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [list_count_sum _ _ (fun x hx => by
        have := hB j (by simpa [Circuit.size] using hj') x hx
        omega), hl j hj']
    rw [Finset.sum_congr rfl this]
    simp; ring
  intro w0 hw0
  by_contra hgt
  have h2 : 2 ≤ v w0 := by simp only [hv]; omega
  set s := insert w0 T with hs
  have hpos : ∀ w ∈ s, 1 ≤ v w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · omega
    · exact hcov w hw
  have hsplit : ∑ w ∈ s, v w = ∑ w ∈ s, 1 + ∑ w ∈ s, (v w - 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw; have := hpos w hw; omega
  have hone : v w0 - 1 ≤ ∑ w ∈ s, (v w - 1) :=
    Finset.single_le_sum (f := fun w => v w - 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_insert_self w0 T)
  have hcs : T.card ≤ s.card := Finset.card_le_card (Finset.subset_insert w0 T)
  have hsub : s ⊆ Finset.range (N + C.size) :=
    Finset.insert_subset (Finset.mem_range.mpr hw0) hT
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := v) hsub (fun _ _ _ => Nat.zero_le _)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsplit
  omega

def inw (b f r c : ℕ) : ℕ := b + (f + 1) * r + c

def gout (N b f r : ℕ) : ℕ := if f = 0 then inw b f r 0 else N + (f * r + (f - 1))

def orG (N b a f : ℕ) (j : ℕ) : Gate :=
  if j < f * (a + 1) then
    ⟨GateOp.and, [if j % f = 0 then inw b f (j / f) 0 else N + j - 1, inw b f (j / f) (j % f + 1)]⟩
  else
    ⟨GateOp.or, [if j = f * (a + 1) then gout N b f 0 else N + j - 1,
      gout N b f (j - f * (a + 1) + 1)]⟩

def orOut (N b a f : ℕ) : ℕ := if a = 0 then gout N b f 0 else N + (f * (a + 1) + a) - 1

def orC (N b a f : ℕ) : Circuit :=
  mkC (f * (a + 1) + a) (orG N b a f) (orOut N b a f)

theorem block_lt (b a f r c N : ℕ) (hr : r ≤ a) (hc : c ≤ f) (hN : b + (a + 1) * (f + 1) ≤ N) :
    inw b f r c < N := by
  unfold inw
  have : (f + 1) * r ≤ (f + 1) * a := Nat.mul_le_mul_left _ hr
  have e : (a + 1) * (f + 1) = (f + 1) * a + f + 1 := by ring
  omega

theorem orG_and (N b a f r c : ℕ) (hr : r ≤ a) (hc : c < f) :
    orG N b a f (f * r + c) = ⟨GateOp.and,
      [if c = 0 then inw b f r 0 else N + (f * r + c) - 1, inw b f r (c + 1)]⟩ := by
  obtain ⟨h1, h2⟩ := divmod f r c hc
  have : f * r ≤ f * a := Nat.mul_le_mul_left _ hr
  have e : f * (a + 1) = f * a + f := by ring
  unfold orG
  rw [if_pos (by omega), h1, h2]

theorem orG_or (N b a f s : ℕ) :
    orG N b a f (f * (a + 1) + s) = ⟨GateOp.or,
      [if s = 0 then gout N b f 0 else N + (f * (a + 1) + s) - 1, gout N b f (s + 1)]⟩ := by
  unfold orG
  rw [if_neg (by omega)]
  congr 3
  · by_cases hs : s = 0 <;> simp [hs]
  · congr 1; omega

theorem orG_shape (N b a f j : ℕ) :
    ((orG N b a f j).op = GateOp.and ∨ (orG N b a f j).op = GateOp.or) ∧
      (orG N b a f j).inputs.length = 2 := by
  unfold orG; split_ifs <;> simp

theorem orG_back (N b a f : ℕ) (hN : b + (a + 1) * (f + 1) ≤ N) :
    ∀ j < f * (a + 1) + a, ∀ i ∈ (orG N b a f j).inputs, i < N + j := by
  have gl : ∀ r ≤ a, gout N b f r < N ∨ gout N b f r = N + (f * r + (f - 1)) ∧ 0 < f := by
    intro r hr
    unfold gout
    split_ifs with hf
    · exact Or.inl (block_lt b a f r 0 N hr (by omega) hN)
    · exact Or.inr ⟨rfl, by omega⟩
  intro j hj i hi
  by_cases hja : j < f * (a + 1)
  · have hf : 0 < f := by
      rcases Nat.eq_zero_or_pos f with h | h
      · subst h; simp at hja
      · exact h
    have hr : j / f ≤ a := by
      have := (Nat.div_lt_iff_lt_mul hf).mpr (by rw [mul_comm]; exact hja)
      omega
    obtain ⟨h1, h2⟩ := divmod f (j / f) (j % f) (Nat.mod_lt _ hf)
    have hjd : f * (j / f) + j % f = j := Nat.div_add_mod j f
    rw [← hjd, orG_and N b a f (j / f) (j % f) hr (Nat.mod_lt _ hf)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · split_ifs
      · have := block_lt b a f (j / f) 0 N hr (by omega) hN; omega
      · omega
    · have := block_lt b a f (j / f) (j % f + 1) N hr (by have := Nat.mod_lt j hf; omega) hN
      omega
  · obtain ⟨s, rfl⟩ : ∃ s, j = f * (a + 1) + s := ⟨j - f * (a + 1), by omega⟩
    rw [orG_or] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · split_ifs
      · rcases gl 0 (by omega) with h | ⟨h, _⟩
        · omega
        · rw [h]; have : f * 0 = 0 := by ring
          rw [this]; have : f ≤ f * (a + 1) := Nat.le_mul_of_pos_right f (by omega)
          omega
      · omega
    · rcases gl (s + 1) (by omega) with h | ⟨h, _⟩
      · omega
      · rw [h]
        have : f * (s + 1) ≤ f * a := Nat.mul_le_mul_left _ (by omega)
        have e : f * (a + 1) = f * a + f := by ring
        omega

theorem reads_of_mem (C : Circuit) (j : ℕ) (hj : j < C.size) (w : ℕ)
    (hw : w ∈ (gateAt C j).inputs) : 1 ≤ readsIn C (Finset.range C.size) w :=
  le_trans (List.count_pos_iff.mpr hw) (count_le_reads C j hj w)

section OrC
variable (N b a f : ℕ) (x : List Bool) (hx : x.length = N) (hN : b + (a + 1) * (f + 1) ≤ N)
include hx hN

theorem orC_and :
    ∀ r ≤ a, ∀ c < f, (((orC N b a f).wires x).getD (N + (f * r + c)) false = true ↔
      ∀ c' ≤ c + 1, x.getD (inw b f r c') false = true) := by
  intro r hr c
  have hin : ∀ c' ≤ f, ((orC N b a f).wires x).getD (inw b f r c') false =
      x.getD (inw b f r c') false := fun c' hc' =>
    wire_input' _ x _ (by rw [hx]; exact block_lt b a f r c' N hr hc' hN)
  have hfr : f * r ≤ f * a := Nat.mul_le_mul_left _ hr
  have e : f * (a + 1) = f * a + f := by ring
  induction c with
  | zero =>
    intro hc
    have hw := mkC_wire N (f * (a + 1) + a) (orG N b a f) (orOut N b a f) x hx (orG_back N b a f hN) (f * r + 0) (by omega)
    rw [orG_and N b a f r 0 hr hc] at hw
    unfold orC
    rw [hw]
    simp only [if_true, List.map_cons, List.map_nil]
    unfold orC at hin
    rw [hin 0 (by omega), hin 1 (by omega)]
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true]
    rw [forall_le_succ (fun c' => x.getD (inw b f r c') false = true) 0]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun c' hc' => by rwa [show c' = 0 by omega], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1 0 le_rfl, h2⟩
  | succ c ih =>
    intro hc
    have hw := mkC_wire N (f * (a + 1) + a) (orG N b a f) (orOut N b a f) x hx (orG_back N b a f hN) (f * r + (c + 1))
      (by omega)
    rw [orG_and N b a f r (c + 1) hr hc] at hw
    unfold orC
    rw [hw]
    simp only [show c + 1 ≠ 0 by omega, if_false, List.map_cons, List.map_nil]
    rw [show N + (f * r + (c + 1)) - 1 = N + (f * r + c) by omega]
    unfold orC at ih hin
    rw [hin (c + 1 + 1) (by omega)]
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true]
    rw [ih (by omega), forall_le_succ (fun c' => x.getD (inw b f r c') false = true) (c + 1)]

theorem orC_gout :
    ∀ r ≤ a, (((orC N b a f).wires x).getD (gout N b f r) false = true ↔
      ∀ c ≤ f, x.getD (inw b f r c) false = true) := by
  intro r hr
  unfold gout
  split_ifs with hf
  · rw [wire_input' _ x _ (by rw [hx]; exact block_lt b a f r 0 N hr (by omega) hN)]
    subst hf
    constructor
    · intro h c hc; rwa [show c = 0 by omega]
    · intro h; exact h 0 le_rfl
  · rw [orC_and N b a f x hx hN r hr (f - 1) (by omega), show f - 1 + 1 = f by omega]

theorem orC_or :
    ∀ s < a, (((orC N b a f).wires x).getD (N + (f * (a + 1) + s)) false = true ↔
      ∃ r ≤ s + 1, ∀ c ≤ f, x.getD (inw b f r c) false = true) := by
  intro s
  induction s with
  | zero =>
    intro hs
    have hw := mkC_wire N (f * (a + 1) + a) (orG N b a f) (orOut N b a f) x hx (orG_back N b a f hN) (f * (a + 1) + 0)
      (by omega)
    rw [orG_or] at hw
    unfold orC
    rw [hw]
    simp only [if_true, List.map_cons, List.map_nil]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true]
    have g0 := orC_gout N b a f x hx hN 0 (by omega)
    have g1 := orC_gout N b a f x hx hN (0 + 1) (by omega)
    unfold orC at g0 g1
    rw [g0, g1, exists_le_succ (fun r => ∀ c ≤ f, x.getD (inw b f r c) false = true) 0]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨0, le_rfl, h⟩
      · exact Or.inr h
    · rintro (⟨r, hr, h⟩ | h)
      · rw [show r = 0 by omega] at h; exact Or.inl h
      · exact Or.inr h
  | succ s ih =>
    intro hs
    have hw := mkC_wire N (f * (a + 1) + a) (orG N b a f) (orOut N b a f) x hx (orG_back N b a f hN) (f * (a + 1) + (s + 1))
      (by omega)
    rw [orG_or] at hw
    unfold orC
    rw [hw]
    simp only [show s + 1 ≠ 0 by omega, if_false, List.map_cons, List.map_nil]
    rw [show N + (f * (a + 1) + (s + 1)) - 1 = N + (f * (a + 1) + s) by omega]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true]
    have g1 := orC_gout N b a f x hx hN (s + 1 + 1) (by omega)
    unfold orC at g1 ih
    rw [g1, ih (by omega), exists_le_succ (fun r => ∀ c ≤ f, x.getD (inw b f r c) false = true)
      (s + 1)]

theorem orC_out :
    ((orC N b a f).wires x).getD (orC N b a f).output false = true ↔
      ∃ r ≤ a, ∀ c ≤ f, x.getD (inw b f r c) false = true := by
  change ((orC N b a f).wires x).getD (orOut N b a f) false = true ↔ _
  unfold orOut
  split_ifs with ha
  · rw [orC_gout N b a f x hx hN 0 (by omega)]
    subst ha
    constructor
    · intro h; exact ⟨0, le_rfl, h⟩
    · rintro ⟨r, hr, h⟩; rwa [show r = 0 by omega] at h
  · rw [show N + (f * (a + 1) + a) - 1 = N + (f * (a + 1) + (a - 1)) by omega,
      orC_or N b a f x hx hN (a - 1) (by omega), show a - 1 + 1 = a by omega]

end OrC

theorem orC_size (N b a f : ℕ) : (orC N b a f).size + 1 = (a + 1) * (f + 1) := by
  unfold orC; rw [mkC_size]; ring

theorem orC_valid (N b a f : ℕ) (hN : b + (a + 1) * (f + 1) ≤ N) :
    PEqualNP.MetaComplexity.FanInTwo (orC N b a f) ∧ ReadsBack N (orC N b a f) ∧
      (orC N b a f).output < N + (orC N b a f).size ∧
      PEqualNP.NotBracket.notCount (orC N b a f) = 0 := by
  refine ⟨mkC_fan _ _ _ (fun j _ => ⟨(orG_shape N b a f j).1, (orG_shape N b a f j).2.le⟩),
    mkC_back _ _ _ _ (orG_back N b a f hN), ?_, mkC_not _ _ _ (fun j _ => (orG_shape N b a f j).1)⟩
  unfold orC
  rw [mkC_size]
  change orOut N b a f < _
  unfold orOut
  split_ifs with ha
  · subst ha
    unfold gout
    split_ifs with hf
    · have := block_lt b 0 f 0 0 N le_rfl (by omega) hN; omega
    · have : f * 0 = 0 := by ring
      omega
  · omega

theorem orC_tree (N b a f : ℕ) (hN : b + (a + 1) * (f + 1) ≤ N) :
    ∀ w < N + (orC N b a f).size, readsIn (orC N b a f) (Finset.range (orC N b a f).size) w +
      (if (orC N b a f).output = w then 1 else 0) ≤ 1 := by
  have hsz : (orC N b a f).size = f * (a + 1) + a := mkC_size _ _ _
  have hM : (a + 1) * (f + 1) = f * (a + 1) + a + 1 := by ring
  have hga : ∀ j < f * (a + 1) + a, gateAt (orC N b a f) j = orG N b a f j :=
    fun j hj => mkC_gateAt _ _ _ j hj
  have hrd : ∀ j < f * (a + 1) + a, ∀ w ∈ (orG N b a f j).inputs,
      1 ≤ readsIn (orC N b a f) (Finset.range (orC N b a f).size) w := by
    intro j hj w hw
    exact reads_of_mem _ j (by rw [hsz]; exact hj) w (by rw [hga j hj]; exact hw)
  have hout : (orC N b a f).output = orOut N b a f := rfl
  have gcov : ∀ r ≤ a, 1 ≤ readsIn (orC N b a f) (Finset.range (orC N b a f).size)
      (gout N b f r) + (if (orC N b a f).output = gout N b f r then 1 else 0) := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · by_cases ha : a = 0
      · rw [hout, orOut, if_pos ha, if_pos rfl]; omega
      · have := hrd (f * (a + 1) + 0) (by omega) (gout N b f 0) (by rw [orG_or]; simp)
        omega
    · have := hrd (f * (a + 1) + (r - 1)) (by omega) (gout N b f r)
        (by rw [orG_or, show r - 1 + 1 = r by omega]; simp)
      omega
  apply tree_count (orC N b a f) N
    (fun j hj => by rw [hga j (by omega)]; exact (orG_shape N b a f j).2)
    (orC_valid N b a f hN).2.1 (orC_valid N b a f hN).2.2.1
    (Finset.Ico b (b + (a + 1) * (f + 1)) ∪ Finset.Ico N (N + (orC N b a f).size))
  · intro w hw
    simp only [Finset.mem_union, Finset.mem_Ico] at hw
    rw [Finset.mem_range]; omega
  · rw [Finset.card_union_of_disjoint, Nat.card_Ico, Nat.card_Ico, hsz]
    · omega
    · rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [Finset.mem_Ico] at h1 h2
      omega
  · intro w hw
    simp only [Finset.mem_union, Finset.mem_Ico] at hw
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨p, rfl⟩ : ∃ p, w = b + p := ⟨w - b, by omega⟩
      have hp : p < (a + 1) * (f + 1) := by omega
      have hr : p / (f + 1) ≤ a := by
        have := (Nat.div_lt_iff_lt_mul (show 0 < f + 1 by omega)).mpr hp
        omega
      have hc : p % (f + 1) < f + 1 := Nat.mod_lt _ (show 0 < f + 1 by omega)
      have hpd : (f + 1) * (p / (f + 1)) + p % (f + 1) = p := Nat.div_add_mod p (f + 1)
      have hw : b + p = inw b f (p / (f + 1)) (p % (f + 1)) := by unfold inw; omega
      rw [hw]
      set r := p / (f + 1)
      set c := p % (f + 1)
      have hfr : f * r ≤ f * a := Nat.mul_le_mul_left _ hr
      have e : f * (a + 1) = f * a + f := by ring
      by_cases hc0 : c = 0
      · by_cases hf : f = 0
        · have := gcov r hr
          unfold gout at this
          rw [if_pos hf] at this
          rw [hc0]; exact this
        · have := hrd (f * r + 0) (by omega) (inw b f r 0)
            (by rw [orG_and N b a f r 0 hr (by omega)]; simp)
          rw [hc0]; omega
      · have := hrd (f * r + (c - 1)) (by omega) (inw b f r c)
          (by rw [orG_and N b a f r (c - 1) hr (by omega), show c - 1 + 1 = c by omega]; simp)
        omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      rw [hsz] at h2
      by_cases hja : j < f * (a + 1)
      · have hf : 0 < f := by
          rcases Nat.eq_zero_or_pos f with h | h
          · subst h; simp at hja
          · exact h
        have hr : j / f ≤ a := by
          have := (Nat.div_lt_iff_lt_mul hf).mpr (by rw [mul_comm]; exact hja)
          omega
        have hc : j % f < f := Nat.mod_lt _ hf
        have hjd : f * (j / f) + j % f = j := Nat.div_add_mod j f
        set r := j / f
        set c := j % f
        have hfr : f * r ≤ f * a := Nat.mul_le_mul_left _ hr
        have e : f * (a + 1) = f * a + f := by ring
        by_cases hcf : c + 1 < f
        · have := hrd (f * r + (c + 1)) (by omega) (N + j)
            (by rw [orG_and N b a f r (c + 1) hr hcf]; simp; omega)
          omega
        · have := gcov r hr
          unfold gout at this
          rw [if_neg (by omega), show N + (f * r + (f - 1)) = N + j by omega] at this
          exact this
      · obtain ⟨s, rfl⟩ : ∃ s, j = f * (a + 1) + s := ⟨j - f * (a + 1), by omega⟩
        by_cases hs : s + 1 < a
        · have := hrd (f * (a + 1) + (s + 1)) (by omega) (N + (f * (a + 1) + s))
            (by rw [orG_or]; simp; omega)
          omega
        · have : (orC N b a f).output = N + (f * (a + 1) + s) := by
            rw [hout, orOut, if_neg (by omega)]; omega
          rw [if_pos this]; omega

def bef (N θ cF cT p q : ℕ) : ℕ :=
  if q = 0 then cT else if p = 0 then cF else N + (2 * (θ * (p - 1) + (q - 1)) + 1)

def thG (N b θ cF cT j : ℕ) : Gate :=
  if j % 2 = 0 then ⟨GateOp.and, [b + j / 2 / θ, bef N θ cF cT (j / 2 / θ) (j / 2 % θ)]⟩
  else ⟨GateOp.or, [bef N θ cF cT (j / 2 / θ) (j / 2 % θ + 1), N + 2 * (j / 2)]⟩

def thC (N b t θ cF cT : ℕ) : Circuit :=
  mkC (2 * (θ * t)) (thG N b θ cF cT) (N + 2 * (θ * t) - 1)

theorem thdec (θ p q e : ℕ) (hq : q < θ) (he : e < 2) :
    (2 * (θ * p + q) + e) / 2 = θ * p + q ∧ (2 * (θ * p + q) + e) % 2 = e ∧
      (θ * p + q) / θ = p ∧ (θ * p + q) % θ = q := by
  obtain ⟨h1, h2⟩ := divmod θ p q hq
  refine ⟨by omega, by omega, h1, h2⟩

theorem thG_and (N b θ cF cT p q : ℕ) (hq : q < θ) :
    thG N b θ cF cT (2 * (θ * p + q)) = ⟨GateOp.and, [b + p, bef N θ cF cT p q]⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := thdec θ p q 0 hq (by omega)
  simp only [Nat.add_zero] at h1 h2
  unfold thG; rw [h2, if_pos rfl, h1, h3, h4]

theorem thG_or (N b θ cF cT p q : ℕ) (hq : q < θ) :
    thG N b θ cF cT (2 * (θ * p + q) + 1) =
      ⟨GateOp.or, [bef N θ cF cT p (q + 1), N + 2 * (θ * p + q)]⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := thdec θ p q 1 hq (by omega)
  unfold thG; rw [h2, if_neg (by omega), h1, h3, h4]

theorem th_split (θ t j : ℕ) (hθ : 0 < θ) (hj : j < 2 * (θ * t)) :
    ∃ p q e, p < t ∧ q < θ ∧ e < 2 ∧ j = 2 * (θ * p + q) + e := by
  refine ⟨j / 2 / θ, j / 2 % θ, j % 2, ?_, Nat.mod_lt _ hθ, Nat.mod_lt _ (by omega), ?_⟩
  · apply (Nat.div_lt_iff_lt_mul hθ).mpr
    have : j / 2 < θ * t := by omega
    rw [mul_comm]; exact this
  · have h1 := Nat.div_add_mod j 2
    have h2 := Nat.div_add_mod (j / 2) θ
    omega

theorem thG_back (N b t θ cF cT : ℕ) (hθ : 0 < θ) (hb : b + t ≤ N) (hF : cF < N)
    (hT : cT < N) : ∀ j < 2 * (θ * t), ∀ i ∈ (thG N b θ cF cT j).inputs, i < N + j := by
  intro j hj i hi
  obtain ⟨p, q, e, hp, hq, he, rfl⟩ := th_split θ t j hθ hj
  have befb : ∀ q', q' ≤ θ → bef N θ cF cT p q' < N ∨
      (0 < p ∧ 0 < q' ∧ bef N θ cF cT p q' = N + (2 * (θ * (p - 1) + (q' - 1)) + 1)) := by
    intro q' hq'
    unfold bef
    split_ifs with h1 h2
    · exact Or.inl hT
    · exact Or.inl hF
    · exact Or.inr ⟨by omega, by omega, rfl⟩
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [Nat.add_zero, thG_and N b θ cF cT p q hq] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · omega
    · rcases befb q hq.le with h | ⟨h0, h1, h⟩
      · omega
      · rw [h]
        obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
        have : θ * (p' + 1) = θ * p' + θ := by ring
        rw [show p' + 1 - 1 = p' by omega]
        omega
  · rw [thG_or N b θ cF cT p q hq] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rcases befb (q + 1) hq with h | ⟨h0, h1, h⟩
      · omega
      · rw [h]
        obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
        have : θ * (p' + 1) = θ * p' + θ := by ring
        rw [show p' + 1 - 1 = p' by omega]
        omega
    · omega

theorem thG_shape (N b θ cF cT j : ℕ) :
    ((thG N b θ cF cT j).op = GateOp.and ∨ (thG N b θ cF cT j).op = GateOp.or) ∧
      (thG N b θ cF cT j).inputs.length ≤ 2 := by
  unfold thG; split_ifs <;> simp

def ones (x : List Bool) (b p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun c => x.getD (b + c) false = true)).card

theorem ones_succ (x : List Bool) (b p : ℕ) :
    ones x b (p + 1) = ones x b p + (if x.getD (b + p) false = true then 1 else 0) := by
  unfold ones
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem thC_val (N b t θ cF cT : ℕ) (hθ : 0 < θ) (hb : b + t ≤ N) (hF : cF < N)
    (hT : cT < N) (x : List Bool) (hx : x.length = N) (hxF : x.getD cF false = false)
    (hxT : x.getD cT false = true) :
    ∀ p < t, ∀ q < θ, (((thC N b t θ cF cT).wires x).getD (N + (2 * (θ * p + q) + 1)) false
      = true ↔ q + 1 ≤ ones x b (p + 1)) := by
  have hB := thG_back N b t θ cF cT hθ hb hF hT
  set W := fun i => ((thC N b t θ cF cT).wires x).getD i false with hW
  have hwF : W cF = false := by
    simp only [hW]; rw [wire_input' _ x _ (by omega), hxF]
  have hwT : W cT = true := by
    simp only [hW]; rw [wire_input' _ x _ (by omega), hxT]
  have befval : ∀ p, (p = 0 ∨ ∀ q < θ, (W (N + (2 * (θ * (p - 1) + q) + 1)) = true ↔
      q + 1 ≤ ones x b (p - 1 + 1))) → ∀ q ≤ θ, (W (bef N θ cF cT p q) = true ↔ q ≤ ones x b p) := by
    intro p hp q hq
    unfold bef
    split_ifs with h1 h2
    · rw [hwT]; simp [h1]
    · rw [hwF, h2]; simp [ones]; omega
    · rcases hp with hp | hp
      · exact absurd hp h2
      · rw [hp (q - 1) (by omega), show q - 1 + 1 = q by omega, show p - 1 + 1 = p by omega]
  have step : ∀ p < t, (p = 0 ∨ ∀ q < θ, (W (N + (2 * (θ * (p - 1) + q) + 1)) = true ↔
      q + 1 ≤ ones x b (p - 1 + 1))) → ∀ q < θ, (W (N + (2 * (θ * p + q) + 1)) = true ↔
      q + 1 ≤ ones x b (p + 1)) := by
    intro p hp hprev q hq
    have hpt : θ * p + θ ≤ θ * t := by
      have := Nat.mul_le_mul_left θ (show p + 1 ≤ t by omega)
      have e : θ * (p + 1) = θ * p + θ := by ring
      omega
    have hor := mkC_wire N (2 * (θ * t)) (thG N b θ cF cT) (N + 2 * (θ * t) - 1) x hx hB
      (2 * (θ * p + q) + 1) (by omega)
    have hand := mkC_wire N (2 * (θ * t)) (thG N b θ cF cT) (N + 2 * (θ * t) - 1) x hx hB
      (2 * (θ * p + q)) (by omega)
    rw [thG_or N b θ cF cT p q hq] at hor
    rw [thG_and N b θ cF cT p q hq] at hand
    have hxb : W (b + p) = x.getD (b + p) false := by
      simp only [hW]; rw [wire_input' _ x _ (by omega)]
    change W (N + (2 * (θ * p + q) + 1)) = _ at hor
    change W (N + 2 * (θ * p + q)) = _ at hand
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true] at hor hand
    change _ = (W (bef N θ cF cT p (q + 1)) || W (N + 2 * (θ * p + q))) at hor
    change _ = (W (b + p) && W (bef N θ cF cT p q)) at hand
    rw [hor, hand, hxb, Bool.or_eq_true, Bool.and_eq_true, befval p hprev (q + 1) hq,
      befval p hprev q hq.le, ones_succ]
    cases x.getD (b + p) false <;> simp <;> omega
  intro p
  induction p with
  | zero => intro hp; exact step 0 hp (Or.inl rfl)
  | succ p ih =>
    intro hp
    refine step (p + 1) hp (Or.inr ?_)
    rw [show p + 1 - 1 = p by omega]
    exact ih (by omega)

theorem thC_out (N b t θ cF cT : ℕ) (hθ : 0 < θ) (ht : 0 < t) (hb : b + t ≤ N) (hF : cF < N)
    (hT : cT < N) (x : List Bool) (hx : x.length = N) (hxF : x.getD cF false = false)
    (hxT : x.getD cT false = true) :
    ((thC N b t θ cF cT).wires x).getD (thC N b t θ cF cT).output false = true ↔
      θ ≤ ones x b t := by
  have := thC_val N b t θ cF cT hθ hb hF hT x hx hxF hxT (t - 1) (by omega) (θ - 1) (by omega)
  have e : N + (2 * (θ * (t - 1) + (θ - 1)) + 1) = N + 2 * (θ * t) - 1 := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have : θ * (t' + 1) = θ * t' + θ := by ring
    rw [show t' + 1 - 1 = t' by omega]
    omega
  rw [e, show θ - 1 + 1 = θ by omega, show t - 1 + 1 = t by omega] at this
  exact this

theorem thC_valid (N b t θ cF cT : ℕ) (hθ : 0 < θ) (ht : 0 < t) (hb : b + t ≤ N) (hF : cF < N)
    (hT : cT < N) :
    PEqualNP.MetaComplexity.FanInTwo (thC N b t θ cF cT) ∧ ReadsBack N (thC N b t θ cF cT) ∧
      (thC N b t θ cF cT).output < N + (thC N b t θ cF cT).size ∧
      PEqualNP.NotBracket.notCount (thC N b t θ cF cT) = 0 ∧
      (thC N b t θ cF cT).size = 2 * (θ * t) := by
  refine ⟨mkC_fan _ _ _ (fun j _ => thG_shape N b θ cF cT j),
    mkC_back _ _ _ _ (thG_back N b t θ cF cT hθ hb hF hT), ?_,
    mkC_not _ _ _ (fun j _ => (thG_shape N b θ cF cT j).1), mkC_size _ _ _⟩
  unfold thC
  rw [mkC_size]
  change N + 2 * (θ * t) - 1 < _
  have : 0 < θ * t := Nat.mul_pos hθ ht
  omega

theorem card_ge {k : ℕ} (U : Finset ℕ) (φ : ℕ → ℕ) (hφ : ∀ c1 ∈ U, ∀ c2 ∈ U, φ c1 = φ c2 → c1 = c2)
    (s : Finset (Fin k)) (h : ∀ c ∈ U, ∃ z ∈ s, z.val = φ c) : U.card ≤ s.card := by
  have h1 : U.card ≤ (s.image Fin.val).card := by
    apply Finset.card_le_card_of_injOn φ
    · intro c hc
      obtain ⟨z, hz, e⟩ := h c hc
      exact Finset.mem_image.mpr ⟨z, hz, e⟩
    · intro c1 hc1 c2 hc2 e
      exact hφ c1 hc1 c2 hc2 e
  exact h1.trans Finset.card_image_le

theorem grp_inj (b f r1 r2 c1 c2 : ℕ) (h1 : c1 ≤ f) (h2 : c2 ≤ f)
    (e : b + (f + 1) * r1 + c1 = b + (f + 1) * r2 + c2) : r1 = r2 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.mul_le_mul_left (f + 1) (show r1 + 1 ≤ r2 by omega)
    have e2 : (f + 1) * (r1 + 1) = (f + 1) * r1 + f + 1 := by ring
    omega
  · have := Nat.mul_le_mul_left (f + 1) (show r2 + 1 ≤ r1 by omega)
    have e2 : (f + 1) * (r2 + 1) = (f + 1) * r2 + f + 1 := by ring
    omega

theorem dec_eq {p : Prop} {inst : Decidable p} (b : Bool) (h : b = true ↔ p) :
    b = @decide p inst := by
  cases inst with
  | isFalse hp => cases b <;> simp_all
  | isTrue hp => cases b <;> simp_all

theorem ideal_sum {n k : ℕ} (R : Fin n → Fin n → Prop) (cost : Fin n → ℕ)
    (htrans : ∀ i j h, R i j → R j h → R i h) (hanti : ∀ i j, R i j → R j i → i = j)
    (hrefl : ∀ i, R i i)
    (g : Finset (Fin n) → Finset (Fin k))
    (mono : ∀ A B : Finset (Fin n), (∀ i j, j ∈ A → R i j → i ∈ A) →
      (∀ i j, j ∈ B → R i j → i ∈ B) → A ⊆ B → g A ⊆ g B)
    (step : ∀ (A : Finset (Fin n)) (i : Fin n), (∀ i j, j ∈ A → R i j → i ∈ A) →
      (∀ i' j, j ∈ insert i A → R i' j → i' ∈ insert i A) → i ∉ A →
      cost i ≤ (g (insert i A) \ g A).card) :
    ∀ m (A : Finset (Fin n)), A.card = m → (∀ i j, j ∈ A → R i j → i ∈ A) →
      A.sum cost ≤ (g A).card := by
  intro m
  induction m with
  | zero =>
    intro A hA _
    rw [Finset.card_eq_zero.mp hA]; simp
  | succ m ih =>
    intro A hA hid
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    classical
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image A
      (fun i => (A.filter (fun j => R j i)).card) hne
    have imax : ∀ j ∈ A, R i j → j = i := by
      intro j hj hij
      by_contra hne'
      have hsub : A.filter (fun z => R z i) ⊂ A.filter (fun z => R z j) := by
        refine ⟨fun z hz => ?_, fun h => ?_⟩
        · simp only [Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, htrans _ _ _ hz.2 hij⟩
        · have : j ∈ A.filter (fun z => R z i) := h (by simp [hj, hrefl])
          simp only [Finset.mem_filter] at this
          exact hne' (hanti _ _ this.2 hij)
      have := Finset.card_lt_card hsub
      have := hmax j hj
      omega
    set A' := A.erase i with hA'
    have hid' : ∀ i' j, j ∈ A' → R i' j → i' ∈ A' := by
      intro i' j hj hr
      rw [Finset.mem_erase] at hj ⊢
      refine ⟨?_, hid i' j hj.2 hr⟩
      rintro rfl
      exact hj.1 (imax j hj.2 hr)
    have hins : insert i A' = A := Finset.insert_erase hi
    have hnot : i ∉ A' := Finset.notMem_erase i A
    have hs := step A' i hid' (by rw [hins]; exact hid) hnot
    rw [hins] at hs
    have ih' := ih A' (by rw [Finset.card_erase_of_mem hi]; omega) hid'
    have hsub : g A' ⊆ g A := mono A' A hid' hid (Finset.erase_subset i A)
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    have e1 : A.sum cost = cost i + A'.sum cost := by
      rw [← hins, Finset.sum_insert hnot]
    rw [e1]
    omega

theorem step_bound {k : ℕ} (D : Circuit) (bitsOf : Finset (Fin k) → List Bool)
    (hlen : ∀ Y, (bitsOf Y).length = k + 2)
    (hbit : ∀ Y (x : Fin k), (bitsOf Y).getD x.val false = decide (x ∈ Y))
    (hk0 : ∀ Y, (bitsOf Y).getD k false = false)
    (hk1 : ∀ Y, (bitsOf Y).getD (k + 1) false = true)
    (P Q : Finset (Fin k)) (a f : ℕ)
    (h0 : ∀ y, y ⊆ Q \ P → y.card ≤ f → (D.wires (bitsOf (P ∪ y))).getD D.output false = false)
    (h1 : ∀ y, y ⊆ Q \ P → ((Q \ P) \ y).card ≤ a →
      (D.wires (bitsOf (P ∪ y))).getD D.output false = true) :
    a + f + 1 ≤ (Q \ P).card ∧
      (PEqualNP.MetaComplexity.FanInTwo D → ReadsBack (k + 2) D →
        (∀ x < k + 2 + D.size, readsIn D (Finset.range D.size) x ≤ 1) →
        D.output < k + 2 + D.size → (a + 1) * (f + 1) ≤ (Q \ P).card) := by
  constructor
  · by_contra hlt
    obtain ⟨y, hy, hc⟩ := Finset.exists_subset_card_eq (s := Q \ P) (n := min f (Q \ P).card)
      (min_le_right _ _)
    have e0 := h0 y hy (by omega)
    have e1 := h1 y hy (by rw [Finset.card_sdiff_of_subset hy]; omega)
    rw [e0] at e1
    exact Bool.noConfusion e1
  · intro hF hB hr hout
    exact tree_bound D bitsOf hlen hbit hk0 hk1 P (Q \ P) Finset.disjoint_sdiff hF hB hr hout a f
      h0 h1

end PEqualNP.Outside.L_lib_1450_aux

theorem PEqualNP.Outside.L_lib_1450 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (n k : Nat) (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) (a f : Fin n → Nat),
  (∀ i, R i i) → (∀ i j h, R i j → R j h → R i h) → (∀ i j, R i j → R j i → i = j) →
  let ideal := fun (A : Finset (Fin n)) => ∀ i j, j ∈ A → R i j → i ∈ A
  let bits := fun (Y : Finset (Fin k)) => List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true]
  let t := fun i => a i+f i+1
  let cost := fun i => if i ∈ S then (a i+1)*(f i+1) else t i
  let tree := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∀ j < k+2+D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) j +
      (if D.output=j then 1 else 0) ≤ 1
  let fit := fun (bounded : Prop) =>
    ∃ (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → PEqualNP.CircuitLowerBounds.Circuit),
      (∀ A B, ideal A → ideal B → A ⊆ B → g A ⊆ g B) ∧
      (∀ i, PEqualNP.MetaComplexity.FanInTwo (D i) ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) (D i) ∧ (D i).output < k+2+(D i).size ∧
        (i ∈ S → tree (D i))) ∧
      (∀ A, ideal A → ∀ Y i, (g A \ Y).card ≤ a i → (Y \ g A).card ≤ f i →
        ((D i).wires (bits Y)).getD (D i).output false = decide (i ∈ A)) ∧
      (bounded → (∃ pin : Fin k → Option (Fin n), ∀ A j, j ∈ g A ↔ ∃ i ∈ A, pin j=some i) ∧
        ∀ i, PEqualNP.NotBracket.notCount (D i)=0 ∧
          (D i).size ≤ if i ∈ S then cost i-1 else 2*(t i+1)^2)
  (fit False ↔ (Finset.univ.sum cost ≤ k)) ∧ ((Finset.univ.sum cost ≤ k) → fit True)) := by
  intro n k R S a f hrefl htrans hanti ideal bits t cost tree fit
  have hlen : ∀ Y, (bits Y).length = k + 2 := by intro Y; simp [bits]
  have hbit : ∀ Y (x : Fin k), (bits Y).getD x.val false = decide (x ∈ Y) := by
    intro Y x
    simp only [bits, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp)]
    simp
  have hk0 : ∀ Y, (bits Y).getD k false = false := by
    intro Y
    simp only [bits, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp
  have hk1 : ∀ Y, (bits Y).getD (k + 1) false = true := by
    intro Y
    simp only [bits, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp
  have up : Finset.univ.sum cost ≤ k → fit True := by
    intro hsum
    classical
    let off : Fin n → ℕ := fun i => ∑ j ∈ Finset.univ.filter (fun j => j < i), cost j
    have hoff1 : ∀ i, off i + cost i ≤ k := by
      intro i
      have hs : insert i (Finset.univ.filter (fun j => j < i)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := cost) hs (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_insert (by simp)] at this
      have e : Finset.univ.sum cost = ∑ i, cost i := rfl
      simp only [off]; omega
    have hoff2 : ∀ i i', i < i' → off i + cost i ≤ off i' := by
      intro i i' hii
      have hs : insert i (Finset.univ.filter (fun j => j < i)) ⊆
          Finset.univ.filter (fun j => j < i') := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rcases hz with rfl | hz
        · exact hii
        · exact lt_trans hz hii
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := cost) hs (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_insert (by simp)] at this
      simp only [off]; omega
    have huniq : ∀ i i' (z : ℕ), off i ≤ z → z < off i + cost i → off i' ≤ z →
        z < off i' + cost i' → i = i' := by
      intro i i' z h1 h2 h3 h4
      rcases lt_trichotomy i i' with h | h | h
      · have := hoff2 i i' h; omega
      · exact h
      · have := hoff2 i' i h; omega
    let pin : Fin k → Option (Fin n) := fun j =>
      if h : ∃ i, off i ≤ j.val ∧ j.val < off i + cost i then some h.choose else none
    have hpin : ∀ j i, pin j = some i ↔ off i ≤ j.val ∧ j.val < off i + cost i := by
      intro j i
      simp only [pin]
      split_ifs with h
      · have hc := h.choose_spec
        constructor
        · intro e; simp only [Option.some.injEq] at e; rw [← e]; exact hc
        · intro hi
          rw [huniq _ _ j.val hc.1 hc.2 hi.1 hi.2]
      · simp only [reduceCtorEq, false_iff]
        intro hi; exact h ⟨i, hi⟩
    let g : Finset (Fin n) → Finset (Fin k) := fun A =>
      Finset.univ.filter (fun j => ∃ i ∈ A, pin j = some i)
    have hg : ∀ A j, j ∈ g A ↔ ∃ i ∈ A, pin j = some i := by
      intro A j; simp [g]
    have hblock : ∀ A i (c : ℕ) (hc : c < cost i), ((⟨off i + c, by have := hoff1 i; omega⟩ :
        Fin k) ∈ g A ↔ i ∈ A) := by
      intro A i c hc
      rw [hg]
      constructor
      · rintro ⟨i', hi', e⟩
        rw [hpin] at e
        have : i = i' := huniq i i' (off i + c) (by omega) (by omega) e.1 e.2
        rw [this]; exact hi'
      · intro hi
        exact ⟨i, hi, (hpin _ _).mpr ⟨by simp, by simp; omega⟩⟩
    let D : Fin n → PEqualNP.CircuitLowerBounds.Circuit := fun i =>
      if i ∈ S then PEqualNP.Outside.L_lib_1450_aux.orC (k + 2) (off i) (a i) (f i)
      else PEqualNP.Outside.L_lib_1450_aux.thC (k + 2) (off i) (t i) (f i + 1) k (k + 1)
    have hcS : ∀ i, i ∈ S → cost i = (a i + 1) * (f i + 1) := by
      intro i hi; simp [cost, hi]
    have hcN : ∀ i, i ∉ S → cost i = t i := by
      intro i hi; simp [cost, hi]
    have hxF : ∀ Y, (bits Y).getD k false = false := hk0
    have hxT : ∀ Y, (bits Y).getD (k + 1) false = true := hk1
    have hXY : ∀ Y (z : ℕ) (hz : z < k), ((bits Y).getD z false = true ↔
        (⟨z, hz⟩ : Fin k) ∈ Y) := by
      intro Y z hz
      have := hbit Y ⟨z, hz⟩
      simp only at this
      rw [this, decide_eq_true_iff]
    refine ⟨g, D, ?_, ?_, ?_, fun _ => ⟨⟨pin, hg⟩, ?_⟩⟩
    · intro A B _ _ hAB j hj
      rw [hg] at hj ⊢
      obtain ⟨i, hi, e⟩ := hj
      exact ⟨i, hAB hi, e⟩
    · intro i
      by_cases hS : i ∈ S
      · have hN : off i + (a i + 1) * (f i + 1) ≤ k + 2 := by
          have := hoff1 i; rw [hcS i hS] at this; omega
        have hv := PEqualNP.Outside.L_lib_1450_aux.orC_valid (k + 2) (off i) (a i) (f i) hN
        simp only [D, if_pos hS]
        refine ⟨hv.1, hv.2.1, hv.2.2.1, fun _ w hw => ?_⟩
        have h := PEqualNP.Outside.L_lib_1450_aux.orC_tree (k + 2) (off i) (a i) (f i) hN w hw
        by_cases e : (PEqualNP.Outside.L_lib_1450_aux.orC (k + 2) (off i) (a i) (f i)).output = w
        · simpa [e] using h
        · simpa [e] using h
      · have hN : off i + t i ≤ k + 2 := by
          have := hoff1 i; rw [hcN i hS] at this; omega
        have hv := PEqualNP.Outside.L_lib_1450_aux.thC_valid (k + 2) (off i) (t i) (f i + 1) k
          (k + 1) (by omega) (by simp [t]) hN (by omega) (by omega)
        simp only [D, if_neg hS]
        exact ⟨hv.1, hv.2.1, hv.2.2.1, fun h => absurd h hS⟩
    · intro A _ Y i h1 h2
      by_cases hS : i ∈ S
      · have hN : off i + (a i + 1) * (f i + 1) ≤ k + 2 := by
          have := hoff1 i; rw [hcS i hS] at this; omega
        have hk : off i + (a i + 1) * (f i + 1) ≤ k := by
          have := hoff1 i; rw [hcS i hS] at this; omega
        have hout := PEqualNP.Outside.L_lib_1450_aux.orC_out (k + 2) (off i) (a i) (f i) (bits Y)
          (hlen Y) hN
        have hin : ∀ r ≤ a i, ∀ c ≤ f i,
            PEqualNP.Outside.L_lib_1450_aux.inw (off i) (f i) r c < off i + cost i := by
          intro r hr c hc
          have := PEqualNP.Outside.L_lib_1450_aux.block_lt (off i) (a i) (f i) r c
            (off i + (a i + 1) * (f i + 1)) hr hc le_rfl
          rw [hcS i hS]; exact this
        simp only [D, if_pos hS]
        apply PEqualNP.Outside.L_lib_1450_aux.dec_eq
        constructor
        · intro hW
          by_contra hi
          obtain ⟨r, hr, hall⟩ := hout.mp hW
          have := le_trans (PEqualNP.Outside.L_lib_1450_aux.card_ge (Finset.range (f i + 1))
            (fun c => PEqualNP.Outside.L_lib_1450_aux.inw (off i) (f i) r c)
            (by
              intro c1 _ c2 _ e
              unfold PEqualNP.Outside.L_lib_1450_aux.inw at e; omega)
            _
            (by
              intro c hc
              simp only [Finset.mem_range] at hc
              have hb := hin r hr c (by omega)
              have hk' := hoff1 i
              refine ⟨⟨PEqualNP.Outside.L_lib_1450_aux.inw (off i) (f i) r c, by omega⟩, ?_, rfl⟩
              simp only [Finset.mem_sdiff]
              constructor
              · exact (hXY Y _ (by omega)).mp (hall c (by omega))
              · intro hgA
                have := (hblock A i (PEqualNP.Outside.L_lib_1450_aux.inw (off i) (f i) r c - off i)
                  (by unfold PEqualNP.Outside.L_lib_1450_aux.inw at hb ⊢; omega)).mp
                  (by convert hgA using 2; unfold PEqualNP.Outside.L_lib_1450_aux.inw; omega)
                exact hi this)) h2
          simp at this <;> omega
        · intro hi
          apply hout.mpr
          by_contra hne
          push_neg at hne
          choose cf hcf using hne
          let φ : ℕ → ℕ := fun r => if h : r ≤ a i then
            PEqualNP.Outside.L_lib_1450_aux.inw (off i) (f i) r (cf r h) else 0
          have := le_trans (PEqualNP.Outside.L_lib_1450_aux.card_ge (Finset.range (a i + 1)) φ
            (by
              intro r1 hr1 r2 hr2 e
              simp only [Finset.mem_range] at hr1 hr2
              simp only [φ, dif_pos (show r1 ≤ a i by omega), dif_pos (show r2 ≤ a i by omega),
                PEqualNP.Outside.L_lib_1450_aux.inw] at e
              exact PEqualNP.Outside.L_lib_1450_aux.grp_inj _ _ _ _ _ _
                (hcf r1 (by omega)).1 (hcf r2 (by omega)).1 e)
            _
            (by
              intro r hr
              simp only [Finset.mem_range] at hr
              have hr' : r ≤ a i := by omega
              have hb := hin r hr' (cf r hr') (hcf r hr').1
              have hk' := hoff1 i
              refine ⟨⟨PEqualNP.Outside.L_lib_1450_aux.inw (off i) (f i) r (cf r hr'),
                by omega⟩, ?_, by simp [φ, hr']⟩
              simp only [Finset.mem_sdiff]
              constructor
              · have := (hblock A i (PEqualNP.Outside.L_lib_1450_aux.inw (off i) (f i) r
                  (cf r hr') - off i) (by unfold PEqualNP.Outside.L_lib_1450_aux.inw at hb ⊢; omega)).mpr hi
                convert this using 2
                unfold PEqualNP.Outside.L_lib_1450_aux.inw; omega
              · intro hY
                exact (hcf r hr').2 ((hXY Y _ (by omega)).mpr hY))) h1
          simp at this <;> omega
      · have hN : off i + t i ≤ k + 2 := by
          have := hoff1 i; rw [hcN i hS] at this; omega
        have hk : off i + t i ≤ k := by
          have := hoff1 i; rw [hcN i hS] at this; omega
        have hout := PEqualNP.Outside.L_lib_1450_aux.thC_out (k + 2) (off i) (t i) (f i + 1) k
          (k + 1) (by omega) (by simp [t]) hN (by omega) (by omega) (bits Y) (hlen Y) (hxF Y)
          (hxT Y)
        simp only [D, if_neg hS]
        have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (t i))
          (fun c => (bits Y).getD (off i + c) false = true)
        rw [Finset.card_range] at hsplit
        have ht : t i = a i + f i + 1 := rfl
        apply PEqualNP.Outside.L_lib_1450_aux.dec_eq
        constructor
        · intro hW
          by_contra hi
          have hge := hout.mp hW
          have := le_trans (PEqualNP.Outside.L_lib_1450_aux.card_ge
            ((Finset.range (t i)).filter (fun c => (bits Y).getD (off i + c) false = true))
            (fun c => off i + c) (by intro c1 _ c2 _ e; simp at e; exact e) _
            (by
              intro c hc
              simp only [Finset.mem_filter, Finset.mem_range] at hc
              refine ⟨⟨off i + c, by omega⟩, ?_, rfl⟩
              simp only [Finset.mem_sdiff]
              exact ⟨(hXY Y _ (by omega)).mp hc.2,
                fun hgA => hi ((hblock A i c (by rw [hcN i hS]; exact hc.1)).mp hgA)⟩)) h2
          unfold PEqualNP.Outside.L_lib_1450_aux.ones at hge
          omega
        · intro hi
          apply hout.mpr
          have := le_trans (PEqualNP.Outside.L_lib_1450_aux.card_ge
            ((Finset.range (t i)).filter (fun c => ¬ (bits Y).getD (off i + c) false = true))
            (fun c => off i + c) (by intro c1 _ c2 _ e; simp at e; exact e) _
            (by
              intro c hc
              simp only [Finset.mem_filter, Finset.mem_range] at hc
              refine ⟨⟨off i + c, by omega⟩, ?_, rfl⟩
              simp only [Finset.mem_sdiff]
              exact ⟨(hblock A i c (by rw [hcN i hS]; exact hc.1)).mpr hi,
                fun hY => hc.2 ((hXY Y _ (by omega)).mpr hY)⟩)) h1
          unfold PEqualNP.Outside.L_lib_1450_aux.ones
          omega
    · intro i
      by_cases hS : i ∈ S
      · have hN : off i + (a i + 1) * (f i + 1) ≤ k + 2 := by
          have := hoff1 i; rw [hcS i hS] at this; omega
        have hv := PEqualNP.Outside.L_lib_1450_aux.orC_valid (k + 2) (off i) (a i) (f i) hN
        have hs := PEqualNP.Outside.L_lib_1450_aux.orC_size (k + 2) (off i) (a i) (f i)
        simp only [D, if_pos hS]
        refine ⟨hv.2.2.2, ?_⟩
        rw [hcS i hS]; omega
      · have hN : off i + t i ≤ k + 2 := by
          have := hoff1 i; rw [hcN i hS] at this; omega
        have hv := PEqualNP.Outside.L_lib_1450_aux.thC_valid (k + 2) (off i) (t i) (f i + 1) k
          (k + 1) (by omega) (by simp [t]) hN (by omega) (by omega)
        simp only [D, if_neg hS]
        refine ⟨hv.2.2.2.1, ?_⟩
        rw [hv.2.2.2.2]
        have ht : f i + 1 ≤ t i := by simp [t]
        nlinarith
  have down : fit False → Finset.univ.sum cost ≤ k := by
    rintro ⟨g, D, mono, valid, dec, _⟩
    have step : ∀ (A : Finset (Fin n)) (i : Fin n), (∀ i j, j ∈ A → R i j → i ∈ A) →
        (∀ i' j, j ∈ insert i A → R i' j → i' ∈ insert i A) → i ∉ A →
        cost i ≤ (g (insert i A) \ g A).card := by
      intro A i hA hB hi
      have hsub : g A ⊆ g (insert i A) := mono A _ hA hB (Finset.subset_insert i A)
      have h0 : ∀ y, y ⊆ g (insert i A) \ g A → y.card ≤ f i →
          ((D i).wires (bits (g A ∪ y))).getD (D i).output false = false := by
        intro y hy hc
        have := dec A hA (g A ∪ y) i
          (by
            refine le_trans (le_of_eq ?_) (Nat.zero_le (a i))
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro z hz
            simp only [Finset.mem_sdiff, Finset.mem_union] at hz
            exact hz.2 (Or.inl hz.1))
          (by
            refine le_trans (Finset.card_le_card ?_) hc
            intro z hz
            simp only [Finset.mem_sdiff, Finset.mem_union] at hz
            rcases hz with ⟨h | h, h'⟩
            · exact absurd h h'
            · exact h)
        rw [this]; simp [hi]
      have h1 : ∀ y, y ⊆ g (insert i A) \ g A → ((g (insert i A) \ g A) \ y).card ≤ a i →
          ((D i).wires (bits (g A ∪ y))).getD (D i).output false = true := by
        intro y hy hc
        have := dec (insert i A) hB (g A ∪ y) i
          (by
            refine le_trans (Finset.card_le_card ?_) hc
            intro z hz; simp at hz ⊢; tauto)
          (by
            refine le_trans (le_of_eq ?_) (Nat.zero_le (f i))
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro z hz
            simp only [Finset.mem_sdiff, Finset.mem_union] at hz
            rcases hz with ⟨h | h, h'⟩
            · exact h' (hsub h)
            · exact h' (Finset.mem_sdiff.mp (hy h)).1)
        rw [this]; simp
      obtain ⟨hF, hB', hout, htr⟩ := valid i
      have sb := PEqualNP.Outside.L_lib_1450_aux.step_bound (D i) bits hlen hbit hk0 hk1 (g A) (g (insert i A)) (a i) (f i)
        h0 h1
      simp only [cost]
      split_ifs with hS
      · apply sb.2 hF hB' _ hout
        intro x hx
        have := htr hS x hx
        omega
      · exact sb.1
    have key := PEqualNP.Outside.L_lib_1450_aux.ideal_sum R cost htrans hanti hrefl g mono step _ Finset.univ rfl
      (fun i j _ _ => Finset.mem_univ i)
    exact key.trans ((Finset.card_le_univ _).trans (by simp))
  have weak : fit True → fit False := by
    rintro ⟨g, D, h1, h2, h3, _⟩
    exact ⟨g, D, h1, h2, h3, fun h => h.elim⟩
  exact ⟨⟨down, fun h => weak (up h)⟩, up⟩
