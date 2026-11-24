import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3026

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma foldl_set_eq (gs : List Gate) : ∀ (w : List Bool) (c : ℕ), c < gs.length →
    (gs.foldl stepWire w).getD (w.length + c) false = false →
    (gs.set c ⟨GateOp.or, []⟩).foldl stepWire w = gs.foldl stepWire w := by
  induction gs with
  | nil => intro w c hc; simp at hc
  | cons g gs ih =>
    intro w c hc h
    cases c with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [List.foldl_cons, Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1] at h
      have h3 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      have h2 : stepWire w g = stepWire w ⟨GateOp.or, []⟩ := by
        show w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] = w ++ [false]
        rw [← h3, h]
      rw [h2]
    | succ c =>
      simp only [List.set_cons_succ, List.foldl_cons]
      apply ih
      · simpa using hc
      · have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl]
        rw [List.foldl_cons] at h
        have e : w.length + (c + 1) = w.length + 1 + c := by omega
        rw [← e]
        exact h

lemma foldl_set_lt (gs : List Gate) : ∀ (w : List Bool) (c i : ℕ), i < w.length + c →
    ((gs.set c ⟨GateOp.or, []⟩).foldl stepWire w).getD i false =
      (gs.foldl stepWire w).getD i false := by
  induction gs with
  | nil => intro w c i _; rfl
  | cons g gs ih =>
    intro w c i hi
    cases c with
    | zero =>
      have hi' : i < w.length := by omega
      simp only [List.set_cons_zero, List.foldl_cons]
      rw [foldl_getD_lt gs _ i (by simp [stepWire]; omega),
        foldl_getD_lt gs _ i (by simp [stepWire]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
    | succ c =>
      simp only [List.set_cons_succ, List.foldl_cons]
      apply ih
      simp [stepWire]
      omega

def V {n : ℕ} (C : Circuit) (z : Fin n → Bool) (t : ℕ) : Bool := val C (List.ofFn z) t

lemma V_in {n : ℕ} (C : Circuit) (z : Fin n → Bool) (i : Fin n) : V C z i.val = z i :=
  val_ofFn C z i

lemma V_lt {n : ℕ} (C : Circuit) (z : Fin n → Bool) {t : ℕ} (h : t < n) :
    V C z t = z ⟨t, h⟩ := V_in C z ⟨t, h⟩

lemma V_ge {n : ℕ} (C : Circuit) (z : Fin n → Bool) {t : ℕ} (h : n + C.gates.length ≤ t) :
    V C z t = false := val_ge (n := n) (by simp) h

lemma shape {n : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 n C) {k : ℕ}
    (hk : k < C.gates.length) :
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k ∧
      (((gateAt C k).op = GateOp.and ∧
          ∀ z : Fin n → Bool, V C z (n + k) = (V C z a && V C z b)) ∨
       ((gateAt C k).op = GateOp.or ∧
          ∀ z : Fin n → Bool, V C z (n + k) = (V C z a || V C z b))) := by
  obtain ⟨h1, h2, h3⟩ := hAO
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ (gateAt_mem hk))
  have ha : a < n + k := h2 k hk a (by rw [hab]; simp)
  have hb : b < n + k := h2 k hk b (by rw [hab]; simp)
  refine ⟨a, b, hab, ha, hb, ?_⟩
  rcases h1 _ (gateAt_mem hk) with hop | hop
  · left
    refine ⟨hop, fun z => ?_⟩
    unfold V
    rw [val_gate (n := n) (by simp) hk, hab, hop]
    simp [GateOp.eval, ha, hb]
  · right
    refine ⟨hop, fun z => ?_⟩
    unfold V
    rw [val_gate (n := n) (by simp) hk, hab, hop]
    simp [GateOp.eval, ha, hb]

def Rd (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ b = n + k ∧ a ∈ (gateAt C k).inputs

def ROr (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ b = n + k ∧ a ∈ (gateAt C k).inputs ∧ (gateAt C k).op = GateOp.or

abbrev Bl (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (Rd n C)

abbrev BlOr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (ROr n C)

section
variable {n : ℕ} {C : Circuit}

lemma rd_lt (hAO : PEqualNP.TopForm.IsAO2 n C) {a b : ℕ} (h : Rd n C a b) : a < b := by
  obtain ⟨k, hk, rfl, ha⟩ := h
  exact hAO.2.1 k hk a ha

lemma bl_le (hAO : PEqualNP.TopForm.IsAO2 n C) {a b : ℕ} (h : Bl n C a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (rd_lt hAO hbc).le

lemma blOr_bl {a b : ℕ} (h : BlOr n C a b) : Bl n C a b :=
  by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨k, hk, e, hx, _⟩ := hbc
    exact ih.tail ⟨k, hk, e, hx⟩

lemma bl_step {t k : ℕ} (hk : k < C.gates.length) (ht : t ∈ (gateAt C k).inputs) :
    Bl n C t (n + k) :=
  Relation.ReflTransGen.single ⟨k, hk, rfl, ht⟩

lemma bl_cone (hAO : PEqualNP.TopForm.IsAO2 n C) {k t : ℕ} (h : Bl n C (n + k) t) :
    ∀ j, t = n + j → k = j ∨ InCone n C k j := by
  induction h with
  | refl => intro j hj; left; omega
  | @tail b c' hab hbc ih =>
    intro j hj
    obtain ⟨j', hj', e, hb⟩ := hbc
    have : j' = j := by omega
    subst this
    have hb1 := bl_le hAO hab
    have hb2 := hAO.2.1 j' hj' _ hb
    right
    rw [inCone_iff]
    refine ⟨hj', b - n, by omega, ?_, ?_⟩
    · have : n + (b - n) = b := by omega
      rw [this]
      exact hb
    · exact ih (b - n) (by omega)

lemma V_mono (hAO : PEqualNP.TopForm.IsAO2 n C) {z z' : Fin n → Bool}
    (h : ∀ i, z i = true → z' i = true) :
    ∀ t, V C z t = true → V C z' t = true := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h1 : t < n
    · rw [V_lt C z h1, V_lt C z' h1]
      exact h _
    · by_cases h2 : t < n + C.gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, t = n + k := ⟨t - n, by omega⟩
        have hk : k < C.gates.length := by omega
        obtain ⟨a, b, hab, ha, hb, hv | hv⟩ := shape hAO hk
        · rw [hv.2 z, hv.2 z']
          simp only [Bool.and_eq_true]
          exact fun ⟨x, y⟩ => ⟨ih a ha x, ih b hb y⟩
        · rw [hv.2 z, hv.2 z']
          simp only [Bool.or_eq_true]
          exact fun x => x.imp (ih a ha) (ih b hb)
      · intro hf
        rw [V_ge C z (by omega)] at hf
        cases hf

lemma V_agree (hAO : PEqualNP.TopForm.IsAO2 n C) {z z' : Fin n → Bool} :
    ∀ t, (∀ i : Fin n, Bl n C i.val t → z i = z' i) → V C z t = V C z' t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_cases h1 : t < n
    · rw [V_lt C z h1, V_lt C z' h1]
      exact h ⟨t, h1⟩ Relation.ReflTransGen.refl
    · by_cases h2 : t < n + C.gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, t = n + k := ⟨t - n, by omega⟩
        have hk : k < C.gates.length := by omega
        obtain ⟨a, b, hab, ha, hb, hv⟩ := shape hAO hk
        have ea := ih a ha (fun i hi => h i (hi.tail ⟨k, hk, rfl, by rw [hab]; simp⟩))
        have eb := ih b hb (fun i hi => h i (hi.tail ⟨k, hk, rfl, by rw [hab]; simp⟩))
        rcases hv with hv | hv
        · rw [hv.2 z, hv.2 z', ea, eb]
        · rw [hv.2 z, hv.2 z', ea, eb]
      · rw [V_ge C z (by omega), V_ge C z' (by omega)]

lemma V_zero (hAO : PEqualNP.TopForm.IsAO2 n C) {z : Fin n → Bool} :
    ∀ t, (∀ i : Fin n, Bl n C i.val t → z i = false) → V C z t = false := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_cases h1 : t < n
    · rw [V_lt C z h1]
      exact h ⟨t, h1⟩ Relation.ReflTransGen.refl
    · by_cases h2 : t < n + C.gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, t = n + k := ⟨t - n, by omega⟩
        have hk : k < C.gates.length := by omega
        obtain ⟨a, b, hab, ha, hb, hv⟩ := shape hAO hk
        have ea := ih a ha (fun i hi => h i (hi.tail ⟨k, hk, rfl, by rw [hab]; simp⟩))
        have eb := ih b hb (fun i hi => h i (hi.tail ⟨k, hk, rfl, by rw [hab]; simp⟩))
        rcases hv with hv | hv
        · rw [hv.2 z, ea, eb]; rfl
        · rw [hv.2 z, ea, eb]; rfl
      · rw [V_ge C z (by omega)]

lemma V_pos (hAO : PEqualNP.TopForm.IsAO2 n C) {z : Fin n → Bool} {t : ℕ}
    (h : V C z t = true) : ∃ i : Fin n, Bl n C i.val t ∧ z i = true := by
  by_contra hc
  push Not at hc
  have := V_zero hAO (z := z) t (fun i hi => by simpa using hc i hi)
  rw [this] at h
  cases h

lemma dep_read (hAO : PEqualNP.TopForm.IsAO2 n C) {c : ℕ} {z z' : Fin n → Bool} {i : Fin n}
    (hd : ∀ j, j ≠ i → z j = z' j) (hne : V C z (n + c) ≠ V C z' (n + c)) :
    ∃ k, k < C.gates.length ∧ Bl n C (n + k) (n + c) ∧ i.val ∈ (gateAt C k).inputs := by
  by_contra hc
  apply hne
  apply V_agree hAO
  intro j hj
  by_cases hji : j = i
  · subst hji
    rcases Relation.ReflTransGen.cases_head hj with e | ⟨x, ⟨k, hk, rfl, hx⟩, hx2⟩
    · have := j.isLt
      omega
    · exact (hc ⟨k, hk, hx2, hx⟩).elim
  · exact hd j hji

def Tight (n : ℕ) (C : Circuit) (c : ℕ) : Prop :=
  (∀ k k' t, k < C.gates.length → k' < C.gates.length → Bl n C (n + k) (n + c) →
     Bl n C (n + k') (n + c) → t ∈ (gateAt C k).inputs → t ∈ (gateAt C k').inputs → k = k') ∧
  (∀ k a b, k < C.gates.length → Bl n C (n + k) (n + c) → (gateAt C k).inputs = [a, b] → a ≠ b)

variable {c : ℕ}

lemma chain (hT : Tight n C c) {u w1 : ℕ} (h1 : Bl n C u w1) :
    ∀ {w2 : ℕ}, Bl n C w1 (n + c) → Bl n C w2 (n + c) → Bl n C u w2 →
      Bl n C w1 w2 ∨ Bl n C w2 w1 := by
  induction h1 using Relation.ReflTransGen.head_induction_on with
  | refl => intro w2 _ _ h; exact Or.inl h
  | head hux hx ih =>
    intro w2 hw1 hw2 h2
    rcases Relation.ReflTransGen.cases_head h2 with e | ⟨x', hux', hx'⟩
    · subst e
      exact Or.inr (Relation.ReflTransGen.head hux hx)
    · obtain ⟨k, hk, rfl, hu⟩ := hux
      obtain ⟨k', hk', rfl, hu'⟩ := hux'
      have : k = k' := hT.1 k k' _ hk hk' (hx.trans hw1) (hx'.trans hw2) hu hu'
      subst this
      exact ih hw1 hw2 hx'

lemma disj (hAO : PEqualNP.TopForm.IsAO2 n C) (hT : Tight n C c) {k a b u : ℕ}
    (hk : k < C.gates.length) (hkc : Bl n C (n + k) (n + c))
    (hab : (gateAt C k).inputs = [a, b]) (ha : Bl n C u a) (hb : Bl n C u b) : False := by
  have hne := hT.2 k a b hk hkc hab
  have ma : a ∈ (gateAt C k).inputs := by rw [hab]; simp
  have mb : b ∈ (gateAt C k).inputs := by rw [hab]; simp
  have sa : Bl n C a (n + k) := bl_step hk ma
  have sb : Bl n C b (n + k) := bl_step hk mb
  have la : a < n + k := hAO.2.1 k hk a ma
  have lb : b < n + k := hAO.2.1 k hk b mb
  have key : ∀ a b, a ≠ b → a ∈ (gateAt C k).inputs → Bl n C b (n + k) → b < n + k →
      Bl n C a b → False := by
    intro a b hne ha sb lb h
    rcases Relation.ReflTransGen.cases_head h with e | ⟨x, ⟨k', hk', rfl, hx⟩, hx2⟩
    · exact hne e
    · have e : k' = k := hT.1 k' k a hk' hk ((hx2.trans sb).trans hkc) hkc hx ha
      rw [e] at hx2
      have := bl_le hAO hx2
      omega
  rcases chain hT ha (sa.trans hkc) (sb.trans hkc) hb with h | h
  · exact key a b hne ma sb lb h
  · exact key b a (Ne.symm hne) mb sa la h

lemma onchain (hAO : PEqualNP.TopForm.IsAO2 n C) (hT : Tight n C c) {t s r : ℕ}
    (h : BlOr n C t s) (hs : Bl n C s (n + c)) (hrs : Bl n C r s) :
    Bl n C t r → r ≠ t →
      ∃ k, k < C.gates.length ∧ r = n + k ∧ (gateAt C k).op = GateOp.or := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro htr hne
    exact absurd (le_antisymm (bl_le hAO hrs) (bl_le hAO htr)) hne
  | head htx hx ih =>
    intro htr hne
    rcases Relation.ReflTransGen.cases_head htr with e | ⟨x', ⟨k', hk', rfl, hu'⟩, hx'⟩
    · exact absurd e.symm hne
    · obtain ⟨k, hk, rfl, hu, hop⟩ := htx
      have e : k = k' :=
        hT.1 k k' _ hk hk' ((blOr_bl hx).trans hs) ((hx'.trans hrs).trans hs) hu hu'
      rw [← e] at hx'
      by_cases e2 : r = n + k
      · exact ⟨k, hk, e2, hop⟩
      · exact ih hx' e2

lemma other_zero (hAO : PEqualNP.TopForm.IsAO2 n C) (hT : Tight n C c) {k a b t : ℕ}
    {z : Fin n → Bool} (hk : k < C.gates.length) (hkc : Bl n C (n + k) (n + c))
    (hab : (gateAt C k).inputs = [a, b]) (hz : ∀ i : Fin n, z i = true → Bl n C i.val t) :
    (Bl n C t a → V C z b = false) ∧ (Bl n C t b → V C z a = false) := by
  constructor
  · intro hta
    apply V_zero hAO
    intro i hi
    by_contra hne
    exact disj hAO hT hk hkc hab ((hz i (by simpa using hne)).trans hta) hi
  · intro htb
    apply V_zero hAO
    intro i hi
    by_contra hne
    exact disj hAO hT hk hkc hab hi ((hz i (by simpa using hne)).trans htb)

lemma iso (hAO : PEqualNP.TopForm.IsAO2 n C) (hT : Tight n C c) {z : Fin n → Bool} {t s : ℕ}
    (h : Bl n C t s) :
    Bl n C s (n + c) → (∀ i : Fin n, z i = true → Bl n C i.val t) →
      V C z s = true → V C z t = true := by
  induction h with
  | refl => intro _ _ h; exact h
  | @tail b s' htb hbs ih =>
    intro hs hz hv
    obtain ⟨k, hk, rfl, hb⟩ := hbs
    have hbk : Bl n C b (n + k) := bl_step hk hb
    apply ih (hbk.trans hs) hz
    obtain ⟨a1, a2, hab, ha1, ha2, hv'⟩ := shape hAO hk
    have oz := other_zero hAO hT hk hs hab hz
    rw [hab] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hv' with hv' | hv'
    · rw [hv'.2 z] at hv
      simp only [Bool.and_eq_true] at hv
      rcases hb with rfl | rfl
      · exact hv.1
      · exact hv.2
    · rw [hv'.2 z] at hv
      rcases hb with rfl | rfl
      · rw [oz.1 htb] at hv
        simpa using hv
      · rw [oz.2 htb] at hv
        simpa using hv

lemma orMono (hAO : PEqualNP.TopForm.IsAO2 n C) {z : Fin n → Bool} {t s : ℕ}
    (h : BlOr n C t s) : V C z t = true → V C z s = true := by
  induction h with
  | refl => exact id
  | @tail b s' _ hbs ih =>
    intro hv
    obtain ⟨k, hk, rfl, hb, hop⟩ := hbs
    obtain ⟨a1, a2, hab, ha1, ha2, hv' | hv'⟩ := shape hAO hk
    · rw [hv'.1] at hop
      cases hop
    · rw [hv'.2 z]
      rw [hab] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      have := ih hv
      rcases hb with rfl | rfl <;> simp [this]

lemma and_val (hAO : PEqualNP.TopForm.IsAO2 n C) {a wa wb : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [wa, wb] ∨ (gateAt C a).inputs = [wb, wa]) (z : Fin n → Bool) :
    V C z (n + a) = true ↔ V C z wa = true ∧ V C z wb = true := by
  obtain ⟨a1, a2, hab, _, _, hv | hv⟩ := shape hAO ha
  · rw [hv.2 z, Bool.and_eq_true]
    rcases hin with h | h
    · rw [hab] at h
      simp only [List.cons.injEq, and_true] at h
      rw [h.1, h.2]
    · rw [hab] at h
      simp only [List.cons.injEq, and_true] at h
      rw [h.1, h.2]
      exact and_comm
  · rw [hv.1] at hop
    cases hop

lemma not_below (hAO : PEqualNP.TopForm.IsAO2 n C) (F : (Fin n → Bool) → Prop)
    (h6 : ∀ j, j < C.gates.length → (∀ z, V C z (n + j) = true → F z) → n + j ≠ C.output →
      ∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → ∀ z, V C z (n + k) = true → F z)
    (hout : n + c ≤ C.output) (hc : ¬ ∀ z, V C z (n + c) = true → F z) {t : ℕ}
    (h : Bl n C t (n + c)) :
    ∀ j, t = n + j → ¬ ∀ z, V C z (n + j) = true → F z := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro j hj
    have : c = j := by omega
    subst this
    exact hc
  | head htx hx ih =>
    intro j hj hb
    obtain ⟨k, hk, rfl, ht⟩ := htx
    subst hj
    have h1 := hAO.2.1 k hk _ ht
    have h2 := bl_le hAO hx
    exact ih k rfl (h6 j (by omega) hb (by omega) k hk ht)

def sg {n : ℕ} (x : Fin n) : Fin n → Bool := fun i => decide (i = x)

def pr {n : ℕ} (x y : Fin n) : Fin n → Bool := fun i => decide (i = x ∨ i = y)

def J {n : ℕ} (C : Circuit) (x y : Fin n) (t : ℕ) : Prop :=
  V C (pr x y) t = true ∧ V C (sg x) t = false ∧ V C (sg y) t = false

lemma descent (hAO : PEqualNP.TopForm.IsAO2 n C) (x y : Fin n) :
    ∀ k, k < C.gates.length → J C x y (n + k) →
      ∃ a, a < C.gates.length ∧ BlOr n C (n + a) (n + k) ∧ J C x y (n + a) ∧
        (gateAt C a).op = GateOp.and := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hJ
    obtain ⟨a1, a2, hab, ha1, ha2, hv | hv⟩ := shape hAO hk
    · exact ⟨k, hk, Relation.ReflTransGen.refl, hJ, hv.1⟩
    · obtain ⟨h1, h2, h3⟩ := hJ
      rw [hv.2] at h1 h2 h3
      simp only [Bool.or_eq_true] at h1
      simp only [Bool.or_eq_false_iff] at h2 h3
      have key : ∀ w, w ∈ (gateAt C k).inputs → w < n + k → V C (pr x y) w = true →
          V C (sg x) w = false → V C (sg y) w = false →
          ∃ a, a < C.gates.length ∧ BlOr n C (n + a) (n + k) ∧ J C x y (n + a) ∧
            (gateAt C a).op = GateOp.and := by
        intro w hw hwk e1 e2 e3
        by_cases hwn : w < n
        · rw [V_lt C _ hwn] at e1 e2 e3
          simp only [pr, sg, decide_eq_true_eq, decide_eq_false_iff_not] at e1 e2 e3
          rcases e1 with e | e
          · exact absurd e e2
          · exact absurd e e3
        · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
          obtain ⟨a, ha, hbl, hJa, hop⟩ := ih k' (by omega) (by omega) ⟨e1, e2, e3⟩
          exact ⟨a, ha, hbl.tail ⟨k, hk, rfl, hw, hv.1⟩, hJa, hop⟩
      rcases h1 with h | h
      · exact key a1 (by rw [hab]; simp) ha1 h h2.1 h3.1
      · exact key a2 (by rw [hab]; simp) ha2 h h2.2 h3.2

lemma split (hAO : PEqualNP.TopForm.IsAO2 n C) (hT : Tight n C c) {a : ℕ} {x y : Fin n}
    (ha : a < C.gates.length) (hac : Bl n C (n + a) (n + c))
    (hop : (gateAt C a).op = GateOp.and) (hJ : J C x y (n + a)) :
    ∃ wa wb, ((gateAt C a).inputs = [wa, wb] ∨ (gateAt C a).inputs = [wb, wa]) ∧
      Bl n C x.val wa ∧ Bl n C y.val wb ∧ V C (sg x) wa = true ∧ V C (sg y) wb = true := by
  obtain ⟨a1, a2, hab, ha1, ha2, _⟩ := shape hAO ha
  have hv := (and_val hAO ha hop (Or.inl hab) (pr x y)).mp hJ.1
  have hxy : ∀ w, V C (pr x y) w = true → Bl n C x.val w ∨ Bl n C y.val w := by
    intro w hw
    obtain ⟨i, hi, hz⟩ := V_pos hAO hw
    simp only [pr, decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  have D := fun (u : ℕ) (h1 : Bl n C u a1) (h2 : Bl n C u a2) => disj hAO hT ha hac hab h1 h2
  have agx : ∀ w, ¬ Bl n C y.val w → V C (sg x) w = V C (pr x y) w := by
    intro w hw
    apply V_agree hAO
    intro i hi
    simp only [sg, pr]
    by_cases e : i = y
    · subst e
      exact absurd hi hw
    · simp [e]
  have agy : ∀ w, ¬ Bl n C x.val w → V C (sg y) w = V C (pr x y) w := by
    intro w hw
    apply V_agree hAO
    intro i hi
    simp only [sg, pr]
    by_cases e : i = x
    · subst e
      exact absurd hi hw
    · simp [e]
  rcases hxy a1 hv.1 with h1 | h1 <;> rcases hxy a2 hv.2 with h2 | h2
  · exact (D _ h1 h2).elim
  · exact ⟨a1, a2, Or.inl hab, h1, h2, by rw [agx a1 (fun h => D _ h h2)]; exact hv.1,
      by rw [agy a2 (fun h => D _ h1 h)]; exact hv.2⟩
  · exact ⟨a2, a1, Or.inr hab, h2, h1, by rw [agx a2 (fun h => D _ h1 h)]; exact hv.2,
      by rw [agy a1 (fun h => D _ h h2)]; exact hv.1⟩
  · exact (D _ h1 h2).elim

structure Ctx (n : ℕ) (C : Circuit) (c : ℕ) (F : (Fin n → Bool) → Prop)
    (E : Fin n → Fin n → Prop) : Prop where
  hAO : PEqualNP.TopForm.IsAO2 n C
  hc : c < C.gates.length
  hT : Tight n C c
  hE : ∀ x y, E x y → J C x y (n + c) ∧
    ((∀ z : Fin n → Bool, V C z (n + c) = true → z x = true → F z) ∨
      (∀ z : Fin n → Bool, V C z (n + c) = true → z y = true → F z))
  hV : ∀ (i : Fin n) (k : ℕ), k < C.gates.length → Bl n C (n + k) (n + c) →
    i.val ∈ (gateAt C k).inputs → V C (sg i) (n + c) = true ∨ ∃ y, E i y ∨ E y i
  hnb : ∀ j, j < C.gates.length → Bl n C (n + j) (n + c) →
    ¬ ∀ z : Fin n → Bool, V C z (n + j) = true → F z

variable {F : (Fin n → Bool) → Prop} {E : Fin n → Fin n → Prop}

lemma mate (X : Ctx n C c F E) {a wa wb : ℕ} (ha : a < C.gates.length)
    (hac : BlOr n C (n + a) (n + c)) (hop : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [wa, wb] ∨ (gateAt C a).inputs = [wb, wa]) {u : Fin n}
    (hu : Bl n C u.val wa) :
    ∃ u' : Fin n, Bl n C u'.val wb ∧ V C (sg u) wa = true ∧ V C (sg u') wb = true ∧
      ((∀ z : Fin n → Bool, V C z (n + c) = true → z u = true → F z) ∨
        (∀ z : Fin n → Bool, V C z (n + c) = true → z u' = true → F z)) := by
  have hAO := X.hAO
  have hT := X.hT
  have hacb := blOr_bl hac
  have hwa : wa ∈ (gateAt C a).inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hwb : wb ∈ (gateAt C a).inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hua : Bl n C u.val (n + a) := hu.trans (bl_step ha hwa)
  have D : ∀ v, Bl n C v wa → Bl n C v wb → False := by
    intro v h1 h2
    rcases hin with h | h
    · exact disj hAO hT ha hacb h h1 h2
    · exact disj hAO hT ha hacb h h2 h1
  obtain ⟨k, hk, hkc, huk⟩ : ∃ k, k < C.gates.length ∧ Bl n C (n + k) (n + c) ∧
      u.val ∈ (gateAt C k).inputs := by
    rcases Relation.ReflTransGen.cases_head hua with e | ⟨x, ⟨k, hk, rfl, hx⟩, hx2⟩
    · have := u.isLt
      omega
    · exact ⟨k, hk, hx2.trans hacb, hx⟩
  rcases X.hV u k hk hkc huk with hl | ⟨y, hy⟩
  · exfalso
    have h1 : V C (sg u) (n + a) = true :=
      iso hAO hT hacb Relation.ReflTransGen.refl
        (fun i hi => by
          simp only [sg, decide_eq_true_eq] at hi
          subst hi
          exact hua) hl
    have h2 := ((and_val hAO ha hop hin (sg u)).mp h1).2
    obtain ⟨i, hi, hz⟩ := V_pos hAO h2
    simp only [sg, decide_eq_true_eq] at hz
    subst hz
    exact D _ hu hi
  · have main : ∀ x' y' : Fin n, E x' y' → (u = x' ∨ u = y') →
        ∃ u' : Fin n, Bl n C u'.val wb ∧ V C (sg u) wa = true ∧ V C (sg u') wb = true ∧
          ((∀ z : Fin n → Bool, V C z (n + c) = true → z u = true → F z) ∨
            (∀ z : Fin n → Bool, V C z (n + c) = true → z u' = true → F z)) := by
      intro x' y' hE hux
      obtain ⟨hJ, hQ⟩ := X.hE x' y' hE
      obtain ⟨a', ha', hac', hJ', hop'⟩ := descent hAO x' y' c X.hc hJ
      obtain ⟨wa', wb', hin', hx', hy', vx', vy'⟩ := split hAO hT ha' (blOr_bl hac') hop' hJ'
      have hwa' : wa' ∈ (gateAt C a').inputs := by rcases hin' with h | h <;> rw [h] <;> simp
      have hwb' : wb' ∈ (gateAt C a').inputs := by rcases hin' with h | h <;> rw [h] <;> simp
      have hua' : Bl n C u.val (n + a') := by
        rcases hux with rfl | rfl
        · exact hx'.trans (bl_step ha' hwa')
        · exact hy'.trans (bl_step ha' hwb')
      have haa : a' = a := by
        by_contra hne
        rcases chain hT hua hacb (blOr_bl hac') hua' with h | h
        · obtain ⟨k, hk, e, hopk⟩ :=
            onchain hAO hT hac Relation.ReflTransGen.refl (blOr_bl hac') h (by omega)
          have : k = a' := by omega
          subst this
          rw [hop'] at hopk
          cases hopk
        · obtain ⟨k, hk, e, hopk⟩ :=
            onchain hAO hT hac' Relation.ReflTransGen.refl hacb h (by omega)
          have : k = a := by omega
          subst this
          rw [hop] at hopk
          cases hopk
      subst haa
      have hsw : (wa' = wa ∧ wb' = wb) ∨ (wa' = wb ∧ wb' = wa) := by
        rcases hin with h | h <;> rcases hin' with h' | h' <;> rw [h] at h' <;>
          simp only [List.cons.injEq, and_true] at h' <;> obtain ⟨e1, e2⟩ := h' <;>
          subst e1 <;> subst e2 <;> simp
      rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hux with rfl | rfl
        · exact ⟨y', hy', vx', vy', hQ⟩
        · exact (D _ hu hy').elim
      · rcases hux with rfl | rfl
        · exact (D _ hu hx').elim
        · exact ⟨x', hx', vy', vx', hQ.symm⟩
    rcases hy with h | h
    · exact main u y h (Or.inl rfl)
    · exact main y u h (Or.inr rfl)

lemma tight_false (X : Ctx n C c F E) (side : Fin n → Bool)
    (hF2 : ∀ a b, F (pr a b) → side a ≠ side b)
    (hFm : ∀ z z' : Fin n → Bool, (∀ i, z i = true → z' i = true) → F z → F z')
    (hlin : ∃ v : Fin n, V C (sg v) (n + c) = true) (hE0 : ∃ x y, E x y) : False := by
  have hAO := X.hAO
  have hT := X.hT
  obtain ⟨x0, y0, h0⟩ := hE0
  obtain ⟨v, hv⟩ := hlin
  obtain ⟨a, ha, hac, hJ, hop⟩ := descent hAO x0 y0 c X.hc (X.hE x0 y0 h0).1
  have hacb := blOr_bl hac
  obtain ⟨wa, wb, hin, -, -, -, -⟩ := split hAO hT ha hacb hop hJ
  have hnb := X.hnb a ha hacb
  push Not at hnb
  obtain ⟨z, hz, hFz⟩ := hnb
  obtain ⟨hza, hzb⟩ := (and_val hAO ha hop hin z).mp hz
  obtain ⟨s, hs, zs⟩ := V_pos hAO hza
  obtain ⟨t, ht, zt⟩ := V_pos hAO hzb
  obtain ⟨t1, ht1, vs, vt1, q1⟩ := mate X ha hac hop hin hs
  obtain ⟨s1, hs1, vt, vs1, q2⟩ := mate X ha hac hop hin.symm ht
  have m1 : ∀ p q : Fin n, ∀ i, sg p i = true → pr p q i = true := by
    intro p q i hi
    simp only [sg, decide_eq_true_eq] at hi
    simp [pr, hi]
  have m2 : ∀ p q : Fin n, ∀ i, sg q i = true → pr p q i = true := by
    intro p q i hi
    simp only [sg, decide_eq_true_eq] at hi
    simp [pr, hi]
  have cT : ∀ p q : Fin n, V C (sg p) wa = true → V C (sg q) wb = true →
      V C (pr p q) (n + c) = true := by
    intro p q h1 h2
    apply orMono hAO hac
    rw [and_val hAO ha hop hin]
    exact ⟨V_mono hAO (m1 p q) _ h1, V_mono hAO (m2 p q) _ h2⟩
  have hst : ¬ F (pr s t) := fun h => hFz (hFm _ _ (fun i hi => by
    simp only [pr, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> assumption) h)
  have fs : ¬ (∀ z : Fin n → Bool, V C z (n + c) = true → z s = true → F z) :=
    fun q => hst (q _ (cT s t vs vt) (by simp [pr]))
  have ft : ¬ (∀ z : Fin n → Bool, V C z (n + c) = true → z t = true → F z) :=
    fun q => hst (q _ (cT s t vs vt) (by simp [pr]))
  have q1' := q1.resolve_left fs
  have q2' := q2.resolve_left ft
  have e1 : F (pr s1 t1) := q1' _ (cT s1 t1 vs1 vt1) (by simp [pr])
  have e2 : F (pr v t1) := q1' _ (V_mono hAO (m1 v t1) _ hv) (by simp [pr])
  have e3 : F (pr v s1) := q2' _ (V_mono hAO (m1 v s1) _ hv) (by simp [pr])
  have g1 := hF2 _ _ e1
  have g2 := hF2 _ _ e2
  have g3 := hF2 _ _ e3
  revert g1 g2 g3
  cases side v <;> cases side s1 <;> cases side t1 <;> simp

lemma count (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length) (K : Finset ℕ)
    (hK : ∀ k, k ∈ K ↔ k < C.gates.length ∧ Bl n C (n + k) (n + c))
    (M : Finset (Fin n))
    (hM : ∀ i ∈ M, ∃ k, k < C.gates.length ∧ Bl n C (n + k) (n + c) ∧
      i.val ∈ (gateAt C k).inputs)
    (hlt : K.card < M.card) :
    Tight n C c ∧ ∀ (i : Fin n) (k : ℕ), k < C.gates.length → Bl n C (n + k) (n + c) →
      i.val ∈ (gateAt C k).inputs → i ∈ M := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ℕ × ℕ → ℕ, f = fun s => (gateAt C s.1).inputs.getD s.2 0 := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℕ × ℕ), S = K ×ˢ Finset.range 2 := ⟨_, rfl⟩
  obtain ⟨Vars, hVars⟩ : ∃ Vars : Finset (Fin n), Vars = Finset.univ.filter (fun i : Fin n =>
      ∃ k, k < C.gates.length ∧ Bl n C (n + k) (n + c) ∧ i.val ∈ (gateAt C k).inputs) :=
    ⟨_, rfl⟩
  have hMV : M ⊆ Vars := by
    intro i hi
    rw [hVars, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hM i hi⟩
  have pos : ∀ k t, k < C.gates.length → Bl n C (n + k) (n + c) → t ∈ (gateAt C k).inputs →
      ∃ j, (k, j) ∈ S ∧ f (k, j) = t := by
    intro k t hk hkc ht
    obtain ⟨a, b, hab, -⟩ := shape hAO hk
    have hkK := (hK k).mpr ⟨hk, hkc⟩
    rw [hab] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨0, by rw [hS]; simp [hkK], by rw [hf]; simp [hab]⟩
    · exact ⟨1, by rw [hS]; simp [hkK], by rw [hf]; simp [hab]⟩
  have himg : ∀ k t, k < C.gates.length → Bl n C (n + k) (n + c) → t ∈ (gateAt C k).inputs →
      t ∈ S.image f := by
    intro k t hk hkc ht
    obtain ⟨j, hj, e⟩ := pos k t hk hkc ht
    exact Finset.mem_image.mpr ⟨_, hj, e⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Finset ℕ, T = (K.erase c).image (fun k => n + k) ∪
      Vars.image (fun i : Fin n => i.val) := ⟨_, rfl⟩
  have hTsub : T ⊆ S.image f := by
    intro t ht
    rw [hTdef] at ht
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hkc, hkK⟩ := Finset.mem_erase.mp hk
      obtain ⟨hk1, hk2⟩ := (hK k).mp hkK
      rcases Relation.ReflTransGen.cases_head hk2 with e | ⟨x, ⟨k', hk', rfl, hx⟩, hx2⟩
      · exact absurd (by omega) hkc
      · exact himg k' _ hk' hx2 hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      rw [hVars, Finset.mem_filter] at hi
      obtain ⟨k, hk, hkc, hik⟩ := hi.2
      exact himg k _ hk hkc hik
  have hcK : c ∈ K := (hK c).mpr ⟨hc, Relation.ReflTransGen.refl⟩
  have hTcard : T.card = (K.card - 1) + Vars.card := by
    rw [hTdef, Finset.card_union_of_disjoint,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_image_of_injective _ Fin.val_injective, Finset.card_erase_of_mem hcK]
    rw [Finset.disjoint_left]
    intro t h1 h2
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨i, _, e⟩ := Finset.mem_image.mp h2
    have := i.isLt
    omega
  have hScard : S.card = 2 * K.card := by
    rw [hS, Finset.card_product, Finset.card_range]
    ring
  have h1 : T.card ≤ (S.image f).card := Finset.card_le_card hTsub
  have h2 : (S.image f).card ≤ S.card := Finset.card_image_le
  have h3 : M.card ≤ Vars.card := Finset.card_le_card hMV
  have hKpos : 0 < K.card := Finset.card_pos.mpr ⟨c, hcK⟩
  have hinj : Set.InjOn f S := by
    rw [← Finset.card_image_iff]
    omega
  have hVM : M = Vars := Finset.eq_of_subset_of_card_le hMV (by omega)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k k' t hk hk' hkc hkc' ht ht'
    obtain ⟨j, hj, ej⟩ := pos k t hk hkc ht
    obtain ⟨j', hj', ej'⟩ := pos k' t hk' hkc' ht'
    have := hinj hj hj' (ej.trans ej'.symm)
    exact (Prod.mk.inj this).1
  · intro k a b hk hkc hab e
    have hkK := (hK k).mpr ⟨hk, hkc⟩
    have m0 : (k, 0) ∈ S := by rw [hS]; simp [hkK]
    have m1 : (k, 1) ∈ S := by rw [hS]; simp [hkK]
    have := hinj (Finset.mem_coe.mpr m0) (Finset.mem_coe.mpr m1) (by rw [hf]; simp [hab, e])
    simp at this
  · intro i k hk hkc hik
    rw [hVM, hVars, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, k, hk, hkc, hik⟩

end

def Fz (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (z : Fin (Np + Nl) → Bool) : Prop :=
  ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true

def Lost (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (C : Circuit) (c : ℕ) (p : Fin Np)
    (l : Fin Nl) : Prop :=
  I p l ∧ V C (sg (Fin.castAdd Nl p)) (Np + Nl + c) = false ∧
    V C (sg (Fin.natAdd Np l)) (Np + Nl + c) = false ∧
    circuitFun (Np + Nl) C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) = true ∧
    circuitFun (Np + Nl) (Circuit.mk (C.gates.set c (Gate.mk GateOp.or [])) C.output)
      (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) = false

lemma lost_facts (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (C : Circuit) (c : ℕ)
    (hc : c < C.gates.length) (p : Fin Np) (l : Fin Nl) (h : Lost Np Nl I C c p l) :
    J C (Fin.castAdd Nl p) (Fin.natAdd Np l) (Np + Nl + c) ∧ Np + Nl + c ≤ C.output := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  constructor
  · refine ⟨?_, h1, h2⟩
    by_contra hf
    have hf' : V C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) (Np + Nl + c) = false := by
      simpa using hf
    have key := foldl_set_eq C.gates (List.ofFn (pr (Fin.castAdd Nl p) (Fin.natAdd Np l))) c hc
      (by rw [List.length_ofFn]; exact hf')
    have e : circuitFun (Np + Nl) (Circuit.mk (C.gates.set c (Gate.mk GateOp.or [])) C.output)
        (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) =
        circuitFun (Np + Nl) C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) := by
      show ((C.gates.set c (Gate.mk GateOp.or [])).foldl stepWire
        (List.ofFn (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)))).getD C.output false =
        (C.gates.foldl stepWire
          (List.ofFn (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)))).getD C.output false
      rw [key]
    rw [e, h3] at h4
    cases h4
  · by_contra hf
    have e : circuitFun (Np + Nl) (Circuit.mk (C.gates.set c (Gate.mk GateOp.or [])) C.output)
        (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) =
        circuitFun (Np + Nl) C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) := by
      show ((C.gates.set c (Gate.mk GateOp.or [])).foldl stepWire
        (List.ofFn (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)))).getD C.output false =
        (C.gates.foldl stepWire
          (List.ofFn (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)))).getD C.output false
      exact foldl_set_lt C.gates _ c C.output (by rw [List.length_ofFn]; omega)
    rw [e, h3] at h4
    cases h4

lemma final (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (C : Circuit) (c : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (Np + Nl) C)
    (h6 : ∀ j, j < C.gates.length → (∀ z, V C z (Np + Nl + j) = true → Fz Np Nl I z) →
      Np + Nl + j ≠ C.output → ∀ k, k < C.gates.length → Np + Nl + j ∈ (gateAt C k).inputs →
      ∀ z, V C z (Np + Nl + k) = true → Fz Np Nl I z)
    (hc : c < C.gates.length)
    (hnb : ¬ ∀ z, V C z (Np + Nl + c) = true → Fz Np Nl I z)
    (hlin : ∃ v : Fin (Np + Nl), V C (sg v) (Np + Nl + c) = true)
    (hlost : ∃ p l, Lost Np Nl I C c p l)
    (hpart : ∀ p l, Lost Np Nl I C c p l → ∃ j, j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ (∀ z, V C z (Np + Nl + j) = true → Fz Np Nl I z) ∧
      ∃ w : ℕ, ((gateAt C j).inputs = [Np + Nl + c, w] ∨ (gateAt C j).inputs = [w, Np + Nl + c]) ∧
        (V C (sg (Fin.castAdd Nl p)) w = true ∨ V C (sg (Fin.natAdd Np l)) w = true))
    (A : Finset (Fin (Np + Nl))) (P : Finset (Fin Np)) (L : Finset (Fin Nl)) (KK : Finset ℕ)
    (hA : ∀ v, v ∈ A ↔ V C (sg v) (Np + Nl + c) = true)
    (hP : ∀ p, p ∈ P ↔ ∃ l, Lost Np Nl I C c p l)
    (hL : ∀ l, l ∈ L ↔ ∃ p, Lost Np Nl I C c p l)
    (hKK : ∀ k, k ∈ KK ↔ k < C.gates.length ∧ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k c) :
    A.card + P.card + L.card ≤ KK.card := by
  classical
  obtain ⟨M, hMdef⟩ : ∃ M : Finset (Fin (Np + Nl)),
      M = A ∪ P.image (Fin.castAdd Nl) ∪ L.image (Fin.natAdd Np) := ⟨_, rfl⟩
  have d1 : Disjoint A (P.image (Fin.castAdd Nl)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h2
    obtain ⟨l, hl⟩ := (hP p).mp hp
    have := (hA _).mp h1
    rw [hl.2.1] at this
    cases this
  have d2 : Disjoint (A ∪ P.image (Fin.castAdd Nl)) (L.image (Fin.natAdd Np)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h2
    rcases Finset.mem_union.mp h1 with h | h
    · obtain ⟨p, hp⟩ := (hL l).mp hl
      have := (hA _).mp h
      rw [hp.2.2.1] at this
      cases this
    · obtain ⟨p, _, e⟩ := Finset.mem_image.mp h
      have := congrArg Fin.val e
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      have := p.isLt
      omega
  have hMcard : M.card = A.card + P.card + L.card := by
    rw [hMdef, Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
      Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
      Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)]
  obtain ⟨K, hKdef⟩ : ∃ K : Finset ℕ, K = (Finset.range C.gates.length).filter
      (fun k => Bl (Np + Nl) C (Np + Nl + k) (Np + Nl + c)) := ⟨_, rfl⟩
  have hK : ∀ k, k ∈ K ↔ k < C.gates.length ∧ Bl (Np + Nl) C (Np + Nl + k) (Np + Nl + c) := by
    intro k
    rw [hKdef, Finset.mem_filter, Finset.mem_range]
  have hsub : K ⊆ KK := by
    intro k hk
    obtain ⟨h1, h2⟩ := (hK k).mp hk
    exact (hKK k).mpr ⟨h1, bl_cone hAO h2 c rfl⟩
  rw [← hMcard]
  refine le_trans ?_ (Finset.card_le_card hsub)
  by_contra hlt
  have hlt' : K.card < M.card := by omega
  obtain ⟨p0, l0, hL0⟩ := hlost
  have hout := (lost_facts Np Nl I C c hc p0 l0 hL0).2
  have zf : V C (fun _ : Fin (Np + Nl) => false) (Np + Nl + c) = false :=
    V_zero hAO _ (fun _ _ => rfl)
  have hM : ∀ i ∈ M, ∃ k, k < C.gates.length ∧ Bl (Np + Nl) C (Np + Nl + k) (Np + Nl + c) ∧
      i.val ∈ (gateAt C k).inputs := by
    intro i hi
    rw [hMdef] at hi
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · apply dep_read hAO (z := sg i) (z' := fun _ => false)
        · intro j hj
          simp [sg, hj]
        · rw [(hA i).mp h, zf]
          simp
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨l, hl⟩ := (hP p).mp hp
        have hJ := (lost_facts Np Nl I C c hc p l hl).1
        apply dep_read hAO (z := pr (Fin.castAdd Nl p) (Fin.natAdd Np l))
          (z' := sg (Fin.natAdd Np l))
        · intro j hj
          simp [pr, sg, hj]
        · rw [hJ.1, hJ.2.2]
          simp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨p, hp⟩ := (hL l).mp hl
      have hJ := (lost_facts Np Nl I C c hc p l hp).1
      apply dep_read hAO (z := pr (Fin.castAdd Nl p) (Fin.natAdd Np l))
        (z' := sg (Fin.castAdd Nl p))
      · intro j hj
        simp [pr, sg, hj]
      · rw [hJ.1, hJ.2.1]
        simp
  obtain ⟨hT, hV⟩ := count hAO hc K hK M hM hlt'
  have X : Ctx (Np + Nl) C c (Fz Np Nl I)
      (fun x y => ∃ p l, x = Fin.castAdd Nl p ∧ y = Fin.natAdd Np l ∧ Lost Np Nl I C c p l) := by
    refine ⟨hAO, hc, hT, ?_, ?_, ?_⟩
    · rintro x y ⟨p, l, rfl, rfl, hl⟩
      refine ⟨(lost_facts Np Nl I C c hc p l hl).1, ?_⟩
      obtain ⟨j, hj, hop, hb, w, hin, hw⟩ := hpart p l hl
      have Qof : ∀ u : Fin (Np + Nl), V C (sg u) w = true →
          ∀ z : Fin (Np + Nl) → Bool, V C z (Np + Nl + c) = true → z u = true → Fz Np Nl I z := by
        intro u hu z hz hzu
        apply hb z
        rw [and_val hAO hj hop hin z]
        refine ⟨hz, V_mono hAO (fun i hi => ?_) _ hu⟩
        simp only [sg, decide_eq_true_eq] at hi
        rw [hi]
        exact hzu
      exact hw.imp (Qof _) (Qof _)
    · intro i k hk hkc hik
      have hi := hV i k hk hkc hik
      rw [hMdef] at hi
      rcases Finset.mem_union.mp hi with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inl ((hA i).mp h)
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
          obtain ⟨l, hl⟩ := (hP p).mp hp
          exact Or.inr ⟨Fin.natAdd Np l, Or.inl ⟨p, l, rfl, rfl, hl⟩⟩
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨p, hp⟩ := (hL l).mp hl
        exact Or.inr ⟨Fin.castAdd Nl p, Or.inr ⟨p, l, rfl, rfl, hp⟩⟩
    · intro j hj hjc
      exact not_below hAO (Fz Np Nl I) h6 hout hnb hjc j rfl
  refine tight_false X (fun i => decide (i.val < Np)) ?_ ?_ hlin
    ⟨_, _, p0, l0, rfl, rfl, hL0⟩
  · rintro a b ⟨p, l, _, h1, h2⟩ heq
    have hs1 : decide ((Fin.castAdd Nl p).val < Np) = true := by simp
    have hs2 : decide ((Fin.natAdd Np l).val < Np) = false := by simp
    simp only [pr, decide_eq_true_eq] at h1 h2
    rcases h1 with e | e <;> rcases h2 with e' | e' <;> rw [e] at hs1 <;> rw [e'] at hs2 <;>
      simp_all
  · rintro z z' h ⟨p, l, hI, h1, h2⟩
    exact ⟨p, l, hI, h _ h1, h _ h2⟩

end PEqualNP.Outside.L_meta_3026

theorem PEqualNP.Outside.L_meta_3026 : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (∀ p47 : Fin Np, ∀ l48 : Fin Nl, (I p47 l48 ∧ (C.wires (List.ofFn (fun i51 : Fin (Np + Nl) => decide (i51 = Fin.castAdd Nl p47)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i52 : Fin (Np + Nl) => decide (i52 = Fin.natAdd Np l48)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i53 : Fin (Np + Nl) => decide (i53 = Fin.castAdd Nl p47 ∨ i53 = Fin.natAdd Np l48)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p47 ∨ i54 = Fin.natAdd Np l48)) = false) → ∃ j49 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ z55 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z55)).getD ((Np + Nl) + j49) false = true → ∃ p56 : Fin Np, ∃ l57 : Fin Nl, I p56 l57 ∧ z55 (Fin.castAdd Nl p56) = true ∧ z55 (Fin.natAdd Np l57) = true) ∧ ∃ w50 : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [(Np + Nl) + c, w50] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [w50, (Np + Nl) + c]) ∧ ((C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p47)))).getD (w50) false = true ∨ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l48)))).getD (w50) false = true)) → (Finset.univ.filter fun v60 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i66 : Fin (Np + Nl) => decide (i66 = v60)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p61 : Fin Np => ∃ l62 : Fin Nl, (I p61 l62 ∧ (C.wires (List.ofFn (fun i67 : Fin (Np + Nl) => decide (i67 = Fin.castAdd Nl p61)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i68 : Fin (Np + Nl) => decide (i68 = Fin.natAdd Np l62)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i69 : Fin (Np + Nl) => decide (i69 = Fin.castAdd Nl p61 ∨ i69 = Fin.natAdd Np l62)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i70 : Fin (Np + Nl) => decide (i70 = Fin.castAdd Nl p61 ∨ i70 = Fin.natAdd Np l62)) = false)).card + (Finset.univ.filter fun l64 : Fin Nl => ∃ p63 : Fin Np, (I p63 l64 ∧ (C.wires (List.ofFn (fun i71 : Fin (Np + Nl) => decide (i71 = Fin.castAdd Nl p63)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i72 : Fin (Np + Nl) => decide (i72 = Fin.natAdd Np l64)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i73 : Fin (Np + Nl) => decide (i73 = Fin.castAdd Nl p63 ∨ i73 = Fin.natAdd Np l64)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i74 : Fin (Np + Nl) => decide (i74 = Fin.castAdd Nl p63 ∨ i74 = Fin.natAdd Np l64)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k65 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k65 c).card := by
  intro Np Nl I _ C c _ hAO _ _ _ h6 _ hc hnb _ hlin hlost hpart
  refine PEqualNP.Outside.L_meta_3026.final Np Nl I C c hAO
    (fun j hj hb hne k hk hin => (((h6 j hj hb).2 hne).2 k hk hin).2) hc hnb hlin hlost hpart
    _ _ _ _ ?_ ?_ ?_ ?_
  · intro v
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  · intro p
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  · intro l
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  · intro k
    exact ⟨fun h => ⟨Finset.mem_range.mp (Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2⟩,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h.2⟩⟩
