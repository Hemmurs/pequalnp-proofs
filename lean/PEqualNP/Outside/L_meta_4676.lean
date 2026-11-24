import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4676

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def D : Finset (Fin 13) := {0, 1, 3, 9}

def Spec (f : List Bool → Bool) : Prop :=
  (∀ (p l : Fin 13), p - l ∈ D →
    f ((List.ofFn fun (k : Fin 13) => decide (k = p)) ++ List.ofFn fun (k : Fin 13) => decide (k = l)) = true) ∧
  ∀ (Q : Finset (Fin 13)), Q.card = 4 → (∀ (l : Fin 13), {q ∈ Q | q - l ∈ D}.card ≤ 2) →
    f ((List.ofFn fun (k : Fin 13) => decide (k ∈ Q)) ++
      List.ofFn fun (k : Fin 13) => decide (∀ q ∈ Q, q - k ∉ D)) = false

def X3 (C : Circuit) (L : List ℕ) : Prop :=
  Spec fun x => C.eval (x ++ [L.any fun i => x.getD i false])

def X4 (C : Circuit) : Prop :=
  ∀ (j : Fin C.gates.length), ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val

def reps : List (List ℕ) :=
  [[], [0], [13], [0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17], [0, 20], [13, 14], [13, 15]]

def sig (f : Fin 13 → Fin 13) (i : ℕ) : ℕ :=
  if h : i < 13 then (f ⟨i, h⟩).val
  else if h2 : i < 26 then 13 + (f ⟨i - 13, by omega⟩).val else i

theorem sig_lt (f : Fin 13 → Fin 13) (i : ℕ) (h : i < 26) : sig f i < 26 := by
  unfold sig
  split_ifs
  · have := (f ⟨i, by assumption⟩).isLt; omega
  · have := (f ⟨i - 13, by omega⟩).isLt; omega

theorem sig_ge (f : Fin 13 → Fin 13) (i : ℕ) (h : 26 ≤ i) : sig f i = i := by
  unfold sig
  rw [dif_neg (by omega), dif_neg (by omega)]

def relabel (f : Fin 13 → Fin 13) (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (sig f)⟩, sig f C.output⟩

def Rel (f : Fin 13 → Fin 13) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w'.getD (sig f i) false = w.getD i false

theorem rel_snoc (f : Fin 13 → Fin 13) (w w' : List Bool) (v : Bool) (h26 : 26 ≤ w.length)
    (h : Rel f w w') : Rel f (w ++ [v]) (w' ++ [v]) := by
  obtain ⟨hl, hr⟩ := h
  refine ⟨by simp [hl], fun i => ?_⟩
  by_cases hi : i < w.length
  · have hs : sig f i < w'.length := by
      by_cases h2 : i < 26
      · have := sig_lt f i h2; omega
      · rw [sig_ge f i (by omega)]; omega
    rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hi, hr]
  · have h2 : sig f i = i := sig_ge f i (by omega)
    rw [h2, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

theorem rel_fold (f : Fin 13 → Fin 13) (gs : List Gate) :
    ∀ (w w' : List Bool), 26 ≤ w.length → Rel f w w' →
      Rel f (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        ((gs.map fun g => (⟨g.op, g.inputs.map (sig f)⟩ : Gate)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' _ h; exact h
  | cons g gs ih =>
    intro w w' h26 h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp; omega
    · have e : (g.inputs.map (sig f)).map (fun i => w'.getD i false)
          = g.inputs.map fun i => w.getD i false := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact h.2 i
      rw [e]
      exact rel_snoc f w w' _ h26 h

theorem relabel_eval (f : Fin 13 → Fin 13) (C : Circuit) (w w' : List Bool)
    (h26 : 26 ≤ w.length) (h : Rel f w w') : (relabel f C).eval w' = C.eval w := by
  unfold Circuit.eval Circuit.wires relabel
  exact (rel_fold f C.gates w w' h26 h).2 C.output

theorem relabel_mono (f : Fin 13 → Fin 13) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (relabel f C) := by
  intro g hg
  simp only [relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa using h g0 hg0

theorem relabel_x4 (f : Fin 13 → Fin 13) (C : Circuit) (h : X4 C) : X4 (relabel f C) := by
  intro j i hi
  have hj : j.val < C.gates.length := by
    have := j.isLt
    simpa [relabel] using this
  have e : ((relabel f C).gates.get j).inputs
      = ((C.gates.get ⟨j.val, hj⟩).inputs).map (sig f) :=
    congrArg Gate.inputs (List.getElem_map (fun g => (⟨g.op, g.inputs.map (sig f)⟩ : Gate))
      (l := C.gates) (i := j.val) (h := by simpa using hj))
  rw [e, List.mem_map] at hi
  obtain ⟨i0, hi0, rfl⟩ := hi
  have h0 := h ⟨j.val, hj⟩ i0 (by simpa using hi0)
  simp only at h0
  by_cases h2 : i0 < 26
  · have := sig_lt f i0 h2; omega
  · rw [sig_ge f i0 (by omega)]; exact h0

theorem getD_two (u v : Fin 13 → Bool) (i : ℕ) :
    (List.ofFn u ++ List.ofFn v).getD i false =
      if h : i < 13 then u ⟨i, h⟩ else if h2 : i < 26 then v ⟨i - 13, by omega⟩ else false := by
  by_cases h : i < 13
  · rw [dif_pos h, List.getD_append _ _ _ _ (by simpa using h)]
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dif_neg h, List.getD_append_right _ _ _ _ (by simpa using h)]
    by_cases h2 : i < 26
    · rw [dif_pos h2]
      have : i - 13 < 13 := by omega
      rw [List.getD_eq_getElem _ _ (by simpa using this), List.getElem_ofFn]
      simp
    · rw [dif_neg h2]
      have : ¬ (i - 13 < 13) := by omega
      simp [List.getD_eq_getElem?_getD, this]

theorem rel_two (f : Fin 13 → Fin 13) (u v u' v' : Fin 13 → Bool)
    (hu : ∀ k, u' (f k) = u k) (hv : ∀ k, v' (f k) = v k) :
    Rel f (List.ofFn u ++ List.ofFn v) (List.ofFn u' ++ List.ofFn v') := by
  refine ⟨by simp, fun i => ?_⟩
  rw [getD_two, getD_two]
  by_cases h : i < 13
  · have hs : sig f i = (f ⟨i, h⟩).val := by unfold sig; rw [dif_pos h]
    have hlt : sig f i < 13 := by rw [hs]; exact (f ⟨i, h⟩).isLt
    rw [dif_pos hlt, dif_pos h]
    have : (⟨sig f i, hlt⟩ : Fin 13) = f ⟨i, h⟩ := Fin.ext hs
    rw [this, hu]
  · by_cases h2 : i < 26
    · have hs : sig f i = 13 + (f ⟨i - 13, by omega⟩).val := by
        unfold sig; rw [dif_neg h, dif_pos h2]
      have hlt := (f ⟨i - 13, by omega⟩).isLt
      have hn : ¬ sig f i < 13 := by omega
      have hl : sig f i < 26 := by omega
      rw [dif_neg hn, dif_pos hl, dif_neg h, dif_pos h2]
      have : (⟨sig f i - 13, by omega⟩ : Fin 13) = f ⟨i - 13, by omega⟩ := Fin.ext (by simp [hs])
      rw [this, hv]
    · have hs : sig f i = i := sig_ge f i (by omega)
      rw [hs, dif_neg h, dif_neg h2, dif_neg h, dif_neg h2]

theorem eval_two (f : Fin 13 → Fin 13) (C : Circuit) (L : List ℕ) (x x' : List Bool)
    (hx : x.length = 26) (h : Rel f x x') :
    (relabel f C).eval (x' ++ [(L.map (sig f)).any fun i => x'.getD i false])
      = C.eval (x ++ [L.any fun i => x.getD i false]) := by
  have e : ((L.map (sig f)).any fun i => x'.getD i false) = L.any fun i => x.getD i false := by
    rw [List.any_map]
    congr 1
    funext i
    exact h.2 i
  rw [e]
  exact relabel_eval f C _ _ (by simp; omega) (rel_snoc f x x' _ (by omega) h)

theorem transport (φ : Equiv.Perm (Fin 13)) (hφ : ∀ a b, φ a - φ b ∈ D ↔ a - b ∈ D)
    (C : Circuit) (L : List ℕ) (h : X3 C L) : X3 (relabel φ C) (L.map (sig φ)) := by
  obtain ⟨h1, h2⟩ := h
  have key : ∀ a b, a - φ b ∈ D ↔ φ.symm a - b ∈ D := by
    intro a b
    rw [← hφ (φ.symm a) b, Equiv.apply_symm_apply]
  refine ⟨fun p l hpl => ?_, fun Q hQ hl => ?_⟩
  · have h0 := h1 (φ.symm p) (φ.symm l) (by rw [← hφ]; simpa using hpl)
    refine Eq.trans ?_ h0
    apply eval_two _ _ _ _ _ (by simp)
    apply rel_two
    · intro k; simp [Equiv.eq_symm_apply]
    · intro k; simp [Equiv.eq_symm_apply]
  · have h0 := h2 (Q.map φ.symm.toEmbedding) (by simpa using hQ) (by
      intro l
      have e : {q ∈ Q.map φ.symm.toEmbedding | q - l ∈ D}
          = ({q ∈ Q | q - φ l ∈ D}).map φ.symm.toEmbedding := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_symm]
        rw [key (φ q) l, Equiv.symm_apply_apply]
      rw [e, Finset.card_map]
      exact hl (φ l))
    refine Eq.trans ?_ h0
    apply eval_two _ _ _ _ _ (by simp)
    apply rel_two
    · intro k; simp [Finset.mem_map_equiv]
    · intro k
      simp only [Finset.forall_mem_map, Equiv.coe_toEmbedding, decide_eq_decide]
      constructor
      · intro hh q hq; rw [← key]; exact hh q hq
      · intro hh q hq; rw [key]; exact hh q hq

def E (L L' : List ℕ) : Prop :=
  ∀ x : List Bool, x.length = 26 →
    (L.any fun i => x.getD i false) = L'.any fun i => x.getD i false

theorem x3_congr (C : Circuit) (L L' : List ℕ) (hE : E L L') (h : X3 C L) : X3 C L' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun p l hpl => ?_, fun Q hQ hl => ?_⟩
  · have h0 := h1 p l hpl
    simp only at h0 ⊢
    rw [← hE _ (by simp)]; exact h0
  · have h0 := h2 Q hQ hl
    simp only at h0 ⊢
    rw [← hE _ (by simp)]; exact h0

def mm (j : Fin 3) : Fin 13 := if j = 0 then 1 else if j = 1 then 3 else 9
def mi (j : Fin 3) : Fin 13 := if j = 0 then 1 else if j = 1 then 9 else 3

def fwd (j : Fin 3) (t : Fin 13) (x : Fin 13) : Fin 13 := mm j * x + t

def eqv (j : Fin 3) (t : Fin 13) : Equiv.Perm (Fin 13) where
  toFun := fwd j t
  invFun x := mi j * (x - t)
  left_inv := by revert j t; unfold Function.LeftInverse fwd; decide
  right_inv := by revert j t; unfold Function.RightInverse Function.LeftInverse fwd; decide

theorem mm_D : ∀ (j : Fin 3) (d : Fin 13), mm j * d ∈ D ↔ d ∈ D := by
  unfold D
  decide

open Fin.CommRing in
theorem eqv_col (j : Fin 3) (t : Fin 13) (a b : Fin 13) :
    eqv j t a - eqv j t b ∈ D ↔ a - b ∈ D := by
  have e : eqv j t a - eqv j t b = mm j * (a - b) := by
    show (mm j * a + t) - (mm j * b + t) = _
    ring
  rw [e]
  exact mm_D j (a - b)

def subL (A B : List ℕ) : Bool :=
  A.all fun i => decide (26 ≤ i) || B.any fun k => decide (k = i)

theorem E_of_sub (A B : List ℕ) (h1 : subL A B = true) (h2 : subL B A = true) : E A B := by
  have aux : ∀ (A B : List ℕ), subL A B = true → ∀ x : List Bool, x.length = 26 →
      (A.any fun i => x.getD i false) = true → (B.any fun i => x.getD i false) = true := by
    intro A B h x hx ha
    rw [List.any_eq_true] at ha ⊢
    obtain ⟨i, hi, hv⟩ := ha
    unfold subL at h
    rw [List.all_eq_true] at h
    have := h i hi
    rw [Bool.or_eq_true, List.any_eq_true] at this
    rcases this with h26 | ⟨k, hk, hke⟩
    · have h26' : 26 ≤ i := by simpa using h26
      rw [List.getD_eq_default _ _ (by omega)] at hv
      cases hv
    · have : k = i := by simpa using hke
      exact ⟨i, this ▸ hk, hv⟩
  intro x hx
  rw [Bool.eq_iff_iff]
  exact ⟨aux A B h1 x hx, aux B A h2 x hx⟩

theorem orbit : ∀ a b : Fin 27, ∃ j : Fin 3, ∃ t : Fin 13,
    reps.any (fun L' => subL [sig (fwd j t) a.val, sig (fwd j t) b.val] L' &&
      subL L' [sig (fwd j t) a.val, sig (fwd j t) b.val]) = true := by
  decide +kernel

theorem clampE (L : List ℕ) (hL : L.length ≤ 2) : ∃ a b : Fin 27, E L [a.val, b.val] := by
  have c : ∀ n : ℕ, ∀ x : List Bool, x.length = 26 →
      x.getD n false = x.getD (min n 26) false := by
    intro n x hx
    by_cases h : n < 26
    · rw [min_eq_left (by omega)]
    · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by omega)]
  match L, hL with
  | [], _ =>
    refine ⟨⟨26, by omega⟩, ⟨26, by omega⟩, fun x hx => ?_⟩
    have h26 := List.getD_eq_default x false (show x.length ≤ 26 by omega)
    show false = (x.getD 26 false || (x.getD 26 false || false))
    rw [h26]; rfl
  | [n], _ =>
    refine ⟨⟨min n 26, by omega⟩, ⟨min n 26, by omega⟩, fun x hx => ?_⟩
    show (x.getD n false || false) = (x.getD (min n 26) false || (x.getD (min n 26) false || false))
    rw [← c n x hx]
    cases x.getD n false <;> rfl
  | [n, m], _ =>
    refine ⟨⟨min n 26, by omega⟩, ⟨min m 26, by omega⟩, fun x hx => ?_⟩
    show (x.getD n false || (x.getD m false || false))
      = (x.getD (min n 26) false || (x.getD (min m 26) false || false))
    rw [← c n x hx, ← c m x hx]
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

theorem main (C : Circuit) (L : List ℕ) (hL : L.length ≤ 2) (hM : Monotone2 C) (h4 : X4 C)
    (h3 : X3 C L) :
    ∃ C' : Circuit, ∃ L' ∈ reps, Monotone2 C' ∧ X4 C' ∧ X3 C' L' ∧ C'.size ≤ C.size := by
  obtain ⟨a, b, hab⟩ := clampE L hL
  obtain ⟨j, t, ho⟩ := orbit a b
  rw [List.any_eq_true] at ho
  obtain ⟨L', hL', hs⟩ := ho
  rw [Bool.and_eq_true] at hs
  have h3' := transport (eqv j t) (eqv_col j t) C _ (x3_congr C L _ hab h3)
  refine ⟨relabel (eqv j t) C, L', hL', relabel_mono _ C hM, relabel_x4 _ C h4, ?_, ?_⟩
  · exact x3_congr _ _ _ (E_of_sub _ _ hs.1 hs.2) h3'
  · simp [relabel, Circuit.size]

end PEqualNP.Outside.L_meta_4676

theorem PEqualNP.Outside.L_meta_4676 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List ℕ), x7.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), ∃ x13 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x12 ∧ x4 x12 ∧ x3 x12 x13 ∧ x12.size ≤ x6.size :=
  fun C L hL hM h4 h3 => PEqualNP.Outside.L_meta_4676.main C L hL hM h4 h3
