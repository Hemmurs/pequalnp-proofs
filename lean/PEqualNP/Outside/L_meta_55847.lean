import PEqualNP.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Flatten
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Init
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Bits

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.PM3LeastCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_ok (m : ℕ) (gs : List Gate) (h : CleanL m gs) :
    ∀ g ∈ gs, Ok g := by
  intro g hg
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp hg
  rcases h p g atGate with ⟨op, a, _, inputs⟩ | ⟨ops, a, b, _, _, inputs⟩
  · simp [Ok, op, inputs]
  · rcases ops with op | op <;> simp [Ok, op, inputs]

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => clean_ok _ _ hcl g' hg'
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => clean_ok _ _ hcl g' (List.mem_append_left _ h)
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

end

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.PM3LeastCore

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

private theorem evalAgree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

abbrev Orient (s a b : Bool) : Prop := if s then a = true → b = true else b = true → a = true

def Unate {n : ℕ} (F : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ s, ∀ x y, (∀ j, j ≠ i → x j = y j) → x i = false → y i = true → Orient s (F x) (F y)

private theorem orientKeep : ∀ s a b c d : Bool, Orient s a b → Orient s c d →
    Orient s (a && c) (b && d) ∧ Orient s (a || c) (b || d) := by decide

private theorem orientRefl (s a : Bool) : Orient s a a := by cases s <;> simp [Orient]

theorem formulaUnate {n : ℕ} (i : Fin n) (p : DMFormula n) :
    occurrences i p ≤ 1 → Unate p.eval i := by
  induction p with
  | lit k s =>
    intro _
    by_cases hk : k = i
    · subst k
      refine ⟨s, fun x y _ hx hy => ?_⟩
      cases s <;> simp [DMFormula.eval, Orient, hx, hy]
    · refine ⟨true, fun x y h _ _ => ?_⟩
      rw [show (DMFormula.lit k s).eval x = (DMFormula.lit k s).eval y by
        simp [DMFormula.eval, h k hk]]
      exact orientRefl _ _
  | and p q ihp ihq | or p q ihp ihq =>
    intro h
    change occurrences i p + occurrences i q ≤ 1 at h
    have absent (r : DMFormula n) (hr : occurrences i r = 0)
        (x y : Fin n → Bool) (hxy : ∀ j, j ≠ i → x j = y j) : r.eval x = r.eval y := by
      apply evalAgree
      intro j hj
      exact hxy j (by rintro rfl; omega)
    by_cases hp : occurrences i p = 0
    · obtain ⟨s, hs⟩ := ihq (by omega)
      refine ⟨s, fun x y hxy hx hy => ?_⟩
      have h₁ : Orient s (p.eval x) (p.eval y) := by
        rw [absent p hp x y hxy]
        exact orientRefl _ _
      first
      | exact (orientKeep s _ _ _ _ h₁ (hs x y hxy hx hy)).1
      | exact (orientKeep s _ _ _ _ h₁ (hs x y hxy hx hy)).2
    · obtain ⟨s, hs⟩ := ihp (by omega)
      refine ⟨s, fun x y hxy hx hy => ?_⟩
      have h₂ : Orient s (q.eval x) (q.eval y) := by
        rw [absent q (by omega) x y hxy]
        exact orientRefl _ _
      first
      | exact (orientKeep s _ _ _ _ (hs x y hxy hx hy) h₂).1
      | exact (orientKeep s _ _ _ _ (hs x y hxy hx hy) h₂).2

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula

namespace PEqualNP.Outside.L_meta_55847_aux.Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

end PEqualNP.Outside.L_meta_55847_aux.Helpers

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula

open PEqualNP.MetaComplexity

def complement {n : Nat} : DMFormula n → DMFormula n
  | .lit i s => .lit i (!s)
  | .and a b => .or (complement a) (complement b)
  | .or a b => .and (complement a) (complement b)

theorem complement_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (complement p).eval x = !(p.eval x) := by
  induction p with
  | lit i s => cases s <;> cases h : x i <;> simp [complement, DMFormula.eval, h]
  | and a b ha hb | or a b ha hb =>
    simp only [complement, DMFormula.eval, ha, hb]
    cases a.eval x <;> cases b.eval x <;> rfl

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedUniqueRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_55847_aux.Helpers
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula

def propagateDirection (op : GateOp) (direction : Bool) : Bool :=
  match op with
  | .not => !direction
  | _ => direction

def SignedRead (n : Nat) (gs : List Gate) (source target : Nat × Bool) : Prop :=
  ∃ p g, gs[p]? = some g ∧ source.1 ∈ g.inputs ∧
    target = (n + p, propagateDirection g.op source.2)

abbrev SignedPath (n : Nat) (gs : List Gate) := Relation.ReflTransGen (SignedRead n gs)

theorem signed_read_address_lt {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    {source target : Nat × Bool} (edge : SignedRead n gs source target) : source.1 < target.1 := by
  obtain ⟨p, g, atGate, reads, rfl⟩ := edge
  exact (clean p g atGate).lt _ reads

private theorem complement_preserves_occurrence {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (complement p) = occurrences i p := by
  induction p <;> simp_all [complement, occurrences]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then complement (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = complement (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, complement_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, complement_preserves_occurrence]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedUniqueRead

namespace PEqualNP.Outside.L_meta_55847_aux.ListTwoPositions

private theorem splitLookup {α : Type} (xs : List α) (i : Nat) (a : α)
    (hit : xs[i]? = some a) :
    xs = xs.take i ++ (a :: xs.drop (i + 1)) ∧ (xs.take i).length = i := by
  obtain ⟨available, value⟩ := List.getElem?_eq_some_iff.mp hit
  refine ⟨?_, List.length_take_of_le (Nat.le_of_lt available)⟩
  calc
    xs = xs.take i ++ xs.drop i := (List.take_append_drop i xs).symm
    _ = xs.take i ++ (a :: xs.drop (i + 1)) := by
      rw [List.drop_eq_getElem_cons available, value]

theorem splitAtTwoLookups {α : Type} (xs : List α) (i j : Nat) (a b : α)
    (order : i < j) (first : xs[i]? = some a) (second : xs[j]? = some b) :
    ∃ pre mid post : List α,
      xs = (pre ++ ([a] ++ mid)) ++ ([b] ++ post) ∧
      pre.length = i ∧ (pre ++ ([a] ++ mid)).length = j ∧
      mid.length = j - (i + 1) := by
  let pre := xs.take i
  let tail := xs.drop (i + 1)
  let offset := j - (i + 1)
  have addr : i + 1 + offset = j := by
    dsimp only [offset]
    omega
  have secondTail : tail[offset]? = some b := by
    change (xs.drop (i + 1))[offset]? = some b
    rw [List.getElem?_drop, addr]
    exact second
  let mid := tail.take offset
  let post := tail.drop (offset + 1)
  have firstSplit : xs = pre ++ (a :: tail) := (splitLookup xs i a first).1
  have secondSplit : tail = mid ++ (b :: post) :=
    (splitLookup tail offset b secondTail).1
  have preLen : pre.length = i := (splitLookup xs i a first).2
  have midLen : mid.length = offset := (splitLookup tail offset b secondTail).2
  have secondPrefixLen : (pre ++ ([a] ++ mid)).length = j := by
    simp only [List.length_append, List.length_cons, List.length_nil, preLen, midLen] <;> omega
  refine ⟨pre, mid, post, ?_, preLen, secondPrefixLen, midLen⟩
  calc
    xs = pre ++ (a :: tail) := firstSplit
    _ = pre ++ (a :: (mid ++ (b :: post))) := congrArg (fun l => pre ++ (a :: l)) secondSplit
    _ = (pre ++ ([a] ++ mid)) ++ ([b] ++ post) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]

end PEqualNP.Outside.L_meta_55847_aux.ListTwoPositions

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedReadLocal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_55847_aux.Helpers
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedUniqueRead
open PEqualNP.Outside.L_meta_55847_aux.ListTwoPositions

abbrev AddressRead (n : Nat) (gs : List Gate) (a b : Nat) : Prop :=
  ∃ s : Bool, SignedRead n gs (a, true) (b, s)

private theorem address_read_lt {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    {a b : Nat} (edge : AddressRead n gs a b) : a < b := by
  obtain ⟨_, step⟩ := edge
  exact signed_read_address_lt clean step

private theorem address_read_target_gate {n : Nat} {gs : List Gate}
    {a b : Nat} (edge : AddressRead n gs a b) : n ≤ b := by
  obtain ⟨_, p, _, _, _, addr⟩ := edge
  have hb : b = n + p := congrArg Prod.fst addr
  omega

private theorem two_reader_positions {gs : List Gate} {p q a : Nat} {g h : Gate}
    (order : p < q) (pg : gs[p]? = some g) (qh : gs[q]? = some h)
    (gm : a ∈ g.inputs) (hm : a ∈ h.inputs) : 2 ≤ (gs.flatMap Gate.inputs).count a := by
  obtain ⟨pre, mid, post, split, _, _, _⟩ := splitAtTwoLookups gs p q g h order pg qh
  have cg := List.count_pos_iff.mpr gm
  have ch := List.count_pos_iff.mpr hm
  rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append]
  omega

private theorem address_read_unique {n : Nat} {gs : List Gate} {a b c : Nat}
    (once : (gs.flatMap Gate.inputs).count a ≤ 1)
    (left : AddressRead n gs a b) (right : AddressRead n gs a c) : b = c := by
  obtain ⟨_, p, g, pg, gm, eb⟩ := left
  obtain ⟨_, q, h, qh, hm, ec⟩ := right
  change a ∈ g.inputs at gm
  change a ∈ h.inputs at hm
  have bp : b = n + p := congrArg Prod.fst eb
  have cq : c = n + q := congrArg Prod.fst ec
  rcases lt_trichotomy p q with order | same | reverse
  · have tooMany := two_reader_positions order pg qh gm hm
    omega
  · omega
  · have tooMany := two_reader_positions reverse qh pg hm gm
    omega

private theorem input_edge {n : Nat} {gs : List Gate} {p a : Nat} {g : Gate}
    (atGate : gs[p]? = some g) (member : a ∈ g.inputs) :
    AddressRead n gs a (n + p) := by
  refine ⟨propagateDirection g.op true, ?_⟩
  exact ⟨p, g, atGate, member, rfl⟩

abbrev AddressPath (n : Nat) (gs : List Gate) :=
  Relation.ReflTransGen (AddressRead n gs)

private theorem address_path_le {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    {a b : Nat} (path : AddressPath n gs a b) : a ≤ b := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ edge ih => exact le_trans ih (le_of_lt (address_read_lt clean edge))

private theorem address_path_raw_or_gate {n : Nat} {gs : List Gate} {raw b : Nat}
    (path : AddressPath n gs raw b) : b = raw ∨ n ≤ b := by
  induction path with
  | refl => exact Or.inl rfl
  | tail _ edge _ => exact Or.inr (address_read_target_gate edge)

private theorem predecessor_bounded {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (pivot cap : Nat)
    (once : ∀ a, AddressPath n gs pivot a → a < cap → (gs.flatMap Gate.inputs).count a ≤ 1)
    (fuel : Nat) :
    ∀ source a b target : Nat, AddressPath n gs pivot source →
      target ≤ cap → target ≤ source + fuel →
      AddressPath n gs source a → AddressRead n gs a target →
      AddressPath n gs source b → AddressRead n gs b target → a = b := by
  induction fuel with
  | zero =>
    intro source a b target _ _ bound pathA edgeA _ _
    have low := address_path_le clean pathA
    have high := address_read_lt clean edgeA
    omega
  | succ fuel ih =>
    intro source a b target fromPivot targetBound bound pathA edgeA pathB edgeB
    have toA := address_path_le clean pathA
    have toTarget := address_read_lt clean edgeA
    have sourceOnce := once source fromPivot (by omega)
    rcases Relation.ReflTransGen.cases_head pathA with sameA | ⟨nextA, firstA, restA⟩
    · subst a
      rcases Relation.ReflTransGen.cases_head pathB with sameB | ⟨nextB, firstB, restB⟩
      · exact sameB
      · have nextEq := address_read_unique sourceOnce edgeA firstB
        have low := address_path_le clean restB
        have high := address_read_lt clean edgeB
        omega
    · have forward := address_read_lt clean firstA
      rcases Relation.ReflTransGen.cases_head pathB with sameB | ⟨nextB, firstB, restB⟩
      · subst b
        have nextEq := address_read_unique sourceOnce firstA edgeB
        have low := address_path_le clean restA
        have high := address_read_lt clean edgeA
        omega
      · have nextEq := address_read_unique sourceOnce firstA firstB
        subst nextB
        exact ih nextA a b target (fromPivot.tail firstA) targetBound (by omega)
          restA edgeA restB edgeB

private theorem unique_predecessor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    {pivot a b target cap : Nat}
    (once : ∀ w, AddressPath n gs pivot w → w < cap → (gs.flatMap Gate.inputs).count w ≤ 1)
    (targetBound : target ≤ cap)
    (pathA : AddressPath n gs pivot a) (edgeA : AddressRead n gs a target)
    (pathB : AddressPath n gs pivot b) (edgeB : AddressRead n gs b target) : a = b :=
  predecessor_bounded clean pivot cap once target pivot a b target .refl targetBound (by omega)
    pathA edgeA pathB edgeB

private theorem positive_summand (weight : Nat → Nat) (xs : List Nat)
    (positive : 0 < (xs.map weight).sum) :
    ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    · have positiveRest : 0 < (rest.map weight).sum := by
        simp only [List.map_cons, List.sum_cons] at positive
        omega
      obtain ⟨b, member, hb⟩ := ih positiveRest
      exact ⟨b, List.mem_cons_of_mem _ member, hb⟩

private theorem positive_weight_has_path {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (pivot : Fin n) (weight : Nat → Nat)
    (rawWeight : ∀ w < n, weight w = if w = pivot.val then 1 else 0)
    (gateWeight : ∀ p g, gs[p]? = some g → weight (n + p) = (g.inputs.map weight).sum) :
    ∀ w, w < n + gs.length → 0 < weight w → AddressPath n gs pivot.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro valid positive
    by_cases raw : w < n
    · rw [rawWeight w raw] at positive
      by_cases same : w = pivot.val
      · subst w
        exact Relation.ReflTransGen.refl
      · simp [same] at positive
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have pos : p < gs.length := by omega
      let g := gs[p]
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pos
      rw [gateWeight p g atGate] at positive
      obtain ⟨a, member, ha⟩ := positive_summand weight g.inputs positive
      have earlier := (clean p g atGate).lt a member
      exact Relation.ReflTransGen.tail (ih a earlier (by omega) ha) (input_edge atGate member)

theorem clean_path_reads_weights_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (pivot : Fin n) (cap : Nat)
    (once : ∀ a, AddressPath n gs pivot.val a → a < cap → (gs.flatMap Gate.inputs).count a ≤ 1)
    (weight : Nat → Nat)
    (rawWeight : ∀ w < n, weight w = if w = pivot.val then 1 else 0)
    (gateWeight : ∀ p g, gs[p]? = some g → weight (n + p) = (g.inputs.map weight).sum) :
    ∀ w, w < n + gs.length → w ≤ cap → weight w ≤ 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro valid bound
    by_cases raw : w < n
    · rw [rawWeight w raw]
      split <;> omega
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have pos : p < gs.length := by omega
      let g := gs[p]
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pos
      rw [gateWeight p g atGate]
      rcases clean p g atGate with ⟨_, a, earlier, inputs⟩ | ⟨_, a, b, ha, hb, inputs⟩
      · simpa [inputs] using ih a earlier (by omega) (by omega)
      · simp only [inputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have aLe := ih a ha (by omega) (by omega)
        have bLe := ih b hb (by omega) (by omega)
        by_contra! greater
        have aMem : a ∈ g.inputs := by simp [inputs]
        have bMem : b ∈ g.inputs := by simp [inputs]
        have path := positive_weight_has_path clean pivot weight rawWeight gateWeight
        have pathA := path a (by omega) (by omega)
        have pathB := path b (by omega) (by omega)
        have eq : a = b := unique_predecessor clean once bound
          pathA (input_edge atGate aMem) pathB (input_edge atGate bMem)
        have gsMem : g ∈ gs := List.mem_of_getElem? atGate
        have singleton : List.Sublist [g] gs := List.singleton_sublist.mpr gsMem
        have inputsSub : List.Sublist g.inputs (gs.flatMap Gate.inputs) := by
          simpa using singleton.flatMap Gate.inputs
        have readCount := (List.Sublist.count_le a inputsSub).trans (once a pathA (by omega))
        rw [inputs, ← eq] at readCount
        simp at readCount

theorem clean_raw_and_gate_reads_weights_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (pivot : Fin n)
    (once : ∀ a, (a = pivot.val ∨ n ≤ a) → (gs.flatMap Gate.inputs).count a ≤ 1)
    (weight : Nat → Nat)
    (rawWeight : ∀ w < n, weight w = if w = pivot.val then 1 else 0)
    (gateWeight : ∀ p g, gs[p]? = some g → weight (n + p) = (g.inputs.map weight).sum) :
    ∀ w, w < n + gs.length → weight w ≤ 1 := by
  intro w valid
  exact clean_path_reads_weights_le_one clean pivot w
    (fun a path _ => once a (address_path_raw_or_gate path)) weight rawWeight gateWeight w valid le_rfl

theorem clean_wireFormula_occurrences_le_one_on_path {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (fallback chosen : Fin n) (w : Nat) (valid : w < n + gs.length)
    (once : ∀ a, AddressPath n gs chosen.val a → a < w → (gs.flatMap Gate.inputs).count a ≤ 1) :
    occurrences chosen (wireFormula fallback gs w) ≤ 1 := by
  let weight : Nat → Nat := fun addr => occurrences chosen (wireFormula fallback gs addr)
  have rawWeight (addr : Nat) (inside : addr < n) :
      weight addr = if addr = chosen.val then 1 else 0 := by
    change occurrences chosen (wireFormula fallback gs addr) = _
    rw [wireFormula_count_input fallback gs chosen ⟨addr, inside⟩]
    by_cases eq : addr = chosen.val
    · have same : (⟨addr, inside⟩ : Fin n) = chosen := Fin.ext eq
      simp [eq]
    · have different : (⟨addr, inside⟩ : Fin n) ≠ chosen :=
        fun same => eq (congrArg Fin.val same)
      simp [different, eq]
  have gateWeight (p : Nat) (g : Gate) (atGate : gs[p]? = some g) :
      weight (n + p) = (g.inputs.map weight).sum :=
    wireFormula_count_gate fallback clean chosen atGate
  exact clean_path_reads_weights_le_one clean chosen w once weight rawWeight gateWeight w valid le_rfl

theorem clean_wireFormula_occurrences_le_one_of_raw_and_gates {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (fallback chosen : Fin n)
    (once : ∀ a, (a = chosen.val ∨ n ≤ a) → (gs.flatMap Gate.inputs).count a ≤ 1)
    (w : Nat) (valid : w < n + gs.length) :
    occurrences chosen (wireFormula fallback gs w) ≤ 1 :=
  clean_wireFormula_occurrences_le_one_on_path clean fallback chosen w valid
    (fun a path _ => once a (address_path_raw_or_gate path))

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedReadLocal

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SharedReadRoutes

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_55847_aux.Helpers PEqualNP.Outside.L_meta_55847_aux.ListTwoPositions

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem vl_congr {n : Nat} (gs : List Gate) (hcl : CleanL n gs)
    (x y : Fin n → Bool) (gidx : Nat) (g : Gate) (hpg : gs[gidx]? = some g)
    (agree : ∀ a ∈ g.inputs, vl gs x a = vl gs y a) :
    vl gs x (n + gidx) = vl gs y (n + gidx) := by
  rw [vl_gate gs hcl x gidx g hpg, vl_gate gs hcl y gidx g hpg]
  congr 1
  exact List.map_congr_left agree

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

theorem read_target_internal {n : Nat} {gs : List Gate}
    {a b : Fin (n + gs.length)} (step : readEdge gs a b) : n ≤ b.val := by
  obtain ⟨p, _, _, hb, _⟩ := step
  omega

theorem read_path_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (path : Relation.ReflTransGen (readEdge gs) a b) :
    a.val ≤ b.val := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact ih.trans (le_of_lt (read_order hcl step))

private theorem two_reads_at_lookups {gs : List Gate} {p q a : Nat} {g h : Gate}
    (order : p < q) (pg : gs[p]? = some g) (qh : gs[q]? = some h)
    (gm : a ∈ g.inputs) (hm : a ∈ h.inputs) : 2 ≤ (gs.flatMap Gate.inputs).count a := by
  obtain ⟨pre, mid, post, split, _, _, _⟩ := splitAtTwoLookups gs p q g h order pg qh
  have cg := List.count_pos_iff.mpr gm
  have ch := List.count_pos_iff.mpr hm
  rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append]
  omega

theorem unique_read_successor {n : Nat} {gs : List Gate} {a b c : Fin (n + gs.length)}
    (once : (gs.flatMap Gate.inputs).count a.val ≤ 1)
    (left : readEdge gs a b) (right : readEdge gs a c) : b = c := by
  obtain ⟨p, g, pg, eb, gm⟩ := left
  obtain ⟨q, h, qh, ec, hm⟩ := right
  apply Fin.ext
  rcases lt_trichotomy p q with order | same | reverse
  · have tooMany := two_reads_at_lookups order pg qh gm hm
    omega
  · omega
  · have tooMany := two_reads_at_lookups reverse qh pg hm gm
    omega

private theorem bypass_impossible {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (raw : Fin n) (cut : Fin (n + gs.length))
    (onceRaw : (gs.flatMap Gate.inputs).count raw.val ≤ 1)
    (onceOthers : ∀ i, n ≤ i → i ≠ cut.val → (gs.flatMap Gate.inputs).count i ≤ 1)
    {source : Fin (n + gs.length)}
    (path : Relation.ReflTransGen (readEdge gs) source cut) :
    (source = inputWire gs raw ∨ n ≤ source.val) →
    ∀ out : Fin (n + gs.length), cut.val < out.val →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) source out := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ out later kept
    rcases kept.cases_head with same | ⟨_, first, _⟩
    · have equal := congrArg Fin.val same
      omega
    · exact first.2.1 rfl
  | @head a next first rest ih =>
    intro start out later kept
    have prev : a.val < cut.val := (read_order clean first).trans_le (read_path_order clean rest)
    rcases kept.cases_head with same | ⟨branch, side, restSide⟩
    · have equal := congrArg Fin.val same
      omega
    · have once : (gs.flatMap Gate.inputs).count a.val ≤ 1 := by
        rcases start with rfl | internal
        · exact onceRaw
        · exact onceOthers a.val internal (by omega)
      have equal := unique_read_successor once first side.1
      subst branch
      exact ih (Or.inr (read_target_internal first)) out later restSide

theorem shared_wire_blocks_bypass {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (raw : Fin n) (cut out : Fin (n + gs.length))
    (onceRaw : (gs.flatMap Gate.inputs).count raw.val ≤ 1)
    (onceOthers : ∀ i, n ≤ i → i ≠ cut.val → (gs.flatMap Gate.inputs).count i ≤ 1)
    (path : Relation.ReflTransGen (readEdge gs) (inputWire gs raw) cut)
    (later : cut.val < out.val) :
    ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs raw) out :=
  bypass_impossible clean raw cut onceRaw onceOthers path (Or.inl rfl) out later

theorem matching_shared_cut_controls_changes {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (onceOthers : ∀ i, n ≤ i → i ≠ cut.val → (gs.flatMap Gate.inputs).count i ≤ 1)
    (later : cut.val < out.val)
    (eachChanged : ∀ raw : Fin n, x raw ≠ y raw →
      (gs.flatMap Gate.inputs).count raw.val ≤ 1 ∧
      Relation.ReflTransGen (readEdge gs) (inputWire gs raw) cut)
    (equalAtCut : vl gs x cut.val = vl gs y cut.val) :
    vl gs x out.val = vl gs y out.val := by
  apply circuit_cut_agreement clean cut out x y equalAtCut
  intro raw changes
  have h := eachChanged raw changes
  exact shared_wire_blocks_bypass clean raw cut out h.1 onceOthers h.2 later

theorem wire_change_traces_to_raw {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (wire : Fin (n + gs.length))
    (different : vl gs x wire.val ≠ vl gs y wire.val) :
    ∃ raw : Fin n, x raw ≠ y raw ∧
      Relation.ReflTransGen (readEdge gs) (inputWire gs raw) wire := by
  have trace : ∀ rank (w : Fin (n + gs.length)), w.val = rank →
      vl gs x w.val ≠ vl gs y w.val →
      ∃ raw : Fin n, x raw ≠ y raw ∧
        Relation.ReflTransGen (readEdge gs) (inputWire gs raw) w := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | _ rank ih =>
      intro w atRank changes
      by_cases isRaw : w.val < n
      · let raw : Fin n := ⟨w.val, isRaw⟩
        have same : inputWire gs raw = w := Fin.ext rfl
        rw [vl_input gs x w.val isRaw, vl_input gs y w.val isRaw] at changes
        exact ⟨raw, changes, same ▸ Relation.ReflTransGen.refl⟩
      · obtain ⟨earlier, edge, differs⟩ := gate_difference clean x y w isRaw changes
        have before := (read_order clean edge).trans_eq atRank
        obtain ⟨raw, rawChange, beforePath⟩ := ih earlier.val before earlier rfl differs
        exact ⟨raw, rawChange, beforePath.tail edge⟩
  exact trace wire.val wire rfl different

theorem wire_agrees_if_reaching_raws_agree {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (x y : Fin n → Bool) (wire : Fin (n + gs.length))
    (agrees : ∀ raw, Relation.ReflTransGen (readEdge gs) (inputWire gs raw) wire →
      x raw = y raw) : vl gs x wire.val = vl gs y wire.val := by
  by_contra different
  obtain ⟨raw, changed, path⟩ := wire_change_traces_to_raw clean x y wire different
  exact changed (agrees raw path)

private theorem gate_positive_mono (g : Gate) (basis : g.op = .and ∨ g.op = .or)
    (x y : Nat → Bool) (monotone : ∀ a ∈ g.inputs, x a = true → y a = true)
    (positive : g.op.eval (g.inputs.map x) = true) : g.op.eval (g.inputs.map y) = true := by
  rcases basis with isAnd | isOr
  · rw [isAnd] at positive ⊢
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at positive ⊢
    exact fun a member => monotone a member (positive a member)
  · rw [isOr] at positive ⊢
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at positive ⊢
    obtain ⟨a, member, value⟩ := positive
    exact ⟨a, member, monotone a member value⟩

private theorem clean_basis_if_not_not {m : Nat} {g : Gate}
    (clean : CleanGate m g) (notNeg : g.op ≠ .not) : g.op = .and ∨ g.op = .or := by
  rcases clean with ⟨isNot, _⟩ | ⟨basis, _⟩
  · exact (notNeg isNot).elim
  · exact basis

private theorem values_mono_before_not {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (k : Fin gs.length) (unique : ∀ p : Fin gs.length, (gs.get p).op = .not → p = k)
    (x y : Fin n → Bool) (rawMono : x ≤ y) :
    ∀ w, w < n + k.val → vl gs x w = true → vl gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro before trueX
    by_cases isRaw : w < n
    · rw [vl_input gs x w isRaw] at trueX
      rw [vl_input gs y w isRaw]
      exact Bool.eq_true_of_true_le (trueX ▸ rawMono ⟨w, isRaw⟩)
    · let p : Fin gs.length := ⟨w - n, by have := k.isLt; omega⟩
      have wireAt : w = n + p.val := by change w = n + (w - n); omega
      let gate := gs.get p
      have stored : gs[p.val]? = some gate := List.getElem?_eq_getElem p.isLt
      have shape := clean p.val gate stored
      have notNeg : gate.op ≠ .not := by
        intro neg
        have eq := unique p neg
        rw [eq] at wireAt
        omega
      rw [wireAt, vl_gate gs clean x p.val gate stored] at trueX
      rw [wireAt, vl_gate gs clean y p.val gate stored]
      apply gate_positive_mono gate (clean_basis_if_not_not shape notNeg)
        (vl gs x) (vl gs y) _ trueX
      intro input present inputTrue
      have earlier : input < w := (shape.lt input present).trans_eq wireAt.symm
      exact ih input earlier (earlier.trans before) inputTrue

theorem not_output_cannot_rise {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (k : Fin gs.length) (neg : (gs.get k).op = .not)
    (unique : ∀ p : Fin gs.length, (gs.get p).op = .not → p = k)
    (x y : Fin n → Bool) (rawMono : x ≤ y) :
    ¬ (vl gs x (n + k.val) = false ∧ vl gs y (n + k.val) = true) := by
  intro rises
  let gate := gs.get k
  have stored : gs[k.val]? = some gate := List.getElem?_eq_getElem k.isLt
  have state := clean k.val gate stored
  rcases state with ⟨_, operand, earlier, args⟩ | ⟨basis, _⟩
  · have notOp : gate.op = .not := neg
    rw [vl_gate gs clean x k.val gate stored, vl_gate gs clean y k.val gate stored, notOp, args] at rises
    have priorX : vl gs x operand = true := by simpa [GateOp.eval] using rises.1
    have priorY : vl gs y operand = false := by simpa [GateOp.eval] using rises.2
    have forced := values_mono_before_not clean k unique x y rawMono operand earlier priorX
    rw [priorY] at forced
    cases forced
  · have notOp : gate.op = .not := neg
    rcases basis with isAnd | isOr
    · rw [notOp] at isAnd
      cases isAnd
    · rw [notOp] at isOr
      cases isOr

private theorem difference_from_or_iff_rising : ∀ a b : Bool,
    (a ≠ (a || b)) ↔ (a = false ∧ b = true) := by
  decide

theorem rise_traces_to_raw_avoiding_not {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (k : Fin gs.length) (neg : (gs.get k).op = .not)
    (unique : ∀ p : Fin gs.length, (gs.get p).op = .not → p = k)
    (x y : Fin n → Bool) (rawMono : x ≤ y)
    (cut w : Fin (n + gs.length)) (cutAt : cut.val = n + k.val)
    (rise : vl gs x w.val = false ∧ vl gs y w.val = true) :
    ∃ raw : Fin n, x raw = false ∧ y raw = true ∧
      Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs raw) w := by
  classical
  let baseline (u : Fin (n + gs.length)) := vl gs x u.val
  let joined (u : Fin (n + gs.length)) := vl gs x u.val || vl gs y u.val
  have tracks (u : Fin (n + gs.length)) :
      baseline u ≠ joined u ↔ vl gs x u.val = false ∧ vl gs y u.val = true :=
    difference_from_or_iff_rising _ _
  have fixedCut : baseline cut = joined cut := by
    by_contra changed
    have rises := (tracks cut).mp changed
    rw [cutAt] at rises
    exact not_output_cannot_rise clean k neg unique x y rawMono rises
  have prev (b : Fin (n + gs.length)) (notInput : ¬ b.val < n) (diff : baseline b ≠ joined b) :
      ∃ a, readEdge gs a b ∧ baseline a ≠ joined a := by
    have rises := (tracks b).mp diff
    let p : Fin gs.length := ⟨b.val - n, by have := b.isLt; omega⟩
    have wireAt : b.val = n + p.val := by change b.val = n + (b.val - n); omega
    let gate := gs.get p
    have stored : gs[p.val]? = some gate := List.getElem?_eq_getElem p.isLt
    have shape := clean p.val gate stored
    have gateNotNeg : gate.op ≠ .not := by
      intro isNot
      have eq := unique p isNot
      have isCut : b = cut := Fin.ext (by rw [wireAt, eq, cutAt])
      exact diff (isCut.symm ▸ fixedCut)
    have basis := clean_basis_if_not_not shape gateNotNeg
    rw [wireAt, vl_gate gs clean x p.val gate stored, vl_gate gs clean y p.val gate stored] at rises
    obtain ⟨a, present, left, right⟩ : ∃ a ∈ gate.inputs,
        vl gs x a = false ∧ vl gs y a = true := by
      by_contra none
      have forces (a : Nat) (present : a ∈ gate.inputs) (value : vl gs y a = true) :
          vl gs x a = true := by
        cases left : vl gs x a
        · exact (none ⟨a, present, left, value⟩).elim
        · rfl
      have forced := gate_positive_mono gate basis (vl gs y) (vl gs x) forces rises.2
      rw [rises.1] at forced
      cases forced
    have beforeB := (shape.lt a present).trans_eq wireAt.symm
    let u : Fin (n + gs.length) := ⟨a, beforeB.trans b.isLt⟩
    exact ⟨u, ⟨p.val, gate, stored, wireAt, present⟩, (tracks u).mpr ⟨left, right⟩⟩
  obtain ⟨a, isRaw, changed, path⟩ :=
    difference_traces Fin.val (fun v : Fin (n + gs.length) => v.val < n)
      (readEdge gs) cut baseline joined (fun _ _ => read_order clean) prev fixedCut ((tracks w).mpr rise)
  let raw : Fin n := ⟨a.val, isRaw⟩
  have sameWire : inputWire gs raw = a := Fin.ext rfl
  have values := (tracks a).mp changed
  rw [vl_input gs x a.val isRaw, vl_input gs y a.val isRaw] at values
  exact ⟨raw, values.1, values.2, by simpa only [sameWire] using path⟩

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SharedReadRoutes

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedReadLocal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_55847_aux.Helpers
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SharedReadRoutes
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedUniqueRead

theorem addressRead_iff_readEdge {n : Nat} {gs : List Gate}
    (a b : Fin (n + gs.length)) :
    AddressRead n gs a.val b.val ↔ readEdge gs a b := by
  constructor
  · rintro ⟨s, p, g, pg, gm, dst⟩
    exact ⟨p, g, pg, congrArg Prod.fst dst, gm⟩
  · rintro ⟨p, g, pg, dst, gm⟩
    exact ⟨propagateDirection g.op true, p, g, pg, gm, Prod.ext dst rfl⟩

theorem addressPath_to_readPath {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    {a b : Nat} (path : AddressPath n gs a b) (av : a < n + gs.length)
    (bv : b < n + gs.length) :
    Relation.ReflTransGen (readEdge gs) (⟨a, av⟩ : Fin (n + gs.length)) ⟨b, bv⟩ := by
  revert bv
  induction path with
  | refl =>
    intro _
    exact .refl
  | @tail x y _ step ih =>
    intro yv
    have xv : x < n + gs.length := by
      obtain ⟨_, hs⟩ := step
      exact lt_trans (signed_read_address_lt clean hs) yv
    exact (ih xv).tail ((addressRead_iff_readEdge ⟨x, xv⟩ ⟨y, yv⟩).mp step)

theorem readPath_to_addressPath {n : Nat} {gs : List Gate}
    {a b : Fin (n + gs.length)} (path : Relation.ReflTransGen (readEdge gs) a b) :
    AddressPath n gs a.val b.val := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail ((addressRead_iff_readEdge _ _).mpr step)

theorem clean_wireFormula_occurrences_le_one_on_readPath {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (fallback chosen : Fin n) (w : Fin (n + gs.length))
    (once : ∀ a : Fin (n + gs.length),
      Relation.ReflTransGen (readEdge gs) (inputWire gs chosen) a →
      a.val < w.val → (gs.flatMap Gate.inputs).count a.val ≤ 1) :
    occurrences chosen (wireFormula fallback gs w.val) ≤ 1 := by
  apply clean_wireFormula_occurrences_le_one_on_path clean fallback chosen w.val w.isLt
  intro a path earlier
  have av : a < n + gs.length := earlier.trans w.isLt
  let chosenWire := inputWire gs chosen
  exact once ⟨a, av⟩ (addressPath_to_readPath clean path chosenWire.isLt av) earlier

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedReadLocal

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ClosedWalkCount

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula
open scoped BigOperators

def addr (r a b : Nat) : Fin 12 := Fin.ofNat 12 (4 * r + a + 2 * b)

def star (s t u : Fin 2) : List (Fin 12) :=
  [addr 0 s.val t.val, addr 1 t.val u.val, addr 2 u.val s.val]

def Incident (i j : Fin 12) : Prop :=
  i ≠ j ∧ ∃ s t u : Fin 2, i ∈ star s t u ∧ j ∈ star s t u

theorem occurrence_sum_eq_leaves {n : Nat} (formula : DMFormula n) :
    (∑ i : Fin n, occurrences i formula) = formula.leaves := by
  induction formula with
  | lit i b => simp [occurrences, DMFormula.leaves]
  | and a b ha hb | or a b ha hb =>
    simp only [occurrences, DMFormula.leaves, Finset.sum_add_distrib, ha, hb]

private theorem group_leaves (p : DMFormula 12)
    (essential : ∀ i, 0 < occurrences i p)
    (noShared : ∀ i j, Incident i j →
      occurrences i p = 1 → occurrences j p = 1 → False)
    (i j k : Fin 12)
    (ij : Incident i j) (ik : Incident i k) (jk : Incident j k) :
    5 ≤ occurrences i p + occurrences j p + occurrences k p := by
  have ni := essential i
  have nj := essential j
  have nk := essential k
  have hij : ¬ (occurrences i p = 1 ∧ occurrences j p = 1) :=
    fun h => noShared i j ij h.1 h.2
  have hik : ¬ (occurrences i p = 1 ∧ occurrences k p = 1) :=
    fun h => noShared i k ik h.1 h.2
  have hjk : ¬ (occurrences j p = 1 ∧ occurrences k p = 1) :=
    fun h => noShared j k jk h.1 h.2
  omega

theorem leaves_ge_twenty (p : DMFormula 12)
    (essential : ∀ i, 0 < occurrences i p)
    (noShared : ∀ i j, Incident i j →
      occurrences i p = 1 → occurrences j p = 1 → False) :
    20 ≤ p.leaves := by
  let group := group_leaves p essential noShared
  have h000 := group 0 4 8
    ⟨by decide, 0, 0, 0, by decide, by decide⟩
    ⟨by decide, 0, 0, 0, by decide, by decide⟩
    ⟨by decide, 0, 0, 0, by decide, by decide⟩
  have h011 := group 2 7 9
    ⟨by decide, 0, 1, 1, by decide, by decide⟩
    ⟨by decide, 0, 1, 1, by decide, by decide⟩
    ⟨by decide, 0, 1, 1, by decide, by decide⟩
  have h101 := group 1 6 11
    ⟨by decide, 1, 0, 1, by decide, by decide⟩
    ⟨by decide, 1, 0, 1, by decide, by decide⟩
    ⟨by decide, 1, 0, 1, by decide, by decide⟩
  have h110 := group 3 5 10
    ⟨by decide, 1, 1, 0, by decide, by decide⟩
    ⟨by decide, 1, 1, 0, by decide, by decide⟩
    ⟨by decide, 1, 1, 0, by decide, by decide⟩
  have total := occurrence_sum_eq_leaves p
  simp [Fin.sum_univ_succ] at total
  change occurrences 0 p + (occurrences 1 p + (occurrences 2 p +
    (occurrences 3 p + (occurrences 4 p + (occurrences 5 p +
      (occurrences 6 p + (occurrences 7 p + (occurrences 8 p +
        (occurrences 9 p + (occurrences 10 p + occurrences 11 p)))))))))) =
      p.leaves at total
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ClosedWalkCount

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.DMFixedPair

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula

def withPair {n : Nat} (base : Fin n → Bool) (i j : Fin n) (a b : Bool) : Fin n → Bool :=
  fun k => if k = i then a else if k = j then b else base k

def HasProjection {n : Nat} (F : DMFormula n) (i j : Fin n) (op : Bool → Bool → Bool) : Prop :=
  ∃ base : Fin n → Bool, ∀ a b : Bool, F.eval (withPair base i j a b) = op a b

def HasAndProjection {n : Nat} (F : DMFormula n) (i j : Fin n) : Prop :=
  HasProjection F i j (· && ·)

def HasOrProjection {n : Nat} (F : DMFormula n) (i j : Fin n) : Prop :=
  HasProjection F i j (· || ·)

theorem eval_eq_of_agree_on_occurrences {n : Nat} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem ignores_first {n : Nat} (F : DMFormula n) (base : Fin n → Bool) (i j : Fin n)
    (missing : occurrences i F = 0) (a a' b : Bool) :
    F.eval (withPair base i j a b) = F.eval (withPair base i j a' b) := by
  apply eval_eq_of_agree_on_occurrences
  intro k hk
  have different : k ≠ i := by rintro rfl; omega
  simp [withPair, different]

private theorem ignores_second {n : Nat} (F : DMFormula n) (base : Fin n → Bool) (i j : Fin n)
    (missing : occurrences j F = 0) (a b b' : Bool) :
    F.eval (withPair base i j a b) = F.eval (withPair base i j a b') := by
  apply eval_eq_of_agree_on_occurrences
  intro k hk
  have different : k ≠ j := by rintro rfl; omega
  simp [withPair, different]

private def gateValue (isAnd a b : Bool) : Bool :=
  if isAnd then a && b else a || b

private theorem gateValue_comm (isAnd a b : Bool) :
    gateValue isAnd a b = gateValue isAnd b a := by
  cases isAnd <;> simp [gateValue, Bool.and_comm, Bool.or_comm]

private theorem and_true_parts (a b : Bool) (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem or_false_parts (a b : Bool) (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

private theorem projection_to_left {n : Nat} (F L R : DMFormula n) (isAnd : Bool) (i j : Fin n)
    (evaluates : ∀ x, F.eval x = gateValue isAnd (L.eval x) (R.eval x))
    (hi : occurrences i R = 0) (hj : occurrences j R = 0)
    (op : Bool → Bool → Bool) (lowValue : op false false = false) (highValue : op true true = true)
    (projects : HasProjection F i j op) : HasProjection L i j op := by
  obtain ⟨base, truth⟩ := projects
  have fixed (a b c d : Bool) :
      R.eval (withPair base i j a b) = R.eval (withPair base i j c d) :=
    (ignores_first R base i j hi a c b).trans (ignores_second R base i j hj c b d)
  refine ⟨base, ?_⟩
  intro a b
  cases isAnd
  · have low := truth false false
    rw [evaluates, lowValue] at low
    have neutral := (or_false_parts _ _ (by simpa [gateValue] using low)).2
    simpa [evaluates, gateValue, fixed a b false false, neutral] using truth a b
  · have high := truth true true
    rw [evaluates, highValue] at high
    have neutral := (and_true_parts _ _ (by simpa [gateValue] using high)).2
    simpa [evaluates, gateValue, fixed a b true true, neutral] using truth a b

private theorem no_cross_opposite {n : Nat} (F L R : DMFormula n) (isAnd : Bool) (i j : Fin n)
    (evaluates : ∀ x, F.eval x = gateValue isAnd (L.eval x) (R.eval x))
    (leftMissing : occurrences j L = 0) (rightMissing : occurrences i R = 0)
    (projects : HasProjection F i j (gateValue (!isAnd))) : False := by
  obtain ⟨base, truth⟩ := projects
  cases isAnd
  · have off10 : (L.eval (withPair base i j true false) || R.eval (withPair base i j true false)) = false := by
      simpa [evaluates, gateValue] using truth true false
    have off01 : (L.eval (withPair base i j false true) || R.eval (withPair base i j false true)) = false := by
      simpa [evaluates, gateValue] using truth false true
    have offL := (or_false_parts _ _ off10).1
    have offR := (or_false_parts _ _ off01).2
    have on11 : (L.eval (withPair base i j true true) || R.eval (withPair base i j true true)) = true := by
      simpa [evaluates, gateValue] using truth true true
    rw [ignores_second L base i j leftMissing true true false,
      ignores_first R base i j rightMissing true false true, offL, offR] at on11
    cases on11
  · have on01 : (L.eval (withPair base i j false true) && R.eval (withPair base i j false true)) = true := by
      simpa [evaluates, gateValue] using truth false true
    have on10 : (L.eval (withPair base i j true false) && R.eval (withPair base i j true false)) = true := by
      simpa [evaluates, gateValue] using truth true false
    have onL := (and_true_parts _ _ on01).1
    have onR := (and_true_parts _ _ on10).2
    have off00 : (L.eval (withPair base i j false false) && R.eval (withPair base i j false false)) = false := by
      simpa [evaluates, gateValue] using truth false false
    rw [ignores_second L base i j leftMissing false false true,
      ignores_first R base i j rightMissing false true false, onL, onR] at off00
    cases off00

private theorem both_projections_to_left {n : Nat} (F L R : DMFormula n) (isAnd : Bool) (i j : Fin n)
    (evaluates : ∀ x, F.eval x = gateValue isAnd (L.eval x) (R.eval x))
    (hi : occurrences i R = 0) (hj : occurrences j R = 0)
    (h : HasAndProjection F i j ∧ HasOrProjection F i j) :
    HasAndProjection L i j ∧ HasOrProjection L i j :=
  ⟨projection_to_left F L R isAnd i j evaluates hi hj (· && ·) rfl rfl h.1,
   projection_to_left F L R isAnd i j evaluates hi hj (· || ·) rfl rfl h.2⟩

private theorem opposite_projection {n : Nat} (F : DMFormula n) (i j : Fin n) (isAnd : Bool)
    (h : HasAndProjection F i j ∧ HasOrProjection F i j) :
    HasProjection F i j (gateValue (!isAnd)) := by
  cases isAnd
  · exact h.1
  · exact h.2

private theorem split_one {a b : Nat} (h : a + b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega

private theorem combine_no_both {n : Nat} (F L R : DMFormula n) (isAnd : Bool) (i j : Fin n)
    (evaluates : ∀ x, F.eval x = gateValue isAnd (L.eval x) (R.eval x))
    (counts : ∀ k, occurrences k F = occurrences k L + occurrences k R)
    (leftIH : occurrences i L = 1 → occurrences j L = 1 → ¬ (HasAndProjection L i j ∧ HasOrProjection L i j))
    (rightIH : occurrences i R = 1 → occurrences j R = 1 → ¬ (HasAndProjection R i j ∧ HasOrProjection R i j))
    (hi : occurrences i F = 1) (hj : occurrences j F = 1) :
    ¬ (HasAndProjection F i j ∧ HasOrProjection F i j) := by
  intro h
  have swapped (x : Fin n → Bool) : F.eval x = gateValue isAnd (R.eval x) (L.eval x) :=
    (evaluates x).trans (gateValue_comm _ _ _)
  rcases split_one ((counts i).symm.trans hi) with ⟨li, ri⟩ | ⟨li, ri⟩ <;>
    rcases split_one ((counts j).symm.trans hj) with ⟨lj, rj⟩ | ⟨lj, rj⟩
  · exact leftIH li lj (both_projections_to_left F L R isAnd i j evaluates ri rj h)
  · exact no_cross_opposite F L R isAnd i j evaluates lj ri (opposite_projection F i j isAnd h)
  · exact no_cross_opposite F R L isAnd i j swapped rj li (opposite_projection F i j isAnd h)
  · exact rightIH ri rj (both_projections_to_left F R L isAnd i j swapped li lj h)

theorem not_and_or_projections_of_single_occurrences {n : Nat} (F : DMFormula n) (i j : Fin n)
    (different : i ≠ j) : occurrences i F = 1 → occurrences j F = 1 →
    ¬ (HasAndProjection F i j ∧ HasOrProjection F i j) := by
  induction F with
  | lit k polarity =>
    intro hi hj _
    have ki : k = i := by
      by_contra h
      simp [occurrences, h] at hi
    have kj : k = j := by
      by_contra h
      simp [occurrences, h] at hj
    exact different (ki.symm.trans kj)
  | and L R ihL ihR =>
    exact combine_no_both (.and L R) L R true i j (fun _ => rfl) (fun _ => rfl) ihL ihR
  | or L R ihL ihR =>
    exact combine_no_both (.or L R) L R false i j (fun _ => rfl) (fun _ => rfl) ihL ihR

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.DMFixedPair

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPairLower

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula (occurrences)
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.DMFixedPair (withPair)
open scoped BigOperators

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
    (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
    (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def contains (m : Nat) (i : Fin 9) : Bool := m.testBit i.val

private def matchings : List Nat := [273, 161, 266, 98, 140, 84]

private def firstMatch (p : Nat → Bool) : Nat := (matchings.find? p).getD 0

def compatible (i j : Fin 9) : Bool :=
  !(i.val / 3 == j.val / 3) && !(i.val % 3 == j.val % 3)

def andBase (i j : Fin 9) : Fin 9 → Bool :=
  contains (firstMatch fun m => contains m i && contains m j)

def orBase (i j : Fin 9) : Fin 9 → Bool :=
  contains (Nat.lor
    (firstMatch fun m => contains m i && !contains m j)
    (firstMatch fun m => contains m j && !contains m i))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem matching_pair_projections :
    ∀ i j : Fin 9, compatible i j = true →
      (∀ a b : Bool, matching (withPair (andBase i j) i j a b) = (a && b)) ∧
      (∀ a b : Bool, matching (withPair (orBase i j) i j a b) = (a || b)) := by
  decide +kernel

private def singleInput (i : Fin 9) (v : Bool) : Fin 9 → Bool :=
  fun k => if k = i then v else contains (firstMatch fun m => contains m i) k

set_option maxRecDepth 12000 in
private theorem matching_single_projection :
    ∀ i : Fin 9, matching (singleInput i false) = false ∧
      matching (singleInput i true) = true := by
  decide +kernel

theorem every_raw_occurs (F : DMFormula 9) (computes : ∀ x, F.eval x = matching x)
    (i : Fin 9) : 0 < occurrences i F := by
  by_contra! absent
  have same : F.eval (singleInput i false) = F.eval (singleInput i true) := by
    apply DMFixedPair.eval_eq_of_agree_on_occurrences
    intro k present
    have different : k ≠ i := by
      rintro rfl
      omega
    simp [singleInput, different]
  simp only [computes, (matching_single_projection i).1, (matching_single_projection i).2,
    Bool.false_eq_true] at same

theorem matching_compatible_pair_requires_repeat (F : DMFormula 9)
    (computes : ∀ x, F.eval x = matching x) (i j : Fin 9)
    (pair : compatible i j = true)
    (onceI : occurrences i F ≤ 1) (onceJ : occurrences j F ≤ 1) : False := by
  have different : i ≠ j := by
    rintro rfl
    simp [compatible] at pair
  have projections := matching_pair_projections i j pair
  have presentI := every_raw_occurs F computes i
  have presentJ := every_raw_occurs F computes j
  exact DMFixedPair.not_and_or_projections_of_single_occurrences F i j different
    (by omega) (by omega)
    ⟨⟨andBase i j, fun a b => (computes _).trans (projections.1 a b)⟩,
      ⟨orBase i j, fun a b => (computes _).trans (projections.2 a b)⟩⟩

private theorem matching_triple_occurrences (F : DMFormula 9)
    (computes : ∀ x, F.eval x = matching x) (i j k : Fin 9)
    (ij : compatible i j = true) (ik : compatible i k = true)
    (jk : compatible j k = true) :
    5 ≤ occurrences i F + occurrences j F + occurrences k F := by
  have presentI := every_raw_occurs F computes i
  have presentJ := every_raw_occurs F computes j
  have presentK := every_raw_occurs F computes k
  have pair := matching_compatible_pair_requires_repeat F computes
  have repeatIJ : ¬ (occurrences i F ≤ 1 ∧ occurrences j F ≤ 1) :=
    fun h => pair i j ij h.1 h.2
  have repeatIK : ¬ (occurrences i F ≤ 1 ∧ occurrences k F ≤ 1) :=
    fun h => pair i k ik h.1 h.2
  have repeatJK : ¬ (occurrences j F ≤ 1 ∧ occurrences k F ≤ 1) :=
    fun h => pair j k jk h.1 h.2
  omega

theorem matching_formula_leaves_ge_fifteen (F : DMFormula 9)
    (computes : ∀ x, F.eval x = matching x) : 15 ≤ F.leaves := by
  have g := matching_triple_occurrences F computes
  have p0 := g 0 4 8 (by decide) (by decide) (by decide)
  have p1 := g 1 5 6 (by decide) (by decide) (by decide)
  have p2 := g 2 3 7 (by decide) (by decide) (by decide)
  have total := ClosedWalkCount.occurrence_sum_eq_leaves F
  simp [Fin.sum_univ_succ] at total
  change occurrences 0 F + (occurrences 1 F + (occurrences 2 F +
    (occurrences 3 F + (occurrences 4 F + (occurrences 5 F +
      (occurrences 6 F + (occurrences 7 F + occurrences 8 F))))))) = F.leaves at total
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPairLower

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPairLower

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.DMFixedPair (withPair)

private theorem complement_occurrences {n : Nat} (f : DMFormula n) (i : Fin n) :
    occurrences i (complement f) = occurrences i f := by
  induction f with
  | lit k s => rfl
  | and p q hp hq | or p q hp hq => simp [complement, occurrences, hp, hq]

private theorem withPair_agrees_except (base : Fin 9 → Bool) (i j : Fin 9)
    (a b c d : Bool) (k : Fin 9) (ki : k ≠ i) (kj : k ≠ j) :
    withPair base i j a b k = withPair base i j c d k := by
  simp [withPair, ki, kj]

private theorem directed_values :
    ∀ s low high : Bool, Orient s low high → low ≠ high →
      low = !s ∧ high = s := by
  decide

private theorem binary_readout :
    ∀ s v p : Bool, (v = !s → p = false) → (v = s → p = true) →
      v = (if s then p else !p) := by
  decide

theorem compatible_pair_no_single_bit_with_once_inputs (F : DMFormula 9) (i j : Fin 9)
    (compat : compatible i j = true)
    (isolate : ∀ x y : Fin 9 → Bool,
      (∀ k, k ≠ i → k ≠ j → x k = y k) → F.eval x = F.eval y →
      matching x = matching y)
    (readI : occurrences i F ≤ 1) (readJ : occurrences j F ≤ 1) : False := by
  have distinct : i ≠ j := by rintro rfl; simp [compatible] at compat
  obtain ⟨direction, oriented⟩ := formulaUnate i F readI
  let positive := if direction then F else complement F
  have selected (base : Fin 9 → Bool) (op : Bool → Bool → Bool)
      (proj : ∀ a b : Bool, matching (withPair base i j a b) = op a b)
      (e : Bool) (lo : op false e = false) (hi : op true e = true) (a b : Bool) :
      positive.eval (withPair base i j a b) = op a b := by
    let lower := withPair base i j false e
    let upper := withPair base i j true e
    let probe := withPair base i j a b
    have differs : F.eval lower ≠ F.eval upper := by
      intro same
      have result := isolate lower upper (withPair_agrees_except base i j false e true e) same
      rw [proj, proj, lo, hi] at result
      contradiction
    have directionLowHigh : Orient direction (F.eval lower) (F.eval upper) := by
      apply oriented lower upper
      · intro k hk
        simp [lower, upper, withPair, hk]
      · simp [lower, withPair]
      · simp [upper, withPair]
    obtain ⟨directionLow, directionHigh⟩ := directed_values direction _ _ directionLowHigh differs
    have lowerResult : F.eval probe = !direction → op a b = false := by
      intro p
      have result := isolate probe lower (withPair_agrees_except base i j a b false e)
        (p.trans directionLow.symm)
      rw [proj, proj, lo] at result
      exact result
    have upperResult : F.eval probe = direction → op a b = true := by
      intro p
      have result := isolate probe upper (withPair_agrees_except base i j a b true e)
        (p.trans directionHigh.symm)
      rw [proj, proj, hi] at result
      exact result
    have value := binary_readout direction _ _ lowerResult upperResult
    cases hd : direction <;> simp [positive, hd, complement_eval, value, probe] at *
  have countPos (k : Fin 9) : occurrences k positive = occurrences k F := by
    cases hd : direction <;> simp [positive, hd, complement_occurrences]
  obtain ⟨pAnd, pOr⟩ := matching_pair_projections i j compat
  have andProj := selected (andBase i j) (· && ·) pAnd true rfl rfl
  have orProj := selected (orBase i j) (· || ·) pOr false rfl rfl
  have readPosI : 0 < occurrences i positive := by
    by_contra! absent
    have same : positive.eval (withPair (andBase i j) i j false true) =
        positive.eval (withPair (andBase i j) i j true true) := by
      apply DMFixedPair.eval_eq_of_agree_on_occurrences
      intro k hk
      have ne : k ≠ i := by rintro rfl; omega
      simp [withPair, ne]
    simp only [andProj, Bool.false_and, Bool.true_and, Bool.false_eq_true] at same
  have readPosJ : 0 < occurrences j positive := by
    by_contra! absent
    have same : positive.eval (withPair (andBase i j) i j true false) =
        positive.eval (withPair (andBase i j) i j true true) := by
      apply DMFixedPair.eval_eq_of_agree_on_occurrences
      intro k hk
      have ne : k ≠ j := by rintro rfl; omega
      simp [withPair, ne]
    simp only [andProj, Bool.true_and, Bool.false_eq_true] at same
  have countI := countPos i
  have countJ := countPos j
  exact DMFixedPair.not_and_or_projections_of_single_occurrences positive i j distinct
    (by omega) (by omega) ⟨⟨andBase i j, andProj⟩, ⟨orBase i j, orProj⟩⟩

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPairLower

namespace PEqualNP.Outside.L_meta_55847_aux.Deg3
open PEqualNP.CircuitLowerBounds

section Prune

variable {α : Type}

def d3r1Fold (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [Φ g.op (g.inputs.map fun i => w.getD i δ)]) init

theorem d3r1Fold_snoc (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    d3r1Fold δ Φ (gs ++ [g]) init = d3r1Fold δ Φ gs init ++
      [Φ g.op (g.inputs.map fun i => (d3r1Fold δ Φ gs init).getD i δ)] := by
  simp only [d3r1Fold, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem d3r1Fold_length (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    (d3r1Fold δ Φ gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih => rw [d3r1Fold_snoc]; simp [ih]; omega

theorem d3r1Fold_lt (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : i < init.length) : (d3r1Fold δ Φ gs init).getD i δ = init.getD i δ := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih =>
    rw [d3r1Fold_snoc, List.getD_append _ _ _ _ (by rw [d3r1Fold_length]; omega), ih]

theorem d3r1Fold_ge (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : init.length + gs.length ≤ i) : (d3r1Fold δ Φ gs init).getD i δ = δ := by
  rw [List.getD_eq_default _ _ (by rw [d3r1Fold_length]; exact h)]

theorem d3r1Fold_gate (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    ∀ (j : ℕ) (hj : j < gs.length), (d3r1Fold δ Φ gs init).getD (init.length + j) δ =
      Φ gs[j].op (gs[j].inputs.map fun i =>
        if i < init.length + j then (d3r1Fold δ Φ gs init).getD i δ else δ) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hl := d3r1Fold_length δ Φ gs init
    rw [d3r1Fold_snoc]
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ (by omega), ih j hjl]
      simp only [List.getElem_append_left hjl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + j
      · rw [if_pos hi, if_pos hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, if_false]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getElem_append_right (Nat.le_refl _), hl, Nat.sub_self,
        List.getD_cons_zero, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + gs.length
      · rw [if_pos hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, if_false]
        rw [List.getD_eq_default _ _ (by omega)]

end Prune

def d3r1Rank (κ : ℕ → Bool) (t : ℕ) : ℕ := ((List.range t).filter κ).length

theorem d3r1_range_split (κ : ℕ → Bool) (s t : ℕ) (h : s ≤ t) :
    (List.range t).filter κ = (List.range s).filter κ ++ (List.range' s (t - s)).filter κ := by
  rw [← List.filter_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range']
  have := @List.range'_append_1 0 s (t - s)
  simp only [Nat.zero_add] at this
  rw [this]
  congr 1
  omega

theorem d3r1_rank_lt (κ : ℕ → Bool) (s t : ℕ) (hst : s < t) (hs : κ s = true) :
    d3r1Rank κ s < d3r1Rank κ t := by
  unfold d3r1Rank
  rw [d3r1_range_split κ s t hst.le, List.length_append]
  obtain ⟨m, hm⟩ : ∃ m, t - s = m + 1 := ⟨t - s - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hs]
  simp

theorem d3r1_L_get (κ : ℕ → Bool) (len t : ℕ) (ht : t < len) (hk : κ t = true) :
    ((List.range len).filter κ)[d3r1Rank κ t]? = some t := by
  rw [d3r1_range_split κ t len ht.le]
  unfold d3r1Rank
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, len - t = m + 1 := ⟨len - t - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hk]
  simp

theorem d3r1_L_back (κ : ℕ → Bool) (len r : ℕ) (hr : r < ((List.range len).filter κ).length) :
    κ ((List.range len).filter κ)[r] = true ∧ ((List.range len).filter κ)[r] < len ∧
      d3r1Rank κ ((List.range len).filter κ)[r] = r := by
  have hm : ((List.range len).filter κ)[r] ∈ (List.range len).filter κ := List.getElem_mem hr
  have hm2 := List.mem_filter.mp hm
  have hlt := List.mem_range.mp hm2.1
  refine ⟨hm2.2, hlt, ?_⟩
  have hg := d3r1_L_get κ len _ hlt hm2.2
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  have hnd : ((List.range len).filter κ).Nodup := (List.nodup_range).filter _
  exact (hnd.getElem_inj_iff).mp he

def d3r1New (n : ℕ) (κ : ℕ → Bool) (top u : ℕ) : ℕ :=
  if u < n then u else if κ (u - n) then n + d3r1Rank κ (u - n) else n + top

def d3r1Top (κ : ℕ → Bool) (gs : List Gate) : ℕ := ((List.range gs.length).filter κ).length

def d3r1PGate (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) : Gate :=
  { op := (gs.getD t ⟨GateOp.and, []⟩).op,
    inputs := (gs.getD t ⟨GateOp.and, []⟩).inputs.map fun a =>
      if a < n + t then d3r1New n κ (d3r1Top κ gs) a else n + d3r1Rank κ t }

def d3r1Pruned (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) : List Gate :=
  ((List.range gs.length).filter κ).map (d3r1PGate n κ gs)

theorem d3r1_pruned_length (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) :
    (d3r1Pruned n κ gs).length = d3r1Top κ gs := by
  simp [d3r1Pruned, d3r1Top]

theorem d3r1_pruned_get (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (hk : κ t = true) : ∃ h : d3r1Rank κ t < (d3r1Pruned n κ gs).length,
      (d3r1Pruned n κ gs)[d3r1Rank κ t] = d3r1PGate n κ gs t := by
  have hg := d3r1_L_get κ gs.length t ht hk
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  refine ⟨by simpa [d3r1Pruned] using hb, ?_⟩
  simp [d3r1Pruned, he]

theorem d3r1_new_lt (n : ℕ) (κ : ℕ → Bool) (top a t : ℕ) (hat : a < n + t)
    (ha : a < n ∨ κ (a - n) = true) : d3r1New n κ top a < n + d3r1Rank κ t := by
  unfold d3r1New
  by_cases han : a < n
  · rw [if_pos han]; omega
  · have hk := ha.resolve_left han
    rw [if_neg han, if_pos hk]
    have := d3r1_rank_lt κ (a - n) t (by omega) hk
    omega

theorem d3r1_prune_val {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true) :
    ∀ u, (u < n ∨ κ (u - n) = true) →
      (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) u) δ =
        (d3r1Fold δ Φ gs init).getD u δ := by
  subst hn
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < init.length
    · simp only [d3r1New, hun, if_true]
      rw [d3r1Fold_lt _ _ _ _ _ hun, d3r1Fold_lt _ _ _ _ _ hun]
    · have hk : κ (u - init.length) = true := hu.resolve_left hun
      obtain ⟨t, rfl⟩ : ∃ t, u = init.length + t := ⟨u - init.length, by omega⟩
      simp only [Nat.add_sub_cancel_left] at hk
      have ht := hκ t hk
      have hnew : d3r1New init.length κ (d3r1Top κ gs) (init.length + t) =
          init.length + d3r1Rank κ t := by
        simp [d3r1New, hk]
      obtain ⟨hb, hpr⟩ := d3r1_pruned_get init.length κ gs t ht hk
      rw [hnew, d3r1Fold_gate _ _ _ _ _ hb, d3r1Fold_gate _ _ _ _ t ht, hpr]
      have hg : gs.getD t ⟨GateOp.and, []⟩ = gs[t] := List.getD_eq_getElem _ _ ht
      simp only [d3r1PGate, hg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      simp only [Function.comp]
      by_cases hat : a < init.length + t
      · have hA : a < init.length ∨ κ (a - init.length) = true := by
          by_cases han : a < init.length
          · exact Or.inl han
          · exact Or.inr (hcl t ht hk a ha (by omega) hat)
        rw [if_pos hat, if_pos (d3r1_new_lt _ _ _ a t hat hA), if_pos hat]
        exact ih a hat hA
      · simp only [hat, if_false, lt_irrefl]

theorem d3r1_prune_out {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool) (o : ℕ)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true)
    (ho : n ≤ o → o < n + gs.length → κ (o - n) = true) :
    (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) o) δ =
      (d3r1Fold δ Φ gs init).getD o δ := by
  by_cases hA : o < n ∨ κ (o - n) = true
  · exact d3r1_prune_val δ Φ init n hn gs κ hκ hcl o hA
  · have hon : n ≤ o := by omega
    have hk : κ (o - n) = false := by simpa using (fun h => hA (Or.inr h))
    have hol : n + gs.length ≤ o := by
      by_contra h
      rw [ho hon (by omega)] at hk
      exact Bool.noConfusion hk
    have hnew : d3r1New n κ (d3r1Top κ gs) o = n + d3r1Top κ gs := by
      simp [d3r1New, hk, show ¬ o < n by omega]
    rw [hnew, d3r1Fold_ge _ _ _ _ _ (by rw [hn, d3r1_pruned_length]),
      d3r1Fold_ge _ _ _ _ _ (by omega)]

def d3r1R (gs : List Gate) (n : ℕ) : ℕ → ℕ → Prop := fun a1 b1 =>
  a1 < b1 ∧ ∃ i1 : Fin gs.length, b1 = n + i1.val ∧ a1 ∈ (gs.get i1).inputs

theorem d3r1_prune_reach (n : ℕ) (gs : List Gate) (o : ℕ) (κ : ℕ → Bool)
    (hiff : ∀ t, κ t = true ↔ t < gs.length ∧ Relation.ReflTransGen (d3r1R gs n) (n + t) o) :
    ∀ c, Relation.ReflTransGen (d3r1R gs n) c o →
      Relation.ReflTransGen (d3r1R (d3r1Pruned n κ gs) n) (d3r1New n κ (d3r1Top κ gs) c)
        (d3r1New n κ (d3r1Top κ gs) o) := by
  intro c hc
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head c d hcd hdo ih =>
    obtain ⟨hlt, i1, hd, hmem⟩ := hcd
    subst hd
    have hk : κ i1 = true := (hiff i1).mpr ⟨i1.2, hdo⟩
    have hnew : d3r1New n κ (d3r1Top κ gs) (n + i1.val) = n + d3r1Rank κ i1 := by
      simp [d3r1New, hk]
    obtain ⟨hb, hpr⟩ := d3r1_pruned_get n κ gs i1 i1.2 hk
    have hA : c < n ∨ κ (c - n) = true := by
      by_cases hcn : c < n
      · exact Or.inl hcn
      · right
        apply (hiff _).mpr
        refine ⟨by omega, ?_⟩
        rw [show n + (c - n) = c by omega]
        exact Relation.ReflTransGen.head ⟨hlt, i1, rfl, hmem⟩ hdo
    refine Relation.ReflTransGen.head ⟨?_, ⟨d3r1Rank κ i1, hb⟩, hnew, ?_⟩ ih
    · rw [hnew]; exact d3r1_new_lt n κ _ c i1 hlt hA
    · simp only [List.get_eq_getElem, hpr, d3r1PGate]
      rw [List.getD_eq_getElem _ _ i1.2]
      exact List.mem_map.mpr ⟨c, by simpa using hmem, if_pos hlt⟩

theorem d3r1_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = d3r1Fold false GateOp.eval C.gates x := rfl

end PEqualNP.Outside.L_meta_55847_aux.Deg3

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus

open PEqualNP.CircuitLowerBounds

def operandReads (gates : List Gate) : List Nat :=
  gates.flatMap Gate.inputs

def isNot (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

def nonNotCount (gates : List Gate) : Nat :=
  (gates.filter fun g => !(isNot g.op)).length

def usedRawCount (n : Nat) (gates : List Gate) : Nat :=
  ((operandReads gates).toFinset.filter fun w => w < n).card

def excessReads (gates : List Gate) : Nat :=
  (operandReads gates).length - (operandReads gates).toFinset.card

private theorem operandReads_length (gates : List Gate)
    (arity : ∀ g ∈ gates, g.inputs.length = if isNot g.op then 1 else 2) :
    (operandReads gates).length = gates.length + nonNotCount gates := by
  induction gates with
  | nil => simp [operandReads, nonNotCount]
  | cons g tail ih =>
    have hg := arity g (by simp)
    have ht : ∀ a ∈ tail, a.inputs.length = if isNot a.op then 1 else 2 := by
      intro a ha
      exact arity a (by simp [ha])
    have hlen := ih ht
    simp only [operandReads, List.flatMap_cons, List.length_append] at hlen ⊢
    cases hop : g.op <;>
      simp [nonNotCount, isNot, hop] at hg hlen ⊢ <;> omega

theorem excessReads_add_usedRawCount (n : Nat) (C : Circuit)
    (nonempty : C.gates ≠ [])
    (lastOutput : C.output = n + C.gates.length - 1)
    (arity : ∀ g ∈ C.gates, g.inputs.length = if isNot g.op then 1 else 2)
    (backward : ∀ (j : Fin C.gates.length) (w : Nat),
      w ∈ (C.gates.get j).inputs → w < n + j.val)
    (readEarlier : ∀ w : Nat, n ≤ w → w < C.output → w ∈ operandReads C.gates) :
    excessReads C.gates + usedRawCount n C.gates = nonNotCount C.gates + 1 := by
  let reads := (operandReads C.gates).toFinset
  have belowOutput : ∀ w ∈ operandReads C.gates, w < C.output := by
    intro w hw
    rcases List.mem_flatMap.mp hw with ⟨g, hg, hread⟩
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    have hj := backward j w hread
    have hslot := j.isLt
    omega
  have hInterval : reads.filter (fun w => ¬ w < n) = Finset.Ico n C.output := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨hw, hn⟩
      have hm : w ∈ operandReads C.gates := by simpa [reads] using hw
      exact ⟨by omega, belowOutput w hm⟩
    · rintro ⟨hn, ho⟩
      exact ⟨by simpa [reads] using readEarlier w hn ho, by omega⟩
  have hSplit := Finset.card_filter_add_card_filter_not (s := reads) (fun w => w < n)
  rw [hInterval, Nat.card_Ico] at hSplit
  have hLen := operandReads_length C.gates arity
  have hCard : reads.card ≤ (operandReads C.gates).length := List.toFinset_card_le _
  have hPositive : 0 < C.gates.length := List.length_pos_iff.mpr nonempty
  change (operandReads C.gates).length - reads.card +
    (reads.filter fun w => w < n).card = nonNotCount C.gates + 1
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_55847_aux.Deg3
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus

def liveBank (C : Circuit) (n j : Nat) : Finset Nat :=
  (Finset.range (n + j)).filter fun w => w = C.output ∨ w ∈ operandReads (C.gates.drop j)

@[simp] theorem mem_liveBank {C : Circuit} {n j w : Nat} :
    w ∈ liveBank C n j ↔ w < n + j ∧
      (w = C.output ∨ w ∈ operandReads (C.gates.drop j)) := by
  simp [liveBank]

theorem liveBank_start (C : Circuit) (n : Nat)
    (raw : ∀ i : Fin n, i.val ∈ operandReads C.gates) :
    liveBank C n 0 = Finset.range n := by
  ext w
  simp only [mem_liveBank, Nat.add_zero, List.drop_zero, Finset.mem_range]
  exact ⟨And.left, fun h => ⟨h, Or.inr (raw ⟨w, h⟩)⟩⟩

theorem liveBank_end (C : Circuit) (n : Nat) (valid : C.output < n + C.gates.length) :
    liveBank C n C.gates.length = {C.output} := by
  ext w
  simp only [mem_liveBank, List.drop_length, operandReads, List.flatMap_nil,
    List.not_mem_nil, or_false, Finset.mem_singleton]
  exact ⟨And.right, fun h => ⟨h ▸ valid, h⟩⟩

private theorem suffix_reads_cons (C : Circuit) (j : Fin C.gates.length) :
    operandReads (C.gates.drop j.val) =
      (C.gates.get j).inputs ++ operandReads (C.gates.drop (j.val + 1)) := by
  unfold operandReads
  rw [List.drop_eq_getElem_cons j.isLt, List.flatMap_cons]
  rfl

theorem liveBank_operand (C : Circuit) (n : Nat) (j : Fin C.gates.length)
    (backward : ∀ w ∈ (C.gates.get j).inputs, w < n + j.val)
    {w : Nat} (reads : w ∈ (C.gates.get j).inputs) : w ∈ liveBank C n j.val := by
  apply mem_liveBank.mpr
  refine ⟨backward w reads, Or.inr ?_⟩
  rw [suffix_reads_cons C j, List.mem_append]
  exact Or.inl reads

private theorem first_reader {n : Nat} {gs : List Gate} {w o : Nat}
    (path : Relation.ReflTransGen (d3r1R gs n) w o) :
    w = o ∨ ∃ k : Fin gs.length, w < n + k.val ∧ w ∈ (gs.get k).inputs := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | head edge _ _ =>
    obtain ⟨earlier, k, rfl, member⟩ := edge
    exact Or.inr ⟨k, earlier, member⟩

theorem liveBank_new (C : Circuit) (n : Nat) (j : Fin C.gates.length)
    (live : Relation.ReflTransGen (d3r1R C.gates n) (n + j.val) C.output) :
    n + j.val ∈ liveBank C n (j.val + 1) := by
  apply mem_liveBank.mpr
  refine ⟨by omega, ?_⟩
  rcases first_reader live with last | ⟨k, earlier, input⟩
  · exact Or.inl last
  · right
    refine List.mem_flatMap.mpr ⟨C.gates.get k, ?_, input⟩
    apply List.mem_drop_iff_getElem.mpr
    have diff : (j.val + 1) + (k.val - (j.val + 1)) = k.val := by omega
    refine ⟨k.val - (j.val + 1), by have := k.isLt; omega, ?_⟩
    simp [diff]

theorem liveBank_lost (C : Circuit) (n : Nat) (j : Fin C.gates.length) :
    liveBank C n j.val \ liveBank C n (j.val + 1) ⊆ (C.gates.get j).inputs.toFinset := by
  intro w hw
  obtain ⟨present, absent⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨before, old⟩ := mem_liveBank.mp present
  have after : w < n + (j.val + 1) := by omega
  have lost : ¬ (w = C.output ∨ w ∈ operandReads (C.gates.drop (j.val + 1))) :=
    fun h => absent (mem_liveBank.mpr ⟨after, h⟩)
  have oldRead := old.resolve_left (fun h => lost (Or.inl h))
  rw [suffix_reads_cons C j, List.mem_append] at oldRead
  exact List.mem_toFinset.mpr (oldRead.resolve_right (fun h => lost (Or.inr h)))

theorem liveBank_next_subset (C : Circuit) (n : Nat) (j : Fin C.gates.length) :
    liveBank C n (j.val + 1) ⊆ insert (n + j.val) (liveBank C n j.val) := by
  intro w here
  obtain ⟨before, next⟩ := mem_liveBank.mp here
  by_cases new : w = n + j.val
  · exact Finset.mem_insert.mpr (Or.inl new)
  · apply Finset.mem_insert.mpr
    right
    apply mem_liveBank.mpr
    refine ⟨by omega, ?_⟩
    rcases next with output | read
    · exact Or.inl output
    · right
      rw [suffix_reads_cons C j, List.mem_append]
      exact Or.inr read

theorem liveBank_exact_card (C : Circuit) (n : Nat) (j : Fin C.gates.length)
    (live : Relation.ReflTransGen (d3r1R C.gates n) (n + j.val) C.output) :
    (liveBank C n j.val).card + 1 =
      (liveBank C n (j.val + 1)).card +
        (liveBank C n j.val \ liveBank C n (j.val + 1)).card := by
  let old := liveBank C n j.val
  let new := liveBank C n (j.val + 1)
  have present : n + j.val ∈ new := liveBank_new C n j live
  have absent : n + j.val ∉ old :=
    fun h => (Nat.lt_irrefl (n + j.val)) (mem_liveBank.mp h).1
  have eq : new = insert (n + j.val) (old ∩ new) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_inter]
    constructor
    · intro h
      rcases Finset.mem_insert.mp (liveBank_next_subset C n j h) with fresh | earlier
      · exact Or.inl fresh
      · exact Or.inr ⟨earlier, h⟩
    · rintro (rfl | ⟨_, h⟩)
      · exact present
      · exact h
  have fresh : n + j.val ∉ old ∩ new := fun h => absent (Finset.mem_inter.mp h).1
  have cardNext : new.card = (old ∩ new).card + 1 :=
    (congrArg Finset.card eq).trans (Finset.card_insert_of_notMem fresh)
  have cardOld := Finset.card_sdiff_add_card_inter old new
  change old.card + 1 = new.card + (old \ new).card
  omega

theorem liveBank_shrink_bound (C : Circuit) (n : Nat) (j : Fin C.gates.length)
    (live : Relation.ReflTransGen (d3r1R C.gates n) (n + j.val) C.output) :
    (liveBank C n j.val).card + 1 ≤
      (liveBank C n (j.val + 1)).card + (C.gates.get j).inputs.length := by
  have card := liveBank_exact_card C n j live
  have shed := (Finset.card_le_card (liveBank_lost C n j)).trans (List.toFinset_card_le _)
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus

def Essential (n : Nat) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y

private def addWire (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private theorem getD_append_same {xs ys : List Bool} (len : xs.length = ys.length)
    (b : Bool) (w : Nat) (same : xs.getD w false = ys.getD w false) :
    (xs ++ [b]).getD w false = (ys ++ [b]).getD w false := by
  by_cases before : w < xs.length
  · rw [List.getD_append _ _ _ _ before, List.getD_append _ _ _ _ (by omega), same]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), len]

private theorem suffix_agree (gs : List Gate) (out : Nat) (xs ys : List Bool)
    (len : xs.length = ys.length)
    (agree : ∀ w, (w = out ∨ w ∈ operandReads gs) →
      xs.getD w false = ys.getD w false) :
    (gs.foldl addWire xs).getD out false = (gs.foldl addWire ys).getD out false := by
  induction gs generalizing xs ys with
  | nil => exact agree out (Or.inl rfl)
  | cons g rest ih =>
    have readSame :
        g.inputs.map (fun w => xs.getD w false) = g.inputs.map (fun w => ys.getD w false) := by
      apply List.map_congr_left
      intro w hw
      exact agree w (Or.inr (by simp [operandReads, hw]))
    simp only [List.foldl_cons, addWire]
    rw [← readSame]
    apply ih _ _ (by simp [len])
    intro w h
    have same := agree w (h.imp_right (by
      intro h
      change w ∈ g.inputs ++ operandReads rest
      exact List.mem_append.mpr (Or.inr h)))
    exact getD_append_same len _ w same

theorem eval_agree_on_reads (C : Circuit) (xs ys : List Bool)
    (len : xs.length = ys.length)
    (agree : ∀ w, (w = C.output ∨ w ∈ operandReads C.gates) →
      xs.getD w false = ys.getD w false) :
    C.eval xs = C.eval ys :=
  suffix_agree C.gates C.output xs ys len agree

private theorem getD_ofFn_agree_except {n : Nat} {x y : Fin n → Bool} {i : Fin n}
    (agree : ∀ j, j ≠ i → x j = y j) {w : Nat} (different : w ≠ i.val) :
    (List.ofFn x).getD w false = (List.ofFn y).getD w false := by
  by_cases inside : w < n
  · rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa)]
    simp only [List.getElem_ofFn]
    exact agree ⟨w, inside⟩ (fun h => different (congrArg Fin.val h))
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt inside),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt inside)]

theorem raw_live_of_essential (C : Circuit) (n : Nat) (f : (Fin n → Bool) → Bool)
    (essential : Essential n f) (evaluates : ∀ x, C.eval (List.ofFn x) = f x)
    (i : Fin n) : i.val = C.output ∨ i.val ∈ operandReads C.gates := by
  by_contra absent
  obtain ⟨x, y, agree, different⟩ := essential i
  apply different
  rw [← evaluates x, ← evaluates y]
  apply eval_agree_on_reads C _ _ (by simp)
  intro w used
  exact getD_ofFn_agree_except agree (fun eq => absent (eq ▸ used))

theorem liveBank_start_of_essential (C : Circuit) (n : Nat) (f : (Fin n → Bool) → Bool)
    (essential : Essential n f) (evaluates : ∀ x, C.eval (List.ofFn x) = f x) :
    liveBank C n 0 = Finset.range n := by
  ext w
  simp only [mem_liveBank, Nat.add_zero, List.drop_zero, Finset.mem_range]
  exact ⟨And.left, fun h => ⟨h, raw_live_of_essential C n f essential evaluates ⟨w, h⟩⟩⟩

private theorem fold_getD_of_raw (gs : List Gate) (xs : List Bool) (w : Nat)
    (inside : w < xs.length) : (gs.foldl addWire xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons, addWire]
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ inside]

theorem eval_eq_raw {C : Circuit} {xs : List Bool} (inside : C.output < xs.length) :
    C.eval xs = xs.getD C.output false :=
  fold_getD_of_raw C.gates xs C.output inside

theorem output_not_raw_of_essential (C : Circuit) (n : Nat) (two : 2 ≤ n)
    (f : (Fin n → Bool) → Bool) (essential : Essential n f)
    (evaluates : ∀ x, C.eval (List.ofFn x) = f x) : n ≤ C.output := by
  by_contra outside
  have inside : C.output < n := Nat.lt_of_not_ge outside
  obtain ⟨i, alternate⟩ : ∃ i : Fin n, i.val ≠ C.output := by
    by_cases zero : C.output = 0
    · exact ⟨⟨1, by omega⟩, by simp [zero]⟩
    · exact ⟨⟨0, by omega⟩, fun eq => zero eq.symm⟩
  obtain ⟨x, y, agree, different⟩ := essential i
  apply different
  rw [← evaluates x, ← evaluates y,
    eval_eq_raw (by simpa using inside), eval_eq_raw (by simpa using inside)]
  exact getD_ofFn_agree_except agree alternate.symm

theorem reads_raw_of_essential (C : Circuit) (n : Nat) (two : 2 ≤ n)
    (f : (Fin n → Bool) → Bool) (essential : Essential n f)
    (evaluates : ∀ x, C.eval (List.ofFn x) = f x) :
    ∀ i : Fin n, i.val ∈ operandReads C.gates := by
  intro i
  have out := output_not_raw_of_essential C n two f essential evaluates
  exact (raw_live_of_essential C n f essential evaluates i).resolve_left (by
    have := i.isLt
    omega)

private theorem fold_length (gs : List Gate) (xs : List Bool) :
    (gs.foldl addWire xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, ih, addWire, List.length_append, List.length_nil,
      List.length_cons]
    omega

theorem wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.gates.length :=
  fold_length C.gates xs

theorem output_valid_of_essential (C : Circuit) (n : Nat) (nonzero : 0 < n)
    (f : (Fin n → Bool) → Bool) (essential : Essential n f)
    (evaluates : ∀ x, C.eval (List.ofFn x) = f x) : C.output < n + C.gates.length := by
  by_contra invalid
  obtain ⟨x, y, _, diff⟩ := essential ⟨0, nonzero⟩
  have empty (z : Fin n → Bool) : C.eval (List.ofFn z) = false := by
    unfold Circuit.eval
    apply List.getD_eq_default
    simpa [wires_length] using Nat.le_of_not_gt invalid
  apply diff
  rw [← evaluates x, ← evaluates y, empty x, empty y]

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstWireReaders

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def reader (i : ℕ) (g : Gate) : Bool := (normGate g).inputs.contains i

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      change (wiresFrom gs (w ++ [_])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ h]

private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h
  simp

private def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def SameOutside (pin : ℕ) (a b : List Bool) : Prop :=
  ∀ i : ℕ, i ≠ pin → a.getD i false = b.getD i false

private theorem inputEq {n : ℕ} (pin : Fin n) (a b : Fin n → Bool) (eq : ∀ i : Fin n, i ≠ pin → a i = b i) :
    SameOutside pin.val (List.ofFn a) (List.ofFn b) := by
  intro i ne
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rw [eq _ (fun h => ne (congrArg Fin.val h))]
  · rfl

private theorem gateEq (pin : ℕ) (g : Gate) (w z : List Bool) (same : SameOutside pin w z)
    (misses : ¬ reader pin g) : gateValue g w = gateValue g z := by
  unfold gateValue
  rw [← normGate_eval g (fun i => w.getD i false), ← normGate_eval g (fun i => z.getD i false)]
  congr 1
  apply List.map_congr_left
  intro i hi
  apply same i
  rintro rfl
  exact misses (by simpa [reader, List.contains_iff_mem] using hi)

private theorem extendSame (pin : ℕ) (w z : List Bool) (v : Bool) (len : w.length = z.length)
    (same : SameOutside pin w z) : SameOutside pin (w ++ [v]) (z ++ [v]) := by
  intro i ne
  by_cases h : i = w.length
  · rw [getD_snoc_len _ _ _ _ h.symm, getD_snoc_len _ _ _ _ (len.symm.trans h.symm)]
  · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by simpa [← len] using h)]
    exact same i ne

private theorem follow (pin : ℕ) (gs : List Gate) (misses : ∀ g ∈ gs, ¬ reader pin g)
    (w z : List Bool) (len : w.length = z.length) (same : SameOutside pin w z) :
    SameOutside pin (wiresFrom gs w) (wiresFrom gs z) := by
  induction gs generalizing w z with
  | nil => exact same
  | cons g gs ih =>
      change SameOutside pin
        (wiresFrom gs (w ++ [gateValue g w])) (wiresFrom gs (z ++ [gateValue g z]))
      rw [gateEq pin g w z same (misses g (by simp))]
      exact ih (fun gate h => misses gate (by simp [h])) _ _ (by simp [len]) (extendSame pin _ _ _ len same)

private theorem headValue {n : ℕ} (C : Circuit) (g : Gate) (gs : List Gate) (gates : C.gates = g :: gs)
    (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD n false = gateValue g (List.ofFn x) := by
  change (wiresFrom C.gates (List.ofFn x)).getD n false = _
  rw [gates]
  change (wiresFrom gs (List.ofFn x ++ [gateValue g (List.ofFn x)])).getD n false = _
  rw [getD_wiresFrom _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]

theorem atLeastTwo {n : ℕ} (pin : Fin n) (C : Circuit)
    (first target : (Fin n → Bool) → Bool)
    (firstValue : ∀ x, (C.wires (List.ofFn x)).getD n false = first x)
    (computes : ∀ x, C.eval (List.ofFn x) = target x)
    (firstChanges : ∃ a b, (∀ i, i ≠ pin → a i = b i) ∧ first a ≠ first b)
    (outputChanges : ∃ a b, (∀ i, i ≠ pin → a i = b i) ∧ first a = first b ∧ target a ≠ target b)
    (notRaw : ∃ x, x pin ≠ target x) :
    2 ≤ C.gates.countP (reader pin.val) := by
  obtain ⟨a, b, agree, diff⟩ := firstChanges
  cases gates : C.gates with
  | nil =>
      have noFirst (x : Fin n → Bool) : first x = false := by
        rw [← firstValue x]
        change (wiresFrom C.gates (List.ofFn x)).getD n false = false
        rw [gates]
        exact List.getD_eq_default _ _ (by simp [wiresFrom])
      exact False.elim (diff ((noFirst a).trans (noFirst b).symm))
  | cons g gs =>
      have values (x : Fin n → Bool) : gateValue g (List.ofFn x) = first x :=
        (headValue C g gs gates x).symm.trans (firstValue x)
      have headRead : reader pin.val g = true := by
        apply Bool.eq_true_of_ne_false
        intro h
        apply diff
        simpa only [values] using gateEq pin.val g _ _ (inputEq pin _ _ agree) (by simp [h])
      have outputNotRaw : C.output ≠ pin.val := by
        intro output
        obtain ⟨w, wrong⟩ := notRaw
        have eval := computes w
        change (wiresFrom C.gates _).getD C.output false = _ at eval
        rw [output, getD_wiresFrom _ _ _ (by simpa using pin.isLt)] at eval
        apply wrong
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, pin.isLt] using eval
      have tailRead : 0 < gs.countP (reader pin.val) := by
        by_contra h
        have zero : gs.countP (reader pin.val) = 0 := by omega
        obtain ⟨s, t, sameRaw, sameFirst, outDiff⟩ := outputChanges
        have sameGate : gateValue g (List.ofFn s) = gateValue g (List.ofFn t) := by
          simpa only [values] using sameFirst
        have sameWires := follow pin.val gs (List.countP_eq_zero.mp zero)
          (List.ofFn s ++ [gateValue g (List.ofFn s)])
          (List.ofFn t ++ [gateValue g (List.ofFn t)])
          (by simp) (by rw [sameGate]; exact extendSame pin.val _ _ _ (by simp) (inputEq pin _ _ sameRaw))
        have outputs : C.eval (List.ofFn s) = C.eval (List.ofFn t) := by
          change (wiresFrom C.gates _).getD _ false = (wiresFrom C.gates _).getD _ false
          rw [gates]
          exact sameWires C.output outputNotRaw
        exact outDiff (by simpa only [computes] using outputs)
      rw [List.countP_cons, headRead]
      change 2 ≤ gs.countP (reader pin.val) + 1
      omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstWireReaders

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPM3

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_55847_aux.Deg3
open SignedNormalization CircuitReadSurplus

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def firstAnd (x : Fin 9 → Bool) : Bool := x 0 && x 1

private def masks : Fin 9 → Nat := ![273, 266, 140, 266, 273, 161, 98, 161, 273]

private def matchPivot (pin : Fin 9) (value : Bool) (i : Fin 9) : Bool :=
  if i = pin then value else (masks pin).testBit i.val

private theorem matchPivot_agree (pin i : Fin 9) (other : i ≠ pin) :
    matchPivot pin false i = matchPivot pin true i := by simp [matchPivot, other]

private theorem matchPivot_changes :
    ∀ pin : Fin 9, matching (matchPivot pin false) ≠ matching (matchPivot pin true) := by
  decide +kernel

theorem matching_essential : Essential 9 matching :=
  fun pin => ⟨matchPivot pin false, matchPivot pin true, matchPivot_agree pin,
    matchPivot_changes pin⟩

private theorem head_and_value (C : Circuit) (head : C.gates.head? = some ⟨.and, [0, 1]⟩)
    (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 9 false = firstAnd x := by
  cases hs : C.gates with
  | nil => simp [hs] at head
  | cons g rest =>
    have same : g = ⟨.and, [0,1]⟩ := by simpa [hs] using head
    subst g
    rw [d3r1_wires_eq, hs]
    change (d3r1Fold false GateOp.eval rest ((List.ofFn x) ++
      [GateOp.and.eval ([(List.ofFn x).getD 0 false, (List.ofFn x).getD 1 false])])).getD 9 false = _
    rw [d3r1Fold_lt _ _ _ _ _ (by simp)]
    simp [List.getD_append_right, List.getD_eq_getElem?_getD, List.getElem?_ofFn, firstAnd, GateOp.eval]

theorem reader_count_le (pin : Nat) (gates : List Gate) :
    gates.countP (FirstWireReaders.reader pin) ≤ (operandReads gates).count pin := by
  induction gates with
  | nil => rfl
  | cons g rest ih =>
    change (g :: rest).countP (FirstWireReaders.reader pin) ≤
      (g.inputs ++ operandReads rest).count pin
    rw [List.countP_cons, List.count_append]
    cases h : FirstWireReaders.reader pin g
    · simp [h]
      omega
    · have read : pin ∈ (FirstWireReaders.normGate g).inputs := by
        simpa [FirstWireReaders.reader] using h
      have readOrig : pin ∈ g.inputs := by
        cases op : g.op <;> simp [FirstWireReaders.normGate, op] at read
        all_goals first | exact read | exact (List.take_sublist _ _).subset read
      have pos : 0 < g.inputs.count pin := List.count_pos_iff.mpr readOrig
      simp [h]
      omega

private def firstPivot (pin other : Fin 9) (value : Bool) (i : Fin 9) : Bool :=
  if i = pin then value else decide (i = other)

private theorem pin_changes_first (pin : Fin 9) (oneOf : pin = 0 ∨ pin = 1) :
    ∃ x y, (∀ i, i ≠ pin → x i = y i) ∧ firstAnd x ≠ firstAnd y := by
  rcases oneOf with rfl | rfl
  · refine ⟨firstPivot 0 1 false, firstPivot 0 1 true, ?_, by decide +kernel⟩
    intro i other
    simp [firstPivot, other]
  · refine ⟨firstPivot 1 0 false, firstPivot 1 0 true, ?_, by decide +kernel⟩
    intro i other
    simp [firstPivot, other]

private theorem fixed_first_and (pin : Fin 9) (oneOf : pin = 0 ∨ pin = 1) :
    firstAnd (matchPivot pin false) = firstAnd (matchPivot pin true) := by
  rcases oneOf with rfl | rfl <;> decide +kernel

theorem reads_first_repeat (C : Circuit)
    (head : C.gates.head? = some ⟨.and, [0, 1]⟩)
    (computes : ∀ x, C.eval (List.ofFn x) = matching x)
    (pin : Fin 9) (oneOf : pin = 0 ∨ pin = 1) :
    2 ≤ (operandReads C.gates).count pin.val := by
  have outChange : ∃ x y, (∀ i, i ≠ pin → x i = y i) ∧
      firstAnd x = firstAnd y ∧ matching x ≠ matching y :=
    ⟨matchPivot pin false, matchPivot pin true, matchPivot_agree pin,
      fixed_first_and pin oneOf, matchPivot_changes pin⟩
  have notRaw : ∃ x, x pin ≠ matching x := by
    refine ⟨fun i => decide (i = pin), ?_⟩
    rcases oneOf with rfl | rfl <;> decide +kernel
  exact (FirstWireReaders.atLeastTwo pin C firstAnd matching (head_and_value C head)
    computes (pin_changes_first pin oneOf) outChange notRaw).trans (reader_count_le _ _)

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPM3

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPM3

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_55847_aux.Helpers
open CircuitReadSurplus SignedNormalization

def StrictGates (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = .not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = .and ∨ (C.gates.get j).op = .or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])

def InternalLive (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
    ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs

def firstGate : Gate := ⟨.and, [0,1]⟩

def secondGate (wire : Nat) : Gate := ⟨.not, [wire]⟩

theorem gates_with_prefix (C : Circuit) (wire : Nat)
    (first : C.gates.head? = some firstGate)
    (second : C.gates.tail.head? = some (secondGate wire)) :
    ∃ rest, C.gates = firstGate :: secondGate wire :: rest := by
  cases hs : C.gates with
  | nil => simp [hs] at first
  | cons g tail =>
    have a : g = firstGate := by simpa [hs] using first
    cases ht : tail with
    | nil => simp [hs, ht] at second
    | cons h rest =>
      have b : h = secondGate wire := by simpa [hs, ht] using second
      exact ⟨rest, by simp [a, b]⟩

theorem clean_of_strict (C : Circuit) (shape : StrictGates C) : CleanL 9 C.gates := by
  intro j g hg
  obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.mp hg
  let index : Fin C.gates.length := ⟨j, hj⟩
  have eq : C.gates.get index = g := e
  have strict := shape index
  change CleanGate (9 + index.val) g
  rw [eq] at strict
  rcases strict with ⟨op, a, ha, args⟩ | ⟨op, a, b, hab, hb, args⟩
  · exact Or.inl ⟨op, a, ha, args⟩
  · exact Or.inr ⟨op, a, b, hab.trans hb, hb, args⟩

theorem reads_prior_gates (C : Circuit) (last : C.output + 1 = 9 + C.size)
    (live : InternalLive C) :
    ∀ wire : Nat, 9 ≤ wire → wire < C.output → wire ∈ operandReads C.gates := by
  intro wire fromRaw beforeOut
  change C.output + 1 = 9 + C.gates.length at last
  let j : Fin C.gates.length := ⟨wire - 9, by omega⟩
  have hj : j.val + 1 < C.gates.length := by
    change wire - 9 + 1 < C.gates.length
    omega
  obtain ⟨k, _, reads⟩ := live j hj
  have same : 9 + j.val = wire := by change 9 + (wire - 9) = wire; omega
  exact List.mem_flatMap.mpr ⟨C.gates.get k, List.get_mem C.gates k, same ▸ reads⟩

theorem reads_matching_raws (C : Circuit)
    (computes : ∀ x, C.eval (List.ofFn x) = matching x) :
    ∀ i : Fin 9, i.val ∈ operandReads C.gates :=
  reads_raw_of_essential C 9 (by decide) matching matching_essential computes

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPM3

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SharedReadRoutes

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_55847_aux.Helpers

structure FirstFork {n : Nat} (gs : List Gate) (root out : Fin (n + gs.length)) where
  wire : Fin (n + gs.length)
  reaches : Relation.ReflTransGen (readEdge gs) root wire
  terminal : wire = out ∨ 2 ≤ (gs.flatMap Gate.inputs).count wire.val
  onceBefore : ∀ w : Fin (n + gs.length), Relation.ReflTransGen (readEdge gs) root w →
    w.val < wire.val → (gs.flatMap Gate.inputs).count w.val ≤ 1

noncomputable def firstFork {n : Nat} (gs : List Gate) (root out : Fin (n + gs.length))
    (reachesOut : Relation.ReflTransGen (readEdge gs) root out) : FirstFork gs root out := by
  classical
  let eligible (m : Nat) :=
    ∃ w : Fin (n + gs.length), w.val = m ∧ Relation.ReflTransGen (readEdge gs) root w ∧
      (w = out ∨ 2 ≤ (gs.flatMap Gate.inputs).count w.val)
  have existsTerminal : ∃ m, eligible m := ⟨out.val, out, rfl, reachesOut, Or.inl rfl⟩
  let wire := Classical.choose (Nat.find_spec existsTerminal)
  have spec := Classical.choose_spec (Nat.find_spec existsTerminal)
  have address : wire.val = Nat.find existsTerminal := spec.1
  refine ⟨wire, spec.2.1, spec.2.2, fun w path earlier => ?_⟩
  by_contra! fork
  have minimal := Nat.find_min' existsTerminal
    (show eligible w.val from ⟨w, rfl, path, Or.inr (by omega)⟩)
  omega

theorem FirstFork.no_bypass {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    {root out : Fin (n + gs.length)} (fork : FirstFork gs root out)
    (beforeOut : fork.wire.val < out.val) :
    ¬ Relation.ReflTransGen (avoid (readEdge gs) fork.wire) root out := by
  have follow {source : Fin (n + gs.length)}
      (route : Relation.ReflTransGen (readEdge gs) source fork.wire) :
      Relation.ReflTransGen (readEdge gs) root source →
        ¬ Relation.ReflTransGen (avoid (readEdge gs) fork.wire) source out := by
    induction route using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro _ bypass
      rcases bypass.cases_head with equal | ⟨_, first, _⟩
      · exact (Nat.ne_of_lt beforeOut) (congrArg Fin.val equal)
      · exact first.2.1 rfl
    | @head source next first rest ih =>
      intro fromRoot bypass
      have earlier := (read_order clean first).trans_le (read_path_order clean rest)
      rcases bypass.cases_head with equal | ⟨branch, side, bypassRest⟩
      · have eq := congrArg Fin.val equal
        omega
      · have equal := unique_read_successor (fork.onceBefore source fromRoot earlier) first side.1
        subst branch
        exact ih (fromRoot.tail first) bypassRest
  exact follow fork.reaches .refl

theorem FirstFork.sibling_unreachable {n : Nat} {gs : List Gate}
    {rootA rootB out : Fin (n + gs.length)} (a : FirstFork gs rootA out) (b : FirstFork gs rootB out)
    (earlier : a.wire.val < b.wire.val) (last : ∀ w : Fin (n + gs.length), w.val ≤ out.val) :
    ¬ Relation.ReflTransGen (readEdge gs) rootB a.wire := by
  intro path
  have once := b.onceBefore a.wire path earlier
  rcases a.terminal with atOutput | repeated
  · have cap := last b.wire
    rw [atOutput] at earlier
    omega
  · omega

theorem FirstFork.internal_of_single_raw {n : Nat} {gs : List Gate}
    {raw : Fin n} {out : Fin (n + gs.length)} (fork : FirstFork gs (inputWire gs raw) out)
    (once : (gs.flatMap Gate.inputs).count raw.val ≤ 1) (outInternal : n ≤ out.val) :
    n ≤ fork.wire.val := by
  rcases fork.reaches.cases_tail with unmoved | ⟨_, _, step⟩
  · have same := congrArg Fin.val unmoved
    change fork.wire.val = raw.val at same
    rcases fork.terminal with atOutput | repeated
    · simpa only [atOutput] using outInternal
    · rw [same] at repeated
      omega
  · exact read_target_internal step

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SharedReadRoutes

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPairLower

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_55847_aux.Helpers
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula (occurrences)
open SharedReadRoutes SignedReadLocal SignedUniqueRead

noncomputable def matchingFirstFork {gs : List Gate} (clean : CleanL 9 gs)
    (out : Fin (9 + gs.length)) (computes : ∀ x : Fin 9 → Bool, vl gs x out.val = matching x)
    (raw : Fin 9) : FirstFork gs (inputWire gs raw) out := by
  apply firstFork
  obtain ⟨x, y, agree, different⟩ := MatchingPM3.matching_essential raw
  have outDiff : vl gs x out.val ≠ vl gs y out.val := by
    rw [computes x, computes y]
    exact different
  obtain ⟨i, changes, path⟩ := wire_change_traces_to_raw clean x y out outDiff
  have same : i = raw := by
    by_contra notRaw
    exact changes (agree i notRaw)
  subst i
  exact path

theorem matching_same_first_fork_incompatible {gs : List Gate} (clean : CleanL 9 gs)
    {out : Fin (9 + gs.length)} (last : ∀ w : Fin (9 + gs.length), w.val ≤ out.val)
    {a b : Fin 9} (fa : FirstFork gs (inputWire gs a) out)
    (fb : FirstFork gs (inputWire gs b) out) (same : fa.wire = fb.wire)
    (computes : ∀ x : Fin 9 → Bool, vl gs x out.val = matching x) :
    compatible a b = false := by
  cases candidate : compatible a b
  · rfl
  · exfalso
    let f := wireFormula (0 : Fin 9) gs fa.wire.val
    have atFork (x : Fin 9 → Bool) : f.eval x = vl gs x fa.wire.val :=
      wireFormula_eval (0 : Fin 9) clean x fa.wire.val fa.wire.isLt
    have aOnce : occurrences a f ≤ 1 :=
      clean_wireFormula_occurrences_le_one_on_readPath clean 0 a fa.wire fa.onceBefore
    have bOnce : occurrences b f ≤ 1 := by
      apply clean_wireFormula_occurrences_le_one_on_readPath clean 0 b fa.wire
      intro w path earlier
      exact fb.onceBefore w path (by simpa only [← same] using earlier)
    apply compatible_pair_no_single_bit_with_once_inputs f a b candidate _ aOnce bOnce
    intro x y unchanged sameFormula
    have sameFork := (atFork x).symm.trans (sameFormula.trans (atFork y))
    have sameOut : vl gs x out.val = vl gs y out.val := by
      by_cases atOutput : fa.wire = out
      · simpa only [atOutput] using sameFork
      · have earlier : fa.wire.val < out.val := lt_of_le_of_ne (last _) (fun eq => atOutput (Fin.ext eq))
        apply circuit_cut_agreement clean fa.wire out x y sameFork
        intro i changes
        by_cases isA : i = a
        · subst i
          exact fa.no_bypass clean earlier
        by_cases isB : i = b
        · subst i
          have h := fb.no_bypass clean (by simpa only [← same] using earlier)
          simpa only [← same] using h
        exact False.elim (changes (unchanged i isA isB))
    exact (computes x).symm.trans (sameOut.trans (computes y))

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.MatchingPairLower

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization
open PEqualNP.CircuitLowerBounds

def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

def isNot (g : Gate) : Bool := isNotOp g.op

def notCount (gs : List Gate) : Nat := gs.countP isNot

@[simp] theorem isNot_true {g : Gate} : isNot g = true ↔ g.op = GateOp.not := by
  cases g with
  | mk op inputs => cases op <;> simp [isNot, isNotOp]

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus

open scoped BigOperators

theorem sum_count_sub_one (reads : List Nat) :
    (∑ w ∈ reads.toFinset, (reads.count w - 1)) =
      reads.length - reads.toFinset.card := by
  have same : (∑ w ∈ reads.toFinset, ((reads.count w - 1) + 1)) =
      ∑ w ∈ reads.toFinset, reads.count w := by
    apply Finset.sum_congr rfl
    intro w hw
    have pos := List.count_pos_iff.mpr (List.mem_toFinset.mp hw)
    omega
  rw [Finset.sum_add_distrib, ← Finset.card_eq_sum_ones, List.sum_toFinset_count_eq_length] at same
  omega

theorem count_excess_budget (reads : List Nat) (selected : Finset Nat)
    (present : selected ⊆ reads.toFinset) :
    (∑ w ∈ selected, (reads.count w - 1)) ≤ reads.length - reads.toFinset.card := by
  rw [← sum_count_sub_one]
  exact Finset.sum_le_sum_of_subset present

theorem distinct_repeats_card_le (reads : List Nat) (selected : Finset Nat)
    (repeats : ∀ w ∈ selected, 2 ≤ reads.count w) :
    selected.card ≤ reads.length - reads.toFinset.card := by
  have subset : selected ⊆ reads.toFinset := by
    intro w member
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := repeats w member; omega))
  calc
    selected.card = ∑ w ∈ selected, 1 := Finset.card_eq_sum_ones selected
    _ ≤ ∑ w ∈ selected, (reads.count w - 1) := Finset.sum_le_sum fun w hw => by
      have := repeats w hw
      omega
    _ ≤ reads.length - reads.toFinset.card := count_excess_budget reads selected subset

theorem exact_two_repeats (reads : List Nat) {a b : Nat} (different : a ≠ b)
    (cap : reads.length - reads.toFinset.card ≤ 2)
    (repeatA : 2 ≤ reads.count a) (repeatB : 2 ≤ reads.count b) :
    reads.length - reads.toFinset.card = 2 ∧ reads.count a = 2 ∧ reads.count b = 2 ∧
      ∀ w, w ≠ a → w ≠ b → reads.count w ≤ 1 := by
  have memA : a ∈ reads.toFinset := List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have memB : b ∈ reads.toFinset := List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have bound := count_excess_budget reads {a, b} (by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact memA
    · exact memB)
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using different),
    Finset.sum_singleton] at bound
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro w neA neB
  by_contra notSmall
  have againW : 2 ≤ reads.count w := by omega
  have repeats : ∀ k ∈ ({a, b, w} : Finset Nat), 2 ≤ reads.count k := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact repeatA
    · exact repeatB
    · exact againW
  have tooMany := distinct_repeats_card_le reads {a, b, w} repeats
  rw [Finset.card_insert_of_notMem (by simp [different, Ne.symm neA]),
    Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using Ne.symm neB),
    Finset.card_singleton] at tooMany
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_55847_aux.Helpers
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus

private theorem partition_gate_counts (gs : List Gate) :
    nonNotCount gs + notCount gs = gs.length := by
  induction gs with
  | nil => simp [nonNotCount, notCount]
  | cons g rest ih =>
    cases op : g.op <;>
      simp [nonNotCount, CircuitReadSurplus.isNot, notCount,
        SignedNormalization.isNot, isNotOp, op] at ih ⊢ <;> omega

theorem exact_read_not_budget (C : Circuit) (n : Nat)
    (nonempty : C.gates ≠ []) (last : C.output + 1 = n + C.gates.length)
    (shape : ∀ j : Fin C.gates.length, CleanGate (n + j.val) (C.gates.get j))
    (liveRead : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ n + j.val ∈ (C.gates.get k).inputs)
    (raw : ∀ i : Fin n, i.val ∈ operandReads C.gates) :
    excessReads C.gates + notCount C.gates + n = C.gates.length + 1 := by
  have lastOutput : C.output = n + C.gates.length - 1 := by omega
  have arity (g : Gate) (m : g ∈ C.gates) :
      g.inputs.length = if CircuitReadSurplus.isNot g.op then 1 else 2 := by
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp m
    rcases shape j with ⟨op, a, _, ins⟩ | ⟨op, a, b, _, _, ins⟩
    · rw [ins, op]
      simp [CircuitReadSurplus.isNot]
    · rcases op with op | op <;> rw [ins, op] <;> simp [CircuitReadSurplus.isNot]
  have readEarlier (w : Nat) (rawBound : n ≤ w) (beforeOutput : w < C.output) :
      w ∈ operandReads C.gates := by
    let j : Fin C.gates.length := ⟨w - n, by omega⟩
    have idx : n + j.val = w := by dsimp [j]; omega
    have notLast : j.val + 1 < C.gates.length := by dsimp [j]; omega
    obtain ⟨k, _, uses⟩ := liveRead j notLast
    exact List.mem_flatMap.mpr ⟨C.gates.get k, List.get_mem _ _, by simpa only [idx] using uses⟩
  have usedRaw : usedRawCount n C.gates = n := by
    have support :
        (operandReads C.gates).toFinset.filter (fun w => w < n) = Finset.range n := by
      ext w
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_range]
      exact ⟨And.right, fun h => ⟨raw ⟨w, h⟩, h⟩⟩
    simp [usedRawCount, support]
  have count := excessReads_add_usedRawCount n C nonempty lastOutput arity
    (fun j => (shape j).lt) readEarlier
  rw [usedRaw] at count
  have partition := partition_gate_counts C.gates
  omega

theorem positive_not_count (gs : List Gate) {g : Gate} (m : g ∈ gs) (op : g.op = .not) :
    0 < notCount gs :=
  List.countP_pos_iff.mpr ⟨g, m, SignedNormalization.isNot_true.mpr op⟩

theorem unique_not_index_of_count (gs : List Gate) (one : notCount gs = 1) :
    ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
  induction gs with
  | nil => simp [notCount] at one
  | cons g rest ih =>
    by_cases head : g.op = .not
    · have firstTrue := SignedNormalization.isNot_true.mpr head
      have restZero : notCount rest = 0 := by
        simp only [notCount, List.countP_cons, firstTrue, ite_true] at one
        unfold notCount
        omega
      have atHead (i : Fin (g :: rest).length) (op : ((g :: rest).get i).op = .not) : i = 0 := by
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          have impossible := positive_not_count rest (List.get_mem rest i) (show (rest.get i).op = .not from op)
          omega
      intro i j hi hj
      exact (atHead i hi).trans (atHead j hj).symm
    · have firstFalse : SignedNormalization.isNot g = false :=
        Bool.eq_false_iff.mpr (fun h => head (SignedNormalization.isNot_true.mp h))
      have restOne : notCount rest = 1 := by
        simpa [notCount, List.countP_cons, firstFalse] using one
      intro i j hi hj
      cases i using Fin.cases with
      | zero => exact False.elim (head hi)
      | succ i =>
        cases j using Fin.cases with
        | zero => exact False.elim (head hj)
        | succ j => exact congrArg Fin.succ (ih restOne i j hi hj)

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.Slot336

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_55847_aux.Helpers
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.CircuitReadSurplus
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.SignedNormalization

def sortedGate (available : Nat) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a, a < available ∧ g.inputs = [a]) ∨
  ((g.op = .and ∨ g.op = .or) ∧
    ∃ a b, a < b ∧ b < available ∧ g.inputs = [a, b])

theorem sortedGate_clean {available : Nat} {g : Gate} (shape : sortedGate available g) :
    CleanGate available g := by
  rcases shape with one | ⟨op, a, b, ab, bAvail, args⟩
  · exact Or.inl one
  · exact Or.inr ⟨op, a, b, ab.trans bAvail, bAvail, args⟩

theorem nine_input_read_not_budget (C : Circuit) (nonempty : C.gates ≠ [])
    (last : C.output + 1 = 9 + C.size)
    (shape : ∀ j : Fin C.gates.length, sortedGate (9 + j.val) (C.gates.get j))
    (liveRead : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (raw : ∀ i : Fin 9, i.val ∈ operandReads C.gates) :
    excessReads C.gates + notCount C.gates + 8 = C.size := by
  have count := exact_read_not_budget C 9 nonempty last
    (fun j => sortedGate_clean (shape j)) liveRead raw
  change _ = C.gates.length
  omega

theorem second_not_restricts_eleven (C : Circuit)
    (size : C.size ≤ 11) (last : C.output + 1 = 9 + C.size)
    (shape : ∀ j : Fin C.gates.length, sortedGate (9 + j.val) (C.gates.get j))
    (liveRead : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (second : C.gates.tail.head? = some ⟨.not, [3]⟩)
    (raw : ∀ i : Fin 9, i.val ∈ operandReads C.gates)
    (repeat0 : 2 ≤ (operandReads C.gates).count 0)
    (repeat1 : 2 ≤ (operandReads C.gates).count 1) :
    C.size = 11 ∧ excessReads C.gates = 2 ∧ notCount C.gates = 1 ∧
      (∀ j : Fin C.gates.length, (C.gates.get j).op = .not ↔ j.val = 1) ∧
      (operandReads C.gates).count 0 = 2 ∧ (operandReads C.gates).count 1 = 2 ∧
      (operandReads C.gates).count 3 = 1 ∧
      ∀ w, w ≠ 0 → w ≠ 1 → (operandReads C.gates).count w ≤ 1 := by
  have atOne : C.gates[1]? = some ⟨.not, [3]⟩ := by
    simpa only [List.head?_eq_getElem?, List.getElem?_tail] using second
  obtain ⟨index, oneAt⟩ := List.getElem?_eq_some_iff.mp atOne
  let secondIndex : Fin C.gates.length := ⟨1, index⟩
  have secondOp : (C.gates.get secondIndex).op = .not := by
    change C.gates[1].op = .not
    rw [oneAt]
  have nonempty : C.gates ≠ [] := by
    intro empty
    simp [empty] at index
  have positive : 0 < notCount C.gates :=
    positive_not_count C.gates (List.get_mem _ secondIndex) secondOp
  have budget : excessReads C.gates + notCount C.gates + 8 = C.gates.length :=
    nine_input_read_not_budget C nonempty last shape liveRead raw
  have size' : C.gates.length ≤ 11 := size
  have excessCap : excessReads C.gates ≤ 2 := by omega
  obtain ⟨excess, exact0, exact1, others⟩ :=
    exact_two_repeats (operandReads C.gates) (by decide : (0 : Nat) ≠ 1)
      excessCap repeat0 repeat1
  have excess' : excessReads C.gates = 2 := excess
  have sizeExact : C.size = 11 := by
    change C.gates.length = 11
    omega
  have countOne : notCount C.gates = 1 := by omega
  have exactlySecond (j : Fin C.gates.length) : (C.gates.get j).op = .not ↔ j.val = 1 := by
    constructor
    · intro op
      exact congrArg Fin.val (unique_not_index_of_count C.gates countOne j secondIndex op secondOp)
    · intro eq
      have same : j = secondIndex := Fin.ext eq
      exact same.symm ▸ secondOp
  have rawThree : 0 < (operandReads C.gates).count 3 := List.count_pos_iff.mpr (raw 3)
  have atMostThree := others 3 (by decide) (by decide)
  exact ⟨sizeExact, excess', countOne, exactlySecond, exact0, exact1, by omega, others⟩

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.Slot336

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitReadSurplus SharedReadRoutes SignedNormalization

theorem normalized_essential_circuit {n s : Nat} {f : (Fin n → Bool) → Bool}
    (two : 2 ≤ n) (essential : Essential n f) (has : HasCircuitSize n f s) :
    ∃ C : Circuit, C.size ≤ s ∧ C.gates ≠ [] ∧
      C.output + 1 = n + C.gates.length ∧ Helpers.CleanL n C.gates ∧
      (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
        ∃ k : Fin C.gates.length, j.val < k.val ∧ n + j.val ∈ (C.gates.get k).inputs) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  have nonconstant : ∃ x y, f x ≠ f y := by
    obtain ⟨x, y, _, diff⟩ := essential ⟨0, by omega⟩
    exact ⟨x, y, diff⟩
  obtain ⟨gs, o, least, small⟩ := PM3LeastCore.exists_least n f s nonconstant has
  let C : Circuit := ⟨gs, o⟩
  have computes (x : Fin n → Bool) : C.eval (List.ofFn x) = f x := least.hev x
  have internal : n ≤ o := output_not_raw_of_essential C n two f essential computes
  have valid : o < n + gs.length := output_valid_of_essential C n (by omega) f essential computes
  have last : o + 1 = n + gs.length := by
    by_contra wrong
    let p := gs.length - 1
    have existsLast : p < gs.length := by dsimp [p]; omega
    have different : o ≠ n + p := by dsimp [p]; omega
    obtain ⟨q, later, reads⟩ := least.live nonconstant p existsLast different
    have qBound := PM3LeastCore.reads_len reads
    dsimp [p] at later
    omega
  have nonempty : gs ≠ [] := by
    intro empty
    simp [empty] at valid
    omega
  refine ⟨C, small, nonempty, last, least.hcl, ?_, computes⟩
  intro j earlier
  have before : j.val + 1 < gs.length := earlier
  have different : o ≠ n + j.val := by omega
  obtain ⟨q, later, g, atGate, used⟩ := least.live nonconstant j.val j.isLt different
  obtain ⟨qBound, gateEq⟩ := List.getElem?_eq_some_iff.mp atGate
  refine ⟨⟨q, qBound⟩, later, ?_⟩
  change n + j.val ∈ gs[q].inputs
  rw [gateEq]
  exact used

noncomputable def essentialFirstFork {n : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (essential : Essential n f) (clean : Helpers.CleanL n gs)
    (out : Fin (n + gs.length)) (computes : ∀ x : Fin n → Bool, Helpers.vl gs x out.val = f x)
    (raw : Fin n) : FirstFork gs (inputWire gs raw) out := by
  apply firstFork
  obtain ⟨x, y, agree, different⟩ := essential raw
  have outDiff : Helpers.vl gs x out.val ≠ Helpers.vl gs y out.val := by
    simpa only [computes] using different
  obtain ⟨i, changes, path⟩ := wire_change_traces_to_raw clean x y out outDiff
  have same : i = raw := by
    by_contra notRaw
    exact changes (agree i notRaw)
  subst i
  exact path

def singletonInputs (n : Nat) (gs : List Gate) : Finset (Fin n) :=
  Finset.univ.filter fun i => (operandReads gs).count i.val ≤ 1

def firstSharedForks {n : Nat} {gs : List Gate} (out : Fin (n + gs.length))
    (forks : ∀ i : Fin n, FirstFork gs (inputWire gs i) out) : Finset (Fin (n + gs.length)) :=
  ((singletonInputs n gs).image fun i => (forks i).wire).erase out

theorem excess_reads_of_fork_capacity {n capacity : Nat} {gs : List Gate}
    (out : Fin (n + gs.length)) (internal : n ≤ out.val)
    (forks : ∀ i : Fin n, FirstFork gs (inputWire gs i) out)
    (bound : (singletonInputs n gs).card ≤ (firstSharedForks out forks).card + capacity) :
    n ≤ excessReads gs + capacity := by
  classical
  let reads := operandReads gs
  let oneRead (i : Fin n) := reads.count i.val ≤ 1
  let repeated : Finset (Fin n) := Finset.univ.filter fun i => ¬ oneRead i
  have rawCount := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) oneRead
  change (singletonInputs n gs).card + repeated.card = (Finset.univ : Finset (Fin n)).card at rawCount
  rw [Finset.card_univ, Fintype.card_fin] at rawCount
  let rawAddresses := repeated.image Fin.val
  let sharedAddresses := (firstSharedForks out forks).image Fin.val
  have sharedInternal (w : Nat) (hw : w ∈ sharedAddresses) : n ≤ w ∧ 2 ≤ reads.count w := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨off, present⟩ := Finset.mem_erase.mp hv
    obtain ⟨i, hi, same⟩ := Finset.mem_image.mp present
    have once := (Finset.mem_filter.mp hi).2
    have inRange := (forks i).internal_of_single_raw once internal
    have shared := (forks i).terminal.resolve_left (fun sameOut => off (same.symm.trans sameOut))
    change n ≤ v.val ∧ 2 ≤ (gs.flatMap Gate.inputs).count v.val
    simpa only [same] using And.intro inRange shared
  have disjoint : Disjoint rawAddresses sharedAddresses := by
    apply Finset.disjoint_left.mpr
    intro w hw hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact (Nat.not_le_of_lt i.isLt) (sharedInternal i.val hs).1
  have spent := distinct_repeats_card_le reads (rawAddresses ∪ sharedAddresses) (by
    intro w hw
    rcases Finset.mem_union.mp hw with raw | shared
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp raw
      have many := (Finset.mem_filter.mp hi).2
      change ¬ reads.count i.val ≤ 1 at many
      omega
    · exact (sharedInternal w shared).2)
  rw [Finset.card_union_of_disjoint disjoint] at spent
  change (repeated.image Fin.val).card + ((firstSharedForks out forks).image Fin.val).card ≤
    excessReads gs at spent
  rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_image_of_injective _ Fin.val_injective] at spent
  omega

theorem hasCircuitSize_lower_of_fork_capacity {n capacity s : Nat} {f : (Fin n → Bool) → Bool}
    (two : 2 ≤ n) (essential : Essential n f) (has : HasCircuitSize n f s)
    (capacityBound : ∀ (gs : List Gate) (out : Fin (n + gs.length)) (clean : Helpers.CleanL n gs),
      (∀ w : Fin (n + gs.length), w.val ≤ out.val) →
      ∀ computes : ∀ x : Fin n → Bool, Helpers.vl gs x out.val = f x,
        (singletonInputs n gs).card ≤
          (firstSharedForks out (essentialFirstFork essential clean out computes)).card + capacity) :
    n + n ≤ s + capacity + 1 := by
  obtain ⟨C, small, nonempty, last, clean, live, computes⟩ :=
    normalized_essential_circuit two essential has
  have internal := output_not_raw_of_essential C n two f essential computes
  let out : Fin (n + C.gates.length) := ⟨C.output, by omega⟩
  have finalWire (w : Fin (n + C.gates.length)) : w.val ≤ out.val := by
    have := w.isLt
    change w.val ≤ C.output
    omega
  have computesWire (x : Fin n → Bool) : Helpers.vl C.gates x out.val = f x := computes x
  have repeatBound := excess_reads_of_fork_capacity out internal
    (essentialFirstFork essential clean out computesWire)
    (capacityBound C.gates out clean finalWire computesWire)
  have exactBudget := exact_read_not_budget C n nonempty last
    (fun j => clean j.val _ (List.getElem?_eq_getElem j.isLt)) live
    (reads_raw_of_essential C n two f essential computes)
  change C.gates.length ≤ s at small
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.ReadOnceFormula
open PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.DMFixedPair (withPair)
open SharedReadRoutes SignedReadLocal SignedUniqueRead

def PairConflict {n : Nat} (f : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  i ≠ j ∧
    (∃ base : Fin n → Bool, ∀ a b : Bool, f (withPair base i j a b) = (a && b)) ∧
    (∃ base : Fin n → Bool, ∀ a b : Bool, f (withPair base i j a b) = (a || b))

private theorem complement_occurrences {n : Nat} (f : DMFormula n) (i : Fin n) :
    occurrences i (complement f) = occurrences i f := by
  induction f with
  | lit k s => rfl
  | and p q hp hq | or p q hp hq => simp [complement, occurrences, hp, hq]

private theorem withPair_agrees_except {n : Nat} (base : Fin n → Bool) (i j : Fin n)
    (a b c d : Bool) (k : Fin n) (ki : k ≠ i) (kj : k ≠ j) :
    withPair base i j a b k = withPair base i j c d k := by
  simp [withPair, ki, kj]

private theorem directed_values :
    ∀ s low high : Bool, Orient s low high → low ≠ high →
      low = !s ∧ high = s := by
  decide

private theorem binary_readout :
    ∀ s v p : Bool, (v = !s → p = false) → (v = s → p = true) →
      v = (if s then p else !p) := by
  decide

theorem pair_conflict_no_once_one_bit {n : Nat} {f : (Fin n → Bool) → Bool}
    (F : DMFormula n) (i j : Fin n) (conflict : PairConflict f i j)
    (isolate : ∀ x y : Fin n → Bool,
      (∀ k, k ≠ i → k ≠ j → x k = y k) → F.eval x = F.eval y → f x = f y)
    (readI : occurrences i F ≤ 1) (readJ : occurrences j F ≤ 1) : False := by
  obtain ⟨direction, oriented⟩ := formulaUnate i F readI
  let positive := if direction then F else complement F
  have selected (base : Fin n → Bool) (op : Bool → Bool → Bool)
      (proj : ∀ a b : Bool, f (withPair base i j a b) = op a b)
      (e : Bool) (lo : op false e = false) (hi : op true e = true) (a b : Bool) :
      positive.eval (withPair base i j a b) = op a b := by
    let lower := withPair base i j false e
    let upper := withPair base i j true e
    let probe := withPair base i j a b
    have differs : F.eval lower ≠ F.eval upper := by
      intro same
      have result := isolate lower upper (withPair_agrees_except base i j false e true e) same
      rw [proj, proj, lo, hi] at result
      contradiction
    have directionLowHigh : Orient direction (F.eval lower) (F.eval upper) := by
      apply oriented lower upper
      · intro k hk
        simp [lower, upper, withPair, hk]
      · simp [lower, withPair]
      · simp [upper, withPair]
    obtain ⟨directionLow, directionHigh⟩ := directed_values direction _ _ directionLowHigh differs
    have lowerResult : F.eval probe = !direction → op a b = false := by
      intro p
      have result := isolate probe lower (withPair_agrees_except base i j a b false e)
        (p.trans directionLow.symm)
      rw [proj, proj, lo] at result
      exact result
    have upperResult : F.eval probe = direction → op a b = true := by
      intro p
      have result := isolate probe upper (withPair_agrees_except base i j a b true e)
        (p.trans directionHigh.symm)
      rw [proj, proj, hi] at result
      exact result
    have value := binary_readout direction _ _ lowerResult upperResult
    cases hd : direction <;> simp [positive, hd, complement_eval, value, probe] at *
  have countPos (k : Fin n) : occurrences k positive = occurrences k F := by
    cases hd : direction <;> simp [positive, hd, complement_occurrences]
  obtain ⟨andBase, pAnd⟩ := conflict.2.1
  obtain ⟨orBase, pOr⟩ := conflict.2.2
  have andProj := selected andBase (· && ·) pAnd true rfl rfl
  have orProj := selected orBase (· || ·) pOr false rfl rfl
  have readPosI : 0 < occurrences i positive := by
    by_contra! absent
    have same : positive.eval (withPair andBase i j false true) =
        positive.eval (withPair andBase i j true true) := by
      apply DMFixedPair.eval_eq_of_agree_on_occurrences
      intro k hk
      have ne : k ≠ i := by rintro rfl; omega
      simp [withPair, ne]
    simp only [andProj, Bool.false_and, Bool.true_and, Bool.false_eq_true] at same
  have readPosJ : 0 < occurrences j positive := by
    by_contra! absent
    have same : positive.eval (withPair andBase i j true false) =
        positive.eval (withPair andBase i j true true) := by
      apply DMFixedPair.eval_eq_of_agree_on_occurrences
      intro k hk
      have ne : k ≠ j := by rintro rfl; omega
      simp [withPair, ne]
    simp only [andProj, Bool.true_and, Bool.false_eq_true] at same
  have countI := countPos i
  have countJ := countPos j
  exact DMFixedPair.not_and_or_projections_of_single_occurrences positive i j conflict.1
    (by omega) (by omega) ⟨⟨andBase, andProj⟩, ⟨orBase, orProj⟩⟩

theorem separate_first_forks_of_pair_conflict {n : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (clean : CleanL n gs)
    {out : Fin (n + gs.length)} (last : ∀ w : Fin (n + gs.length), w.val ≤ out.val)
    {a b : Fin n} (fa : FirstFork gs (inputWire gs a) out)
    (fb : FirstFork gs (inputWire gs b) out)
    (computes : ∀ x : Fin n → Bool, vl gs x out.val = f x)
    (conflict : PairConflict f a b) : fa.wire ≠ fb.wire := by
  intro same
  let formula := wireFormula a gs fa.wire.val
  have atFork (x : Fin n → Bool) : formula.eval x = vl gs x fa.wire.val :=
    wireFormula_eval a clean x fa.wire.val fa.wire.isLt
  have aOnce : occurrences a formula ≤ 1 :=
    clean_wireFormula_occurrences_le_one_on_readPath clean a a fa.wire fa.onceBefore
  have bOnce : occurrences b formula ≤ 1 := by
    apply clean_wireFormula_occurrences_le_one_on_readPath clean a b fa.wire
    intro w path earlier
    exact fb.onceBefore w path (by simpa only [← same] using earlier)
  apply pair_conflict_no_once_one_bit formula a b conflict _ aOnce bOnce
  intro x y unchanged sameFormula
  have sameFork := (atFork x).symm.trans (sameFormula.trans (atFork y))
  have sameOut : vl gs x out.val = vl gs y out.val := by
    by_cases atOutput : fa.wire = out
    · simpa only [atOutput] using sameFork
    · have earlier : fa.wire.val < out.val := lt_of_le_of_ne (last _) (fun eq => atOutput (Fin.ext eq))
      apply circuit_cut_agreement clean fa.wire out x y sameFork
      intro i changes
      by_cases isA : i = a
      · subst i
        exact fa.no_bypass clean earlier
      by_cases isB : i = b
      · subst i
        have h := fb.no_bypass clean (by simpa only [← same] using earlier)
        simpa only [← same] using h
      exact False.elim (changes (unchanged i isA isB))
  exact (computes x).symm.trans (sameOut.trans (computes y))

def CutRankThree {n : Nat} (f : (Fin n → Bool) → Bool)
    (inside outside : Finset (Fin n)) : Prop :=
  ∃ make : Fin 3 → Bool → Fin n → Bool,
    (∀ r s t i, i ∉ inside → make r t i = make s t i) ∧
    (∀ r t u i, i ∉ outside → make r t i = make r u i) ∧
    Function.Injective (fun r t => f (make r t))

theorem cut_rank_three_forbids_one_bit {n : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} {inside outside : Finset (Fin n)} (clean : CleanL n gs)
    (cut out : Fin (n + gs.length))
    (blocked : ∀ i ∈ inside, ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out)
    (unrouted : ∀ i ∈ outside, ¬ Relation.ReflTransGen (readEdge gs) (inputWire gs i) cut)
    (computes : ∀ x : Fin n → Bool, vl gs x out.val = f x)
    (rank : CutRankThree f inside outside) : False := by
  obtain ⟨make, variesIn, variesOut, different⟩ := rank
  let encode (r : Fin 3) := vl gs (make r false) cut.val
  have encodeIndependent (r : Fin 3) (test : Bool) :
      vl gs (make r test) cut.val = encode r := by
    apply wire_agrees_if_reaching_raws_agree clean
    intro i reaches
    exact variesOut r test false i (fun member => unrouted i member reaches)
  have encodeInjective : Function.Injective encode := by
    intro r s same
    apply different
    funext test
    have agreesAtCut := (encodeIndependent r test).trans (same.trans (encodeIndependent s test).symm)
    have sameOutput := circuit_cut_agreement clean cut out (make r test) (make s test) agreesAtCut
      (fun i changed => blocked i (by
        by_contra away
        exact changed (variesIn r s test i away)))
    exact (computes _).symm.trans (sameOutput.trans (computes _))
  exact (by decide : ¬ Fintype.card (Fin 3) ≤ Fintype.card Bool)
    (Fintype.card_le_of_injective encode encodeInjective)

theorem earlier_first_fork_group_not_cut_rank_three {n : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} {inside outside : Finset (Fin n)} (clean : CleanL n gs)
    {out cut next : Fin (n + gs.length)} (last : ∀ w : Fin (n + gs.length), w.val ≤ out.val)
    (forks : ∀ i : Fin n, FirstFork gs (inputWire gs i) out)
    (insideNonempty : inside.Nonempty) (earlier : cut.val < next.val)
    (insideFork : ∀ i ∈ inside, (forks i).wire = cut)
    (outsideFork : ∀ i ∈ outside, (forks i).wire = next)
    (computes : ∀ x : Fin n → Bool, vl gs x out.val = f x) :
    ¬ CutRankThree f inside outside := by
  intro rank
  apply cut_rank_three_forbids_one_bit clean cut out _ _ computes rank
  · intro i member
    have before : (forks i).wire.val < out.val := by
      rw [insideFork i member]
      exact earlier.trans_le (last next)
    simpa only [insideFork i member] using (forks i).no_bypass clean before
  · intro j member
    obtain ⟨i, memberI⟩ := insideNonempty
    have before : (forks i).wire.val < (forks j).wire.val := by
      rw [insideFork i memberI, outsideFork j member]
      exact earlier
    simpa only [insideFork i memberI] using (forks i).sibling_unreachable (forks j) before last

def OrderedForkPackingBound {n : Nat} (f : (Fin n → Bool) → Bool) (capacity : Nat) : Prop :=
  ∀ (m : Nat) (raws : Finset (Fin n)) (label : Fin n → Fin m) (out : Fin m),
    (∀ i ∈ raws, (label i).val ≤ out.val) →
    (∀ i ∈ raws, ∀ j ∈ raws, label i = label j → ¬ PairConflict f i j) →
    (∀ earlier later : Fin m, earlier.val < later.val →
      (raws.filter fun i => label i = earlier).Nonempty →
      ¬ CutRankThree f (raws.filter fun i => label i = earlier)
        (raws.filter fun i => label i = later)) →
    raws.card ≤ ((raws.image label).erase out).card + capacity

theorem hasCircuitSize_lower_of_ordered_fork_packing {n capacity s : Nat}
    {f : (Fin n → Bool) → Bool} (two : 2 ≤ n) (essential : SignedNormalization.Essential n f)
    (has : HasCircuitSize n f s) (packing : OrderedForkPackingBound f capacity) :
    n + n ≤ s + capacity + 1 := by
  apply hasCircuitSize_lower_of_fork_capacity two essential has
  intro gs out clean last computes
  let forks := essentialFirstFork essential clean out computes
  let raws := singletonInputs n gs
  let label (i : Fin n) := (forks i).wire
  change raws.card ≤ ((raws.image label).erase out).card + capacity
  apply packing (n + gs.length) raws label out
  · intro i _
    exact last (label i)
  · intro i _ j _ same conflict
    exact separate_first_forks_of_pair_conflict clean last (forks i) (forks j) computes conflict same
  · intro cut next earlier nonempty
    exact earlier_first_fork_group_not_cut_rank_three clean last forks nonempty earlier
      (fun i member => (Finset.mem_filter.mp member).2)
      (fun i member => (Finset.mem_filter.mp member).2) computes

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitReadSurplus SharedReadRoutes SignedNormalization

theorem monotone_replacement_of_ordered_fork_packing {n capacity : Nat}
    {f : (Fin n → Bool) → Bool}
    (two : 2 ≤ n) (essential : Essential n f) (packing : OrderedForkPackingBound f capacity)
    (witness : List Gate) (witnessOutput : Nat)
    (witnessLegal : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (witnessSize : witness.length + capacity ≤ n + n)
    (witnessExact : ∀ x, (Circuit.mk witness witnessOutput).eval (List.ofFn x) = f x)
    (C : Circuit) (fan : FanInTwo C) (computes : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ (gates : List Gate) (output : Nat),
      (∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates.length ≤ C.size ∧ ∀ x, (Circuit.mk gates output).eval (List.ofFn x) = f x := by
  obtain ⟨D, small, nonempty, last, clean, live, exactEval⟩ :=
    normalized_essential_circuit two essential (s := C.size) ⟨C, fan, le_rfl, computes⟩
  by_cases signed : ∃ g ∈ D.gates, g.op = .not
  · let output : Fin (n + D.gates.length) := ⟨D.output, by omega⟩
    have final (w : Fin (n + D.gates.length)) : w.val ≤ output.val := by
      have h := w.isLt
      change w.val ≤ D.output
      omega
    have evalWire (x : Fin n → Bool) : Helpers.vl D.gates x output.val = f x := exactEval x
    let forks := essentialFirstFork essential clean output evalWire
    let raws := singletonInputs n D.gates
    let label (i : Fin n) := (forks i).wire
    have grouped : raws.card ≤ (firstSharedForks output forks).card + capacity := by
      change raws.card ≤ ((raws.image label).erase output).card + capacity
      apply packing (n + D.gates.length) raws label output
      · intro i _
        exact final (label i)
      · intro i _ j _ same conflict
        exact separate_first_forks_of_pair_conflict clean final (forks i) (forks j)
          evalWire conflict same
      · intro cut next earlier nonemptyGroup
        exact earlier_first_fork_group_not_cut_rank_three clean final forks nonemptyGroup earlier
          (fun i member => (Finset.mem_filter.mp member).2)
          (fun i member => (Finset.mem_filter.mp member).2) evalWire
    have outInternal := output_not_raw_of_essential D n two f essential exactEval
    have repeated := excess_reads_of_fork_capacity output outInternal forks grouped
    have budget := exact_read_not_budget D n nonempty last
      (fun j => clean j.val _ (List.getElem?_eq_getElem j.isLt)) live
      (reads_raw_of_essential D n two f essential exactEval)
    obtain ⟨g, mem, isNot⟩ := signed
    have hasNOT := positive_not_count D.gates mem isNot
    change D.gates.length ≤ C.size at small
    exact ⟨witness, witnessOutput, witnessLegal, by omega, witnessExact⟩
  · refine ⟨D.gates, D.output, ?_, small, exactEval⟩
    intro gate member
    obtain ⟨j, found⟩ := List.mem_iff_getElem?.mp member
    rcases clean j gate found with ⟨isNot, _⟩ | ⟨ops, a, b, _, _, inputs⟩
    · exact (signed ⟨gate, member, isNot⟩).elim
    · exact ⟨ops, by simp [inputs]⟩

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

def checkWeightBound {α : Type} (compatible : α → α → Bool) (weight : α → Nat) :
    (allowed : α → Bool) → (budget : Nat) → List α → Bool
  | _, _, [] => true
  | allowed, budget, x :: rest =>
    checkWeightBound compatible weight allowed budget rest &&
      (if allowed x then
        decide (weight x ≤ budget) &&
          checkWeightBound compatible weight (fun y => allowed y && compatible x y)
            (budget - weight x) rest
      else true)

theorem checkWeightBound_sound {α : Type} [DecidableEq α]
    (compatible : α → α → Bool) (weight : α → Nat) (allowed : α → Bool)
    (budget : Nat) (items : List α) (selected : Finset α)
    (valid : checkWeightBound compatible weight allowed budget items = true)
    (candidate : ∀ x ∈ selected, x ∈ items ∧ allowed x = true)
    (pairwise : ∀ x ∈ selected, ∀ y ∈ selected, x ≠ y → compatible x y = true) :
    selected.sum weight ≤ budget := by
  induction items generalizing allowed budget selected with
  | nil =>
    have empty : selected = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx =>
      List.not_mem_nil (candidate x hx).1
    simp [empty]
  | cons x rest ih =>
    obtain ⟨skip, take⟩ := Bool.and_eq_true_iff.mp valid
    by_cases chose : x ∈ selected
    · have ok := (candidate x chose).2
      rw [ite_eq_left ok] at take
      obtain ⟨fits, reduced⟩ := Bool.and_eq_true_iff.mp take
      have included : ∀ y ∈ selected.erase x, y ∈ rest ∧ (allowed y && compatible x y) = true := by
        intro y hy
        obtain ⟨ne, hy⟩ := Finset.mem_erase.mp hy
        obtain ⟨available, passes⟩ := candidate y hy
        exact ⟨(List.mem_cons.mp available).resolve_left ne,
          Bool.and_eq_true_iff.mpr ⟨passes, pairwise x chose y hy ne.symm⟩⟩
      have bound := ih _ _ _ reduced included (fun a ha b hb dab =>
        pairwise a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) dab)
      have total := Finset.sum_erase_add selected weight chose
      change (selected.erase x).sum weight + weight x = selected.sum weight at total
      have weightLe := of_decide_eq_true fits
      omega
    · apply ih _ _ _ skip _ pairwise
      intro y hy
      obtain ⟨available, passes⟩ := candidate y hy
      have ne : y ≠ x := fun eq => chose (eq ▸ hy)
      exact ⟨(List.mem_cons.mp available).resolve_left ne, passes⟩

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

theorem ordered_fork_packing_of_weight_check {n : Nat} {f : (Fin n → Bool) → Bool}
    (groups : List (Finset (Fin n))) (compatible : Finset (Fin n) → Finset (Fin n) → Bool)
    (budget : Nat)
    (covers : ∀ g : Finset (Fin n), 2 ≤ g.card →
      (∀ a ∈ g, ∀ b ∈ g, ¬ PairConflict f a b) → g ∈ groups)
    (compatible_of_rank : ∀ a b : Finset (Fin n), Disjoint a b →
      (¬ CutRankThree f a b ∨ ¬ CutRankThree f b a) → compatible a b = true)
    (checked : checkWeightBound compatible (fun g => g.card - 1) (fun _ => true) budget groups = true) :
    OrderedForkPackingBound f (budget + 1) := by
  intro m raws label out _ noPair noRank
  let used := raws.image label
  let fiber (tag : Fin m) := raws.filter fun i => label i = tag
  let big := used.filter fun tag => 2 ≤ (fiber tag).card
  let selected := big.image fiber
  let weight (s : Finset (Fin n)) := s.card - 1
  have positive {tag : Fin m} (member : tag ∈ used) : 0 < (fiber tag).card := by
    obtain ⟨i, hi, atTag⟩ := Finset.mem_image.mp member
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, atTag⟩⟩
  have differentFibers {a b : Fin m} (ne : a ≠ b) : Disjoint (fiber a) (fiber b) := by
    apply Finset.disjoint_left.mpr
    intro i left right
    exact ne ((Finset.mem_filter.mp left).2.symm.trans (Finset.mem_filter.mp right).2)
  have injective : Set.InjOn fiber big := by
    intro a ha b _ same
    by_contra ne
    have disjoint := differentFibers ne
    obtain ⟨i, member⟩ := Finset.card_pos.mp (positive (Finset.mem_filter.mp ha).1)
    exact (Finset.disjoint_left.mp disjoint member (same ▸ member))
  have selectedBound : selected.sum weight ≤ budget := by
    apply checkWeightBound_sound compatible weight (fun _ => true) budget groups selected checked
    · intro g present
      obtain ⟨tag, tagMem, rfl⟩ := Finset.mem_image.mp present
      refine ⟨covers _ (Finset.mem_filter.mp tagMem).2 ?_, rfl⟩
      intro a ha b hb
      obtain ⟨rawA, eqA⟩ := Finset.mem_filter.mp ha
      obtain ⟨rawB, eqB⟩ := Finset.mem_filter.mp hb
      exact noPair a rawA b rawB (eqA.trans eqB.symm)
    · intro a ha b hb diff
      obtain ⟨tagA, memA, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨tagB, memB, rfl⟩ := Finset.mem_image.mp hb
      have ne : tagA ≠ tagB := fun eq => diff (congrArg fiber eq)
      apply compatible_of_rank _ _ (differentFibers ne)
      rcases lt_or_gt_of_ne ne with earlier | earlier
      · exact Or.inl (noRank tagA tagB earlier (Finset.card_pos.mp (positive (Finset.mem_filter.mp memA).1)))
      · exact Or.inr (noRank tagB tagA earlier (Finset.card_pos.mp (positive (Finset.mem_filter.mp memB).1)))
  have count : raws.card = used.card + used.sum (fun tag => weight (fiber tag)) := by
    calc
      raws.card = used.sum (fun tag => (fiber tag).card) := Finset.card_eq_sum_card_image label raws
      _ = used.sum (fun tag => 1 + weight (fiber tag)) := by
        apply Finset.sum_congr rfl
        intro tag member
        have nonzero := positive member
        unfold weight
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have total : selected.sum weight = used.sum (fun tag => weight (fiber tag)) := by
    change (big.image fiber).sum weight = _
    rw [Finset.sum_image injective]
    change (used.filter fun tag => 2 ≤ (fiber tag).card).sum _ = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro tag _
    split
    · rfl
    · unfold weight
      omega
  have removed : used.card ≤ (used.erase out).card + 1 := by
    by_cases present : out ∈ used
    · exact (Finset.card_erase_add_one present).symm.le
    · rw [Finset.erase_eq_of_notMem present]
      omega
  change raws.card ≤ (used.erase out).card + (budget + 1)
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkNumeric

open FirstForkBounds (PairConflict CutRankThree)
open DMFixedPair (withPair)

def input {n : Nat} (word : Nat) (i : Fin n) : Bool :=
  word.testBit i.val

def support (n : Nat) (word : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun i => input word i

theorem mem_support {n word : Nat} {i : Fin n} :
    i ∈ support n word ↔ input word i = true := by
  simp [support]

def subset (word container : Nat) : Bool :=
  (word &&& container) == word

theorem input_zero_of_subset {n word container : Nat} {i : Fin n}
    (inc : subset word container = true) (off : input container i = false) :
    input word i = false := by
  have bits := congrArg (fun k : Nat => k.testBit i.val) (beq_iff_eq.mp inc)
  change container.testBit i.val = false at off
  simpa only [input, Nat.testBit_and, off, Bool.and_false] using bits.symm

theorem support_mono {n word container : Nat} (inc : subset word container = true) :
    support n word ⊆ support n container := by
  intro i belongs
  apply mem_support.mpr
  by_contra! absent
  have inputOn := mem_support.mp belongs
  have inputOff := input_zero_of_subset inc (Bool.eq_false_iff.mpr absent)
  rw [inputOff] at inputOn
  contradiction

def writeBit (word i : Nat) (value : Bool) : Nat :=
  if word.testBit i = value then word else word ^^^ (2 ^ i)

theorem testBit_writeBit (word i j : Nat) (value : Bool) :
    (writeBit word i value).testBit j = if j = i then value else word.testBit j := by
  by_cases same : j = i
  · subst j
    cases bit : word.testBit i <;> cases value <;> simp [writeBit, bit, Nat.testBit_xor]
  · unfold writeBit
    split
    · simp
    · simp [Nat.testBit_xor, Ne.symm same]

def pairRow {n : Nat} (word : Nat) (i j : Fin n) (a b : Bool) : Nat :=
  writeBit (writeBit word j.val b) i.val a

theorem input_pairRow {n : Nat} (word : Nat) (i j : Fin n) (a b : Bool) :
    input (pairRow word i j a b) = withPair (input word) i j a b := by
  funext k
  simp [input, pairRow, withPair, testBit_writeBit, Fin.val_inj]

structure PairDatum (n : Nat) where
  i : Fin n
  j : Fin n
  andBackground : Nat
  orBackground : Nat

def PairDatum.Valid {n : Nat} (w : PairDatum n) (f : (Fin n → Bool) → Bool) : Prop :=
  w.i ≠ w.j ∧
    (∀ a b : Bool, f (input (pairRow w.andBackground w.i w.j a b)) = (a && b)) ∧
    (∀ a b : Bool, f (input (pairRow w.orBackground w.i w.j a b)) = (a || b))

instance {n : Nat} (w : PairDatum n) (f : (Fin n → Bool) → Bool) : Decidable (w.Valid f) := by
  unfold PairDatum.Valid
  infer_instance

def PairDatum.check {n : Nat} (w : PairDatum n) (f : (Fin n → Bool) → Bool) : Bool :=
  decide (w.Valid f)

theorem PairDatum.pair_conflict {n : Nat} {f : (Fin n → Bool) → Bool} {w : PairDatum n}
    (valid : w.check f = true) : PairConflict f w.i w.j := by
  obtain ⟨distinct, andBranch, orBranch⟩ : w.Valid f := of_decide_eq_true valid
  refine ⟨distinct, ⟨input w.andBackground, ?_⟩, ⟨input w.orBackground, ?_⟩⟩
  · intro a b
    simpa only [input_pairRow] using andBranch a b
  · intro a b
    simpa only [input_pairRow] using orBranch a b

def allows {n : Nat} (pairs : List (PairDatum n)) (word : Nat) : Bool :=
  pairs.all fun w => !(input word w.i && input word w.j)

theorem allows_of_no_conflicts {n : Nat} {f : (Fin n → Bool) → Bool}
    (pairs : List (PairDatum n)) (valid : ∀ w ∈ pairs, w.check f = true) (word : Nat)
    (noConflicts : ∀ i ∈ support n word, ∀ j ∈ support n word, ¬ PairConflict f i j) :
    allows pairs word = true := by
  apply List.all_eq_true.mpr
  intro w present
  cases both : (input word w.i && input word w.j)
  · rfl
  · obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp both
    exact False.elim (noConflicts w.i (mem_support.mpr left) w.j (mem_support.mpr right)
      (PairDatum.pair_conflict (valid w present)))

structure RankDatum where
  p : Nat
  q : Nat
  background : Nat
  r0 : Nat
  r1 : Nat
  r2 : Nat
  c0 : Nat
  c1 : Nat

def RankDatum.row (w : RankDatum) (r : Fin 3) : Nat :=
  if r = 0 then w.r0 else if r = 1 then w.r1 else w.r2

def RankDatum.column (w : RankDatum) (b : Bool) : Nat :=
  if b then w.c1 else w.c0

def RankDatum.rowMask (w : RankDatum) (r : Fin 3) (b : Bool) : Nat :=
  w.background ||| w.row r ||| w.column b

def RankDatum.rankCode {n : Nat} (w : RankDatum) (f : (Fin n → Bool) → Bool)
    (r : Fin 3) : Nat :=
  (if f (input (w.rowMask r false)) then 1 else 0) +
    (if f (input (w.rowMask r true)) then 2 else 0)

def RankDatum.Valid {n : Nat} (w : RankDatum) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ r : Fin 3, subset (w.row r) w.p = true) ∧
    (∀ b : Bool, subset (w.column b) w.q = true) ∧
    (∀ r s : Fin 3, r ≠ s → w.rankCode f r ≠ w.rankCode f s)

instance {n : Nat} (w : RankDatum) (f : (Fin n → Bool) → Bool) : Decidable (w.Valid f) := by
  unfold RankDatum.Valid
  infer_instance

def RankDatum.check {n : Nat} (w : RankDatum) (f : (Fin n → Bool) → Bool) : Bool :=
  decide (w.Valid f)

theorem RankDatum.cut_rank {n : Nat} {f : (Fin n → Bool) → Bool} {w : RankDatum}
    (valid : w.check f = true) {a b : Nat}
    (left : subset w.p a = true) (right : subset w.q b = true) :
    CutRankThree f (support n a) (support n b) := by
  obtain ⟨validRows, validColumns, distinct⟩ : w.Valid f := of_decide_eq_true valid
  refine ⟨fun r c => input (w.rowMask r c), ?_, ?_, ?_⟩
  · intro r s t i away
    have off := input_zero_of_subset left (Bool.eq_false_iff.mpr (fun h => away (mem_support.mpr h)))
    have first := input_zero_of_subset (validRows r) off
    have second := input_zero_of_subset (validRows s) off
    simp only [RankDatum.rowMask, input, Nat.testBit_or] at first second ⊢
    rw [first, second]
  · intro r t u i away
    have off := input_zero_of_subset right (Bool.eq_false_iff.mpr (fun h => away (mem_support.mpr h)))
    have first := input_zero_of_subset (validColumns t) off
    have second := input_zero_of_subset (validColumns u) off
    simp only [RankDatum.rowMask, input, Nat.testBit_or] at first second ⊢
    rw [first, second]
  · intro r s agree
    by_contra different
    have atFalse : f (input (w.rowMask r false)) = f (input (w.rowMask s false)) := congrFun agree false
    have atTrue : f (input (w.rowMask r true)) = f (input (w.rowMask s true)) := congrFun agree true
    exact distinct r s different (by unfold RankDatum.rankCode; rw [atFalse, atTrue])

def blocked (ranks : List RankDatum) (a b : Nat) : Bool :=
  ranks.any fun w => subset w.p a && subset w.q b

theorem blocked_rank {n : Nat} {f : (Fin n → Bool) → Bool}
    (ranks : List RankDatum) (valid : ∀ w ∈ ranks, w.check f = true) {a b : Nat}
    (reject : blocked ranks a b = true) :
    CutRankThree f (support n a) (support n b) := by
  obtain ⟨w, present, both⟩ := List.any_eq_true.mp reject
  obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp both
  exact RankDatum.cut_rank (valid w present) left right

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkNumeric

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

open FirstForkNumeric

def groupWord {n : Nat} (g : Finset (Fin n)) : Nat :=
  Nat.ofBits (fun i => decide (i ∈ g))

@[simp] theorem support_groupWord {n : Nat} (g : Finset (Fin n)) :
    support n (groupWord g) = g := by
  ext i
  simp [support, input, groupWord]

def groupsFromMasks (n : Nat) (pairs : List (PairDatum n)) : List (Finset (Fin n)) :=
  ((List.range (2 ^ n)).filter fun w => allows pairs w && decide (2 ≤ (support n w).card)).map
    (support n)

def compatibleFromMasks {n : Nat} (ranks : List RankDatum) (a b : Finset (Fin n)) : Bool :=
  Bool.and (decide (Disjoint a b))
    (Bool.not (Bool.and (blocked ranks (groupWord a) (groupWord b))
      (blocked ranks (groupWord b) (groupWord a))))

theorem ordered_fork_packing_of_mask_checks {n : Nat} {f : (Fin n → Bool) → Bool}
    (pairs : List (PairDatum n)) (ranks : List RankDatum) (budget : Nat)
    (pairsChecked : (pairs.all fun w => w.check f) = true)
    (ranksChecked : (ranks.all fun w => w.check f) = true)
    (packingChecked :
      checkWeightBound (compatibleFromMasks ranks) (fun g => g.card - 1) (fun _ => true)
        budget (groupsFromMasks n pairs) = true) :
    OrderedForkPackingBound f (budget + 1) := by
  apply ordered_fork_packing_of_weight_check (groupsFromMasks n pairs) (compatibleFromMasks ranks)
    budget _ _ packingChecked
  · intro g large noConflicts
    have valid : ∀ w ∈ pairs, w.check f = true := List.all_eq_true.mp pairsChecked
    have mayChoose : allows pairs (groupWord g) = true := allows_of_no_conflicts pairs valid _
      (by simpa only [support_groupWord] using noConflicts)
    apply List.mem_map.mpr
    refine ⟨groupWord g, ?_, support_groupWord g⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.ofBits_lt_two_pow _),
      Bool.and_eq_true_iff.mpr ⟨mayChoose, by simpa only [support_groupWord] using (decide_eq_true large)⟩⟩
  · intro a b apart oneWay
    have valid : ∀ w ∈ ranks, w.check f = true := List.all_eq_true.mp ranksChecked
    have noBoth : (blocked ranks (groupWord a) (groupWord b) &&
        blocked ranks (groupWord b) (groupWord a)) = false := by
      cases both : (blocked ranks (groupWord a) (groupWord b) &&
          blocked ranks (groupWord b) (groupWord a))
      · rfl
      · exfalso
        obtain ⟨inOrder, reversed⟩ := Bool.and_eq_true_iff.mp both
        rcases oneWay with forward | backward
        · exact forward (by simpa only [support_groupWord] using (blocked_rank ranks valid inOrder))
        · exact backward (by simpa only [support_groupWord] using (blocked_rank ranks valid reversed))
    simp [compatibleFromMasks, apart, noBoth]

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.Graph55847Packing

open PEqualNP.MetaComplexity FirstForkBounds FirstForkNumeric

def edges : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7]

def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

private def pairWitnesses : List (PairDatum 8) := [
  ⟨0, 4, 4, 64⟩,
  ⟨0, 5, 8, 20⟩,
  ⟨0, 6, 2, 16⟩,
  ⟨0, 7, 0, 16⟩,
  ⟨1, 4, 4, 128⟩,
  ⟨1, 5, 8, 20⟩,
  ⟨1, 7, 64, 16⟩,
  ⟨2, 5, 8, 64⟩,
  ⟨2, 6, 2, 32⟩,
  ⟨2, 7, 0, 32⟩,
  ⟨3, 7, 0, 66⟩,
  ⟨4, 6, 0, 1⟩,
  ⟨4, 7, 0, 1⟩,
  ⟨5, 6, 0, 1⟩,
  ⟨5, 7, 0, 1⟩]

private def rankWitnesses : List RankDatum := [
  ⟨3, 192, 0, 1, 2, 0, 64, 128⟩,
  ⟨192, 3, 0, 64, 128, 0, 1, 2⟩,
  ⟨5, 48, 8, 1, 4, 0, 16, 32⟩,
  ⟨48, 5, 8, 16, 32, 0, 1, 4⟩,
  ⟨6, 192, 0, 2, 4, 0, 64, 128⟩,
  ⟨192, 6, 0, 64, 128, 0, 2, 4⟩]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem packing_bound : OrderedForkPackingBound target 4 :=
  ordered_fork_packing_of_mask_checks pairWitnesses rankWitnesses 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def pivotRows : Array Nat := #[16, 16, 32, 64, 1, 1, 1, 1]

private def pivot (i : Fin 8) (value : Bool) (j : Fin 8) : Bool :=
  if j = i then value else (pivotRows.getD i.val 0).testBit j.val

private theorem pivot_changes : ∀ i : Fin 8,
    target (pivot i false) ≠ target (pivot i true) := by decide +kernel

theorem target_essential : SignedNormalization.Essential 8 target := by
  intro i
  refine ⟨pivot i false, pivot i true, ?_, pivot_changes i⟩
  intro j different
  simp [pivot, different]

theorem circuit_size_lower (size : Nat) (has : HasCircuitSize 8 target size) :
    11 ≤ size := by
  have bound := hasCircuitSize_lower_of_ordered_fork_packing (by decide) target_essential has packing_bound
  omega

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.Graph55847Packing

namespace PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.OneNot55847

open PEqualNP.CircuitLowerBounds

def edges : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7]

def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

def tape : List Gate :=
  [⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [9, 10]⟩,
   ⟨.and, [2, 5]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [14, 3]⟩,
   ⟨.or, [6, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [18, 17]⟩]

def witness : Circuit := ⟨tape, 19⟩

theorem tape_legal : ∀ g ∈ tape,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [tape]

theorem tape_count : tape.length = 12 := by decide

private def extend (a0 a1 a2 : Bool) (tail : Fin 5 → Bool) (i : Fin 8) : Bool :=
  if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2 else tail (Fin.ofNat 5 (i.val - 3))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem tape_tail_exact (a0 a1 a2 : Bool) :
    ∀ y : Fin 5 → Bool, witness.eval (List.ofFn (extend a0 a1 a2 y)) = target (extend a0 a1 a2 y) := by
  cases a0 <;> cases a1 <;> cases a2 <;> decide +kernel

theorem tape_exact : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = target x := by
  intro x
  let tail (i : Fin 5) := x (Fin.natAdd 3 i)
  have same : extend (x 0) (x 1) (x 2) tail = x := by
    have index : ∀ i : Fin 8, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      decide +kernel
    funext i
    rcases index i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [← same]
  exact tape_tail_exact (x 0) (x 1) (x 2) tail

theorem replacement_at_size (size : Nat) (h : 12 ≤ size) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ size ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gates' o').eval (List.ofFn x) = target x :=
  ⟨tape, 19, tape_legal, by simpa only [tape_count] using h, tape_exact⟩

end PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.OneNot55847

theorem PEqualNP.Outside.L_meta_55847 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
:= by
  intro gates output legal _ computes
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, output⟩
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g included
    obtain ⟨basis, arity⟩ := legal g included
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using basis, arity⟩
  exact PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.FirstForkBounds.monotone_replacement_of_ordered_fork_packing (by decide) PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.Graph55847Packing.target_essential PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.Graph55847Packing.packing_bound
    PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.OneNot55847.tape PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.OneNot55847.witness.output PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.OneNot55847.tape_legal
    (by rw [PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.OneNot55847.tape_count] <;> decide +kernel) PEqualNP.Outside.L_meta_55847_aux.LocalInvestigation.OneNot55847.tape_exact C fan computes
