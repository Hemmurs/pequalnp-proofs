import PEqualNP.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
namespace PEqualNP.Outside.L_meta_55659
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace ForestCore
def pn (a b : Nat) : Nat := a * 1000000000000000000 + b
open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]
def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)
private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩
def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)
private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]
private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b
private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]
def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a
def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]
theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih
theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩
theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _
theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl
theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩
def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs
theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig := [(BitVec.ofNat 512 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)),(BitVec.ofNat 512 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc)),(BitVec.ofNat 512 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0)),(BitVec.ofNat 512 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),(BitVec.ofNat 512 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),(BitVec.ofNat 512 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000)),(BitVec.ofNat 512 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000)),(BitVec.ofNat 512 (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000)),(BitVec.ofNat 512 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000))]
def graph : Sig := (BitVec.ofNat 512 (0xfffffffffffffffffffffffffffefffefffffffefffffffcfefefafaeeccaa00fffffffffffffffffffffffffffefffefffffffefffffffcfefefafaeeccaa00))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv
theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega
def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i,(asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp
def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),(∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))
theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))
theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h
abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)
theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)
def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none
theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)
theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]
theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp
theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm
def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)
theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)
theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 8).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def qG_ (m : Nat) : Sig :=
  let x := vertex m
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001)
  | 1 => (0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001)
  | 2 => (0x100000000000000010000000000000000000000000000000000000000000000010000000000000001)
  | 3 => (0x10000000000000000000000000000000000000000000000000000000000000001)
  | 4 => (0x1000000000000000100000000000000010000000000000001)
  | 5 => (0x100000000000000000000000000000001)
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem qP_ (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := qG_ m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def columnPairs (m z s : Nat) (G : Sig) : List (Sig × Row × Row) :=
  if m.testBit 8 then
    (selected s).map fun (i,a) =>
      let v := 1 <<< i
      let candidates := (0 :: (List.range 8).map (fun j => 1 <<< j))
      let r := (candidates.find? fun r =>
        bit (Fin.ofNat 512 r) G != bit (Fin.ofNat 512 (r ||| v)) G).getD 0
      (a, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| v))
  else supportPairs (z/512+80) s
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (qG_ q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (qG_ q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (qG_ q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (qP_ _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (qP_ _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (qP_ _ ok.1.1.1) (qP_ _ hh.1.1) (valid q) p bank hr ha)
def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (qG_ old) && plainWord (qG_ old) && (varsX old).all plainWord) && properB (qG_ rep) &&
    checkMap (swaps.map swapRows) (varsX old) (qG_ old) (varsX rep) (qG_ rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (qG_ rep) L) : Lower u (varsX old) (qG_ old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (qP_ _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (qP_ _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (qG_ e.1) e.2) (q : Nat) :
    Lower u (varsX q) (qG_ q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2
def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True
theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩
theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)
def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)
theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he
abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨by omega,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (qG_ m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases ht : m.testBit 8 = true
  · simp only [bit,qG_,liftGoal,if_pos ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
  · simp only [bit,qG_,liftGoal,if_neg ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl
def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0
def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)
theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs
theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto
theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)
theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)
def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)
def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)
def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)
def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []
def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (qP_ _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (qG_ e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (qG_ m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]
def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]
theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs
theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js
theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)
theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
end ForestCore
end PEqualNP.Outside.L_meta_55659
namespace PEqualNP.Outside.L_meta_55659.ForestCore
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
private def proofWord80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0
def g82Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f)),(BitVec.ofNat 152 (0x49204920492049204920492049204920492049))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7)),(BitVec.ofNat 152 (0x92409240924092409240924092409240924092))),(0x0,0x0),((BitVec.ofNat 152 (0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8)),(BitVec.ofNat 152 (0x24812481248124812481248124812481248124))),(0x0,0x0),(0x0,0x0)]
def g82C : List ColumnInfo := []
def g82A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
def g82D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g82L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g82D3)
  | _ => emptyPacking
def g82I (_ _ : Nat) : Option (Nat × Nat) := none
def g82 : Forest := ⟨82,3,fun i => g82Y[i]?.getD (0,0),g82C,g82A,g82L,g82I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82P3_0 : block g82 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g82B3 : block g82 3 0 1=true := g82P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82T : checkedTables g82 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g82 0 0 0 = true)
  · exact (rfl : block g82 1 0 0 = true)
  · exact (rfl : block g82 2 0 0 = true)
  · exact g82B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82G : graphValid g82 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low82 : Lower true (varsX 82) (qG_ 82) 4 := lower_forest (g:=g82) (i:=0) (hints:=16842816) (before_sound [] baseKnown) g82G g82T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior506 : Lower true (varsX 506) (qG_ 506) 7 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 208 0)
    (raw := varsX 506) (T := qG_ 506) (xs := [(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior505 : Lower true (varsX 505) (qG_ 505) 7 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 208 0)
    (raw := varsX 505) (T := qG_ 505) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior504 : Lower true (varsX 504) (qG_ 504) 6 := by
  have h := lift_ok (u := true) (ms := ([33,50,84]).map swapRows ++ fixRows 144 0)
    (raw := varsX 504) (T := qG_ 504) (xs := [(inputs.getD 4 zero,64,80),(inputs.getD 7 zero,8,136)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80),(inputs.getD 7 zero,8,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior499 : Lower true (varsX 499) (qG_ 499) 7 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 162 0)
    (raw := varsX 499) (T := qG_ 499) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior498 : Lower true (varsX 498) (qG_ 498) 6 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 96 0)
    (raw := varsX 498) (T := qG_ 498) (xs := [(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior497 : Lower true (varsX 497) (qG_ 497) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 160 0)
    (raw := varsX 497) (T := qG_ 497) (xs := [(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior496 : Lower true (varsX 496) (qG_ 496) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 496) (T := qG_ 496) (xs := [(inputs.getD 5 zero,64,96)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,64,96)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior491 : Lower true (varsX 491) (qG_ 491) 7 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 194 0)
    (raw := varsX 491) (T := qG_ 491) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior490 : Lower true (varsX 490) (qG_ 490) 6 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 192 0)
    (raw := varsX 490) (T := qG_ 490) (xs := [(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior489 : Lower true (varsX 489) (qG_ 489) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 192 0)
    (raw := varsX 489) (T := qG_ 489) (xs := [(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior488 : Lower true (varsX 488) (qG_ 488) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84]).map swapRows ++ fixRows 128 0)
    (raw := varsX 488) (T := qG_ 488) (xs := [(inputs.getD 7 zero,8,136)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,8,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior483 : Lower true (varsX 483) (qG_ 483) 6 := by
  have h := lift_ok (u := true) (ms := ([16,84]).map swapRows ++ fixRows 130 0)
    (raw := varsX 483) (T := qG_ 483) (xs := [(inputs.getD 1 zero,32,34),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior482 : Lower true (varsX 482) (qG_ 482) 5 := by
  have h := lift_ok (u := true) (ms := ([84,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 482) (T := qG_ 482) (xs := [(inputs.getD 6 zero,32,96)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,32,96)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior481 : Lower true (varsX 481) (qG_ 481) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84]).map swapRows ++ fixRows 128 0)
    (raw := varsX 481) (T := qG_ 481) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior480 : Lower true (varsX 480) (qG_ 480) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,116,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 480) (T := qG_ 480) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior475 : Lower true (varsX 475) (qG_ 475) 7 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 146 0)
    (raw := varsX 475) (T := qG_ 475) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior474 : Lower true (varsX 474) (qG_ 474) 6 := by
  have h := lift_ok (u := true) (ms := ([67,118]).map swapRows ++ fixRows 80 0)
    (raw := varsX 474) (T := qG_ 474) (xs := [(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior473 : Lower true (varsX 473) (qG_ 473) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 144 0)
    (raw := varsX 473) (T := qG_ 473) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior472 : Lower true (varsX 472) (qG_ 472) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,117,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 472) (T := qG_ 472) (xs := [(inputs.getD 4 zero,64,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior467 : Lower true (varsX 467) (qG_ 467) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 130 0)
    (raw := varsX 467) (T := qG_ 467) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior466 : Lower true (varsX 466) (qG_ 466) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 466) (T := qG_ 466) (xs := [(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior465 : Lower true (varsX 465) (qG_ 465) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 128 0)
    (raw := varsX 465) (T := qG_ 465) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior464 : Lower true (varsX 464) (qG_ 464) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 464) (T := qG_ 464) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior459 : Lower true (varsX 459) (qG_ 459) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 130 0)
    (raw := varsX 459) (T := qG_ 459) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior458 : Lower true (varsX 458) (qG_ 458) 5 := by
  have h := lift_ok (u := true) (ms := ([67,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 458) (T := qG_ 458) (xs := [(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior457 : Lower true (varsX 457) (qG_ 457) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 128 0)
    (raw := varsX 457) (T := qG_ 457) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior456 : Lower true (varsX 456) (qG_ 456) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 456) (T := qG_ 456) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior451 : Lower true (varsX 451) (qG_ 451) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,117,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 451) (T := qG_ 451) (xs := [(inputs.getD 1 zero,128,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,128,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior449 : Lower true (varsX 449) (qG_ 449) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 449) (T := qG_ 449) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior443 : Lower true (varsX 443) (qG_ 443) 7 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 146 0)
    (raw := varsX 443) (T := qG_ 443) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior442 : Lower true (varsX 442) (qG_ 442) 6 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 144 0)
    (raw := varsX 442) (T := qG_ 442) (xs := [(inputs.getD 4 zero,2,18),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,2,18),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior441 : Lower true (varsX 441) (qG_ 441) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 144 0)
    (raw := varsX 441) (T := qG_ 441) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior440 : Lower true (varsX 440) (qG_ 440) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 440) (T := qG_ 440) (xs := [(inputs.getD 4 zero,128,144)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,128,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior435 : Lower true (varsX 435) (qG_ 435) 6 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 34 0)
    (raw := varsX 435) (T := qG_ 435) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior434 : Lower true (varsX 434) (qG_ 434) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 434) (T := qG_ 434) (xs := [(inputs.getD 5 zero,2,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior433 : Lower true (varsX 433) (qG_ 433) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 433) (T := qG_ 433) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior427 : Lower true (varsX 427) (qG_ 427) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 130 0)
    (raw := varsX 427) (T := qG_ 427) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior426 : Lower true (varsX 426) (qG_ 426) 5 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 426) (T := qG_ 426) (xs := [(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior425 : Lower true (varsX 425) (qG_ 425) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 425) (T := qG_ 425) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior424 : Lower true (varsX 424) (qG_ 424) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 424) (T := qG_ 424) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior419 : Lower true (varsX 419) (qG_ 419) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 419) (T := qG_ 419) (xs := [(inputs.getD 1 zero,32,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior418 : Lower true (varsX 418) (qG_ 418) 4 := by
  have h := lift_ok (u := true) (ms := ([84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 418) (T := qG_ 418) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior417 : Lower true (varsX 417) (qG_ 417) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 417) (T := qG_ 417) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior411 : Lower true (varsX 411) (qG_ 411) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 18 0)
    (raw := varsX 411) (T := qG_ 411) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior410 : Lower true (varsX 410) (qG_ 410) 5 := by
  have h := lift_ok (u := true) (ms := ([67,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 410) (T := qG_ 410) (xs := [(inputs.getD 4 zero,2,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,2,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior409 : Lower true (varsX 409) (qG_ 409) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 409) (T := qG_ 409) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior403 : Lower true (varsX 403) (qG_ 403) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 403) (T := qG_ 403) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior402 : Lower true (varsX 402) (qG_ 402) 4 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 402) (T := qG_ 402) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior401 : Lower true (varsX 401) (qG_ 401) 4 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 401) (T := qG_ 401) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior395 : Lower true (varsX 395) (qG_ 395) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 395) (T := qG_ 395) (xs := [(inputs.getD 1 zero,8,10)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior394 : Lower true (varsX 394) (qG_ 394) 4 := by
  have h := lift_ok (u := true) (ms := ([67,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 394) (T := qG_ 394) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior393 : Lower true (varsX 393) (qG_ 393) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 393) (T := qG_ 393) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior379 : Lower true (varsX 379) (qG_ 379) 7 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 82 0)
    (raw := varsX 379) (T := qG_ 379) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior378 : Lower true (varsX 378) (qG_ 378) 6 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 80 0)
    (raw := varsX 378) (T := qG_ 378) (xs := [(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior377 : Lower true (varsX 377) (qG_ 377) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 80 0)
    (raw := varsX 377) (T := qG_ 377) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior376 : Lower true (varsX 376) (qG_ 376) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84]).map swapRows ++ fixRows 16 0)
    (raw := varsX 376) (T := qG_ 376) (xs := [(inputs.getD 4 zero,64,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior371 : Lower true (varsX 371) (qG_ 371) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 34 0)
    (raw := varsX 371) (T := qG_ 371) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior369 : Lower true (varsX 369) (qG_ 369) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 32 0)
    (raw := varsX 369) (T := qG_ 369) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior363 : Lower true (varsX 363) (qG_ 363) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 66 0)
    (raw := varsX 363) (T := qG_ 363) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior362 : Lower true (varsX 362) (qG_ 362) 5 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 64 0)
    (raw := varsX 362) (T := qG_ 362) (xs := [(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior361 : Lower true (varsX 361) (qG_ 361) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 64 0)
    (raw := varsX 361) (T := qG_ 361) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior360 : Lower true (varsX 360) (qG_ 360) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 360) (T := qG_ 360) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior355 : Lower true (varsX 355) (qG_ 355) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84]).map swapRows ++ fixRows 2 0)
    (raw := varsX 355) (T := qG_ 355) (xs := [(inputs.getD 1 zero,32,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior353 : Lower true (varsX 353) (qG_ 353) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 353) (T := qG_ 353) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior347 : Lower true (varsX 347) (qG_ 347) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 18 0)
    (raw := varsX 347) (T := qG_ 347) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior345 : Lower true (varsX 345) (qG_ 345) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 16 0)
    (raw := varsX 345) (T := qG_ 345) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior339 : Lower true (varsX 339) (qG_ 339) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 2 0)
    (raw := varsX 339) (T := qG_ 339) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior337 : Lower true (varsX 337) (qG_ 337) 4 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 0 0)
    (raw := varsX 337) (T := qG_ 337) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior331 : Lower true (varsX 331) (qG_ 331) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 2 0)
    (raw := varsX 331) (T := qG_ 331) (xs := [(inputs.getD 1 zero,8,10)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior329 : Lower true (varsX 329) (qG_ 329) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 329) (T := qG_ 329) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior315 : Lower true (varsX 315) (qG_ 315) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 18 0)
    (raw := varsX 315) (T := qG_ 315) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior314 : Lower true (varsX 314) (qG_ 314) 5 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 314) (T := qG_ 314) (xs := [(inputs.getD 4 zero,2,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,2,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior313 : Lower true (varsX 313) (qG_ 313) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 313) (T := qG_ 313) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior299 : Lower true (varsX 299) (qG_ 299) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 2 0)
    (raw := varsX 299) (T := qG_ 299) (xs := [(inputs.getD 1 zero,8,10)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior298 : Lower true (varsX 298) (qG_ 298) 4 := by
  have h := lift_ok (u := true) (ms := ([67,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 298) (T := qG_ 298) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior297 : Lower true (varsX 297) (qG_ 297) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 297) (T := qG_ 297) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
def generatedKnown : List (Nat × Nat) := [(506,7),(505,7),(504,6),(499,7),(498,6),(497,6),(496,5),(491,7),(490,6),(489,6),(488,5),(483,6),(482,5),(481,5),(480,4),(475,7),(474,6),(473,6),(472,5),(467,6),(466,5),(465,5),(464,4),(459,6),(458,5),(457,5),(456,4),(451,5),(449,4),(443,7),(442,6),(441,6),(440,5),(435,6),(434,5),(433,5),(427,6),(426,5),(425,5),(424,4),(419,5),(418,4),(417,4),(411,6),(410,5),(409,5),(403,5),(402,4),(401,4),(395,5),(394,4),(393,4),(379,7),(378,6),(377,6),(376,5),(371,6),(369,5),(363,6),(362,5),(361,5),(360,4),(355,5),(353,4),(347,6),(345,5),(339,5),(337,4),(331,5),(329,4),(315,6),(314,5),(313,5),(299,5),(298,4),(297,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by
  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior506
  · exact prior505
  · exact prior504
  · exact prior499
  · exact prior498
  · exact prior497
  · exact prior496
  · exact prior491
  · exact prior490
  · exact prior489
  · exact prior488
  · exact prior483
  · exact prior482
  · exact prior481
  · exact prior480
  · exact prior475
  · exact prior474
  · exact prior473
  · exact prior472
  · exact prior467
  · exact prior466
  · exact prior465
  · exact prior464
  · exact prior459
  · exact prior458
  · exact prior457
  · exact prior456
  · exact prior451
  · exact prior449
  · exact prior443
  · exact prior442
  · exact prior441
  · exact prior440
  · exact prior435
  · exact prior434
  · exact prior433
  · exact prior427
  · exact prior426
  · exact prior425
  · exact prior424
  · exact prior419
  · exact prior418
  · exact prior417
  · exact prior411
  · exact prior410
  · exact prior409
  · exact prior403
  · exact prior402
  · exact prior401
  · exact prior395
  · exact prior394
  · exact prior393
  · exact prior379
  · exact prior378
  · exact prior377
  · exact prior376
  · exact prior371
  · exact prior369
  · exact prior363
  · exact prior362
  · exact prior361
  · exact prior360
  · exact prior355
  · exact prior353
  · exact prior347
  · exact prior345
  · exact prior339
  · exact prior337
  · exact prior331
  · exact prior329
  · exact prior315
  · exact prior314
  · exact prior313
  · exact prior299
  · exact prior298
  · exact prior297
def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (0xffffe000e0c7625404060c38c004c007893673), BitVec.ofNat 152 (0xffffe4a40d1000000c02144940044002811231)),(BitVec.ofNat 152 (0x3000880a8180073c72007112611cb9c), BitVec.ofNat 152 (0x6f48d3540021e96564d60051126014294)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0),(BitVec.ofNat 152 (0xffffe01c0330e50c20198007c0980238660c1f), BitVec.ofNat 152 (0x901304a00006028809280880208220c0a)),(BitVec.ofNat 152 (0x6004010830c0e003f804e023c0780fe0), BitVec.ofNat 152 (0x190b72caa001e169a9b284a02240780d40)),(BitVec.ofNat 152 (0x380183e11c10301fc0007003c007ff000), BitVec.ofNat 152 (0x100a4280a00181412920050024005ca000)),(BitVec.ofNat 152 (0x1c001fc01e0203fe000038003fff800000), BitVec.ofNat 152 (0x2508025400212944204280019b5000000)),(BitVec.ofNat 152 (0x1fffe0000003fc0000003fffc000000000), BitVec.ofNat 152 (0x1ffc0000000012528000000000)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0)]
def generatedColumns : List ColumnInfo := [(1,0,506,0,7),(2,0,505,0,7),(3,0,504,0,6),(8,0,499,0,7),(9,0,498,0,6),(10,0,497,0,6),(11,0,496,0,5),(16,0,491,0,7),(17,0,490,0,6),(18,0,489,0,6),(19,0,488,0,5),(24,0,483,0,6),(25,0,482,0,5),(26,0,481,0,5),(27,0,480,0,4),(32,0,475,0,7),(33,0,474,0,6),(34,0,473,0,6),(35,0,472,0,5),(40,0,467,0,6),(41,0,466,0,5),(42,0,465,0,5),(43,0,464,0,4),(48,0,459,0,6),(49,0,458,0,5),(50,0,457,0,5),(51,0,456,0,4),(56,0,451,0,5),(58,0,449,0,4),(64,0,443,0,7),(65,0,442,0,6),(66,0,441,0,6),(67,0,440,0,5),(72,0,435,0,6),(73,0,434,0,5),(74,0,433,0,5),(80,0,427,0,6),(81,0,426,0,5),(82,0,425,0,5),(83,0,424,0,4),(88,0,419,0,5),(89,0,418,0,4),(90,0,417,0,4),(96,0,411,0,6),(97,0,410,0,5),(98,0,409,0,5),(104,0,403,0,5),(105,0,402,0,4),(106,0,401,0,4),(112,0,395,0,5),(113,0,394,0,4),(114,0,393,0,4),(128,0,379,0,7),(129,0,378,0,6),(130,0,377,0,6),(131,0,376,0,5),(136,0,371,0,6),(138,0,369,0,5),(144,0,363,0,6),(145,0,362,0,5),(146,0,361,0,5),(147,0,360,0,4),(152,0,355,0,5),(154,0,353,0,4),(160,0,347,0,6),(162,0,345,0,5),(168,0,339,0,5),(170,0,337,0,4),(176,0,331,0,5),(178,0,329,0,4),(192,0,315,0,6),(193,0,314,0,5),(194,0,313,0,5),(208,0,299,0,5),(209,0,298,0,4),(210,0,297,0,4)]
def genData3 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x48f30918301811398f11b2e8d9655c054423207a8e4f66d32aec100a884640f51c2ecda655d82015108c09ea385d9b52abb0c02a211143d9713b369957608054422227a8e1772d32aec180a884244f51c2ecda6e615701510)
def genData4 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x37edab56d432ec6b14c3b08b9ad2afaaaa92829ba5a91a328b218849fe7e1f27b1e6711a2639886097c5d9705a964579585494c519404e9344b9284891c459023b8e8388dc320c22f0b62c09c25890228841f8781c86c1986016854138481083c0d8300a824078180480c01800f201c652106654244c910f081c652197418244c910f041c655d9664d8201510e282ba5a548418244c910e281ba5a548418244c910e281b66a548418244c910e2819a4999241984cc910e2812a6599241984cc910e182ca52197418244c910e181ca52197418244c910e06198699a255c0558910d441b66c95764c0558910d421b66c9576500558910d302cb52106654244c910d301cb52106654244c910d301b06d948654244c910d281c6ee548418244c910d281ba6c148658244c910d281b6ee548418244c910d281b26599049984cc910d181b06d94865c244c910c463b9699a255c0558910c461b66cba955c0558910c383b9681a6520244c910c383a9ed9a0520244c910c382caee548418244c910c382baee548418244c910c381caee548418244c910c381baee548418244c910c381b06dba9520244c910c187a9edda6520244c910c153a9ecda855c0558910c153986cba36595701510c133a9ed1a855c0558910b303c66c148654244c910b283ca6c148658244c910b283c96d948418244c910b283c66c148658244c910b281c6ee548418244c910b183c76d948640244c910b183c66c14865c244c910b143c36a19255c0558910b123c46a19255c0558910b113c46e15764c0558910b113c36e1576500558910b107c76d948654244c910b087c76e948658244c910b053c36a19655c0558910b033c46a19655c0558910a943ca6d95764d8201510a463c9699a255c0558910a461c6ea5a255c0558910a461c2ea5a655c0558910a383ca6c148658244c910a383c96e948418244c910a383c9681a6520244c910a383c66c3a9520244c910a381caee548418244c910a381c9ae948418244c910a381c6ea5a0520244c910a381c0ea5a6520244c910a187ca6d94865c244c910a187c76dba9520244c910a153ca6e15764c0558910a153c36e3a955c0558910a133ca6e1576500558910a133c46e3a955c05589109941c9ecda655d82015109941c4ecda655d82015109941c2ecda655d82015109851c2ecda955d86015109383c66c3a9520244c9109381c6ee5a0520244c9109381c0ee5a6520244c9109187c76dba9520244c9109153c36e3a955c05589109151c2ee5a655d83015109151c2ecda6e6157015109133c46e3a955c05589108d13c46cba365957015108953c86cba365957015108953c36dba864957015108953c36cba865957015108951c2ecda6e6157015108933c46dba864957015108933c46cba865957015108517c46cba3661065d710) else (0xc0181c0181c030102822a0182a018100003022c018204801048010480103022c018260181a0181a0181a01810180604004801000000a08a8060a822a018250181000000000000000000000000000000048010480100000c0604000000c060400000000000000000000000000000000000))
def genIndex4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xd4d6f035fac0f03253f0f0f0612)
def genData5 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x8910cac334c920cbaa05886473a96995701562443238db752ab80ab1221919669964817558b10c8cb34c92c0baac58863a3a4e8998419424431c8cd32483309992218e46699049984cc910c70f52d329012264886385b6ea548091324430b9d4d50ab80ab122185cea5a855c0558910c2e750cb324ab80a88617398e999255c054430b9cc744cb2ae02a2185cae3a955c0558910c2e371d4aae02ac4886171a668b9855c05442ea1d9b4caba40a92217186c1964817558b10b7076cd029012264885b81b26412661332442d49db340a42c8992216a46d99241984cc910b3276ed329082264885987b76994809132442cb1dcb4cabb0402a21658ed9a955d8201510b2c76cd22aec100a885963b46995760805442cb1d934cabb0402a21654ed9a255d8301510b2a766d42ae02ac4885953b36995760805442ca9d934cabb0602a2164ced1a855c0558910b0e772d12aec300a885873b66895761805442c39d9352abb0c02a215e0aeb42641644c910ad876ccc24c822648855c3b76612059132442ab1dcb44ab80ab12215586cba955c0558910a8e772d32ae02ac4885471b6ea557015624429c8dca40cb309992214e1ee5a6520244c910a70b6dd4a9012264885173b96a157015624428b9dcb4cabb0402a2145cee5a255d8601510a2e770cb324ab80a885173b668b9855c054428b9d934dcc2ae02a2145c6e6a855c0558910a2e371d4aae02ac4885171b6e619255c054428b8d9730cb2ae02a213e0ed1a841a244c9109f0369d420d12264884d51b2e8d9655c054425e1d935283308992212f06cba9419844c910978365d420cc2264884b93b968906613324425c9db35290309992212e4ec9a941984cc910972374c920cc2664884997b76a526613324424b9db345cc2ae02a2125cec9a6e61570151092e36dd4324ab80a884971b2ea19655c054424abd9b52c02eab162124ded1a96017558b108f8772d420d122648847c3b26a580591324423e0dcf5083448992211f06cba9419844c9108f8365d4320b2264884597b468b93619754422aad9746cc20cbae210e5ed1a2e4d8759510833f68d1726c3aca887301b05219509132443980a420cca84899221ca06c148658244c910e502d2a420c122648872814868196091324438c0d8290cb84899221c6052197418244c910e282aecb326c100a886a81a652120591324431c1d4b40a4048992218e06c3a9520244c910c70352a420c1226488615398e8d9655c05442ca1d9b4cabb0402a21614ecda955d8601510a70772d029012264885383b952106091324429c0d8752a404899221454ee5a655d8301510a2a766d3730ab80a884953b369b9855c05443480d12ae02b0999221a4055da4a4d8201510d022aed300ac2664886111a955c0561332443088abb49c930602a21244ee95701584cc910) else (if j<2 then (0x172db8b9c50e226fab755b50da26c135bdab8d49694b4259eccf06683329954ca46423191888c31608aff97f0bf25efaf657a6bc05d6ae9d70eb745b0ad39690b4259e2cd9660b105782ba95aeac4558aa454e2a5e525a915464a124ffa7e53e69ed4ed26e931a9874b3a55129c93b49aa4551ea8e246e23591a08bd455229113c88b442a1fd0d8859429a13508e83441720a104480f3fe1fd8fe07ea3f21f44f7c7b83cc1de0eca75f3ac9ce4e667203869be8db46c73609aecd6a6af3549a8cd3a69734899c4cd666532f9930c72633316989cc4261b30a983cc126032fe97dcb4654f27d92d08c040c1dc0d906542d6141092048423c11b07f035016e0b405882b812207402b80e803a0007a81b65210609132443d40d8290b12c899221ea061162601644c910f502d29024cc2664887a81486896059132443d40a42c4982c899221ea04999241984cc910f28766d32aec100a887941b655d9360805443c30db2aecb30402a21e186c9576498601510f0c33083240baac5887853b36a55761805443b40a42c4c82c899221d506c95764c0558910ea4364abb2802ac4887461a66495701562443a30cb344ab80ab1221d18659924197540b10e8c320cb240baac588746190649605d562c43a28db2aec980ab1221d0c6d9576500558910e70772d029012264887383b952106091324439c0db290c804899221ce06c148658244c910e70352a420c122648873819264126613324439c0a4744c82c899221ce04a52065984cc910e60b6ca432a12264887291966490661332443948cb3209330999221ca16e948658244c910e50b24b4a4cc2664887185b652197091324438b154324ab80ab1221c586a19255c0558910e2c330d12ae02ac488716190661205d562c438b0c8324c02eab1621c54ee5a655d8301510e2a766d3730ab80a88715398e8d9655c054438a95c2aec980ab1221c546e15764c0558910e26570abb2802ac4887131b855d94015624438395432cab80ab1221c1c6a19655c0558910e0e330d32ae02ac488707196661065d502c43838c8330b02eab1621c1c641966017558b10e0cb2cc9300baac5886e83b46992059132443740d3290902c899221ba069943481644c910dd0348b1300b2264886e81a45893059132443630d4a0c902eab1621b18699a255c0558910d70574a420c12264886b81ba52106091324435c0d4a409330999221ae0691a2419844c910d70340d329012264886b812a6490661332443550d3290902c899221aa869162601644c910d52352b120cc2664886a916968906613324434b0d4b4cabb0402a21a58699a455d8201510d2a771d1b2cab80a886953b3ea19655c054434a9d9b4dcc2ae02a21a54ea3a36595701510d2a34cd12aec180a886871a968957618054432b1d4b44ab80ab12219586cba955c055) else (0x1806048300141060620c04000a0220c04081030202210603300819083008110801902030206040400480109002120a02041200400000906010209060102202028b804137806081360a01010122008009bc036010300004de01b008190614081026f00d8040c0a0a5030209002a04042400c081810140814101182010302980c080c0a603020282940c08240c0408847204094080848140810480100000a0200012004240081822c0305206040280b01810000000286ac040986b41008081003020050400b0d6808130d68081048010900203010109050102090020000481816033010204dd01a808180c1460604a040403060205052818128d6408140801000020300c818100060602000c1805818080000c0c040000606021100400000024008480100136c040813740409808080018d5408100a0c058080d010131ac8102302020000000000000488a40c10000120404c08080000000000000000822c50826d00d8054020d0b8811628600d8058020c822c50826d00d8054020c822650a01980a80416171022c50c01b00b004190458a104da01b00a8041a171022a50c01a80b0041a86b014e0840330110041805e01600a281042113284136406602901062115284136406a029010645c208900c804100000211026c80c40411170822650a01980a8041884409b203101040000004e32040c28104013b0820318041004e32080c481040138c81030a041004ec2080c601040138c81030a041217908f83e41da0c705082540a9ffafdd7e53eddf2ef917bf3dade96f387993cb1e4cf067733b4dd80ea0746b9e9ce8e6)))
def genIndex5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1c0381d6941072bb8f00780309fa1db20f80169be004a2f80203fe00e269060c5a019f001ad902275240b7803c00e409c67801c1fe00f0000abc00054f000a4bc00644f0060c3c01e0041af803c01e09f007800009829f007803c0013eda77803c00a37f004954c01215421f803e1de0061b6c32ca2283eaad6d14a6128acc6d20c44c32e18f800c1de00823f803c0023cba9d85cc77e00e986c7d27a532a1f6547c01e00f00780365fe085a49228c99e00005092e673a1e29d0809c9c02ef007463c00489303f80088ca23e24780363be00290a4cfc01e00886e43fc01224f007802c50406fa36e65835e00f9c4d3fc01e00f00355a42601471c20afc01a0c7d47803c01e00f0054f3c42b1a92b6473c01c2f722a4b9521744f00032ba77e00510550fc00412f006c7bc01e0081ee06d353242f007803c01e00298f803c01e006137803494f1b405ff1f44b41c7a15817c01e00d00ac834a480d713f802020e49b9f80d36a0a3fe8c90b2066000d2000462d8c4c21825130431088648450200661cc02)
def genData6 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0x10ce464196613324433914864164cc910ce45219059132443387a9520244c910ce15219609132443173986595701510c5ce619255c05443171a6e615701510c5c68b9855c054431719855c0558910be0e894059132442f81a6d09044c910be06834259132442ec1a6c9d064c910bb069a9241932442ec1a6989064c910bb069a3049932442ec1a6483644c910bb06992059132442ec1a3c9d6058910bb068f2158162442ec1a2da1064c910b98e816549952442e61a6d412654910b54e8d9655c05442bc1a241b844c910af06890660e52442bc1a24198390910ae8ea14241842442b91a948184cc910ae46a50661332442b91a241984cc910a5cea19655c05442973a86495701510a5c69b9855c05442971a2e6157015109f0e8990591324427c1a9c9d064c9109f06a562419324427c1a949b044c9109f06a520d91324427c1a9482764c9109f06a506891324427c1a9418244c9109f069b92411324427c1a2e61064c9109f068b94419324427c1a0e49644c91095cea55701562442557a3661065d710e5055e936080544394157a0d8201510e5055d93608054439415760e8201510e5055d836080544392157a118201510e4855d8460805443921426017510b10e4495e05613324439115701584cc910e1855e86608054438615761a8201510e1855d866080544385157a198301510e1455d86a0c05443851576198301510e09509865d442c435419255c05cc910d4455d940173244350950652835c850d184199201975c434515765805cc910d144199301975c4338148640244c910cc1521950913244328548658244c910c6152197091324431615764880d4d10c5855d9220265443161576488059510c5855d92201534431609855d2054910c54661570173244315157e498301510c5455d93203524431515764c8099510c5455d93201654431515764c8054910c54261574c1534431315765080d4910c4c55d9420152443125985097510b10c4654194e097314311575652839cb10c455d594a0e62c43115756528384b10c455d594a0e02c43115576528394b10c1c6199021975c430715765880d4d10c1c55d9620352443071576588054d10c1c55d96201524430709855d6059510c196199221975c430558664c865d710ae06929360805442b81a201584cc910ac4a977061332442a91a601584cc910a58ea157a0805442963a855d8201510a54ea157a0c05442953a855d8301510a49ea1425d442c42915a59c584cc810a1cea157a1805442871a7d81859c6609586879754172142553a955c05cc9109546879754173142515a4a4e825d71091cea50601975c42471a5a5f86419108e46a40561332442391a4e4983015108e1ea54809132442171a9d62570151085c6a687d4353442171a9a1f50d491085c6a687d4265442077a9618865d710) else (if j<2 then (0x4910b596a5205d562c42d57a36595754910b1de999255d65442c75a95817558b10af8e899460162442bd3a9419844c910af4ea10661132442bd3a6641844c910af4e8d0661132442bd1a9419844c910af46a10661132442bd1a3419844c910aec6918059132442b95a949984cc910adce958781562442b72a9d418654910adc6978781562442af3a661d0654910a7ce81985d5624429f1a0a617558910a7c682785d5624429d7a7659844c910a75e8d985d5624429b7a46617558910a5dea5805d562c42977a66617540b10a5de81985d562c42975a96017558b10a5d6a10660975c427e3a265d65409109f8e8990591324427e1a2e4d06509109f4ea506611324427d3a8641644c9109f4e9998411324427d3a4661064c9109f4e8d97595024427d3a3641644c9109f46a580591324427d1a94c1644c9109f46a394419324427d1a4e61064c9109f469393419324425d7a7661644c91097568b9361975442577a2661065d7108fcea587815624423f3a8641644c9108fce9998411324423f3a4661064c9108fce9192e0d064423f3a366106509108fce81985d9524423f1a9e1e05589108fc6a580591324423f1a8e4d06509108fc69393601624423f1a3e5180589108fc68397619524423f1a0a6175589108f5e8d985d9524423d5a2e4d87595108ede91985d9524421f7a7661644c910877e8d985d9524421dda2e4d875951086fe91985d952443e8342581644c910fa05894059132443c616255d0654910f18419205d562c43b824841a244c910ee06814809132443b8148481644c910ee05210609132443b812948184cc910ee04812661332443b21424198510910eb058906e1132443ac1624198394910eb05890660e42443aa1685090610910ea85918049942443aa1426418610910ea45a50661332443a916241984cc910ea45216059332443a9148581644c910ea15216259132443a6165e012654910e685098741842443961a955d8201510e586995760805443961a455d8201510e5855d9660805443951a655d8301510e546895760c0544394950619835c850e1c6a55761805443871a255d8601510e1c6016841975c438716855d0654910e1c55d926180544378392501644c910de0d09905913244374106654244c910db0e4960591324436c1a0658244c910db064960d91324436c16949b044c910db05a506891324436c169418244c910db058b94419324436c162643644c910db058990591324436c10664f2058910da86516241942443661656490654910d9855992815624435c197418244c910d5864957419524435619255c0558910d58641925d502c435515764c0558910d4c55d94015624434719655c0558910d19659925d562c433c29841a244c910cf065993608054433a1985090610910ce468194a0e624433919264184cc9) else (0x44c910ee46814859132443b919241984cc910ee46412661332443b9184619044c910ee46118059132443b91484d9044c910ee45213059132443b9143601644c910ee44819661332443b85a6520244c910ee14a52661332443b61574818654910eb858b805d952443ae16261d0654910eb85898141952443ae162601644c910eb45a50661132443ad168419844c910eb458d0661132443ab148581644c910ea95216259132443a956949984cc910e9ce958059562443a716855d0654910e9c5a15141952443a716561d0654910e9c5958141952443a71566017558910e995958749952443a65656052654910e5cea19655c05443973a86495701510e5caa15701562443971a855c0558910e5c6995760805443971a255d8601510e5c661065d502c43971856017558910e5c55f9061952443971096017558b10e5c4210660975c43965984817558b10e59649805d562c438e96261d0654910e395e1625d9524438e56261d1654910e39589815d9524438796855d0654910e1e5958741952443875985817558b10e1d659805d562c4387568419825d710df0e9192419324437c3a3649064c910df0e8990591324437c392619044c910df0e4980591324437c1a941a244c910df06a506091324437c1a7649064c910df069192419324437c198499044c910df066120591324437c193481644c910df064994419324437c19061a244c910df060196891324437a3a46490650910de8651924194244379198501644c910de464d405913244379148641644c910de450d9059132443763a56490654910dd8655205d952443761954811654910dd86495741952443761925450654910db8e8996411624436e19649e0558910db8659205d5624436e19259e0558910db858990591324436e127e416558910db466160591324436d193581644c910d9a5959241952443665955897654910d996556245952443573a955c0558910d5c6615701562443571966495701510d5c641965d502c43569954817654910d5a6495741952443565926597540b10d59649905d562c43557a3661065d710d39659925d5624434e5965c97558910d39659215d562443475966417558b10d1b655625d9524433e3a86490690910cf8e8998419424433e198481644c910cf4e8d98419324433d1a364b8341910cf466136411324433d1984c1644c910cf464d80591324433d190659844c910cf462586411324433d189601644c910cec52190591324433959265984cc910cbc66160591324431af94e498759120c5d661965d502c43175986417558b10bf0ea10689132442fc3a2651064c910bf06a10689132442fc1a2419844c910be46918059132442f91a44c1644c910bb8e899458162442ee1a6481644c910b5ce999255c05442d73a26595701510b5c6a5065d502c42d67a2659575))) else (if j<5 then (if j<4 then (0xf361e633cb47944f241e453c7878ccf121e1b3c247824f001df73bdc77acef41ddf3ba0771cedc1daf3b4c768ceca1d8b3af875cceb81d673abc7554ea91d4f3a987524ea31d433a6874ace941d253a44747ce8e1d133a207434e851cfb39f073bce761ce339c07374e6a1ccb39907314e611cbf397872e4e581ca1393c726ce4c1c8f39187224e431c83390071f4e3d1c7738b87104e0d1bf3378c6e7cdb61b45363c6bf4d681ab5353469fcd291a3134086744cd5198332c46474c8118d531506204c2a182730005f4cbd3177f2ea45cacb7c16cb2d545a54b3416532c4c5844afb15e12b685664ac215632a90549ca7d14d9295851e4a23141927d84efc9c6135926584bfc96f12b12514495c915120323a046748bb1149224443d486a10bf213c420c834104d2064405c7fe0fdb1f803e947c50f691e903ce478c0ef71dac3aa47410e551c5038346f60dd11b6036546ba0d531a6434446780cdb197432946450c69189c308460f0bf717b82ebc5ca0b7916bc2d0c58e0aef15902ab45490a7714b8290451309ff13a426ac4c209691284249c47d08cd114021cc426080d0f9c1e9c3c007530e581c1436306870cc018e430905eb0b8816742b8054f0a4413ec26a04b9092411ac222041d07bc0f0c1d4038106b40c9c18002e505940abc14a026d049808c410b01fb03a806e40c9017702b804d408700e10168021c02d001b0000fe0d098641132443f8342601644c910fe06910689132443f8148499044c910fe05212059132443f8143481644c910fb06a56241932443ec1a7589064c910fb06896059132443ec168649064c910fb05a10689132443ec162651064c910fb05898059132443ec1624c1644c910fb05890661132443ea1945890650910fa85912640d42443ea162501644c910fa45216059132443e9143581644c910fa15216259132443e8543589644c910f985959049952443e6162d417654910f985895741952443e61625450654910f985592781562443e61564817558910f586995748152443d61a255c0558910f58649065d502c43d61754817654910f5855d9049952443d61574811654910f58425205d562c43d53a36595701510f38649605d562443ce17649e0558910f385d92760162443ce1764817558910f385c9605d562443ce1215817558910f1c6995701562443c71a255d6059510f1c5a5065d502c43c71585817558910f1c55d6059572443c71575816544910f1c425605d562c43c696255d0654910f196995749952443c65964817558b10f19649605d562c43c65755897654910f195895745952443c65625457654910f19559725d562443bc1a241b844c910ef06890661132443bc1a24198390910ef06018689132443bc180499844c910ef04818661132443ba1985090610910ee85212059132443b91a65210) else (0x2201040208108088041008204202201040208108088041008c850a4c830a2c81060271204145104084045001c09c482052442022010642261e0184064046021808044042041040271208149108088041808044042041048b88228a109b8068048831e2e208a28426e01a01601078b88228a109b8068058041e2e208a28426e01a016010702081891080c808904182ac290284082462452442432422410a02c02502202091891491090c90890428082062442032022410602041451040c5084041809c4810514410210114007027420814c108088041808205244203242201060ab0a40a102091891491090c908904280b0094088082462452442432422410a02081491080c90880418081061441031021410602081491080c90880418082052442032422010602321429320c28b20419089878061019011808642361f019918c04c836021d08c07246301320c542361f019918c04c836021d08d88206301320f800642361f01c918c04c83180b409808c080402081891080c80890418082052442032422010602081891080c80890418082052442032422010602c02502202051851451050c508504280b409808c080402d0260230201228727406201a01300862a139d01820620430218888c78066060818816810c0882a139d0182062043021808104102101040204104084041008104102101040204104084041008c850a4c830a2c810622331f818a04b00140810410210104020210208204100820420220104027120414510408404180820420220104823c1f01c31890498318080440420410402081080880410a84e74060818810c0868a1c9d018806804c02192e108928426d0190150107020012a1000aa08006a041c08006844803802b020418702001611200e10a006c041c2ac290284080468458448438428418a02d0260230201262b4c44986530225f54bc0975d2e725bf4b6c969d2c925894b0095dd2b4255f4aac953529f25294a349445287250b4a0493fd27b24d54998932525d24ab4944927d248248148e491a522d2451489c90fd212241b4818900d1fd23f147dc8f7d1ee23d947ac8f4d1e823cd47888ed51d6239d47108dcd1b5236746a48cdd191231346208c1d18222fb45e48b8d16722bf456c8acd15522a745488a3d140227744e8897d1282247447c88bd110221d441c87fd0f821d5438086f50d7218d42f085a50b0214b428484e50982127423c84550862109420083c507420d941a0830505f20af4158828d04d2091411081fd038206740c8816d02c204f408c80f50172025403880350021ffb3ff07fbcff01fd73fa87f2cfe41fbf3f787eb4fd21fa13f307e3cfbd1f653eac7d34fa51f413e7c7cecf991f293e4c7c8cf8d1f173e1c7c14f7e1eed3dbc7b6cf691ecf3d8c7b0cf5d1eb73d507a7cf4e1e8d3d0879ec)) else (if j<6 then (0x1840222a101400c0062050041c0bc05805084201050224a101400c0064050041c3100eccd40c806806281a810803b2b8335222206204180bc06005805281a81061c002f018016014143080bc2b826d060058054051440832810b1350ae0a80a110088a840500300188140107c35020414c1040cc084041d0d409c0830430230106c35020418414410c08c041e0d50820530420330220107435027020c10c08c041b0d4081053041033021010702201461000c4080060041d0d409c0830430230106c35020414c1040cc084041c1204d409c08087d40060c602f0290222a1820806c04220d5082053042033022010702f016014910204144b044844030228a111000c0068050041c0bc05805030228a111000c0068050041c0bc058050302201400c006104b044844030224a111000c0064050041c4d40bc058050402f0160140c4d40bc058052440502201400c006104d40bc058051040513502f0290222a141e8041d0d42b82a028467450224a111000c0064050041d4d40bc0a4088a86082079010843512041451040c5084045002008c08047c850830811800783512081491080c9088041e0d4482052442032422010743512041451040c508404500201200e58d40c00a808c47e810802982211000e00c8068041c284053040032020018010702201400c006004140ed08b28446101b015010722209b018097206204183100ec0c806806025d819810802fa22018016014110a061c3080bc06005805044064b84224a109b406405404483222e208a28426e01a01601220c8235027020610608604198d40808518408318208107235027020a10a08a041a8d4080852840832820810743512041440c404144b0448440312c11211018f804144b044844063c402201400c00610088050030018402201400c00610088050030018413502f016014104d40bc058050810502201400c0061008805003001840c202900e00c100bc0a408a28501050ae0a80a129d804168d6080202901400e00c20414088050030018010502201400c00600414088a840500300188140107222aa1018206a05204180eccd40ca88806806281872b83352226a12066052041c8d409c081800402021420c204600148d409c082800402021420c204a00140bc058052440402201400c00600414088050030018010502201400c006004144d40bc058050810514701600e006204144b0448440302211000c006004144b0448440302900e00c404104d40bc058051010502f016014510110d448105144103142101070009d0820530420220106020810808804130d5082053042032022010702081080880410082042022010402081080880410082042022010402321429320c28b20418a84e7406a06081a810c08783b027320818a04b0018082042022010402081080880410082042) else (0x20c04440109b41800c0c26c830201801420c0c0101205044d4050200c042f803021350149100c830120c0403011350140a03010140406010180140826c050830301420c080881000022040120049204dc09e08808051200401370060808a01020060408206080848001820370060801810370060801810048301028472230201061281010c6022088181206044801001208802000000000204040508102004042f8030209b01400c0c2f826d05030040400c409b8160c26c060050830483b2b82040d060810200830100830120c04061810209bc06c040c26d0602206040820040003102fa05830be00c080301010600508303418a040a0d418060408a01821378060801208060808c8802023220088d409c08180040202046000c0c14c0c090d409c0830330105c350204040e8d508c20220531928681031200508c1a040448018200508018200408060488e0182a0404482810242304052010200052440200830111004010100604050141800c0883810005010103018040405010c420e0831010180406005028040601810208010228200a0d410201810005010031083820c40400480412014351204040d0d50114003635a0409810102080100050804480100012004000404050120e040ec030203b00c08020e04041604020e04009b604088381028d58102a0404030101491008030100c04060101804001406810160c6040a81018480448018200608c1a0404000030181880c08030182f81608030100c040a06a040a01810c60a10a0181018101604044801000000000a14a0c0a4101000000020601000008a48382000ec100060100050c060181000000000806048a483820000081810000000000000b812c112110100bc058052440453502f0290222a1820180e48d4850830810c00602982211000e00c8068041d08b28426d01b01501060c202f09b01601411020ca04222e208b28601b016010622209b01820620428318ae0888818810a0c50224a101400c0064050041c0a4050038030402201400c006100880500300))))
def genIndex6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x1e0014947800f001c1b9da02044b064829bc00307970e9e001c17f800e17c0642c9af800f00024bfc007800721be003c0078006003e003c007800f00146fbc0078005029e002425f800f001e003cd9faa1b261e0018d288544504a10a82668aca0b7e003c007959f001e000831601ce06cc5e2515003c0421e003c0078008242c477c004a20a31b28c7c003013f30de003c007800f001e003c007800f001a011438f80cf00daaa3c002098c0f7e0018a1f800a12e11f482c682a416682f44a9c280a0628520d10f800f001e00392b7072435a625104cf800f00021f7c00606ff001248bc005932f000c1a45b31802704ba27b80bf800f00142974bef800002b6049c31f800f000e09fc00289d9095a0e990b588660cbe00303c7800d0a6e199c2ed8512467e003c0070a7c0c3e003c0000470107e003c0038a27225c2f3846d8801021e00254ff8006181406fc006269f001e003c006a0ff001e003c007800c09fe003818081ec162a24fd0fcabce413e003c003838f001654892d72300263e00109b2aa7812cc15bd5eb8bbb04405b6c617800774709630444248545d0d9fd018b2af481e001422b0a0527ba633c00481871735223c004b1a80ebe003c00494df001e003c006891c0f8022bc00585fe447062011a115f3093e001cca2172b066c1dbc00383ea4f7e003c0078007377e003d9ff800f000ca1fc007800f00188b7c007800f42302c2c14f800f001e00104ff800d585c1ebc45b356f000e5bbc007800f000c9fe00b32a26359603d90aa89cf001e003c107a4160c8223a05d787ed059e2dbc000885545fee83c007800f001e003c00320af001c10cc44f2028033e003c00780094cdc08ec15ea054152e0ee4408a5bf001e003dcf282ea4fd82b7c5aa18af000a55d4497800e285e003c001ac050e6a1dc40568c1f001e003c00098fd4280aae420780000bd4157c0032182503e00209cf800611fe003c002859f001e00241bf800554aa864028227c1042a02009ba884e073e0000002257417fe003d05aaa6d121e0020557805a09d6b07d54f06cf001e001c38398ef001ca27c007800f001e001855a26850d4c2e144d70a4b0a501b501300a304cf85874a74a2c5507223350bba9ef00062d3c0018480549e003893706000692649041181af001219e8b2400bf0002173c007800c02341698234868448ea578c20b835f001e0015113a3f0825e00152cf087d137e000816f800703b00fe02bf80011504027c007800d27765cfc007800412b4134803f80041430918c5ba0ae150ce1ffc00781f7006a47fc007800897de001945227ae554ca83c002824d16520f45cfc00d1894411832402450804c73871845ce38100930d1c000308609000a08308218200604d1001ce0143871000801ed0840c00041040020800c1053145003483100002) else (0x106b256b60a3d15c00ee15faafc8a4f800f))
def genData7 (j : Nat) : Nat := if 20 ≤ j then 0 else (if j<10 then (if j<5 then (if j<2 then (if j<1 then (0x85741630ab4c90ae82a615669221975c42acd2441aeb88559a48765d710ab34902cbae215669201975c42acb24432eb88559648835d710ab2c90ecbae215659205975c42acb24032eb88556e5d509cc50aadcbaa0b98a155b9154173142ab3262ba0b1055625d5341530aab49d04bae215569321975c42aad26412eb88555a4c765d710aab4982cbae215569301975c42aab2b38a640855564e825d710aaac990cbae215559320975c42aab263b2eb8855564c165d710aaac980cbae215399415d05882a6d28412eb8854d650825d710a96ca88e922414f297e19064429e32fb04e33053c646505d850a74c90ce832214d99319d0644295b2c23a489051ee5d509d850a3dc8aa0bb0a14799615d058c28f32c2ba0b1051e6585741530a3ccaca0bb0a14799519d064428ed2c41aeb8851da58825d710a3acb106bae214759620975c427c32442a0c884f86488540d109f0c9101a9a213e192202654427c324402ca884f86488054d109f04c240a92213d39260c054427a33002e64884f464c85419109e8c990a812213d193203524427a326404ca884f464c80595109e8c9900a92213d0984c1534427632842a04884ec65080d49109d8ca100a92213a79850842c4274f30a1084884e5652839cb109caca5073922139594a0e62c4272b2941cc4884e56528394b109caca5072922139594a0e12c4272b2941c24884e56528380b109caca507012213739855c054426e7308280b884dce6105015109b94ad0f8322137295a1f034426e52b43e04884dca5687419109b94ad0e81a2137295a1d024426e52b40e0c884dca5681c0d109b94ad038122137191e1d501426d32442a0ca84d664c8541950979cc20c036212f196215034425e32c42a04884bc65880d4d10978cb101a92212f196201534425e32c402a4884bc26160595108f9cc2ae02a211f198dd7034423e331bae048847c66306dd5108ceca704b98c319d94e097318233b29c12e628467652839cb618ceca507396c119d94a0e72c4233b2941ce530c67652839ca608ceca507394a119d94a0e7284233b2941ce488467652839c8618ceca507390c119d94a0e7214233b2941ce40845ee6157015108bdcc2a1bb0a117a9815d058c22f5302ba0b1045e66357940508bbcc2ea3ae21177985d4754422ef30ba8c78845de617518b108bbcc2ea216211769895d150422eb30ba8c78845d6617518b108bacc2ea2162117597a1463c422eb2f428c58845d65e8510b108bacbd0a0b62117597a1413c422eb2f428258845d65687c19108bacad0f81a2117595a1f024422eb2b438c78845d6568718b108bacad0e2162117595a07768c22eb2b40eed1045d65681dd8108bacad03ba44117595a07730422eb2b40ee40865855d8201510ca8abb0602a219157561332c430e2aec300a8845ce615701510) else (0x68865c55c80d4910cb8ab90132a2197157201654432e2ae402a68865c55c8054910cb4abb0402c2196957608054432d2a0c16ec28659e0a825d710cb2bad0439e2196575a0863c432caeb41027886595d68200f10cb2bab0439e219657560863c432caeac1027886595d58200f10cb2abd0432e2196557a0853c432caaf4100b8865955d8219710cb2abb0429e219655760805c432b2aec180b0865655d8301510caca8704b98a19595060f761432af0741aeb886555d6839cb10caabad073162195575a0e42c432aaeb41c25886555d68380b10caabad063962195575a0c62c432aaeb41885886555d68304b10caabad06016219557560e72c432aaeac1cc5886555d58390b10caabab07096219557560e02c432aaeac18e5886555d58318b10caabab06216219557560c12c432aaeac18058865555e8394b10caaabd0632e2195557a0c52c432aaaf4180b8865555d8394b10caaabb0632e219555760c52c432aaaec180b8864d5d684ccb10c9abad083962193575a1062c4326aeb420258864d5d68400b10c9abab09996219357561072c4326aeac20c58864d5d58404b10c9abab080162193557a1052c4326aaec20a58863ca1d8601510c792bb0c02a218f157618054430f2aec300b0861e55d8601510c3bc350cbae21876865d473c430ed0cba8e58861da197510b10c3b432ea09e21876865d412c430ed0cba8078861da197500b10c3ac32ea39e21875865d472c430eb0cba8858861d6197504f10c3ac32ea09621875865d403c430eb0cba8058861d618865d710c3aabd0c29e2187557a1852c430eaaf4300b8861d55d8614f10c3aabb0c296218755761805c42f872c90264885f0e49804c910be1c9208992217c19309d02442f8325b8264885f064b064c910be0c9608992217c192a0132442f832510264885f0649064c910be0c906e81a217c19201732442f832112264885f0640244c910bd0ca04e812217919401732442ec32a13a04885d4a5770cc910ba94aee099221751950dd03442e8b2a12264885b86582740910b70c90ce832216d1960dd03442da32c02e64885b464c6741910b62cb048992216719519d06442bc323282e428574646505cc50ae2cb848992215a59111d24482b1b2941ce430d63652839c860ac6ca507390a158d94a0d72186b1b2941ae430563652835c850ac6ca506b90615739855c05442ae72ec0aa02855ce5d509c450ab9cbaa0b88a157295c1b75442ae5212ba2a0855ca40165d710ab8cc4af02a2157197d4271942ae32fa82e32855c65e8154050ab8cad0f8322157195a1f03442ae32b43e048855c656815c061ab8cad02b80635719595c05442ae321c2aeb8855c643759d710ab8c810cbae215719020d75c42ae320412eb8855c640765d710ab5cbaa1390a156b9754172142ad722a82e42855a64)) else (if j<3 then (0xc2a0b92e228754c0d7580f10ea948aa0b98a1d525781732443aa322a82e62875455e8301510ea8abb0602a21d51574c153443aa2ae02e6488754541739c450ea8a82e6b88a1d4950a0d72143a92a139ae428752541835c850ea4a82e7390a1d49505cd72143a52a13a2e42874a541745c850e93a12eb21621d25425d442c438e60d032eb8871ca45505d850e38c8aa0bb0a1c7157a18054438e2aec300a8871c55d6059510e38a82ed388a1c71505d9711438e20c032eb8871a542765c850e34a82ed390a1c69505d9721438cec4bacc588716542765cc50e2ca82ed398a1c59505d9731438aec6bacc7886f0a4d8201510de141b0402a21bc19360805443783074100a886f060d8201510de09070899221bc12060e6244378240c1ca4886f04818390910dd14230402a21ba1846080544374284c0085886e85098010910dc9b830999221b9310613328437260cc2664886e4a4184cc910dc94030999221b92306133244372440c2664886e481584cc910dc8c830999221b9180613324437229182664886e452104cc910dc8a420899221b91306133244372240c2664886e441984cc910dc802b0999221b86488913244370a9012264886d8d5d8201510db1a8b0402a21b6320616718836c50ac100a886d855d8201510db0a8b0402a21b610560805c436c20ac100a886d4d5d8301510da9a8b0602a21b5330616718c36a50ac180a886d455d8301510da8a8b0602a21b510560c05c436a20ac180a886c95098510b10d92a130a21221b167561332c4362aeac2665886b8a198201510d70c350402a21ae186608054435c20cc100d886b4a198301510d68c350602a21ad18660c054435a20cc180d886a95098610b10d52a130c21221a7360616719834e6aec300a8869cd458601510d3942b0c02a21a7157618054434e2a2c300a8869c4198501b10d3882b0c02e21a7105618054433c50ec100a8867895d8201510cf0abb0402a219d28760c054433a4aec180a8867455d8301510cd443a84822419a54261c42c4334a84c388488665dd584ccb10ccbbab0999221996716133204332aeac2665886655d584cc910cb9cc2ae02a2197387a05501432e70ec0aa02865ce17805d510cb9bc6ae02a2197358dd7034432e6b1bae048865cd625701510cb948f0ea80a197287d43534432e50fa86a48865ca1f5099510cb942d0e02a2197280616719832e500c2ce31865ca01859c620cb9402ea31e21972805d462c432e500ba8858865ca017504f10cb9402ea096219719895e054432e323c3aa02865c61e85c4210cb8c02ea39e21971805d472c432e300ba8c78865c6017518b10cb8c02ea2162197157a0065c432e2af400a78865c55e8014b10cb8abb0c02a219715760c054432e2aec100a8865c55d8019710cb8abb0029e219715760052c432e2ae406a) else (if j<4 then (0x18424435e2c1c2ac4886bc5838458910d78b0706b1221af160613624435e2c0c16ca886bc58182d8d10d74c12c1b2241ae982581644835d2d093608906ba5a106c9120d74b170a83241ae962e11064835d2c5c0a0c906ba58980d9120d74b1301b0a419f287418424433e30e830848867c6037558910cf8bb303822419cd8660e7214339b0cc1ae4286735d983c9120cbcc3aa0b10a1975985d562c432eb30baa058865d659859c620cbac930b38cc19758660975c432eb00c32eb8865d601825d710cbac02eab16219755761952c432eaaec32a4885f8e512058910bf1c9a40b12217e192d9502442fc325b1a04885f864b0458910bf0c9606b12217e192a1902442fc3253b204885f864a6058910bf0c9440b12217e19285902442fc32502ac4885f86490694910bf0c920d212217e19241a32442fc324832a4885f86490650910bf0c920c992217e19201562442fc32193ac4885f4e61064c910be9ca20c992217d39341932442fa72483264885f4661064c910be8cc208992217d196c1132442fa32d40264885f465a304c910be8cb440992217d193a0906442fa32683264885f464d044c910be8c980ab12217d19241b32442fa32483264885f4643644c910be8c84ec992217d1908d932442fa32103264885f464164cc910be8c82c8992217c99398906482f8f24b2264885f165a244c910be2cb048992217c593c9d62442f8b2790ac4885f164f2058910be2c96c8992217c5929d932442f8b2503264885ec6500558910bb9c82aca922177196d4152442ee325a82ca885bce516058910b79c82cab12216f196c1162442de32d81ac4885bc65a6058910b78cb440b12216f19681562442de32c822c4885bc6580558910b78c86ceb12216f190d9562442de321b22c4885ba65a6241920af94bc0ab12215d79361975442b9b2793ac52857364f2758950ae6c9e4eb10a15cd929cd62142af72ea82c42855d661065d7109f9cc20d212213f398419424427e73083084884fce5180589109f9c9b00b12213f390619524427e331b2a04884fc66363409109f8cc608b12213f198c0d624427e3313b204884fc66205589109f8cc240b12213f19841a724427e330834a4884fc66106909109f8cc20d192213f198419424427e33083264884fc66106109109f8cc209b12213f198411324427e33002ac4884fc65b84409109f8cb706812213f196e01524427e32d40484884fc65a80509109f8cb500212213f194e09064427e325c1a0c884fc64b80595109f8c870eb12213f190e15624427e321c22c4884fc64383589109f8c850d212213f190a19424427e32143084884f5e4d87595108efc9b0eb2a21f834241132443d82c48326488758c097580b10eb148aa0b90a1d619154172143ac2af4100a8875855d8201510eb0aba40a9221d61505ca71143a) else (0x21ee32158162443dc40c902c4887b859d2058910f70b120d29221ee16241a42443dc2c483464887b85890654910f70b120ca1221ee16241932443dc2c2902c4887b849d6058910f7090ac0b1221ee120d9562443dc241b22c4887b84816558910f7083640b1221ee10648162c43dc20c902c4887b4da1064c910f69b1a0c99221ed36241932443da2d083264887b458d064c910f68b120d99221ed16241932443da2c1b2264887b458164cc910f68b02c899221ec562d9132443d8ac4b2264887ac5190458910f54b1280b2241ea94258164483d4ac8932848879c5950654910f38abac0b2a21e715681562443ce2a2b02ca887995952654b10f32b2a4ca9221de120dd562443b8ae4bb2648875c95e0558910eb8cb2ae02a21d719255c05443ae320baa058875c55d0654910eb8ab80ab1221d710841975c43ae20cbaa058875a55d2054910eb4a830cb90a1d692754162143acb24baac5887596497540b10eb2aba4ca9621d655749952443aca40baac5887565417358850e9ca82e8b10a1cf162419718839e2c1baac48873c5817558910e78b02c8b8c41cf160589719439e2c0b12e31873a59d2058a10e74b3a40b1221ce96241b744839d2c4836e29073a49d6058a50e7493ac0b1461ce927581628439d24eb02c4887395d92758910e72b3a42b1221ce52758562443972cea02c89072e51d6059220e5ca3ac0b2241cad675096448395a8eb12c89071e59d5058850e3cabac0b2a21c7950609761438eb2cbaac58871d5a1065d710e3ab02eab1621c75565d562c437c700932a4886f86598201510df0c024d29221be18049a424437c30093464886f86012650910df0c024c99221be126607044837c241c2ac4886f84838458910df090706b1221be12061a524437c240c3484886f8481868c910df09030ca9221be120619424437c240c3264886f4a0d0650910de8c830899221bd180611324437a3009b264886f45818398910de89830c99221bd130611324437a20dc2264886f441a8390910de88350621221bd106613324437a20cc2264886f4419839c910de88330729221bd10660e424437a20cc1c24886f44198380910de88330621221bc90660f2448378a4dc2264886f14998394910de29330721221bb148413624437629082264886ea6094059120dd4a1300b2241ba5426184244372b2cc2664886e564984cc910dcaa42c999221b95485913244372a4cc2664886dce015654910db9a830ca9221b7106a14424436e20cc2884886bcda10690910d79b420ca1221af368418424435e324c300a886bc6428610910d78c830c21221af180d95624435e301b22c4886bc6016558910d78b420d39221af16841a524435e2d083484886bc5a1068c910d78b420d09221af16841a024435e2d0832a4886bc5a10650910d78b420c99221af1684)))) else (if j<7 then (if j<6 then (0xb02eab1221cf960595724439eb2cbaac48873d5d97558910e7ab3a2ab1221cf5615d5624439dac4bb2a48873b5897558520e7693acab1221cbf9459d644837e72ac02c4886fce518058910df9c9b00b1221bf391601624437e720c32a4886fce1e0558910df9c02eca9221bf19841a424437e33083284886fc6610610910df8cbb00b1221bf195601624437e328c02c4886fc64d8058910df8c3c0ab1221bf187419524437e30c82264886fc6190350910df8c230483221bf181419524437e300c2ac4886fc6017558910df8c02c899221bf18058d424437e2ecc140a886fc419844c910df5c9300b2241be920619524437cb0e932a4886f96052654910debc9b0eb2a21bd596611324437ab0cc2264886f54d9844c910ddaa42c899221b7985601625436eb0eab2a4886dd6055654910dbaabb0ca9221b7551619524435f300b2ac4886be5a10654910d7cb420ca12619f987419524433ef22c3ac48867de057558910cfb4c2eab12219f6785d5624433eb30baac48867d61d1654910cfac3304baa219f5815d9524433eb02baac48867d5e17654910cfabc2eab12219ef985db244833df24c3ac89067b61d2654910cefc9b0eb2a219dd9360b735832faaec32a4885fce518241910bf9c9a0ca12217f39061562442fe720b2ae4885fc6620558910bf8cc00ab12217f19759502442fe32d02ae4885fc641644c910bf8c82c6a12217eb9261106482fd324832a4885f5661644c910beac9ac899221775955d952442eeb2a8b2a4885bd6597558910b77c92e8b12c15f79660975442bef24c32ea8857d65d655c910afacbaca892215ef9261176482afb2abb2a48853f65975589109fdc830ca92213f990e05625427ef2ec32a4884fde5987549109fbcab0eb12213f79261d654427ef22c32a4884fda6175589109facc2eca92213f598591324427eb308b2a4884fd65f85589109facaf0eb12213f595e05624423ff2ec32a48847fe5987549108ffcab0eb12211ff9460b735823ff26c3ac89047fe4987595108fecc2eca92211fd97e05625423fb2bc0aec9047f64f845d920fe193a0c99221fc29648132443f852483264887f0989064c910fe11824c99221fc20241932443f832c90264887f0649064c910fe0c044899221fc16241932443f826093264887f049d064c910fe09360899221fc12641132443f8241b2264887f0482764c910fe09046c99221fc12061132443f8240bb264887f0481644c910fe09026c99221fc12049b32443f820d12264887f0418244c910fe08140c99221fc10241932443f468483484887e85090610910fd0a024ca1221f914841132443f228682264887e450164cc910fc8a02c899221f874259132443ec6a0932a4887d855d2054910fb0a8a40a9221f612055952443dc6ce902c4887b8d852058910f7193ac0b12) else (0x2419320a0103b4814a3ffa1fde8fe007e2e3eda1f388f7447b283d571e770f29878d23c2c1df78ee9c76663af61d570e998742639c01cc18e518721238ab1c370e0c46f9037751b968db946d5036601b068d7406b26354b1a870d34468e6343619e68cdbc660c32b319358c88c63cc317d188a0c33060f2303c17ff8bedc5ef42f27176a0ba5c5cb42e1d16f00b6605aa02d13166b0b1e058762bfe15e08ae1056782ae9154b0a90c53e0297c149a0a32c50402775138609a8c4c8a25dc12b4094804984241711b608c384534225210fa08658427020cf103307f9c3f281f2b0f6c079903bf61d7c0e8f0727c382a1bd80dcd86cc835921a600cfb86638324a18bc0c2985fa82f4417390b6805a4c2c9616030acd054f029a6147509df84c502540122c08dc0456821f810a9082583f881ef20f100759039501bec0d9806978334418e60c0a05c002d0c160c0ac905460293c140e09a904a5823b41160085203fa01e840e8606e50343819280c0405ba02b9014d409f00484020d80ec806ea0338017d80af80502024400e80057001d0007400007f86592058910ff0c920d21221fe19241942443fc320932a4887f861d2058910ff093c0ab1221fe12760162443fc24c82264887f84990350910ff09030ab1221fe1205d952443fc240baac4887f8481644c910ff0902c6a1221fe12045952443fa33083264887f4651064c910fe8c920c99221fd18641132443fa300b2264887f44d9044c910fe8982c899221fd13058d42443fa20cc2264887f4419344c910fe2c344899221fc52661132443f6280b2264887ea6510649120fcaa42c899221f954359132443ee6a0bb2a4887dcd41655c910fb8ac40ab1221f715759502443ee2ae832a4887dc5450654910fb4a920ab0a41f692055952443ecaae932a4887d95452654910f78ca2c0b1221ef19258162443de30eb02c4887bc6016558910f78b3c0ab1221ef16760162443de2c881ac4887bc5818558910f78b02eab1221ef16059572443de2c0b2a24887bc581644c910f78b02c6a1221ef16045562443dd30eb120c907ba5898441920f74b120ca9221ee962419424c3dd2c482ac2907ba4816558910f72b12eca9221ee56259132443dcac48b2a4887b949d6558910f7290acab1221ed963419424c3d5ac8932849879e6156058950f3cb2a0ca9221e75565d562443cdaca932a48877c641625c650ef8c06eab1221df1805d562443be2ed02ae48877c5d97540910ef8832eab9221de9205d952443bcb24baac4887795c97558910ef290aeab1221dd79361975443b5f28bb2489075e61d5058850ebcaba0ca9221d75965d502c43aeb2cabaa48875d6495759510ebac82eab1621d75755d952443aeaaeb2ae48875d55d6544910ebaaba2ca9221d75515d952443aea0cc12eb8875b55d2654910e7c)) else (if j<8 then (0xbb22dd818eb8275873a9b9d3c8e97b7499ba3d9d146e850740439f01cedae6f973533994dcc2ce5d972c8b9525ca18e4cf724939129c7d8e38e719838b1dc4e8e22c70ecb8619c250e0ca7030b800dbf4adf5d6f8ab7b09bcf4de276eea375d9ba46dcd06e3eb70d5b798db796d9336b4db4d4da0c6ccc36465b176d8736c1035f09ae86d6cf6b4935955ac1ad5af6aae35425a998d46e6a0db4ef5a6bed317696234a1da47ed1e168ccb44c1a178d069680b33eb59e88cee66744338a99b56cd2c6656b30b997b6cb726584b2a55946ec9ce64ad323c590fac7fe63d031cdd8dc8c67b63093164d8a28c495620b30e5d8630c2af611db07a18340c158608db03798100c0225fdcafd6d7e26bed65f2baf8117b78bd745e90af2b578f6bc285deaaedb1761cba9a5d23ae7a57316b9385c72ae249707eb7ec5bc72dcc16da4b6745b10ad70d6ae0b51d5a652d1dd6874b3f259cfacd0565dcb2905929ac859639cb17058892c2d160acb00357d2abd755e14aeac57272b7c15b24ad3f568c2b41d5910abdd55caaacdd552eaa4f5503aa5f55280a903545daa1754fe8a754538629b114c74a5dc52cfa95894a08a4c7522f2908547c8a3a751b528c5d4572a2715109a85cd4256a0e35021a80193f929f814fa227c1d3d949e6c4f17a77c93b6a9d574e7ca72f138a69c164deca6dc1360e9a9e4d1aa67e1337699524c74a61a9301897b94ba825b9d2cfc95ff4ac5a54b5295c944549e324cf1257a925f48e5245b121da908f4818a3f211f008f4347622396d1c3c8de146c1a346919a48c95460b22eb516e08b33456aa29b11406898444a3a2429119a88904429a20590fb2879c439f21b550d1a862f42e3216250a1484a142322109d07d483ad41a7a0abd04e4821440ba20459015a80443fed9fdc8fe287e7f3f001f630fa5c7c993e2e1eff8f72a7b2c3d671e9c0f42479b43c951e3b4f14a78523bff9de58ee5a76c43b2d9d7c8eb3e750a3a509d164e82273b339aa9cc08e4f0721a38de1c4f4e192706b38011bebcdeb86efe37501b82cdaec6d18365d1b1f4d7fc6bc135b71ac6cd57a6a6a35111a768d2f8693434761a20cd06067f333c519cdccdf466bd331f19780cb466550326e19224c86c63c231b218c44c57c626b310c18740c2a260fe305018084bf5a5f652f8397ad0bcd85e242ee317574ba145ccd2e3216fecb7505b6b2d8696ae8b4ce5a142ce616534b20a58a72c2f9605caf8857712b9a15b58ac6c55f92abd154c8a9d454a22a279501ca77e5377299794b9ca53e524c2902146f0a2e8512c287214244a07c500127d713d6c9e3c4ee12731137b89b624d27265f1315497c24b62255b929e8942249922494923b0911c485123ee91d4c8e2c46ad2338118a08bd6458d22a29137089284457220d10ec486e8430b21569093c83e) else (if j<9 then (0x121c02802180f811013012418021a1a820821022024001810410811012000a08208408809000504c47e0c1118190224390620a408a04647e0a11181842602483204482323f04247c0c213012419022410410811012000a08208408809000503f04204404800282082102202400140fc10811012000a07e0840880900058770d4138208310520840c811010a8770d4138208310520840c811010a0961161da3906609d1181c831810a8770d4138208310520840c811010a4768d4138204308510820c410810aa34ed1a068cb54633a306517ee8bbf45c3a2d9516028a9d451ca27ad1392899144a1a23d5117a88854426a1fa50f368763437fa1a6d0c9a85e942c2a14dd09a68485421ba1055078e838f41a0a0bcd057682994130a084d038a81774089a0315011a805540199ff3cff027f493f889fab4fcea7e3d3ef79f62cfad27d5d3ea89f464f9ee7cbf3e439f194f85a7bf53dde9edbcf69a7aff3d4d9e934f3fe79b13cbc9e4acf1e678e73c4c9e1dcf0aa77f13bd19dd54ee6676cf3b2a9d7c4eb1a753f3a8e9d3ece9b274a13a1e9d06ce7c673c139b99cc94e5da72b539549ca74e522725938fa9c69ce2de7163387f9c31ce0f27057381a9c04cdf8a6f7737aa9bc74ddca6e97373a9b94cdc626e0f36eb9b67cdafa6d5b36869b2fcd90e6c4f360b9af7cd74e6b2d35649a9ecd45a6a0b34de9a614d29a68ff34639a23cd106684b33f399ebccf46676b339999beccd8666a13334998c4cbf265c132b999544ca5e64cb3254991c4c87263d531d998d94c62e62b3314898964c44261ff30e3985e4c2826109306898264c0ee60292fe297e8cbf025f5f2f9e97c6cbdf25ed72f6597a4cbce25e232f00977d4bb7a5d852eb197504ba3e5ce72e6d9733cb95a5c8b2e3f97174b84a5c032df096f54b5da5a5d2cd096394affa56ff2b37956cca9ee53f9297d9484ca282506f27c393a7c9b424c8d25d292af493aa4945244491f348dca45e722a09121487be42e120e69049c80aa3f831f798f77c79ee3c3b1dca8eb64743a39611c5d8dffc6eb236b31b068d544698233c319838c92c631e30e918218be1c5d962e2516b48b30c580e2b77155d8a74c528628b313fb89d444cd2256b123688f74466e229110d4883b43fde1f5f0f468774439d21c590dd986b2c347619950c82860742ec216e70b368550c28b61373095b84844227e106d07e383b7c1bee0d3b06558301416920a8d04e88250410de07c90391819f40bae0531022f80ee405ce022b00c28037c0071ff7cff6b7f763f989fbdcfd857e9ebf3a9f902fc447de83ee21f680faf87d583e949f3fef9b77cb23e445f192f8817c1cbdf6deefaf7147b60bd935eb9cf57b7a943d2fde86af3cc79bcbcc99e564f23e78f03c5dde21cf0b07823bbfd1df42ef2d775cbb8e9dbb8ed527674) else (0x1422002003004204400906a0b0d5825348088d082003c674a03c6740a00c00c010613a0508800c2100180210220558a41420804e9182284488810c21442083104204782c04a0881001e2304508911021842884106208408f03c0508800c21001802102200f29d0304400600a01041882102280f19d02803003004184e81422003084006008408803c0508800c2100180210220110a102824c0608b00a01080442840a09301822c030050084c22c3e0648c40580920f01601241ec229438800d11880d01602483c045c229420708c40580920c70778d6114a123101a02c049064c22c3c0708c40580920c70940ca114a1c3c4620340580920ca84587c0c91880b01241e02c02483d8452871001a23101a02c04907808b8458780c40580920f01600201dc229438780c40680b01241e02c00583746a0804e81242002904006408009001807808008008008503c04004004004281e0250400540800d01001400240f0128200260400680800a00120780941001502002c0400500090408780911101442403105004482043c0488880981001882802241021e0244440510900b01001120780941001502003404005000903c04a0800981001a02002800481e0250400540800b01001400261a82082102202400181612b04a4901112104047c0f120b0958252480889082023e078903c04004004004281e33a0600600a010301e33a05006006008309d0304400600a01041882102244e81422003084006008408803c0608800c01402083104204481e0284400610800c01081100b0128220400794e9182284488810c2144208310420480c646a2ac520a10402750c21442083104204004800f03c6740921001482003204004800a03c6740921001482003204004800a03ca740911001442003104004400a87108f0f81980d01701601221c422c3c06203404c0580088438740c40680980b000f08e5081c23301a02c849064438c6908a5091880d21602483261161f03246202c0490780b009308f0f81980d01642483c0580498458780c40680920f016002210e1e03101a02483c0580088458780c40580920f01600221162003446202c04907808884787c0cc0680b21241e02c024c22c3c0620340490780b00110870e81880d01241e02c004422c3c06202c0490780b00e00241ba350400780921001482003204004800c03c04004004004281e02002002002140f010010010010a07808008008008503e04404805004283704004805006004302623e8614ba0c516821439008c8fa1452683145a04506402323e84147a0c516811419007c88108208400546a0990c297418a2d04287211a823428a4d0628b408a0c804684147a0c516811418e0988fc1892f03245c0890e402323f05249c0c917012419008c8fc1091f03245c04906401f02202402802140f81181))))) else (if j<15 then (if j<12 then (if j<11 then (0x60400480400600428a133a0508800800c01081100d410012014018010c0885091031e0304580600a010906a0800900a00c008683a040040040042c1d0200200200214110a122063c0608b00c01402120880980c00c010584787c0cc0680b21241e02c024c22c3c0620340490780b00110870e81880d01241e02c00443884787c0cc0680b80b00910e21161e03101a02602c004421c3a06203404c0580078458780bc0680980b000e8d410210410811000c11d1a82c04a0881001e4308510820c410810012003c0f010010010010a07808008008008503ca740911001442003104004481f22042082100140f8116200258400560800980123181b8ab1482841009d0340580900e014018011c07808008008008503c04004004004281e0248400520800c81001200261a820821022024001810410811012000a08208408809000503e04404805004281f02302303805004303704004b0800ac1001b02002c00501f02202402802140f49d02202402802189a82d04c08c1001f180f91832e430c590830e381f22864c8618b20860c703e04404805004281e02002002002140f010010010010a0780941001502003404004401e02002002002140f018018028040a0b41302304007d0e314618c10903e4618a10c21061d820e07c0880900ac10010c07c0880900ac10010c08088108208400526a0b41302304007c603e460cb90c316420c38e07c0880900a008503e04404805004293504044084104200301e02002002002140f010010010010a0780941001502003404004401e02002002002140f0184200300500840c811011208e0f91432643184104306402d04c08c1001f438c6186308240f91432643184104306381f02202584005004301f02202584005004302022042082100141c82323f0528840c81101280120e411c1f22864c8618b20860c926a0b41302304007c603e450c990c316410c18e07c0880900a008503e04404805004293504044084104200301e02002002002140f914620430c5904306381f22864c8618b20860c704404c06006008281e02002002002140f010010010010b07408008008008506a0800900a00c008606a0800900a00c008604404c06006008281e02002002002140f01282002a04006808008803c04004004004281e02002002002140f018018028040a07808008008008506a0800900a00c008603e460cb90c316420c38e07c8a19321862c821831c0f91832e430c590830e381f22864c8618b20860c706a0b0d5825348088d082003c674a03c6740c00c014020613a0608800c0140208310420448ab1482841009d2304508911021842884106208408f0580941102003c4608a1122204308510820c410811e0780c11001802804106208408903ca740a1100184200300420448a193a0520800800c0120110284ce8) else (0xe02884004006008808803c04004004004281f23065c8618b21061c704687e0a21101342202483404804a04705249c0ca11012418e08e0a610819422024831c11a1f82884404d0880920d012012811a2082984204404907800803e04404d0880920c010e08e0a493819422024831c11c1091f03284404906381f02202684404906008704104204404907000607208d0fc1442303245c04906809009608e0a49381922e024831c1c8238298420648b80920c807208d0fc1442303245c0490680900960e411a208298420648b80920f001407c0880980920c010d0d411c1492703245c04906402382123e0648b80920c703e04404c04906008604104204404907000604687e0a49381942202483201602504407c0f11ca31432841207e0a493819422024831c0fc10811012000a0e411a1f82924e0648b80920c90582ac128a40442840f81e13a481f82924e0648b80920c703f0420440480028264470528840c81121f021007c08d10013012418021c11c14a2103245c04906381f02344004c0490600870410420440490700068768e41322383125e0a40c81121f021607c0880980920c010d0d411c1492703245c04906401f02202602483004302082102202483800301f8294420648b80920c703f05249c0c917012418e27408008008008513a04a0800a81001a0200220634351562905082013b0620a41081902202002380f010010010010a0de1a82003c04a0800a81001a020022c9a82d04c08c1001f180f811410a1c02802180f811012811418021811a1051e83145a04506381f02282143805004301f02202502283004302042082143a04400302042082102283400301f02282143805004301f022025022830043023420a3d0628b408a0c703e0450428700a008603e04404a0450600860408410428740880060408410420450680060900b41302304007c603f0624bc0c917022438e07e0a49381922e024831c0fc10811012000a07e0c49781922e044871c0fc1492703245c04906381f821022024001411014018018020a0ec128220300500608b014020030042c6112c0520888911001c030030042810012014010010a0e41191f02a4440680c00c01402102202602223c0508800c00c01081100241111e0284400600600840880120888f0142200304580600840880140888f0142200304580600820c811002ca38c217c2e09b93505e0a41101602803806006008782002402003002145099d028440040060084088012700960290444488818f01c030030042c110a122063c0608b00c01041920800900a00800851426740a110010018021022010012014010010a0888f0152220260400600b01081140e41111e02a44406c0c01201802c0420460200240200300214110a122063c0608b00c01402120800900a008008506a0800900a00c008)) else (if j<13 then (0x9d0250400540800d01001400244e810010010010a0de1a82013a04a0800a81001a020022c0f81282002a0400680800a001207808008008008503c04004004004281e02002002002144e810010010010a274094100150200340400440c686a2ac520a10402760c41482103204404004709d02002002002144e81282002a04006808008818d0d4558a41420804ec1882904206408808008e0444840980c2160188280420110a102824c0608b00a0104192088508141260304580600a0109444c780cc1840c81702302602483d444a858f01a83081b02302251131e03081502302602c0080948e419223444a859031f63c0720c205c08684a06409d11a22542c818f41840d810b46a09c1021842884106208408800a03c0490800a41001902002202382c04a0881001e4308510820c410810011a07c0900a00c008513a0490800a41001902002200f19d0248400520800c8100112078ce81242002904006408008913a0490800a41001902002200f01282002a04006808008813a0688900e01502083102204e8162240388500680840881562905082013a4688b11221c42883102304e810010010010a0804fa10410811000c0804fa10410c1d022001c1009f4208210230340038262408618820c410a1d823002411920428c4106308408a0d801208c9021051e83184204506c00903e0458820850e01582002600481f022c4004b08408a0c01300241b82013a0480500600438470580941102003d0620a41081902202002340f01142002504005408009001207c08a0850e014010c07c08809408a0c010c8d41321852e83145a0850e423504685149a0c516811419008d0828f418a2d022831c1602504407c0f518a2944286508a09400c03f0628840c81121e82500200fc14a210328440490740088770d4138208310520840c81101200170ee1a8270410620840c81101200150d41041482103204404800402c1560945202214207c0f09d240fc1892f03245c0890e381f82924e0648b80920c78760820c51081902282500206302082944206508809400886a2ac520a10402768c514a2143284504a006c350580941102003d4628a510a1942282500361d82083144206408a09400808e0820a51081942202500200f010010010010a0de1a82003c04a0800a81001a020022c0f010010010010a07c8a19321862c821831c0f81181121c02d0400438262470628a40c81121e821007c08c0890e016820021c1041081121e02400180f81181121c028021a1a82683125e0648b81121c803e0460448700a00860410420448780900060580941101f03c4728a50ca08481f8314520640890f410703f04204404800282c1560945202214207c0f09d240fc1892f03245c0890e381f82102202400140f010010010010a0de1a82003c04a0800a81001a020022c1121) else (if j<14 then (0x2724105288408809400803c04004004004281e02002002002141121e02884004006008808803c04004004004282243c0510800c01001802202240f010010010010a07808008008008503c04004004004281e020020020021411a1051e83145a04506383904685149a0c51681141904d410110210410800c0780941001502003404004404786a0b01282204007a0c41482103204404004743504104204404800343504104204404800304a08e31a1dc350640bc1602904e0941102003c701e02002002002140f010010010010a4d410110210410800c07808008008008503c04004004004281e02002002002151a823428a4d0628b408a0c803c04004004004281e02002002002140f010010010010a8d41321852e83145a0850e40a193a0520800800c01201102740800800800851432740a41001802003004804489d02002002002144e810010010010a0a5110142200380608b40c81090442840a09301822c03004106482243c0504980c1160180208324110a10288400608b00c010419227408008008008513a0400400400428221420504980c1160140208324110a102824c0608b00c01041928e511a2263e0640c20640a811813012d1131e03081502302602c008444c780c206408c09800e0ed1131e03025d03204604c0090768898f01812e81902302600483b444c780c09740c81181300241da22542c780c20640a81141b0260058c916209d50b2073a0680c206408503b0648880d01812e81902100ec12a2203025c0600a01021d032042c1dc22a3c0604bc0680940a80120be1101812e0580a112220022034042c6102f84426c0c0160284488800c80d010c0760951101812e0300500810e8190216ae1112a103081902a04506404a07a0ed5c33766a0c813a2203406103204341daa173a06103204604c0080522a21111031e0380680c11701a02172e2114a113701a02c04906409d0250400540800d01001102740941001502003404005000904084104204606800613a04004004004283786a0804e81282002a04006808008b03e04a0800a81001a02002800481e02002002002140f010010010010a2740941001502003404004409d0250400540800d010014002410210410c1d02200184e810010010010a0de1a82013a04a0800a81001a020022c0f81282002a0400680800a001207808008008008503c0400400400428221420504980c1160140210088508141260304580600a0109444c780cc1840c817023026024a394468898f81983081902e04604c04b13a04004004004289d02002002002144e810010010010a07808008008008513a04004004004289d02002002002144e810010010010a0780800800800850442840a09301822c0280420110a102824c0608b00c01402128d410210410811000c274094100150200340400440) else (0x6404245c022142440c780c1160180280410658b886e0885081401822c0300500820cb1710dc110a10280304580600a01041962e21a8221420500608b00c014020832c5f0b826a0bc5701602a0528820c408594738c2e09a816a240390640a00c810b1704d411014a200320400600848351426740a1100184200300420450c605e0a4114a103c810718c2b8540a113b010618d0d4570a814227460760d41781602828c606a0bc14822141a82202803003004204400806a0880a00c00c01081100201a8b40440500600600840880120d4110140180180210220040c606a2b8540a133a303505e0580a110141a8a133a0508800c21001802102200584706a2d00b00e00c408706e0d45a02f05208860760d45a02f02c05061680880a00c00c010818f0d45099d02c4480710a00d010811512223c3784020210280304580600820c70420500608b00c010418e0840a51001822c8400600820c90420528800c11642003004201a82223c0508800c21001802102282413504e08288508a083935044a840a00c00c81402104ec9a82f8440580a40680840225420400600640a01071840be1101602901a020e0ec14c2201c032034041c178290452850f206408383505e0a41141e40c81071840d414a2201c03103204201a82223c05006006008408806a0888f01401801802102202383584005807006409008818c2b8540a133b01a020e0d41111e0280300300420440228400500600600900870450780a00c00c814020e08950814018019028041c112a102803003205008382f8440580a406141d8298440380640618112a102003003205008383b06a0be1101602844203100a611018028038064061c1a8a133a0500600600840880440500600600828220280300300414570a814307a03404181111e0200300300420440080444780800c00c01081100201111e0200300300420440080760d417c2202c05108406201a8294440380620640838c605e0a4112a183c41882104800b00e00c810810c2e017829044479032041c5f0b805e8880b01440c81081842e014a2201c03103204209a8229420500600680a01082764d417a2202c0510320420114a1020030034050083c4886f080384009c02580a41111222063c0700c00c010b28e3085f0b826e4d4178290440580a00e018018021e08108208408a0d000c0780941001502003404004404786a0b01282204007a0c41482103204404004743504104204404800343504104204404800304705e0a4138221420800f41481801a021807808008008008503c04004004004282042082143a04400301e0250400540800d0100110284ce81622402a04006808408908f0d4160250440800f41882904206408808008e86a08208408809000686a0820840880900060940c81482704a2901001e83103005408321d8)))) else (if j<17 then (if j<16 then (0x111e141d83505e0580a0a0d417829044479020c0880a00c00c012010c0880a00c00c010504405006006008282202803003004141101401801802402181a82202803003004805000818c2e017829044a860340420610c01700bc0b01480d010817c2e85c1350520380640680848225420400600640a01071700bc1482223c818617c2e017816028441030e3085c02901c030842061c1d8351680bc0b01440c810806e0d45a02f0520890f10620610b806a2d01480e01882083120ec1c0b405e0580a41020840421800e01781602884c82100880a00c00c011000c0880a00c00c011018c0dc1a82f05208890a041c1a82f02c05089a04182383502c03803105408383b1680bc0b014426410708e0d45a01601c0190290420111200200300300420438225420400600640a010746a0888f01601c019020e0d411014018018020c0840a61001822e0400600820c90420530800c810018020e0e011014c20030030041c1a82223c050060060083848072ae01802a04785306604271a8230408530820cc10810846a0c01382304027f08608c09800a0738d45182013e8530820cc1081300161201cb350600a81181fa08404826a09c1001f600302304007c8a10c208c0075708d49021462083184204206302f05208c110a143f85306205c08584718c0bc1482304428510206c085022028030030041411014018018020a0d417829044819020c3085c03505203806206408402202803003004204400704405006006008408800e0880a00c00c010508e2e01a81601c01902402201101401801802102200382202803003004106408801011c5c03502c0380320480440c615c2a05099d00830470450780a00c00c010704405006006008283b04405006006008304726a0bc1482254307802103089a82f02c050020c0ec9a8290440500700c00c01091426740a11001842003004204400a0440500600600820c810e4d414c2201c032034041c9a82f8440600b01422101a02124d414c220300380600880d010926a0895081401801902804205f03b26a0a61100e01901880530880c01422003806406209a82223c0508800c0100180210220059350444780a11001802003004204400b26a0888f0142200300400600840880164d41111e0284400600800c010811002c111a102803003105008383b26a0a61101801c030044062414c220300508800e01802203120d45099d0284400610800c01081144d4112a10280300320500840b826a0895081401801902804245f13505e8880c0160284410320428a39352400588900e01401881123089a8294440600700c01081902144d41111e0284400600800c010811002c9a82f4440600b01422081881844d417a220300580a11040c48220280308580600840c73800bc5701602a0528820c40849c02586ac8911122063e) else (0x4480032041c1a82c03005009010404800806a0880a00c00c01101200201a8220280300300440480080440500600600840061700dd1b03502c03803404204493826a0880a00c00c010716c4d411014018018020e0d411014018018021001c1a8220280300300420038350440500600600840071700de1a81601c01902804204483746a05807006808408706e0d91a81601c01a02c04204483786a0580700600a81081108e01a82f02c052081041c1a82c030050090102003c3505e0580a21302041070708d41781602904e08104221a82f02c05009a1020838350444780a11001842003004204400b08e3181bc3505809c1282204087c0f102301a82243c0510800c4100180220228240395708d41802a04647f02121209a82704087e800c0e55c235428831023001c6323505e0a41182223e47b021211c570a8142010506a2864e81482003204006009008a0440500600600820c60440500600600820c60440500600600820c61840bc0b014420010617c0ec1480e0188200300420110140180180240280038b805e0a41120640830be1700bc0b01440c81071842e01480e018819020e0880a00c00c010418c0880a00c00c010418c0880a00c00c010418d3185c02f05208850a0640840c21700bc0b01412681902102f85c1350520380608b40c81090530880a00e01901a020e0bd1109b0300580a11001881902140a51109b0300508800e01822d032042c1d82901c0300420640838229420500600680a010717c2e81480e01822d04206408482944426c4b8142200380608b41081902182f814a220284400700c40c81090452840a00c00d014020e08a5081001801a028041c1db3505e8880c01602802103204286102f4440600b01422003103204291b82244005006006008808848e2e01121e0280300340500848b80452840a21001801a02804251b82244005006006008808846a0890f0140180180220240048229420400600680a01070440500640b00c012018e2f8148a80294400700d01822d02142e0110a10280304580600a01041942e0110a10298400608b00c014020832c1d83505e0580a11080d01081840a61109b12e0504991001c0320340430210c04700bc0b01402704082123021a82f02c0510981020840b80442840a09301822c0300500820cb1880ed9a8321638880d01903025f03604315c22254226c0c09740c81502283286103b05e2bb1101812e0580a8142208230360438611c005e2b84d81802c0540a110419810c570cd5112a183081902a04506484726a2b8540a103c30c615c2a050a06141111e0200300340500838229420400600680a010726a0880a00c00c01062764d4178160290186044a840800c00c814020e0d450c9d0290400640800c012011408a5081001801a028041c114a102003003405008383505e0a41)) else (if j<18 then (0x400588900e41801902102286113505e8880b01422083103204281d8294448500700c1160210320428110140180180208318e012c0444488800c00c010817008a5091001801a02804209a82223c0508800c00c01081100289a82223c0508800c0100180210220058225420400600640a01071700895081401801902804206102f02c05049a1000838c20530884d8180284400700c80d010b0760a61101812e0508800e01802203404301781802c0508820640838c23800bc0c0160284410320424e00b82586ac8911122063d0612318570a8142a74020c11c110a10400780b41401d0300340420460221420810f81e02c03803404204504798c0bc14822142079021011c1a81601c01a021021c2383502c03803005808408806f0d41101401801802102201b43504405006006008408804405006006008408800e2e01b83502c0380340420440b826a0880a00c00c01071704d411014018018020e2e09a822028030030041c238b826a0bc1482254201081704d417816028010617c0ec5c1350520880a00e01801802162e01ba3602c0380340420440b806f0d40b00e00c01081102e21a81601c01902804204403706a0bc1482214281070760d41781602824d020e11e630b806a0bc1482240840350440500600600840880100d411014018018021001c1a8220280300300420440081847009a82901c032030e3089a8290300380600880c41350440500600600830be0764d41480e01901a02100ec5d1350520600700c01101a02144d411014018018020c4d411014018018020c2f89a82f0300580a11040c413505e0600b01440c81071847009a82f0300580a11040c810a17c2e09a82f15c0580a81412744106163085c13505e2b80b015029441062042c6003505e0580a110186023805e0580a41020838c086a0bc0b01442641071844d4178ae02c0540a093421010a08e3189a82f0520895081e20238c606f0d41602704a0881001e20458c606a2b8540a133a304718c0de1a82704087c0f102249a82f05208c110a143d010808e3189a82f05208c110a143d010a04405807006408408626e0580720c00c810810f0d45099d02c4480710a00d01081148d413820c21823020d8d410214c20833042041c1011f428831022001823d3505e0a4112a1040078034042a1a92082944206508809400826a09c1021f2002a354288310220014238221420810f81e02d0500740c00d010811a0d41121e0288400620800c01101140888f0142200308400600840880140e55c6350600a81191f408402304047d0a20c4098007a6a0bc148230442850fa1e808484705e0a4118221428810f404241cab846a8510620460038350444780a1100184200300420450350444780a1100184200300420450350440500600600900a00108d41101601c018810c8d41782904) else (if j<19 then (0x600c408300c08060081014018101406630b8044284426e88810006102383724001841840510606850104001820764d406064d40a1100c9a804081dc14080c20c081d818828030418806106064ec06043085f018018203b03005006082fa8800c0c4dc1802803041883080c014109a814020189b03005106080600a20c0c9baa100c1a0604630a133a182040c102204001830440800306080030411c108e08c207208c11060d40a1100c1a804200183700c81481082e01a8220c1b806081a8060a06023185c02294220222400183040818204081821883080c014109d80c0811006085a10340018c006a0520808088100008e08820720814418103904610230424023089d80c080a40c08230b804418220411822240184808e08c11080d4022000d1aa042041a35044810306e018206e080030608003040023240018300c0806062443744b080487084202060d4021000c11025211a820c08204826e09e11020162382304041848728d490204109ba2200c1a06050302018126e888266b08c10104102382088900481810900dc90060dc900060c1b80608900060800008710d4286a0888f404121a8148081c35018101318114a1408212000c1137542018300808140402020dc031020c2382223c1814041d80c0890006089ba2300c1c140606020501446082223c112000c120c050a028de508060c6123b0181c35820102240c10234401023440144821410c417c26e0b414145f09b8280304137050060626c0a20c0c11024dc11a060c11a060811a06081182240c182240c102280c1004dd11840e41b806204212000c10048003050bc93844dd110491e11048881240018226e88822400182070010208405082068801214083e07603104088181029010226a030298c08a5091e1103023185099d0c1a80420019480408390309018103005022760302820082284010c441c830318883020910182091018209101828800c2384101838910de13c2011030281814080c06060302818124008108e0305018189043883068181020b40e090720c0a03020e4180c082380c1000406060602010e060b40e0a03030181009b8222400508900c01401802102289a82202803003004189a8225420500600640a010826a0895081401801902804205f1350440518800c11682003004289a82223c0508800c01001802102200593504405006006008314726e4d41101401801802100a41111001c0304580600841471842f85c13726a0880a00c00c010b17c0ec148220280380608b41001802164dc900162240380600a00c01081143089a8220294400640800c01091840bc110160294400600600848be26a0bd1101602844106206408514726a4800b11201c8300320420450c226a0a51121401c0304580840c810b1842f814a221360508800e01822d03204309b9352) else (0x1080044d402044d40a0040c5c0220081a3))))))
def genIndex7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x84141363c003c003c003802281f0d25251628399833bc00092f474178f1730d30d61d40719fcd8a505db0cc04a2fc00150ffc0004e7c401bc003c000c56fc00173d0c3ec45735737c00222fb463fc002d53e126bc000c2fcc5ef0983c001c493c6efc003c50e139604b2552a0b2903ac462bc0015557005fc000c4680577c0008dc09d97c003c00095dbc00353f7c00204c908dbc001c473d0c7126fc003d17ccafb80a3c001cdf3f07bc0025377c20a06c555160710c4acc43f849fc003185bc003c001471fc003c0001eb4116accf5c60886420b6a81024381d2d3c00086bcb572d1029be2dee6124bc003c003c003c003c003c00392cbc003c0018e2fc001070fc003c003c000c97f00e3c002811fc00276d152f3c003c003c16c8c35822b1473c00283b904d3414ccc184091434208c39283c003c003c001ca73c0028a63c003c017c003c001829417264a6f5199d37f41f90269dae3464e1be8c1ecd27ac2dc14de2488468a04c78283c000d2b642ebd345ca890a87c003c003c002d6fbc003454fc001527fc0014317853fc0004466018a4221f420872fd2dc0b824584412a5a00d2e7c0b2143d9510c3e20187c00170cfc00082c8b06776b44333c0d7c6e3c00303f2429cc302d53ac4bd800bc003c003c00255dfc003c003c003c003c109804bc003c003a533c002817385fd028bc003c003c0034650c4544513c00085a784ffc0008657c002539e45d7c001866bc3d440fa02c398748413c001021bc003c003c000069f06994697c00180c17019c05bc003c0039817c001d8e0d70544da058bc001c323c00084069443c7199633cb8a8347c003501d4854120fc0aa4b77891bc002894100ed7289057f10dfc003c003121a8cbfc000c4e6c087c003c003459fc0010aabc0031615c13c4180c3c353f81214019b0a4259b3c3cc485380dc162689158e8d009eb247c002c25fc001cd6f0dab86d2c02d8d55421202668385552dc373c0011323c5b7c003c003c5c70eeb920ad123c001823a49ebc1758e7843dfc00258de956d402b51dc45de00071167424ea6ea44210c0c41da544741ad82aec4e2860d09e30590d44d03e8435d572b51e0406b7672027bc001d05f1487c003c003c00181a7c0030c4bc003c8f083f58833c002ca83c0017583c003c003c003c001d37bc000106210cb75c74d8fc00006e68149409a040801410800c55c83033010027d60480870435c10000000010c304304131e0840014d40c20c108c00f00005418201c5001975538004013c00060031831460c214000e1c118906f2e10a72c82840d000314100810200e20c0c02a70023910c36c50c512508f1c00412060022450410430c90023820c00c10032000010421423c10412c400b0011420050150801800430030800800000040090810430030c01031c04031ca2c3) else (if j<2 then (0xc001561e560fc003c003c00280a6135d81c7c003c002d2dbc000427444cfc003c003c00100ffc0021643c00182e7d63fc000bd73c001470bc000366f4153c003c003c003c0000c995b4bc003c003c003c003c003c0035cb7c00080e5091d162bc931920303b40a79d46c0568038f563bc001b683c0018dcbc002c953c000d3710073c003c002dddc5212815604a7c14281b6c013c00242b04ef9c00218619abbc001c8f64024464bc003c003c003c003c003c117c00203686723c003c001115980510497c00084628e740a7d9274d05911ccc61fc00242ef06cbc003c003c00181ea8c67554bc0004517c003c001c62ef23d10e3c003c001c28ed0151b0a53f3954e00e8145fc04449e505bd8b6c42a4417cc076c96240b78521940043a2433fcb8e435bc003c003c00085970a66c8d1c5fa46b102b786ab4a9341ba0f23419fc00109f686599467c003c000cba3c003c2f8426145f3c001086fc003c002e3efc000ca76844155d501e2064603e54233c003c003827113a1b3cd42a0c527c000c2f31678437a4393c003c002c037c001a4dbc00391730533c000c52a8d49830cb0b00c53c003403bc003547c5623c003c001c37c458d470784b7c000866eda889153c0017a8bc0005303c00204c3c003c003c0000dcf02264b63c001815fc0014dc6d154d5f3c000ccc9c09a3693c00109c7c003c000045bc00252598313c001c6c3066795ec0123d393c000022f418c80f7c003c002c693c0000d339b72c366dc639abe949fc003c003c000c51fc000044e570380c582cfc003c001040c0717c00100c84a280aad962fc003c002cc8bb077c001006f0d9013ff45cfc3d24247c003c1d61713c0025312815bc001408951e446d55266b0a641b2d16fc00296ed45e6094d1271447b957a439e56916636dc97c0015e068e3540cd9a3d0e145733d4d58da6cd1756fe4e13055110eac51b493bc001d408919fc000c2424474001ed468067ec26f455e8ba789ec837746ebc20d033700bf42d7c003c003b5cd449a447d1543096d848a52068f2f5527c001d619450a493742abc003c001c502872b13a7c000565383fac3c9c452734d0353c00342c7c000044680f2170840310687832fc000555fc003c000ca04423c1242c44b46a3c003564bc00245a80307c0000c394d47c00081d2432bc00396084c754118d33fc000403d8537c67441ff0057c003c003c0034c13c00346dfc0014253c003c002027fc003c003c003c003c003c003c000859a42e358b3c000cbb3c003c003c0036207c003c003c00084efc000c55a8956571684b90097008c86238067c0014403c003c00114380f0092c7c000ce868363c34b48d7c000c1abc002c56575750d70852fc003c003c00156e1014bc5e20600800f45b1e613c003c003c000442bc00044f61d803503c003c003c003) else (0x4733c003c003c003c003c00086065d0bc003c0000394b0b6d2bcc0afc001c583c00083db845c765d4834ccdbc003c0021463c003c003c000d4e7c003c003c003c003c00204d7c00288cf85a38134cb124207b41b538bc0034663c002457bc00202f7c002f1b68d2d0e88461881bd52e88160417bc001d4bbc001016453cbc00384dcd2efc16bc003c003c003c00086b7c00255ebc0034de113418063c0019583c00198e41644917ac21fc00245074133c0009607c003c0000c2914302043c000c217c003c003964fc0030a9fc003c003c003c003c000cdd3c00134fb52cc00bb88cbc003c003c00051d7d35940815537463bc003c003c003c0039b204bee1260842cb6a7c002412d8c57d39b0e1bd1a7c002c62746ffd197c0037c1842bbc003c00146a7c00283ffc003c0034433c0037dc552fd44abc003c003c00291901e0981cfc003c00105569545072346cd91dac257c003c003c003c003f30bc000467005d085c8453b3337c003c003c003c00206f5c4a3c003c003c003bdcf90f3d1bbd6f3c003c0000d9fcc8fc000c38a03aa1559c427c003c00388fe44f3c000c65f65e3c003c001ca4fc003c003c000041bc003c000e47583bfc003c00080d3c003c00242bd45ebc0000561d51fd5e5c1a3c001dee3c001925586fbc001c07c144941de03a445c3f659c436843bd1a986adc043c003c003c0014614547a868e8486c248034f8193831f440b1bc8c236446c0a3001f7c001804f33d7c10e4291525fc002de7001c3841fc00380db5383c003c003c0024d6a9eddd1c7c003c003825a431bc632c95d867bc003c003c003c003c003c000c5f7c000c5afc0018c25c1cb4197c00251ffc001d51bc003c00051bc05b90482cd65010649dd8637c003c003c000461042850324950d4a23c003c0039384ce4cb495d71b0547cbaec543c003c003c003c003f21fc0008da385480967c003c003c003c003c003c003c00346f0048d972e34b616e6d15d1ddbc003c001872634cd8ac3c000073482d892228e309d73c003c003c0024111013bb5f5581e46dbc001030bc000835684fa0d0ecc32007811cb829b81e7c0028203c002c145c70075bb03c4930d570fc003c000c6b953ebc003c127c003c0005553c0020b1bc00022c14683c003c003c003c2d3b597c00003b144e9c36f)))
def genData8 (j : Nat) : Nat := if 35 ≤ j then 0 else (if j<17 then (if j<8 then (if j<4 then (if j<2 then (if j<1 then (0xe831cb109de831ca109de831c9619de831c9609de831c9509de831c9109de831c8109dd83dd8509dd83dd0209dd839d2209dd839d1209dd839d0209dd839cb619dd839cb609dd839cb109dd839ca619dd839ca609dd839ca509dd839ca109dd839c9109dd839c8619dd839c8609dd839c8509dd839c8109dd831db109dd831da509dd831da209dd831da109dd831d9509dd831d9109dd831d8509dd831d8109dd831d6209dd831d6109dd831d5609dd831d4109dd831d1209dd831d0209dd831cb109dd831ca109dd831c9619dd831c9609dd831c9509dd831c9109dd831c8109dd829cc619dd829cc609dd829cc509dc874d9309dc874d5309be84dd8209be841da209be841d9209be841d8209be841d6209be841cb109be841ca109be841c9619be841c9609be841c9509be841c9109be841c8109bd879d0209bd84dd8209bd841da209bd841d9209bd841d8209bd841d6209bd841cb109bd841ca109bd841c9619bd841c9609bd841c9509bd841c9109bd841c81097f875405097e85ddb1097e85dd83097e85dd02097e85dcf1097e85dcb1097e859c66097e859c63097e859c62097e851db3097e851db1097e851da3097e851da2097e851da1097e851d93097e851d91097e851d83097e851d81097e851d12097e851d02097e851cf1097e851ce1097e851cd6097e851cd1097e851cc1097e851cb1097e851ca1097e851c96097e851c91097e851c81097d879d43097d85ddb1097d85dd83097d85dd02097d85dcf1097d85dcb1097d859c66097d859c63097d859c62097d859c41097d851db3097d851db1097d851da3097d851da2097d851da1097d851d93097d851d91097d851d83097d851d81097d851d12097d851d02097d851cf1097d851ce1097d851cd6097d851cd1097d851cc1097d851cb1097d851ca1097d851c96097d851c91097d851c8108ff87584618ff87580608fe86dd4308fe86dd0208fe861d8508fe861d8318fe861d8308fe861d8208fe861d6308fe861d6208fe861d6108fe861d5308fe861d4308fe861d4108fe861d1208fe861d0208fe861cf108fe861ce108fe861cd508fe861cd108fe861cc108fe861cb108fe861ca108fe861c9508fe861c9108fe861c8108fd879d8508fd879d8318fd879d8308fd879d8208fd86dd4308fd86dd0208fd861d6308fd861d6208fd861d6108fd861d5308fd861d4308fd861d4108fd861d1208fd861d0208fd861cf108fd861ce108fd861cd508fd861cd108fd861cc108fd861cb108fd861ca108fd861c9508fd861c9108fd861c8105f687dc1101fd8784010fc1204c910d725781510d715701510d69505c850d59505cc50c79505d850be18201510bd18301510b9584ccb10b9584cc910b7285dc110af1860151097b8754050975859c660975859c630975859c620975859c410) else (0x1dc8109f6819d7609f6819d7309f6819d6609f6819d6309f6819d6209f6819d5309f6819d4609f6819d4309f6811db309f6811da509f6811da309f6811da209f6811d9509f6811d9309f6811d9209f6811d8509f6811d8319f6811d8309f6811d8209f6811d8109f6811d6309f6811d6209f6811d5609f6811d5309f6811d4309f6811d4109f6811d1209f6811d0209f6811cd609f6811cd509f6811cc109f6811c9609f6811c9509f6811c8109f587d4f109f587d4d109f587d4b109f587d49109f587c54109f587997109f587995109f587415109f587197109f587195109f58718f109f58718d109f58718b109f587189109f58714f109f58714d109f58714b109f587149109f58710b109f587109109f5859c6609f5859c6309f5859c6209f5859c4609f5859c4309f5859c4209f5859c4109f581dda509f581dda309f581dda209f581dd9509f581dd8509f581dd8309f581dd8209f581dd4309f581dd2209f581dd0209f581dcd509f581dc9509f5819d7609f5819d7309f5819d6609f5819d6309f5819d6209f5819d5309f5819d4609f5819d4309f5815d4109f5811db309f5811da509f5811da309f5811da209f5811d9509f5811d9309f5811d9209f5811d8509f5811d8309f5811d8209f5811d6309f5811d6209f5811d5609f5811d5309f5811d4309f5811d1209f5811d0209f5811cd609f5811cd509f5811c9609f5811c9509f487459319f487459109f487455109f48744d109f487449109ef87480209ee82dd8509ee82dd8309ee82dd4309ee821db309ee821db109ee821da509ee821da319ee821da309ee821da109ee821d9509ee821d9309ee821d9109ee821d8509ee821d8309ee821d8109ee821d6309ee821d6109ee821d5609ee821d5309ee821d4309ee821d4109ee821d0209ee821cf109ee821ce109ee821cd619ee821cd609ee821cd509ee821cd109ee821cc109ed82dd8509ed82dd8309ed82dd4309ed821db309ed821db109ed821da509ed821da319ed821da309ed821da109ed821d9509ed821d9309ed821d9109ed821d8509ed821d8309ed821d8109ed821d6309ed821d6109ed821d5609ed821d5309ed821d4309ed821d4109ed821cf109ed821ce109ed821cd619ed821cd609ed821cd509ed821cd109ed821cc109df874c4319df874c0309df825cc619df825cc609df825cc509de83dd8509de83dd0209de839d2209de839d1209de839d0209de839cb619de839cb609de839cb109de839ca619de839ca609de839ca509de839ca109de839c9109de839c8619de839c8609de839c8509de839c8109de831db109de831da509de831da209de831da109de831d9509de831d9109de831d8509de831d8309de831d8109de831d6209de831d6109de831d5609de831d4309de831d4109de831d1209de831d0209d)) else (if j<3 then (0xc910b9d84cc810b7b8754050b7b8154050b7a85c4210b7a85c4110b7a85c1a50b7987d4250b798594050b788541950b7685ddb10b7685dcf10b7685dcb10b7685dc110b76851db10b76851d910b76851cf10b76851cd10b76851cb10b76851c910b768518f10b768518d10b768518b10b768518910b768510b10b768510910b768505b10b768505910b768504f10b768504d10b768504b10b768504910b768501b10b768501910b768500f10b768500d10b768500b10b768500910b7585ddb10b7585dcf10b7585dcb10b7585dc110b7585c4210b7585c4010b75859c660b75859c630b75859c620b75851db10b75851d910b75851cf10b75851cd10b75851cb10b75851c910b758518f10b758518d10b758518b10b758518910b758510b10b758510910b758505b10b758505910b758504f10b758504d10b758504b10b758504910b758501b10b758501910b758500f10b758500d10b758500b10b758500910afa80d9760afa80d8f60afa80d8b60af987d8260af98601610af98601510af6861cf10af6861cd10af6861cb10af6861c910af68614f10af68614d10af68614b10af68614910af68610b10af68610910af68604f10af68604d10af68604b10af68604910af68601710af68601510af68600f10af68600d10af68600b10af68600910af681d8f61af587d8661af5861cf10af5861cd10af5861cb10af5861c910af58614f10af58614d10af58614b10af58614910af58610b10af58610910af58604f10af58604d10af58604b10af58604910af58601710af58601510af58600f10af58600d10af58600b10af586009109fb87580609fb874c0309fb87440109fa80dd8319fa80dd4109fa801da319fa801d9319fa801d8509fa801d8319fa801d8309fa801d8209fa801d8109fa801d4309fa801d0209fa801cd619fa801cc109fa801c9619fa801c8109f980dd8319f9801da319f9801d9319f9801d8319f9801cd619f9801c9619f887419509f887419309f887419209f887419109f887411209f88740d109f887409109f787c54109f787584619f787454109f787440109f7855c6609f7855c6309f7855c6209f7855c4609f7855c4309f7855c4209f687d4f109f687d4d109f687d4b109f687d49109f687c19109f687c15109f687c0d109f687c09109f687997109f687995109f687859109f687855109f68784d109f687849109f6871d5109f687197109f687195109f68718f109f68718d109f68718b109f687189109f68714f109f68714d109f68714b109f687149109f68710b109f687109109f687019109f687015109f68700d109f687009109f681dda509f681dda309f681dda209f681dd9509f681dd8509f681dd8309f681dd8209f681dd8109f681dd4309f681dd2209f681dd0209f681dcd509f681dcc109f681dc9509f68) else (0x10bf180cc910bf180c5610bf180c5410bf1809d910bf1809d510bf1809cd10bf1809c910bf18098d10bf18098910bf18094d10bf18094910bf18090910bf1808c910bf18081910bf18080d10bf18080910bf18058d10bf18058910bf18050910bf1804c910bf1801db10bf1801cf10bf1801cb10bf18019710bf18019510bf18018f10bf18018d10bf18018b10bf18018910bf18014f10bf18014d10bf18014b10bf18014910bf18010b10bf18010910bf08741910bf08740d10bf08740910bf08541910bf08540d10bf08540910bf080d4d10bf080d4910bf08099510bf08059510bf08054d10bf08054910bf08045510bea82c1a20bea82c1620bea82c1220be987c8220be98201610be98201510be6821db10be6821d910be6821cf10be6821cd10be68219710be68219510be68218f10be68218d10be68214f10be68214d10be68205b10be68205910be68204f10be68204d10be68201b10be68201910be68201710be68201510be68200f10be68200d10be5821db10be5821d910be5821cf10be5821cd10be58219710be58219510be58218f10be58218d10be58214f10be58214d10be58205b10be58205910be58204f10be58204d10be58201b10be58201910be58201710be58201510be58200f10be58200d10bda83c1a30bda83c1630bda80cdb30bda80cd730bd987cc230bd98301610bd98301510bd784ccb10bd784cc910bd7844c910bd683c5a31bd6839cb10bd6839c910bd68398b10bd68398910bd68394b10bd68394910bd68390b10bd68390910bd68384b10bd68384910bd68380b10bd68380910bd6831db10bd6831d910bd6831cb10bd6831c910bd68319710bd68319510bd68318b10bd68318910bd68314b10bd68314910bd68310b10bd68310910bd68305b10bd68305910bd68304b10bd68304910bd68301b10bd68301910bd68301710bd68301510bd68300b10bd68300910bd587cc631bd584ccb10bd584cc910bd5844c910bd5839cb10bd5839c910bd58398b10bd58398910bd58394b10bd58394910bd58390b10bd58390910bd5838c910bd58384b10bd58384910bd58380b10bd58380910bd5831db10bd5831d910bd5831cb10bd5831c910bd58319710bd58319510bd58318b10bd58318910bd58314b10bd58314910bd58310b10bd58310910bd58305b10bd58305910bd58304b10bd58304910bd58301b10bd58301910bd58301710bd58301510bd58300b10bd58300910bcd83c9120bb684ccb10bb684cc910bb6841cb10bb6841c910bb68418b10bb68418910bb68414b10bb68414910bb68404b10bb68404910bb68400b10bb68400910bb584ccb10bb584cc910bb5841cb10bb5841c910bb58418b10bb58418910bb58414b10bb58414910bb58404b10bb58404910bb58400b10bb58400910b9d84cca10b9d84c))) else (if j<6 then (if j<5 then (0xd6e755c860d6e755c830d6d759c860d6d759c830d6d755c860d6d755c830d6d505c850d5f305d430d5e759cc60d5e755cc60d5d759cc60d5d755cc60d5d505cc50d5d305d430d3e759d020d3e755d020d3d755d020cfb67c1a50cfb67c1a30cfb67c1a20cfb67c1a10cfb6798060cfa769c031cfa765c031cfa505d850cfa305d830cfa205d820cf987d8260cf9769c031cf9765c031cf9305d830cf86741910cf7769db10cf7769d910cf767c5b10cf767c5a31cf76798461cf6769c450cf6769c430cf6769c420cf6765c450cf6765c430cf6765c420cf66785910cf6315d831cf587d8661cf5769c450cf5769c430cf5769c420cf5765c450cf5765c430cf5765c420cef615c861cef605c860cee769c850cee769c830cee765c850cee765c830ced769c850ced769c830ced765c850ced765c830ced615c861ced605c860ced205d820cdf67cdb30cdf615cc61cdf605cc60cdf37d8f60cdf305d830cde769cc50cde765cc50cdd769cc50cdd765cc50cdd615cc61cdd605cc60cdd315d831cdd305d830cbe769d020cbe765d020cbd769d020cbd765d020c7f605d460c7e769d430c7e765d430c7d769d430c7d765d430c7d605d460c7d505d850bf38640d10bf38640910bf38440910bf38341910bf38340910bf38241910bf38240d10bf380d4d10bf380d4910bf38099510bf3805d910bf3805d510bf3805cd10bf3805c910bf38059510bf38054d10bf38054910bf287c1910bf287c0d10bf287c0910bf28781510bf28741910bf28740d10bf28740910bf28701510bf285dc110bf285c1910bf285c0d10bf285c0910bf28581510bf28501510bf281c1a10bf281c1910bf281c0e10bf281c0d10bf281c0a10bf281c0910bf28181610bf28101610bf28101510bf280d9510bf280d8d10bf280d8910bf280cc910bf280c5b10bf280c5710bf280c5510bf280c4f10bf280c4b10bf28098d10bf28098910bf28094d10bf28094910bf28090910bf2808c910bf28085910bf28084d10bf28084910bf28058d10bf28058910bf28050910bf2804c910bf28019710bf28019510bf28018f10bf28018d10bf28018b10bf28018910bf28014f10bf28014d10bf28014b10bf28014910bf28010b10bf28010910bf28005b10bf28005910bf28004f10bf28004d10bf28004b10bf28004910bf28001910bf28000d10bf28000910bf187c4210bf186dc110bf186c0d10bf186c0910bf18681510bf18601510bf184c0910bf183dc110bf183c1910bf183c0910bf18381510bf18301510bf182dc110bf182c1910bf182c0d10bf18281510bf18201510bf181c1a30bf181c1a20bf181c1930bf181c1920bf181c1630bf181c1620bf181c1530bf181c1120bf18194050bf180ddb10bf180dd710bf180dcf10bf180dcb10bf180d9510bf180d8d10bf180d89) else (0xf305c830dcf274c810dce839c861dce839c860dce839c850dce835c861dce835c860dce835c850dce835c830dce739c861dce739c860dce739c850dce735c861dce735c860dce735c850dcd839c861dcd839c860dcd839c850dcd835c861dcd835c860dcd835c850dcd739c861dcd739c860dcd739c850dcd735c861dcd735c860dcd735c850dcd305c830dcd274c810dba205d020db9205d020db6749c420db6745c420db5749c420db5745c420daf205d020dae749c861dae749c860dae749c850dae749c830dae745c861dae745c860dae745c850dae745c830dad745c861dad745c860dad745c850dad745c830dad205d020dac4749120d9e839d020d9e835d020d9d839d020d9d835d020d7b8754050d7b57c1630d7b57c1620d7b5794050d7a759c061d7a759c031d7a755c061d7a755c031d7a605d460d7a5781510d7a305d430d79755c061d79755c031d79605d460d795701610d795701510d7950dd850d79505d850d79505cc50d79505c850d79305d430d785741630d785741620d785741530d77875d710d77865d710d77855d710d77835d710d77825d710d77765d710d77759d710d77759d510d7757c5410d77165d710d77065d710d76865d710d76859c660d76859c630d76859c620d76859c410d76835d710d76825d710d76819d710d76819d460d76819d430d76815d710d76815d460d76815d430d76765d710d76759c460d76759c430d76759c420d76755c460d76755c430d76755c420d765785510d765781510d765745410d765741510d76165d710d76065d710d75865d710d75859c660d75859c630d75859c620d75859c410d75835d710d75825d710d75819d460d75819d430d75815d460d75815d430d75805d710d75765d710d7575dcf10d7575dcb10d7575d8f10d7575d8b10d7575ccb10d7575c4f10d7575c4b10d7575c0f10d7575c0b10d75759cf10d75759cb10d75759c460d75759c430d75759c420d757598f10d757598b10d757590b10d757584f10d757584b10d757580f10d757580b10d75755cf10d75755cb10d75755c460d75755c430d75755c420d757558f10d757558b10d757550b10d757544f10d757544b10d757540f10d757540b10d75751d710d75751d510d75751cf10d75751cb10d757518f10d757518b10d757510b10d757504f10d757504b10d757500f10d757500b10d7557d9710d7557d4f10d7557d4d10d7557d4b10d7557d4910d7557c5410d755799710d755799510d755794f10d755794b10d755781710d755759710d755759510d755754f10d755754d10d755754b10d755754910d755741710d755719710d755714f10d755714b10d755701710d75165d710d75065d710d74865d710d74835d710d74825d710d74815d710d74765d710d74165d710d74065d710d6e759c860d6e759c830)) else (if j<7 then (0x4c910fd23740d10fd230cc910fd2304c910fd220cc910fd2204c910fd205cc910fd18301510fd180cc910fd1804c910fd130cc910fd13098d10fd13094d10fd13058d10fd13054d10fd1304c910fd120cc910fd106cc910fd1064c910fd104cc910fd1044c910fd03740d10fd005cc910fc7328c910fc6244c910fc5204c910fc4244c910fa94241120fa74290b10fa74290910fa54210b10fa54210910f9684ccb10f9684cc910f9584ccb10f9584cc910f735701510f735101510f7350d4d10f7350d4910f73509c650f735099510f73505c650f735059510f735054d10f735054910f730581710f730581510f7285dc110f7285c4210f728501510f728154050f725781510f7185dc110f7185c4210f718154050f715701510f715101510f71509c450f71505c450f710501710f710501510f705781510f69509c850f69505c850f675294b10f675294910f595341530f59509cc50f59505cc50f575394f10f575394d10ef38641910ef3609c660ef3605c660ef30681b10ef30681910ef28601510ef26741910ef18601510ef160d9510ef160d8d10ef160d8910ef16059510ef16058d10ef16058910ef10601b10ef06741910ee96241920ee76298b10ee76298910ed96341930ed76398f10ed76398d10ed56345931e796541950e79509d850e79505d850e776599710e776599510df3805d510df375c0d10df375c0910df37540d10df37540910df3505c650df31784010df31744010df306dd510df3065c650df3065c630df3065c620df3045c620df287c1910df287c0d10df287c0910df28781510df28701510df2815c061df2815c031df2809c660df2809c630df2809c620df2615c061df2605c460df25781510df25701510df2315c031df2305c430df2205c420df187c4210df180dd510df1615c061df1605c460df15781510df15701510df1315c031df1305c430df1205c420df106dd510df1065c650df1065c630df1065c620deb27c0a10deb2788020dea729c061dea729c031dea725c061dea725c031dea605c860dea505c850de9729c061de9725c061de9725c031de9605c860de7729cb10de7729c910de727c4b10de6729c460de6729c450de6729c430de6725c460de6725c450de6725c430de6615c861de62784910de5729c460de5729c450de5729c430de5725c460de5725c450de5725c430de5615c861ddb37c0e10ddb378c030dda739c061dda735c061dda605cc60dda505cc50dd987cc230dd9739c061dd9735c061dd9605cc60dd775cc910dd7739cf10dd7739cd10dd737c4f10dd7378c431dd6739c460dd6739c450dd6739c420dd6735c460dd6735c450dd6735c420dd671cc810dd6714c810dd6615cc61dd63784d10dd575cc910dd5739c460dd5739c450dd5735c460dd5735c450dd5735c420dd5615cc61dc) else (0x8910ef76758910ef76558910ef76458910ef76158910ef76058910ef56758910ef56558b10ef56558910ef56458910ef56158910ef56058b10ef56058910eed62d9120eed62d8520eed6259120eed6258520df976c1120df97640a10df97640910df906dd120df906dc520df9065d220df9065d120df9065ca50df9065ca30df9065ca10df9065c910df77558910df67158950df5865d510df5825d510df5765d510df5765c910df57644910df5755c910df57558b10df57558910df57544910df5645c620df5629c650df5629c450df5625c650df5625c630df5625c450df5265c620df5165d510df5165c910def2758a50def2758950def2758850ded869c850ded865c850ded76c9120ded7649120ded2758a50ded2758a30ded2758a10ded2758910ded2758850ded26dd120ded26dc520dde7358850ddd7358850dbe7458850dbd7458850dbd4759220dbd4759120d7d5759510d7d5754910cff7458960cff6758a50cff6758950cff6758850cfd829d850cfd825d850cfd67d9120cfd6759220cfd6759120cfd6758a50cfd6758a30cfd6758a10cfd6758950cfd6758910cfd6758850cfd6749a20cfd62dc560bfb8541920bfb8441920bfb8141920bf986c1120bf980d9120bf980d8520bf98098960bf98081920bf98059120bf98058a10bf98058910bf78758910bf78558910bf78458910bf78358910bf78158910bf78058910bf68690910bf68650910bf68610910bf58759510bf58758910bf58754910bf5869c910bf58698910bf58694910bf58690910bf5868c910bf58684910bf58680910bf58654b10bf58654910bf58650910bf5864c910bf58610910bf584d8910bf5844c910bf582d9510bf582d8d10bf5829d910bf58285910bf58281910bf58159510bf58158910bf58154910bf58058b10bf58058910bed86c9120bed82d9120bed82d8520bed8281920bed8259120bdd839c960bdd8398960aff8458960afd8698960afd84d8960afd82d9560afd82d8d609ff8758a509ff87589509ff87588509ff845d9209ff815d9209fd87d91209fd87d85209fd87595109fd87592209fd87591209fd8758a509fd8758a309fd8758a109fd87589109fd87588509fd87549109fd87419209fd86dd1209fd86dc5209fd869ca509fd869c8509fd84dc9609fd82dd5609fd82dcd609fd82dc5609fd829da509fd829d9509fd829d850fe38240910fe3209c620fe3205c620fe30280b10fe30280910fe28201510fe22740910fe18201510fe12098910fe12094910fe12090910fe1208c910fe12058910fe12054910fe12050910fe1204c910fe02740910fd38340d10fd370cc910fd3704c910fd3309c630fd3305c630fd310cca10fd306cc910fd3064c910fd304cc910fd3044c910fd30380f10fd30380d10fd28301510fd280cc910fd28)))) else (if j<12 then (if j<10 then (if j<9 then (0x3a0a7b829ac0a5a829280a39828a40a188282009f50278809cc826e6099f0263009790258e0950824d809230244008ff823b208dc0232e08b602282087c0215e08330204407fe01fac07d801f1407b201e86079101e02077001d7e074c81ce6072681c2606f901b9806d301b0006a301a4a067f819b20659819240638818a006178181c05f68178e05d0816f605ad016680587015da056381542053d8149605150140804ef0137004c4012ce04a081240047f811bc045e81138043d810aa04178101203f400f8403ce00ef603aa80e5e038480db2035c00d24033600c8c030b00bea02e780b5c02c680aba0287809aa02398082201d78069a01758054e01390040c00d200284007c8014c002c00000ff98441920ff98241920ff98058a50ff98058950ff96540910ff90654910ff90650930ff90558520ff58758910ff58558910ff58058910ff57654910ff57558910ff5655c910ff56544910ff5644c910ff56350910ff51654910ff51558910fed2654910fed2650930fed2558520fdd3650930f7d5654910efd8058960efd7458960efd6558910efd6458930efd6258550dff845d920dff815d920dfd8758a50dfd8758950dfd8758850dfd845d920dfd815d920dfd7654910dfd7650930dfd7558910dfd7558520dfd745c960dfd655c910bff845c960bff8158950bfd8654910bfd8650930ff36540910ff36340910ff30458910ff30358910ff28640910ff28241910ff28058910ff27640910ff26058910ff22058910ff21640910ff20640910ff2055c910ff20558910ff18640910ff18241910ff18058910ff17681510ff17640910ff17540910ff16540910ff16340910ff16098910ff16058910ff120d8910ff12058910ff11640910ff1069c910ff10694910ff10690910ff1068c910ff10684910ff10680910ff1065d510ff1065c910ff10654910ff10650910ff1064c910ff10644910ff10640b10ff10640910ff10610910ff104d8910ff10458910ff1044c910ff10358910ff10350910ff00558910fea6241920fe96241920fe926c1120fe92058a10fe92058910fe92054910fe906c9120fe90649120fe72758910fe72158910fe72058910fe52758910fe52694910fe52690910fe5268c910fe52654b10fe52654910fe52650910fe5264c910fe52158910fe52058b10fe52058910fd7644c910fd6764c910fd6364c910fd6064c910fd5844c910fd5764c910fd564cc910fd5644c910fd5364c910fd5344c910fd526cc910fd5064c910fb94059120fad4259120f7b5058a50f795058850f755759510f755754910f755654b10f755654910f755159510f755154910efb6241920ef96241a20ef96241920ef960d9120ef96059510ef96059220ef96059120ef96058a50ef96058a30ef96058a10ef96058950ef96058930ef9605) else (0x7d8d1a034438d0c234200d03e33ff0cfba33db8cf2c33b80ce9433920cdfc33648cd1e332d0cc4032f80cb7632ca8cab6329a8c9f6326a8c936323a8c89e32148c7fc31ec0c75a31aa8c62c316e0c56c31480c4a231158c40a30ef8c37230c48c29e308f8c1ca305a8c100302d0c0402ffd0bf802fcd0bede2fa48be3c2f7c0bd9a2f470bcd02f210bc382efb0bba02ed00bacc2e9b0b9f82e660b92e2e388b86e2e088b7ae2dd88b70c2db00b66a2d878b5c82d370b4542cf58b3942cd48b3062ca70b25a2c860b1d62c650b1522c418b0ba2c118affa2be18af3a2bbe0aeac2b9a8ae282b6d0ad402b330ac582af90ab702ac18aa9c2a8c8a9c82a370a84a29fd0a79429ca8a6c029958a5f629658a518292b8a43a28f40a38428d08a30028af8a20e285f0a11228278a02a27ed89f6a27ae89e1e276809d18272909c1c26e789b2026ab09a2e266e8993c263e898a42613897f825ed8977425cc896b4259c89630257b895ac255a895282539894862511093e424e88931a24a98923c247489168243f89094240a88fc023df88f3c23be88e7c238708dbc235e88d38233d88cb4231c88c2622f688b5222bc88aa62296889fa226b88944223908898220b887ce21e08870421a188608216288516212b0843820e48832820ad0824a20758816c203e08098200907fc41fd407ef01fa187de01f4e87c941efe07b521eab07a101e738798c1e52879121e340788e1e130780a1def8777c1dc4876a81d8f875981d3c8744c1ce9873281ca0871d21c4d870ea1c27870521c0186fc41be086f401bbf86ebc1b9e86e2e1b7886d6e1b4b06ce01b2786c521af786b7e1ac286aaa1a8d869c21a56068ee1a210682e19fb067aa19da066fe19ac86670198b865ec196a8653619358649419148641018f38638218cd862b818960620c1870061741847860d2181785ff417e505f4817bf05eba179e05e36177a85d9e175485d06172e85c6e170b05bea16ea05b6616c905ae216a585a4a1675859941652058fc162c0586415fc0577c15c7056da15a3856381578855781543854ae151b0542a14ed8534214b10525a147c0517c14420509e140d04fca13d804eec13a084e18136904d58134584cd4132484c1e12f704b9a12d604b1612b284a7e1280049b4125a0491c12340487a120b847c411d6846fa11ab846621188045de1153044ce110c843c810d7842e01096041da1059840e8101d03fe20fd683edc0f9503e080f6f03d700f4903ce20f2803c5e0f0703bd00ee103b100eb103a820e8d839ea0e678392a0e2d838560e05037c80dd2836cc0d96035da0d59835240d38834a00d17834120cef033700cc18329c0c8f031f00c69031620c48030d40c24830500c0102fb80bdb02ef80ba102e240b7882d960b5002cf40b2c82c700b0682bc40ad682af00aa182a)) else (if j<11 then (0x6dc619518608616f1857a614e184f6612a984686107183da60e39834c60bd982b4609c9822660769818e604e180e260281805e600717fd05fe117f385fbb17ea05f9797e1c5f7697d985f5597c6a5f0a17be65ed797b1c5eb417a8e5e90979f65e6a979685e49978e45e28978605e07977dc5de6976b85d9d976345d7c975b05d5b9752c5d38174945d14974105cf39738c5cd2973085cb1972845c8e171ec5c659714a5c3f970b25c0f96ffc5bee96f785bcd96ef45baa16e5c5b8196db05b5b96d2c5b3a96ca85b1716c1a5af616b965ad516b085aac96a705a8e169f65a59169225a269683059ec9673459bc9666059739655a59399645458f09634458b41625c587a1619c584a160b4581015fcc57c215e4e576515cda572395bde56e495b1456b215a4a567f959805643158b6560e1578855c2956965588955ae5551154d05519953fc54d8152ce5491951c85452950c2541394fda53d994ee8539d14e14536a94cfa530d94bb852c714aa852859499852419489252029479651c39469a51849459e5145944a25106943ce50de1432250b3141f45049940584ff193ef84f9c13de84f5a93cec4f1693bd24ed513aea4ea013a024e639394c4e429388c4e08937d64de29370c4da8936564d85135be4d5a135124d20133da4cd2132d44c8e131c44c4c930a04c0b12fc24bd392ee44b9c12e064b6712d324b1692bd24ad792ab84a87129944a48128d44a221283c49f49275e49bd126804985925a24950924ce491b923fa48e69233048bb922a24895921ec48681215448381207647f191f1647a891e38477391d82474d91cea472511c4846f291b7e46cc91adc46a1919f44658918ee4619917f245dd1172845ad1165e457a915a8455711510452e9146e4506113cc44e29133e44bc912884485111aa444d910d644189101643e890f5643b890e96439290dfe436a10d5c434190cba431b90bf042df10b2642b690a5c427a10960423b108a0420b107a441d1106d0419c105f2416490528412d1042c40f09033a40bb902a24093101f64059100d2401c8fffe3fe78ff2a3fb28fe603f850fda03f528fcd63f250fc483eff0fba63ed68fb043eab8fa123e5d8f8da3e170f7de3ddf8f7143daa8f6363d730f5623d3b8f4703cfc8f3743cbb0f2a03c978f2123c718f15c3c3a0f07e3c028efaa3bcd8eed63b9b0ee203b6b0ed603b3b0eca03b150ec083aec8eb663ac40eaa63a8c8e9aa3a550e8fe3a278e82a39f28e75639c00e68c39900e5ea39560e4c6391e8e42e38f10e35038bc0e27c388c0e1bc385c0e11a382c0e02837f20df7c37c48dea837948de06376c0dd64373c0dca437138dbf836d70db1036b10da6e36860d9c2365b0d90c36238d82e35ec0d75035b70d69035848d5bc354f8d4e8351a8d42834f70d39034ce8d2ee34a60d24c34) else (0xfeaa3f368fbaa3e768f80a3d8e8f4e23cc48f16a3be68ee923b448eb423a528e7a2397e8e47a38b48e0da37c28dd3a37028dada36608d85235be8d5ca35268d36a347a8d06a33ba8cd6a32b48c8b231a48c4c230ee8c28a301a8be222f3c8bb9a2e7c8b84a2da88b4fa2cd48b2222c328af9a2b728abfa2ab28a8fa29ca8a50a28b08a05227c889d5226f489a022616896b22506891aa23ec88e0a22be888622190883fa20bc8814a1fde87d5a1eec87a0a1dfa8766a1d308731a1c5c86fa21b6086b3a1a3c8674a1968863aa186c8608217de85e2216f68599215e68566a1544853ba1484850e213ce84e0a133684ae2121c8467a1134843a2109c84142100483f0a0f7683caa0eca8395a0dba835ba0d228330a0c4e8300a0bb682daa0b1e82b4a0a868291209f88259a08c0820ba079281bb20646817ea05b881422049e810aa038480c6a02a68073a01328039a009a800c1ffbc7fd49fee87f9f9fe147f6d1fd047f309fc447ef69fb8e7ed09faf67eaa9fa5e7e871f9da7e521f8fc7e2c1f8647e061f7c27ddb1f7207db51f6427d761f5967d551f5127d251f4487cd71f2707c8b9f1927c429f0827c011ef5e7ba41edc27b3d1eca87b199ec1a7af39eb827ad01eaf47aac9ea667a869e9d87a3b1e8a07a151e80879f19e78479d09e6f679ad1e67279899e5da79639e54c79429e4be791f1e43a78d39e30278b01e274788a1e1dc78669e11278319e07a77e39df1a77b39de82778d9ddf4776c9dd70774b9dce277281dc5e76fd1db7676ca9dade76909d9f6766d1d96876499d8e475fe1d7b675c91d6b075919d5dc755c9d508752a1d44875019d3c474e09d33674ba9d2a874859d18e74441d09c740a1cfbe73dc9cf2673b91ce9873931ce0a736d1cd36733d1cc76730d1cbf272ec1cb6e72cb1caea72aa1ca6672891c9d872631c94a72421c8bc721c1c82e71fb1c79671d51c6d671989c5c6714f9c484710e1c3ec70ea9c35e70c49c2c670a11c238707b1c1aa70579c11c700c1bfe46fd99bf1a6f931bdc46f541bcc86f1f1bc306efb9bb2a6eb79ba886e851b9a06e551b9086e2f1b8486dff1b7ba6dc79b6b46d929b5e06d5d9b5166d2d9b4426cf61b36e6ccb1b2c26c989b1806c4f9b0fc6c2e9b06e6c0b1afea6be79af2a6bba1ae7e6b671ad006b191abd26ad01aaae6a899a99e6a4d1a88e69f79a74c69ac1a63c69541a4fa69291a41268e29a32068b29a274688c9a1f0685a1a0ea68279a05c680699fba67d919f0e67a199e08676519d20672399c0666ee99b7866cd99a9a6687199b2664819898660b997d865e31974065ba99694658f995e865649953c65399949a65139939464c31928e6481991886447990b4641018fe063e018eda638318d70633298c4262ec18b2862a098a1862709896c624a9883e61f29878861cc98))) else (if j<14 then (if j<13 then (0x3d0dcab290a10809d068160480e02806008f8ee3509c20862148420c82204800b11c3b0dc350b0250882007818050120400c0280801804009311c3b0dc350b0250882007818050120400c0280801804009311c3b0dc350b0250882007818050120400c028080180400933183b0dc352aca42842027418050120400c028080180400933183b0dc352aca42842027418050120400c02808018040093128450ee390ca238881c0641881a05810d1283d0ec3209e220681881a0428471043c0e4370d82c094220801e06415048110340a024060140254c60ec370d4ab290a10809d06014048100300a02006010024c470ec370d42c094220801e06014048100300a02006010024c481063b0e63509c20862148420c82204800e12c450fe3b8d4330a8260821885210832088120040438ec398d43009c23082188521083208812003c481063b0e6350b42608c2007e1885210832088120046b474ad11ab418acfaab3bcace3ab374acd6ab322acbaab2bcaca12b242ac852b1dcac692b180ac4fab0fcac312b0b4ac26ab080ac122b010abf8aafaaabe42af76abcfaaf1aabbdaaed2ababaae8aab972ae2eab82aadc8ab692ad80ab572ad2eab42aace6ab332ac58aaf6aab5caab7aaa9caa8f2a9c8aa57aa8d6aa0eaa7d0a9d72a6f2a9a22a646a979aa586a949aa4bca90d2a3b6a8ce2a2cea8942a1dca857aa0f4a81daa002a7e629f24a7a9a9e28a76aa9d40a73329c62a6fba9b7aa6cba9abaa696a99f0a661a9908a6252982aa5eda9760a5b8a968ca58da95b8a54ea94e4a5262941aa4e4a9314a4ad29240a4732914ea4392907aa401a8f6aa3bda8ea0a39028db8a34ea8ca8a30d28b98a2c6a8a88a27da895aa22fa8840a1f328780a1caa86b6a190a85c4a14f284d2a11a283e0a0d1282eea0a3a8242a07b28178a048a80cca01da80209ff2a7f7e9fca27eaa9f9027dcc9f53a7cda9f1c27c109eec27b3c9eb227a4a9e7d279949e4d278d49e1d278149defa77729dc7276d09d9ea762e9d762758c9d50274f49d27a74209ceda73569cbb2728c9c90271e09c5da70ee9c19a6fe89bdaa6ef69ba0a6e049b6426d1c9b27a6c349af7a6b889acca6ab49a8da69c29a5da69169a32a687e9a0ca67d299d7a670899aca663e9972a65569938a64969910263c298cea62ee98a62624c987626164983c260a498162600c97f025f7497ca25ed2979ca5dfe9767a5d529741a5cba971ba5c2296f325b7696c825aca969d25a149665a592c962e2583a95ef2573e95b02564c9573a555a953ea549a950c2539e94c5a52989489251b09447a50829403a4f9093c224e6c937e24d66933024c2e92e724b1492a0a49fa925f248f4921b247f891e12473891b62466e9183a45b89151244d091212442490f3a436e90c3a42909089a41b29054a40f2901fa400a8) else (0x400881800a0911e05c0b0240801c707d1e04409014020047078100200400800181e040080100200060781002004008001825478180300a02060811e0480a01802181e0400701002000607810020040040018224781023c0c018041c1e0408f02003008001c1f478110208701402004807810020870100200070951e060970308b028890208728204781202087018021c1e0400821c04004001c1f478110240420c020048078100200420c0200070891e050930308b01885010832820478120280420c021c1e0400801083004001c1e040070100200068d41f044090140200470781001c0400800181e0400800c0200060d81f044098200500801203607c11024058100200480da350809f078128400a82006810022060038378d42027c1e04a100260801a0400881800e0de350809f078128400a82005810022060038368d41f078118400982005810020060034350901702c09020071c3507c1102405008011c350781002004008001c350781002004008001c350781002004008001c35094180300a02060d4200480a01802181e0400701002000607810020040040018220408f0300601060781023c0800c02000707c110208701402004707810020870100200070d4252901825c0c22c0a2240821cb080120208701802181e0400821c04004001c1f0440901083008011c1e0400801083008001c35088a1050930308b01885010832c200480a010830086078100200420c0100070d01f044090140200470d01e040080100200070781001c0400800181e0400800c020006074100200400800181f044070140200460781001c0400800181e0400800c0200060789d040080100200070789d040080100200070789d040080100200070789d0600c02808181e2741001c04008001c1e2741002004004001c220408f0300601060781023c0800c02000707c110208701402004707810020870100200070781825c0c22c0a2240821c9080120208701802181e0400821c04004001c1f0440901083008011c1e0400801083008001c1e050930308b018850108324200480a010830086078100200420c010007074100200400800181f044070140200460781001c0400800181e0400800c0200060781001c0400800181e0400800c0200060789d040080100200070789d040080100200070789d040080100200070789d0600c02808181e2741001c04008001c1e2741002004004001c220408f0300601060781023c0800c02000707c110208701402004707810020870100200070781825c0c22c0a2240821c9080120208701802181e0400821c04004001c1f0440901083008011c1e0400801083008001c1e050930308b018850108324200480a010830086078100200420c010007078100200400400181e040080100100060bc29088160500e030060109318)) else (if j<15 then (0x80100200070b025088200789d469184390c42908301e2741001c04008001c1e2741002004004001c220408f03108018041c1e0408f02003008001c1f044094200420c020048078100200420c02000708ca10549303509018052108328222841424c0c420062140420ca0781424c0c420062140420c90801202908010830087078100200420c010007074100200400800181e0400800c0200061082c8781825c130481023c0881a0480a0038420b2220609704c120408f03206810c1082c8781825c130481023c088160480e02800f08ca1054930348b018052108328222841424c0c22c062140420ca0e42287c148440c22c050108380a01303808e1f056110348b018052108380a01343808a1e052100308b0180420e02800c0861e052100308b0180420e02800b0e422878148400c22c050108380a00303908a20052120308b0140420e022c3808e1f056110348b024060148420e02804e0e022878148400c22c080180420e02800d0861d052100308b020060108380a00303908a1e052100308b0140420e0280600343507c1102405008011c350781002004008001c350781002004008001c350781002004008001c350b0250882007860d4200480a01802181d04008010020006078100200400400181e2741002004008001c1e2741002004008001c350b0ab094a4088a10809f0789d2c1e2741002004004001c220408f0300601060781023c0800c02000707c110240420c020047078100200420c0200070d8232841524c0d22c060148420cb0d4222841424c0c22c062140420cb0781424c0c22c062140420c9080120280420c02181e0400801083004001c3808e1f056110348b0240601602804c0e022878148400c22c080180480a003021874148400c22c080180480a002c350951e061100300a0210641102400c0789d061100300a0210641102400b078100200300800181e04008010020006088144400c01804181e0400800c0200060789d0400801002000707c11440090108300801201e0400801083008001c23284154440d22c060148420ca088a1051100308b0188501083281e051100308b01885010832420049100280420c021c1e0400801083004001c1e0400800c02000607810020030080018350781002004008001c3508814030060106078100200300800181e2741002004008001c1f0440901083008011c1e0400801083008001c3608ca1054930348b01805210832c35088a1050930308b01885010832c1e050930308b018850108324200480a010830086078100200420c0100070d41e074100200400800201f4781102405008011c1e04007010020006078100200300800181f478110260801402004807d1e044090160400801201e04a1002a0801a0400881800a0781284009820068100220600281e04a1002a080160) else (if j<16 then (0x90d8264901945c0d42c0a0250841cb0d420478124400a4200641002400b0789d049100290801904009002820478124400821c0641002400a0811e049100290801083009002835078100200400c020008074100200400800181e040070100200060781001c04008001824488174500b0240801d06410a07c1102405410020047078100200400800181f04409014020046078100200400800181e040080100200060b02508820079164510e43106410b09522061140300a021064109080120280641002181d040080100200060781001c0400800181e040080100100060789d040080100200070789d040080100200070b025088200789d459144390c41904301e274184500c0280841904241e2741001c04008001c1e2741002004004001c1e0408f02003008001c1f0440821c05410020048078100208701002000709923065150340a0248821d06414b09522061140300a0208741904281e061140300a020874190424200480821c06410021c1e0400821c04004001c1d040080100200060781001c0400800181e040070100200060d42405c0b0240801c70d41f044090140200470d41e040080100200070d81f044090140200470d41e040080100200070d41e040080100200070d42c094220801e1835094180300a02060d4200480a01802181d040080100200060781001c0400800181e040080100100060789d040080100200070789d040080100200070d42c2ac25290222842027c1e274b0789d0600c02808181e2741001c04008001c1e2741002004004001c1f0440821c05008011c1e0400821c04008001c36098a4064970348b02809220872c35094a4060970308b02889020872c1e060970308b028890208724200480821c06008607810020870100100070d81f0440901c0500801203507810020070100200080e02387c15844090180580a01283808a1e052100200601202800a0861d0521002006012028009074100200400800181e0400800c0200060961e0408f0300a0220681202800b0a6220408f0380c42d0a42206810b0961e0408f02c0a022058120380a0030232841524c0d424060148420ca088a105093031080188501083282287c1484409420050108380a012c2387c1584409018052108380a012c2287814840080180420e02800a0861e05210020060108380a00282287814840080140420e02800a08a2005212029080140420e02282387c1584409018052108380a012c2287814840080180420e02800a0861d05210020060108380a00282287814840080140420e02806002c1f0440942005008011c1e04008010020006078100200400800181e040080100200060b025088200791a4610e4310a420b080120290801802181d040080100200060781001c0400800181e040080100100060789d040080100200070789d04) else (0x70789d04008010010007089200408f0310a0180440890781023c0800c02000709520061120300a0208741902281e061120300a0208741902241e0400821c04004001c22480144480c4280601083408a078144480c42806010834089078100200420c01000711c2c0942207c1e2741c8620c0260830470b0250882007c1e276188300a820c11c2c0942207c1e2741c8520c0160430470b0250882007c1e2761483006810c0789d04510025080150400801400b8d42c2ac25290222841f0789d28470b0ab094a4088a10801f0789d2c470b0250882007c1e2761885210832088100280100d42c2ac25290222841f0789d28350b0ab094a4088a10801f0789d2c35094a4060970308b0240821ca0d4252901825c0c22c0a0240821cb0d4222841424c0c22c05010832835088a1050930308b01805010832c1e2741825c0c22c0902087243b0789d060970308b02809020872c1e2741424c0c22c050108324470789d050930308b01805010832c222841023c0c22c050108324222841023c0c22c060140420ca11e350b0250882027c1e862148420c8220400a0040478d42c094220809f07a18852108320881002801011e350b0250882027c1e862148420c8220400a0040460b0250882027c1e862148420c8220400a003c470b0240882027c1e85e148420b8220781002801011c2c094210809f07a1884e1082e088120300a0040478d42c0942207c1e862148420c82204006003c1e04008010020006078100200400800181e040080100200060b025088200785074100200400800181e04007010020006078100200300800181e040070100200060d41e0400801002000707810020030080018470b0250882007a188300a820a11c2c094220801e8520c01a04282c2ac25290222842027c1e274a11c2c090220809f0789d86e1885e0c82c098220740460b0250882027c1e27618852108320881002801011c2c090220809f0789d862148420c8220400a0040470b0250842027c1e27618852108320881002801011c2c090220809f0789d8620c02a0830460b0250882027c1e27618852108320881002801011c2c090220809f0789d85e148420b8220781002801111c2c0942207c1e27618852108320881001800f0d42405c0b0240801c70d41e040080100200070d41e040080100200070d41e040080100200070d42c094220801e1835094180300a02060d4220500c01804181d040080100200060781001c0400800181e0400800c0200060789d040080100200070789d040080100200070d42c2ac25290222842027c1e274b0789d0600c02808181e2741001c04008001c220408f0300601060781023c0800c0200070d4252901825c0c22c0a2240821cb0781825c0c22c0a2240821c90d4222841424c0c22c062140420cb0781424c0c22c062140420c)))))) else (if j<26 then (if j<21 then (if j<19 then (if j<18 then (0x901282047c124440a4240420c02404a078114400942005410020050028461003a0e0360d4340b42608c2007c19054120440d0280901805008015c470b0250881f07918451104310841001400e0d41e040080100200400201e04a1002a0801a0400a002437078128400a8200681002800a0dc1e04a1002a0801a0400a002836078128400a8200681002800a078128400981c06810028009078128400a8200580c0280090789d065110340a026084190540901303d0789d069120380a82106408a0789d05511035090180581102404b11c1e274164480e428068110228350781002004008001c1e04008010020006078100200400800181e040080100200060b0250881f0789d46515449114350a425064150240510dc2c094220801e2751a459124390a419023820478124400a4200641002400a0dc1e274124400a4200641002400b0dc20478124400821c0641002400b0dc20478124400a4200420c02400b0dc1e274120280600870b0250881f0789d46515449114350a425064150240510d42c094220801f0789d469164490e42906408f0951f06111030090208741905409013035094a4480184480c028090208741902342247c144440c4240501083409012c35088a1480144480c428060140420d02341e274184440c0240821d0641502404c0ec1e274184480c028090208741902301e274144440c4240501083409012c470789d051120310a0180501083408c0891f0408f031090140420d02404b088a14801023c0c428060140420d02301e040080100200060d41e274100200400800203507810020870100200080d41e040080108300800201e04008010020006078100200400800181e040080100200060b025088200791a459124390a41902301d040080100200060781001c0400800181e0400800c020006078100200400400181e04007010020006078100200400800181e0400800c0200060781a4480e02889821064089078100200400400181e059120390a0188581102241e040080100100060b025088200789d469164490e42906408d0789d065120340a0260881d06408b0789d04a1002a0801a0400a00281e274128400a8200681002800a0789d04a1002a0801a0400a00281e2741a4480e0290982106408a0789d04a1002a0801a0400a00281e274128400981c0681002800a0912005d1202c090200741902281e04008010020006078100200400800181e040080100200060b025088200791a459124390a419023025480184480c02808419022422480144480c4280601102241d0400801002000607c1101c0500801181e04007010020006078100200300800181e040080100100060789d040080100200070789d040080100200070b025088200789d469164490e42906408d0789d061120300a0210640890789d040070100200) else (0xc11020870140200470dc2007c120440821c0601402004b07c110240420c0200470dc2007c120440a0240420c02004b0d41e040080100200070d41e0400801002000707810020870100200070d41e0400821c0400800201e0400801083008001c35078100200420c0200080d02c094220801e46114449104310a421064110240110d025478184400c02808419044090030340891e051100310801804409002c340781002004008001c1e2741002004008001c370d41f274120400a0200601002000c07c11020870140200470dc200480821c06008707c110240420c0200470dc200480a0108300870789d060970308b0240821c90ec1e2741825c0c22c0a0240821cb0789d050930308b0140420c911c1e2741424c0c22c060140420cb088a10408f0308b0140420c9088a10408f0308b0180501083281f0440821c05008011c370801f048110208701805008012c1f0440901083008011c370801f048110280901083008012c1e2741002004008001c350789d0400801002000807810020870100200070d41e0400821c0400800201e0400801083008001c35078100200420c0200080d02647c194440d028094190540901303407c1102405008011c1f0440821c05008011c370801202087018021c1f0440901083008011c37080120280420c021c1e2741825c0c22c0902087243b0789d060970308b02809020872c1e2741424c0c22c050108324470789d050930308b01805010832c222841023c0c22c050108324222841023c0c22c060140420ca07c11020870140200470dc2007c120440821c0601402004b07c110240420c0200470dc2007c120440a0240420c02004b0789d040080100200070d41e274100200400800201e0400821c04008001c350781002087010020008078100200420c0200070d41e04008010830080020461003a0e0360d4340b0250882007818050120400c0280801804008005c3a0901e05c1002c09020070180400800343607c1e04410024080140400801000c07c1101c0500801181e0400801001000607c110250801402004709920065120340a0250841902281d0400801002000607c1101c0500801181e04007010020006078100200300800181e040080100100060789d040070100200070781023c0800c02000709920065120340a0248821d06408b078100208701001000708d20055120350a0180521083408b078100200420c01000707c1101c0500801183607c1102405008011c36098190340a024607c1101c05008011836098a4064970348b02809220872c3608ca1054930348b01805210832c350b12b09524089210811f0791d2c3509524061170310b02909021072c3508921051130310b01905011032c350811f049110290901905009012c224841023c0c42c064140440ca0811f04911020870190500)) else (if j<20 then (0xca0962205110030090208781a05810b0ec2529222051100300a0240821e06810d07c114400901083008012037080124400a010830088088a1051100308b0140420c90d422284144400c22c060140420cb0789d051100308b0140420c911c1e274144400c22c060140420cb07c1144009010830080120370801f049100280901083008012c1e0400801083008001c35078100200420c0200080ee3909622060970500c0240821e0681604383b094a48881825c140300a0240821e06810e07c110240420c0200470dc200480a0108300870d4222841424c0c22c05010832835088a1050930308b01805010832c1e2741424c0c22c050108324470789d050930308b01805010832c1f0440901083008011c370801f048110280901083008012c1e0400801083008001c35078100200420c0200080ee3988b1e0620681604c0b00283d0ee3909e2388b200681881a0581302363988b1e0620581302c070024350781002004008001c37078128400a8200681002800a0781184009820058100200600283607c1e044090140200480791d040080100200070d41e07410020040080020350781002004008001c350b12b09524089210811f0791d2c1f4781102405008011c1f478110260801402004807d1e04409016040080120370d81e048118400a026080180581002006003c1f4781102405008011c350811e0480a018021c1f47811020870140200480dc20478120208701802201f478110240420c0200480dc20478120280420c0220254781825c0c22c09020872435094a44781825c0c22c0a0240821cc0891e050930308b0140420c90d4222851e050930308b018050108330224781023c0c22c050108324222851e0408f0308b01805010832c1f4781102405008011c350801f478120440a0240601402004c07d1e0440821c050080120370801f478120440821c0601402004c07d1e04409010830080120370801f478120440a0240420c02004c07810020040080018350781002004008001c1e0400821c04008001c350781002087010020008078100200420c0200070d41e040080108300800223507c1102405008011c3607c11026080140200480d81f04409016040080120378d42007c1e04a1002a0801a0400801800e8d42007e108220480078d41f84208812001a35082108220480068d42084208812001a35082108220480060d41f044090140200470d4200480a01802181f0440821c05008011c370801202087018021c1f0440901083008011c37080120280420c021c35094a4060970308b0240821ca0d4252901825c0c22c0a0240821cb0d4222841424c0c22c05010832835088a1050930308b01805010832c222841023c0c22c050108324222841023c0c22c060140420ca0d41f044090140200470d42007c120440a0240601402004b07) else (0x48100280801804008003025888144400c0240821e06816042c3b094a4888144400c028090208781a0434292a222051100380d0308b81a042c1f0440941c05008011c2287c1484409420050108380a012c3d088a1880148480a420060140420e0234222841424c0c4200501083243b088a1050930310801805010832c228781424c0c4200501083244a088a18781424c0c420060140420cc088a105210031080140420c9088a105210031080180501083282287c1484409420050108380a012c3d088a1880148480a420060140420e02342287814840080140420e02800a0ec222861e05210020060140420e02800d07c11025080140200470d4200480a42006008707c11025080108300801203708012029080108300880b0250881f0789d471194610d4310a4250838350b0250882007c1e2751a4610e4310a420e088a105093031080140420c90d4222841424c0c420060140420cb0789d05093031080140420c911c1e2741424c0c420060140420cb088a10408f031080140420c9088a10408f031080180501083281f0440942005008011c350801f048110290801805008012c1f044094200420c0200480dc2007c120440a4200420c02004b07810020040080018350781002004008001c1e2741002004008001c350789d04008010020008078100200420c0200070d41e040080108300800203607c110240701402004810e390be22060970541424d114400881a05810f0ec2f2ba220609705815050934491002206810f3082f2ba2226c1805815050934491003206810f0e42287c148440c22c050108380a01302228620052120308b0180501083808c088a1050930308b0140420c9088a1050930308b0180501083283908a1e050930308b0140420ca088a18781424c0c22c060140420cb0e422284148400c22c05010832822284148400c22c060140420ca088a1050930308b020060140420cb0e42287c148440c22c050108380a01302228620052120308b0180501083808c0e422878148400c22c050108380a0030222861e052100308b018050108380a00343507c1102405008011c350801202806008607c110240420c0200470dc200480a0108300870d42c2ac25290222841f0789d28350b0ab094a4088a10801f0789d2c35088a1050930308b0140420ca0d4222841424c0c22c060140420cb0789d050930308b0140420c911c1e2741424c0c22c060140420cb088a10408f0308b0140420c9088a10408f0308b0180501083283507c1102405008011c350801f048110280901805008012c1f0440901083008011c370801f048110280901083008012c350781002004008001c350781002004008001c1e2741002004008001c350789d04008010020008078100200420c0200070d41e0400801083008002022084148400c02c060140400))) else (if j<23 then (if j<22 then (0x3083b2e0370d42f0a422058140380c018043cc20bc290881605093048100380c01804343b0a4220500e0308b02808018042c3507c1102405008011c1f0440821c05008011c1f0440901083008011c350b0ab094a4088a107c1e274a0d42c2ac25290222842007c1e274b0d4252901825c0c22c09020872835094a4060970308b02809020872c35088a1050930308b0140420ca0d4222841424c0c22c060140420cb0789d060970308b0240821c90ec1e2741825c0c22c0a0240821cb0789d050930308b0140420c911c1e2741424c0c22c060140420cb088a10408f0308b0140420c9088a10408f0308b01805010832835080120280600860dc200480821c0600870dc200480a0108300870d42c6ac2569022684200799d283b0799d0600c028081c470799d0500c018041c3b274184400c0280841904409002cc6274144400c4200601102400a0d4ab290a10809d46114449104310a421064110240110d42c094220801e46114449104310a421064110240110ec1e061100300a0210641102400b11c1e051100310801804409002837078124400a4200641002400a078100200440c020007078100200440c020007078100200440c0200070d41e040080100300800201e2741002004008001c370d41f274120400a0200601002000c07c11024054100200470d4200480a01904008707c11020870150400801203708012020870190400880b0250881f0789d471154510d431064150438350b0250882007c1e275164510e43106410e0952206114030090208741905410b0d42529122061140300a0240821d06410d0789d06114030090208741905410b0ec1e274184500c028090208741904301f0440901504008011c350801f048110280901904008012c1f0440821c054100200480dc2007c120440821c0641002004b07810020040080018350781002004008001c1e2741002004008001c350789d0400801002000807810020870100200070d41e0400821c0400800203507c1102405008011c350801202806008607c11020870140200470dc200480821c0600870d42c2ac25290222841f0789d28350b0ab094a4088a10801f0789d2c35094a4060970308b0240821ca0d4252901825c0c22c0a0240821cb0789d060970308b0240821c90ec1e2741825c0c22c0a0240821cb0d41f044090140200470d42007c120440a0240601402004b07c11020870140200470dc2007c120440821c0601402004b0d41e040080100200070d41e040080100200070789d040080100200070d41e274100200400800201e0400821c04008001c350781002087010020008078100210701002000707810021070100200070911e05d1002c09020074190440900301e05d1002c090200741904409002c3507810020070100200080789d040080100200070dc3507c9d0) else (0x2c35088a1478144400c420060140420d02400e0789d0611003009020874190440900303b0789d061100300a0240821d0641102400e0789d05110031080140420d02400b11c1e274144400c420060140420d02400d0891e0408f031080140420d02400b088a14781023c0c420060140420d02400d07d1e04510025080150400801400b0d42007d1e04910029080190400801400d07d1e04510020870150400801400b0dc2007d1e04910020870190400801400d07d1e04510025080108300801400b0dc2007d1e04910029080108300801400d0d41e040080100200070d41e0400821c04008002035078100200420c0200080d41e04008010020040020410f0390d8350b42608c2007c19054120440d02809018050080154470ec370d42c094220801e06014048100300a0200601002001411c3b0dc350b0250882007818050120400c02808018040080050c93183b0dc352c4ae2aca809ca428420274e3183b0dc352aca42842027418050120400c028080180400800502c07818050120400c028080180400800343c0981f064110340a024080180500801343b0941e060100300a0200601002000c0ec25078180400c02808018040080030c92c4a809ca4284202741a0600e0300a020e0ec352909d060100300a0200601002000d0e42307c150440d0240601404008013022078140400c0200601002000a0881e0501003008018040080028c62b8a828420274160500e03006010c0d4a1274140400c0200601002000b078100200400800181e040080100200060ec25078180400c0280801804008003022078140400c0200601002000a0d41e040080100200070d41e040080100200070ec25078180400c0280801804008003022078140400c0200601002000a0d61d0400801002000707c110240500801183607c1e044090140200480d81f044090200500801203607c110240501002004811c3b0dc352d0320bc2c0a427094220801e38473083b0dc352d0320a4270941a0600e0300a021011c3b0dc352d02f0a422058140380c01804383b09422060140300a02087018042c370d81e048114400a025080180541002005003c3607811440094200541002005002c470ec370d4b409c20068160480e02806008e11c2c094220801e2741a058120380a01802383b09420060120300a02087018022c22080140480c0280601083008a0ec252901825c0c22c0a0240821cb088a1050930308b0180501083283b0941e060970308b02809020872c220781424c0c22c060140420ca088a1050100308b018050108328222841424c0c020060140420ca11c3b0dc352d02c094220801e06014048100300a020060100200150ec25078180400c0280821c0601002000d0881e05010030080180420c02000b1283d0ecba0dc350c82909c25068180380c028084047)) else (if j<24 then (0xec250600c0280818220500c0180414220501003006010611c3b0dc350c82909c25068180380c0280838220500c02006010611c3b0dc350bc29088160500e03006010d0ec25088180500c028080180428c62aca4284202741a0600e0300a020c318ab290a10809d058140380c0180430c62aca42842027461043c0e4360d4270801a058120380a0180238480b42608c2007c1e068160480e02806008e0f026080190480d0280902006008b0e423080150480d0280601404008b324c60ec370d4320bc2c0a427094220801e38c92c4a809ca4088200781a0600e0300a020e11cae2a0a10801e058140380c0180430360801e048100280801804008002c370801e048100240801804008002c370801e048100280801404008002c370809d0480a018021c360811f049110290901905009012c370811f049110240801905009012c370811f049110290901404009012c370809d048100280801804008002c470d82c094220801e67419054120440d0280901805008014cc60b025088200799d06014048100300a0200601002001211c2c290220801e67418050120400c02808018040080048470b025284200799d06014048100300a020060100200120d49d04008010020007318ab290a10809d06014048100300a0200601002001107810020040090100070d820078120400a020060100240400301e0400801002404001c370801e04810024080180400901000c07810020040090100070dc20078120400a020050100240400301e274128400a8200681002406002c1e27410020040090100080dc1f274120400a02006010024040030350b0250882007918451124410c42908419044090044350951e061100300a0210641102400c0d422478144400c4200601102400b0ec22478144400821c0601102400b07d1e04510025080150400801400b07811440094200541002005002837078124400a4200641002005002c1f47811440080150400801400a07d1e045100250801002005002835094a4478184400c028090208741904409003c35088a1478144400c420060140420d02400e0ec1e061100300a0240821d0641102400d11c1e051100310801805010834090030222851e0400c420060140420d02400c0ec222851e05110020060140420d02400d0d420478124400a4200641002400b0dc20478124400821c0641002400b0dc20478124400a4200420c02400b0d425478184400c02808419044090030350891e051100310801804409002c2247810031080180440900243b0891e051100200601102400a0b0250881f0789d46114449104310a421064110240110d42c094220801f0789d46114449104310a421064110240130951e06110030090208741904409003035094a4478184400c028090208741904409003c22478144400c420050108340900) else (if j<25 then (0x88100280108d42c2ac25290222841f0789d2a3b07e18a5e0ca2e08a1c80e41f852938328b81283223507e10822048006120410f0390dc364d42d098230801f06415048110340a024060140200574ed3509c20461144410c42104400b4d42d098230801f193b07d1865d0c62d0861c80e41f451934318b4118320364d41f0781144009420054100200500353507c1102405008011d3507c1102405008011d3508110421044006078100200400800181e040070100200060d01e040080100200070781001c040080018340781002004008001c1e040070100200060d01e040080100200070781001c040080018350781d040080100200080781001c0400800181e040080100200060d01e040080100200070d01e040080100200070d01e040080100200070d41e07410020040080020350781002007010020008078100200300800181e0400800c02000607810020030080018350781002004008001c350781002004008001c350781002004008001c350781002004008001c340781002004008001c1f0440701402004607c1101c0500801181d040080100200060781001c0400800181e0400800c020006118400e8380d8350d02c094220801e06014048100300a0200601002001707c1101c0500801181f044070140200460e824078170400b0240801c0601002000d0d4200480a01802183507c1102405008011c35080120280600860d41f044090140200470d81f044090140200470d01f04409014020047074100200400800181e04007010020006078100200300800181d040080100200060781001c0400800181e0400800c0200060d4200480a01802181f044070140200461003a0e0360d4340b42608c2007c19054120440d028090180500801581d040080100200060781001c0400800181e0400800c020006074100200400800181e04007010020006078100200300800183407c1102405008011c340781002004008001c1d040080100200060781001c0400800181d040080100200060781001c0400800181d040080100200060781001c0400800181d040080100200060781001c0400800183407c1102405008011c340781002004008001c35078100200400c0200080d42405c0b0240801c70d01f044090140200470d01e040080100200070d0252901825c0c22c0a2240821cb0781001c0400800181d04008010020006074100200400800181d04008010020006074100200400800183407c1102405008011c340781002004008001c3607c11024070140200480d41e0400801c0400800201e0400800c020006078100200300800181e0400800c02000607810020030080018340781002004008001c1e040070100200060781001c0400800181e040070100200060781001c040080018340781002004008001c350781d040080100200080) else (0xda3507c1e04610026080160400801800d12d3b0cc2a09c2608c2007c1c4610c420d0e4300a8230801f071144310428460b0250882027c1e27618852108320881002801011c2c090220809f0789d85e148420b822078100280111182c094220801e862148420c8220400a0038470b0240882007a178521082e0881e0400a003d3509c2007d184511043108411002c481043c0e4370d9350b42608c2007c19054120440d0280901805008015c3607c11026080140200480d81f04409016040080120481063b0e635ad0330a8270981c8620c820e120418ec398d6b40c02a08c1c8520c810d8ec39098238621483208a1e04283607c11026080140200480d81f0440901604008012235082108220480068d42084208812001a3b0d82607e180460c82287018050080134390d82307e140460c02604a0c02004c0d01e040080100200070781001c0400800181e0400800c0200068ee3509a18a5e0ca2e08a1c98d423852938328b81283203908e148420ca2e04a0c88ec360981f8601183208a1c0601402004d0e43608c1f85011830098128300801323b8d426082188420c82287812002c398d423082148420c82204a0e002c3c0d82607c190440d028098200601402004e0e43608c1f05411034090180581002004d0d01e040080100200070781001c0400800181e0400800c02000612c450fe3bae8398d4330a8270981c8620c820f10c3f0e6b88d4300a823072148320430430e43008c1c852938420c810a0f0360981f064110340a02608018050080138390d82307c150440d024060160400801363b8d427082188420c82204800a8d420852108320881200203607c1102405008011c370801f0480a018021c3607c11822870140200480d81f044098128300801223509a18a5e0ca2e08a1c88d423852938328b81283203908e10a3e0ca2e04a0c80d81f04608a1c0500801203607c1102604a0c0200488d42084208a1e0480078d42084208812838007120418ec398d6b40c82f0b42c0a426094230882007c1e48478ec2c0942207c1e2741c8620c0260834470b0250882007c1e276188300a820c11c390b0250881f0789d0721483005810d11c2c094220801f0789d8520c01a04301e04510025080150400801400a11c2c2ac25290222841f0789d28470b0ab094a4088a10801f0789d2e3b0981f862978328b82287243908c1f852938328b8128324478d42c0942207c1e2761885210832088100280101284811cc61063b0e6350c82f0b42c0a426094230882007c1e504a1204731a3b8d4320bc2c0a427094220801e3c4a8ec320a426094a408c2007c1e07218830098210128320a427098252902007a188300a820d0e42f0a423088a10801f0781c8520c0160438470bc2909c23088a10801e8520c01a0434478d42c094220801f07a1885210832))))) else (if j<30 then (if j<28 then (if j<27 then (0x181d040080100200060781001c0400800183407c1102405008011c340781002004008001c1d040080100200060781001c0400800183407c1102405008011c340781002004008001c1d040080100200060781001c04008001835078100200400c0200081082204c0c0180418258781023c0b028088160480e02800c0961e0400b028088160480e02800b1082c8781825c130481023c088160480e02800f1082c8781804c12040088160480e02800d11c350b0250882007818050120400c028080180400800481e2741002004008001c1e2741002004008001c1d0400801002000607c9e0440901402004707c9e044070140200470d01f0440901402004707c1101c050080118340781002004008001c3707c9d0480a018021c1e040070100200060d01f0440901402004707c1101c050080118461003a0e0360d4340b0250882007818050120400c0280801804008005c350781002004008001c378d420078128400a8200681002800c0d41e0400801002000711c3b0dc350b0250882007818050120400c028080180400800503b0d425078180400c02808018040080034350881e050100300801804008002c3a0901e05c1002c0902007018040080034350781002004008001c350781002004008001c3b078180300a020611c360b0250881f0789d06415048110340a02406014020053121350b42608c2007c70d81f07811024050080120484ec2d098230801f07118431082c480e42d098230801f07114431042c3607c1102405008011c1e2741102405008011c370789d0480a018021c1e27411440094200541002005002c3607c1102405008011d3508110421044006120414ec394d5b40cc300b42a09c2608c2007cf078128400a820068100220600281e04a100260801a0400881800a078128400a820058100220600281e04610026080160400801800a4ec2607d1865d0c62d0861c90e42307d1464d0c62d0460c90789d04510025080150400801400b0789d04a1002a0801a0400a00281e274128400981c0681002800a4d41f44108411001836078128400a8200681002800a078128400981c06810028009120414ec394d5b40b42608c2007c19054120440d028090180500801581e040080100200060781001c0400800181e0400800c0200060d01e040080100200070781001c0400800181e0400800c0200060dc1e274120280600870dc1e274128400a8200681002800b4d41f44108411001837078128400a8200681002800a120414ec394d5b40b42608c2007c19054120440d02809018050080158481053b0e5356d027081184511043108411003c4b120414ec394d4330c02d0a827098230801f3c368d42027c1e04a1002a0801a0400881800e0de350809f078128400982006810022060038378d42027c1e04a1002a080160400881800e) else (0xd01f044090140200470d01f0440901402004707c1101c050080118461003a0e0360d4340b0250882007818050120400c0280801804008005c1f0440901083008011c37080120280420c021c1f0440901083008011c1e04008010020006074100200400800181e040070100200060d01e04008010020007074100200400800181e040070100200060d01f044090140200470dc200480a0108300870d01e04008010020007074100200400800181e040070100200060d01e04008010020007074100200400800181e04007010020006118400e8380d8350d02d098230801f06415048110340a0240601402005707810020870100200070781001c0400800181f0440922005008011c3407c1102405008011c340781002004008001c1d040080100200060e824078170400b0240801c0601002000d0d01f044090140200470d01f04409014020047118400e8380d8350d02c094220801e06014048100300a020060100200170f4222851e0591202a0801a04408b07c11020870140200470dc200480821c06008707c110208701402004707c1101c0500801181e04008010020006074100200400800181e0400800c0200060d01e04008010020007074100200400800181e0400800c0200060891e0511002005011024050028390891e05110030080140440901400c0d01f044090140200470dc200480821c0600871282f09c2508c222852047a188520c82006810f0d01e0400801002000707410020040080018340781002004008001c1d0400801002000607810020030080018461003a0e0360d4340b42608c2007c19054120440d0280901805008015c1e040070100200060e422478144400c22c080140420d0240500382387c1584409018052108380a012c2287814840080180420e02800a0861d05210020060108380a00283808e1f056110240601602804a0e02287814840080180480a00282187414840080180480a00242287814840070180480a00241f04409014020046078100200400800181d040080100200060d01f044090140200470d01e04008010020007074100200400800183808e1f056110348b024060148420e02804e0e022878148400c22c080180420e02800d0861d052100308b020060108380a00303808e1f05611034090180580a012c3808a1e05210030080180480a002c21874148400c0200601202800a0d01f044090140200470d01e04008010020007074100200400800183407c1102405008011c340781002004008001c1d040080100200060d41e0400801c040080020390891e05110030080140440901400c07810020030080018380841e04c1002c080140400c02000c078100200300800181e0400800c020006078100200300800181e0400800c020006078100200300800181f04409014020046078100200400800)) else (if j<29 then (0x80100200070d4200480a0180218352741002004008001c470ec370d4b40c82f0b02909c2508820078e11cc20ec370d4b40c82909c25068180380c0280840470ec370d4b40bc29088160500e03006010e128473183b0dc350c82f0b02909c2508820078f1283d0ecba0dc350c82909c25068180380c028084047308be0ecb80dc350bc29088160500e0300601100d41e040080100200070d4200480a0180218471083e0ec390e0370d42f0a422058140380c018044435088a1050930308b0140420ca0d4222841424c0c22c060140420cb1283d0ec3a0dc350c82909c25068180380c028084035094a4060970308b0240821ca0d4252901825c0c22c0a0240821cb12c450fc3d0f03b0e8390dc360cc2a09c260701a0640e0340a0255128471183b0dc350c82f0b02909c2508820078f0d41e040080100200070d41e040080100200070d42c2ac25290222841f0789d28350b0ab094a4088a10801f0789d2c480b42c0982508c220801f078a0dc1e04a1002a0801a0400a002837078128400a8200681002800a0f4250781a0480e02a08018022822078160480e028068100225464ad244842047418050120400c028080180400800441e040080100100060d81f07811040090200501002004003037078124400a4200641002400a0d41e040080100200070d41e040080100200070d41e040080100200070d41e040080100200070d41e04008010020007078100200400800181e04008010020006318372aca4284202741a058120380a0180238352741002004008001c3507c1102405008011c1f0440881c05008011c1e0400801002204001c1e0400841c04008810008078100200440c0220400203407c1102405008011c340781002004008001cc60dcab290a10809d068160480e02806008e0dc9d04a1002a0801a0400a00281f044070140200460781001c0400800181e0400800c0200060d81f078110400902005010020040030370809d0480a018021c461003a0e0360d4340b42608c2007c19054120440d0280901805008015c461003a0e0360d4340b0250882007818050120400c0280801804008005cc62aca428420274631a352aca42842027618852108320881002800f0e82407c170440b0240801c0601402004d0e824078170400b0240801c0601002000d0e021078130400b02005010030080030470f4374d42c094220801e068160480e02806009011c3b0dc350b0250882007818050120400c02808018040080050470ec370d42c094220801e06014048100300a0200601002001411c3b0dc350b0250882007818050120400c028080180400800501e0400801083008001c1e0400800c02000607c110240521002004707c1101c052100200470d01f0440901402004707c1101c050080118340781002004008001c1d040080100200060) else (0xec22478144400821c0601102400b0891e051100308b0200601102400b0ec222851e05110020060140420d02400d088a1478144400c22c0801805010834090038c92b827290a14819d060160500c02808018043c352741002004008001c3b09422060140300a02087018042cbe0a4220500e0308b01804243b09422060140300a02087018042c3b094a4060970308b0280821ca0ec250781825c0c22c0a02087284a0f43b2e8370d4320a4270941a0600e0300a0210128320a427094a4088200781a0600e0300a020f0ec29088180500e0308b028080180430222841424c0c020060140420ca1283d0ecba2e1374d42f09c2508818058140300a02006011351cc22f83b2e1374d42f0a422058140380c01804402f088180581424d124400c028080180434c20bc29088180581424d124400e03006010e0dc200480801802183b2859d051100200601102400a0ec222841424c0821c060140420cb7012c6ac29089124451063c0e03006010d0891e0511003008018044090028222851063c0c22c060140420ca1082f0a4220581404c120400e03006010d088a10408f0308b0140420c9088a10408f0308b01805010832839088a1050930308b0140420ca088a1050930308b01805010832825888144400c0240821e06816042c3b094a4888144400c028090208781a04343b8e4258881825c14030090208781a05810e0ec2529222060970500c028090208781a043837274128400a8200681002800a0dc9d04a1002a0801a0400a0028c62aca4284202741a0600e0300a020c318ab290a10809d058140380c01804301e4741002004008001cc62aca42842027460d41e47410020040080020c93183b0dc352c4ae2aca809ca428420274e324b12a027290a10809d068180380c0280838c62b8a828420274160500e03006010c0789d040080100200070d41e274100200400800203607c1e04409014020048078118400982005810020060028352741002004008001c37078128400a8200681002800a0dc20274120280600870d81f044090140200470d81f078118400982005810020060030478d42c094220801e862148420c8220400a003c378d420274128400a8200681002800c0dc1f04a1002a0801a0400a0028350781002004008001c350781002004008001c350781002004008001c350781002004008001c37274120280600860d41e040080100200070d41e040080100200070789d050930308b0140420c911c1e2741424c0c22c060140420cb128320a42709424088200781a0600e0300a020f0d41e040080100200070d41e040080100200070789d060970308b0240821c90ec1e2741825c0c22c0a0240821cb0d41e040080100200070d41e040080100200070d41e040080100200070d41e040080100200070d41e040080100200070d49d0400))) else (if j<32 then (if j<31 then (0x601504808e2e0352d022878148400c8200601202800d120c60dc368d4270801f4490a4190230392e0370d823480164480e4280601502353708ca10801f059120390a018058110234b80d422478144400c42006011022cb80d422478144400c42006011022c380881403006010031c3b0e0352d02f0581404d0424470e0352d0160380601504808a0e0352d0220500c018048009108c00e02f0581404d042235088a1050930308b01885010832e34088a1050930308b01885010832c3e0e02f05814442041c380d43408814030060108324400ec350d02f0581481080e0370d4340bc2908a1e4109108380d4340a40e0320841092e0350891e0511003108018044090030b92e02f0a42247a1483206810a0d421474144400c4200601102400b1082f88816051108320681090dd20059120390a01a0440890ec380d42f488160521043106410b11c380d62005a1203a0a01904808b120470de3509c204490a41890d42c47818050120410841102400b1082f488160510c41870d422478144400c4200601102400b0d422478144400c4200601102400b0d422478144400c4200601102400b0e437480164480e4280620350851d051100310801804409002d3708c22080164480e42806810a0e03508a1e052100320801804808b088148400c018041822880148480c82806012022421878148400c820060108380a002c350861d05210032080180420e02800c0ec350be22058144420c81a0428370d42f0a4228791443106410a0d429489140380c82106410911c35880168480e828064120228352d022878148400c8200601202800c0dc352d02f0a4228791443106410b2d021874148400c8200601202800b0d41e04008010020007078100200440c0200070d41e040080110300800201e0400801083008001c35078100200420c0200080d49d040080100200070dc200480a0180400870d49d04008010020007088a1050930308b0180420c90881e050930308b0180420c9088a1050100308b0180420c9088a105093030080180420c911cc22f83b2e0370d42f0a422058140380c0180440470bc29088a10801e058140380c0180434c20bc290881605093048100380c01804343b0a4220500e0308b02808018042c37080120280400860d41e040080100200070e4230891f05511024080180501102404d0e4230891f055110340c024060140440901381e0400841c04008001c3507810021070100200080891e05110020050110240500283b0891e051100200601102400a0891e05110030080180440900283b0891e051100200601102400a0891e05110030080180440900281e0400821c04008001c3507810020870100200080d49d040080100200070ec22478144400821c0601102400b0891e051100308b0200601102400b0dc200480a0200600870) else (0x50861d05210032080180420e02800c0d421874148400c8200601202800b0e02205210030060107108384d42f0581484e1001090d4220500c0180440070d4220500c0180440070d4220500c0180440072e0378d416038060140440890d421474144400c4200601102400b109384d4220500c0180420372d935088140300601080d421474144400c4200601102400b0d421474144400c4200601102400b0d421474144400c4200601102400b0d421474144400c4200601102400b0d42c0601404810400710a350bc1605013041042047318378d42c09c250882007c1e408c11c222842007c1e05a1403a0c01a04408d0ec350bc160509381070d4b408814030060110020370d4b40bc2908a041cb40851d051100310801804409002cb40861d05210032080180480a002c350861d05210032080180480a002c3b0e0350bc16052101c350b01805012041001c380d42f05814841041c350881403006011001c350881403006011001c350881403006011001c47118350bc290891e81082e0370d8350580e01a0440890d421474144400c4200601102400b0e035088140300601203400911c350580e0188541070dc350bc290881e81070ec350bc1605010810711c350580e01a0400870d4220500c0180400070ec352d02f058140410420470d4b40580e0190400880d63408814030060108320352d0220500c018040008108c00d42f058140410420390d42247814030060110224b80dc3508920058140380c01804408c2e037480164480e428068110228b80bc2908c222851e8520c81a042cbe2e02f2ba22058150511083206810c308b80a4a888a140380d0310881a0430b80dc23480164480e4280601604408c2e0350891e051100310801804409003135088a1052100308b01805010832d3b4d42f2ba22058150509383206810c4d4222841023c0c22c060140420cb120c60de3509c204490a41890e4b80dd20059120390a01894dc2328420059120390a01a0428b80dc2228620052120320a0180501083808e2e0352d0222841424c0c22c060140420cd2e0222861e050930308b018050108330b8088a1052100308b01805010832cb8088a1050930320801805010832cb80dc2228620052120320a0180501083808e2e035088a1878148400c820060140420e02800f318b80bc2908c222861483205810b11cc62e02f0a423088a18520c81a0430c2300b80bcae888160541424e0c81a0434be0ecba2e1350a4a888a140380d0308b81a043cb8088a10408f0308b01805010832cc00ec352d02f2ba22058150511083206810e30a3b0a4a88889b25c1424d100380d0308b81a0440b80dc352d02f0a423088a18791443106410e308b80d4b40a4a8489140380d03208419043847318b80d4b4880168480e828064120234472e0352d023880168480e828)) else (if j<33 then (0x20881a0438c2701350bcae88818058150511083206810e0ecba4d4292a222062140380d0308b02206810f0ec292a22206097051100380d0308b02206810f2e135088a10509303208018050108331350891e051100300801804409002c423002f05814041041c423002f0581404c1041080d421474144400c4200601102400b0d422478144400c4200601102400b12047318378d42c09c250882007902304708c2228420078168500e830068110234c60e5350bc2908c222841e810a11cc64d42f0a423088a107a04284811cc60de350b027094220801f07902343908c222842007c1e05a1403a0c01805811023c352d0220500c0180440c80e03508814030060110380090d4220500c0180440c70ec352d02f05814041042047318370d42c09c2508820079022cc00d42c06014048104008108c00d42f058140410420b80d4220500c0180440082e03508814030060110020b80d4220500c0180440082e0350bc290891e01070f8b80d4290380c4200420392e0370d422058140380c01804408c11cc62e0352d016038068110228b80dc352d02f0a423088a147a042c3b2e0352d02f2b8160541424d10810c11cb80d4b408c160380601604408b2e0352d0220500c018044090028392e0370d416038068110224c62e0350bc2908c2247a042447318b80d42f0a423088a147a042cc2300b80d42f2b81605414442042c392e0370d83508c160380601604408c2e03508814030060110020b80d4220500c0180440900243b0e0352d02f0581404d0424470e0352d01603806015042442300380d42f0581404d0424380dcb60d416038060150424420d422052100300601080d4220500c0180400070dd360d416038068100220424d4220500c018041c374d4220500c0180400880d42c06014048100007109350bc16052130400420350881403006010001c350881403006010001c350881403006010001c374d416038068140400880de35088a1478164480e428068110232350891e059120390a01a04408a120470dd358b02789622080991c2f09c23088204510c0190428374d4270821e0480a0180224374d41603806810021c370d9350580e01a058100224370811e058120380a01a04008a0e6b88d42f0a4230891f47a1483005810d11e350bc2908c222852047a1483006810d0dc2007d1e058120380a01a058100231420d42c87818050120420881202800c0d422878148400c8200601202800b0d421874148400c8200601202800b0d4224861e05210032080180480a00303508a1e05210032080180480a002c350861d05210032080180480a002c3508a1e05210032080180440e02800c0dd3509c2007e1e0480a0180228374d416038060160400880d4210500c0180420d0020b88d4210500c0180420c80d421474144400c420060108340900303) else (if j<34 then (0x804183b0d42268414030064140424b80d422478144400c42006011022c470d420058120380a01a04008a2e0352d022478144400c4200601102400d2e035088a1478144400c420060140420d02400f11c35080160480e028068100228350881e050100300801804008002c370819d058120380a01804008a318352b8a82859d0500c0180428350881403006010611c3b0dc3508814030060109308be2e035088140300601090dc3509c20a74120280600890dc35080160480e028068100228470dc20078168501203a0c02806810023447718350bc290882007a1483206810c0ec350a42588a140380c0280881a04303b0d4b408aa10500c01a05010a11cc20ecb80dc352d0220500c018043035088a1050930308b01805010832cb80d4222841424c0c22c060140420cc0dd36080160480e0280681002283d0dd3508820050120300a01804008c128472e1350881e0500c01a05010b2e13508aa1050100300681404283b2e13508aa10500c02006814042c3d0dd3508820050120300a01804008c0ec350881e0501003008018040080030374d42c09c25088200781202806008c0dd35080160480e028060100228474d42f0a422a841e0500c018042cc24d42f088160501003006010a0ed350a422060140380c02006010b0dd35080160480e0280681404008b0d4220500c0180400070d422078140400c0200601002000b2e13508aa10400c01a0501090ec350bc22058144400c0180428c20d42f088160511003006010a3083b0a422060144400e030080180430be0ec350a4220500e03108018042d3b0a422050100380c42006010a0d4a1674144400c4200601102400b0d4b408814030060110320471083b0e0370d4b40881403006010c4e03508814030060120020b80d4220500c0180440080e4b80dc35088160500e03006011023047088a10801e058140380c01804408c0e13508814030060120320424d42f0581484c041cb80de35088a10500c0180501083408c2e0370da35088a10500c0180501083408d2e035088a10500c01805010834090030392e0378d416038060110224b84d4222861e0500c01805010832cb84d422284148400c01805010832cb84d4222841424c0c820060140420cc0e4b84d42f0a423088a18780428472e1350bc2908c222861e010a308b84d42f2b8160541424e10010b2f83b2e1350a4a8088140380d0308b82006010f0e4b80de3508c160380601404408b2e03508814030060110020b80d4220500c018044090024be4d42f2ba2206016054144420c81a04354771935480164480e8300a01a04408c309350a4a8888188500e0340c22c0881a0439350891e051100300801804409002cc22f8292a22226c18051100380d0308b81a043c394dd35480164480e8300a01a04408c3083b4d42f2ba22060160541444) else (0x300350501010352d00440c42e0350110010b80d422010411c220820611370882001844ec0c082001820e4b80dc064085318b8088a147852e0350110010394de220800614470dc2308920018651c2308206104851c230820614c4308180520c153b8500c0c394dc238882001860e43708c224800618470e42308a201414042001824ec0c084811c2308a0614380d40420d0014400d41444041204708c2281850520c083701828e2350511081058e00640830d404400311c2247830d40440031081444030e4370190211378882001844ee14030311e390dc22480061a37488060c14442040d47082060e380511081042e120018308c22818330a0c08370d42f0a4220801e8520c81a042cc20d429096228500e0300a02206810c308350891e0511003108018044090030be0d422478144400c4200601102400c0d4220500c01)))))))
def genIndex8 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0x7a700fde7f8001e0001e150c0b5f8001a5b5c8351e00078001251d7800000f2c052ee50ef80012095780004066f83e785a7926e1e000780010173f0355e00078001e00009147c0e1400c1a0de915e3e0000048e2057b80dee83198515e0007800044fff8605c0c178001a56178001e0005677be000304b2c13c78001e000687f8d9e202193c08a807574953ea1c0a007987cb61128026805109a489a1fac97f74202f800060ba803c52174f8001e00078000e02478001c8d65182fa60e4b777420c70369e00031488218c78001e000780014de7c9797c16ae06f7e00000509e5fbf9712a1b878001e00038264692a68428aa07c05a2410be125be00078000214f5807709ff204d260dc98460a013495fc600e9a34a299a6840dc1c8f00d708b6f034e4189c113660597816de0004e0d2a190903c1e000216ebe000704f8409cf21a5aa11fa46064f2666f0e947b26cf81adca33c6108a678fe0002809de0000070900b4484d5e0007800024e1f15ca408c8043d21d25a1bbe0007b76a8def90544e010c824fc1dfa972908c4f8001e00078001e0005b45fa098f8000e130a96dac06bcb0aa49de194dfe000183e3a0444178b40bff04d758d9f8000c1b0c0073e00050005e0007800001c0e8293807ada3fde00078000a02ba0327e000482f7a16ff800188c5607b740fd78000400278001e00078000805ec17bfe00078001e0000e0788919b81a7e000201f7e00078001e1c1f8001c909427de494eba663e0003860f21e5080d8cd68f800000ca7800164cb8a49fe00060185e0003831649b7f8000a0103912ad169300f701b6415344600a9371c9cf010a1800a0e000a60804ba20010b8012007801a74080011828002245a6024c001080c000384400150201021804100263c7351808800122810000287045e1039808008242a28c0406081052e14887387d9210600001025c184020018000084104204080145428004040030e0051a020c28c064038204002051c087010a064010018185061430626740010494206300c380020c0004e09307000400004101820e00b1d00081040e10c870c042a1080028b0830000100428000140022a044850e0c00204001001cc4c8108086830a08205000800902151a0040000014340800c08099026c180001408210003880004084020820c0000101000c08a1e145821c10083060800c080420c1e04000042c00100044110014101102800128046840e2000c02403900208380002008004040821c10182004c58900140800221580020030b00149801848002061400200103000c1409d08185860c080070408204182400d081000002042010000100000c080140c080003818804082810808081065c78000000000004f011438000040c10002041804a1448304140000a00002080418004484880420401060c08a) else (if j<2 then (0x608df8001890610625e000787b3e0006a536e8ecfe06bc9a77800064695066a80ad9856be0000a657494f426198de12855988fb824a5e00078001612578001299f167b4e44b78001e1e0b813fe00078001e0003073d0028a25f2802c78000597e520cfc044ba533e00060219e0001125fc0a9922d8a06d5373520400a471e000786f3e000613a46158e025dc20bf8001e0006849321e87252c7e005039c659678001e04250359e000685660515507a60002f80c5e0001627be1af9a2ffa161f800044c4780010132d94c68141f8001e00078000007fe27ffe00078001e00078001e000595c3e00078001e0003830fe00078001e00078001e000087c1e00078001e00078000454bf8001a99678001a18fe300a413d28743e0000042a59fe00095e000107fde00078001e1168035be0006b113ca09e97e3e0007800025670f6ca60434013de0000e379e000483bf29f5581ad615bea469e00000750e1f9200a5e00078452093982561e00022621e00078001ba0b78001e00078000860378001e0007800160f678001c013f8001e00078001e0007800100be78000c1834855ded28f80010e10f800161fb4020d790df8001e0007a35c982f78001e0003266a602378001c10778001e59ef8001619b7800080bef069ca9256919660e5104b69de6c85546012c047404c2f8001e000007348c2cf8000016878001e0001112fe101d868fc0e2995e609d8f2521a1f3885ae010fd868144c31a562e91e59476c2039678724b5082070075002deeca418595c208d836c017fb91a0e17db0730f830ca629cd4df8001e0007b515b8c9eb72e417ab819541e1f8638c194484cfe08d010d6a122780016d4f3881fc9d978000a18d883a88034b8733a165ea821603f78001e4d9981ec8208285162530bb653e000604dd20d3182abc1f878000c4964e49ca0844a626206ff9113e00043533c0a628825e000506b3e00021566c9ddfb0a9a0bc614952134312566d55f07b00031f8001e00078001e00058466a1ca5954405cbd9507e00028716f8b07800198a1f1496015cf8000e177b94fbe0006874de199f8001e0002350b197a4235409969003981a330309a9f6232fe15693147e4032d8393c20eba3e74917f8000891278001e00078001a0a730388a956880fb88d0a0416617e7800060548b7e3e000280bbe00078000403d78001c0517074ac573f8001e0004036f082a981c261110039ae8d078001e06860159e00078001e0002018fe1b378001007a78001e000296dd651312427e00073469e00001337e00078001e00078001e00078001e00020425e000081a3e00032423e00028261e00061338e95cf8258c16a78000898db008ae09178001e000680e9a98e910d5096f494f30517c8227e00078001e0003a0a0a5d56972be00078001e0004802460bcf8001e0) else (0x1dd7883c2076c044f4466f810b21e36a43b892e8036700e0f82c7ec2f9822da0aff080465476866fe0000143de000725106d1ad83ea989e01385e0001161844f176295c20578001ec29b8078b915f8001e0004179d6a06a92eb0c64f828de00078001e00072673011278001e00078001e1ab000ade0007800138d978001e00078001e0002c605e00078001e00078001f91f983ee651cf80010140f8001e000500b321bd78001e00078001e00010284d9ae934c325b2b8659ede4603f34d6bf800100b77800125d4b834461b7002dbe0004280c213dd84eac99c7800141a1e8399e000325bfe0005b60a61ae8a40c0126f8001e00078001e0006268ea4e8f8001e0007800120e7d36ad05b61b40ae49b331a4edeb31281e9fa78001814db81b3e00031140405758290019978001e000780003dc778000c86ff800180e07800041042836be000004a9e000780018574201270062f800125ec8a679e0005009e401ef8000c9ad78001181c7800161a17800181494a2d0c57c7800178c1f8001e0002072de00008055e00078000004b6179a840240603e00058561e00002553a1bf300b5e00078001e0001042d808a2884080a2a14f8016378001e000780006095b002d2d4c78000200c9261ba153f343c0d8378001e0007800109537800085e66266de000496f3699ef80004139f8001008fe847161530e2f9e0007800080a6c12728033f8001e0007800121af285b260d5f8001e084a85c6002e203d3e04db36e329cd78000000678001e0007800140a938377e00078001e00078001e000524f1e00078001e00078001e0007800162077800041abf8001c0d1f9417407ef800041f7b00a1e000730b680df58523e00079670214e02502e5847800141c82233f39f4897e5e0004006fccfd0069f2012204afe0001e29320b9303b1e000780006164827d1e000696b3e0001064421a8f8001b8dc197d44128a84c1a1c9ee6fb581bf800028fca0583212b780012434186db45100072a4162f8000013198806a20e404a1056688845d9f7506ab09d6711a9818a40754c0caf8000a4f3f8001e00078000e99fc777ec1f748053a9a47800100cc780012e031a692c54fb023ac08b982c5e000380c9e000080eb413f307bfa9595833be00078001e0003a661e00078001e00030622a9f078001e00018713e00078001e000780000019305684dc720141e00078001e000483a7e00050173e000602cfe0002a46e044ec1415053dfa345e9dbf8001e00040737a1c2e06c9e00008803e000004c9e00078001e0a7f800060a5e25a3e1858841ee903e014fc5ef1a0b3c0d078001e00078000edad78001e00078001e4a2b17e76dc80249389cbf80014c6b78001e0000862ce0633016140fe60313e00040007e047403f1e0007800059ce1032cea095a567411dc616be00078))) else (if j<5 then (if j<4 then (0x85b9e0007800001b4e075fe0000a785c5b3e75e8e583a671da1bc52570e03cc17936072f8001e00078000017ee071de000406d0c041522de7910087c521d77800005ebf8001e0006e2e7e00078000858ae0275e00078000c193805bbe00078001e00078000216740739e089406682079683abe0000810fe0007800161a4f8001e00078001410e78000e087e80c3e0005e5d461df310d980171a476c133524ec98dd73731001478001e00078000050ff8000656578001e1486817e61db2879f6103e06ffd9b6d2357e000587d5249a9a400e1e678001c0c817787e000681a559647800180c6e83cce079f849cc4ec815a03914c820ff9e6523d409c4780014154b156b4157c6333e00050247e00078001405c780000104b0143a10cd85bcc075d80e5e000780006146780012dbef800065203061de0005a753a565c271f45c1c282fe0007800080534e310a5158a36de00019451e00050133a0203a529e0004871be2027800069a0f8001e000406edc9a7e807ee9607800049d2c82b3e1e90125d49c74865be0003000fa210a23dcc067f800150b55151ac951a040360161827605af78001e00078001092678001e00078000e16d78001e0001249a6c66f8001e0007800109d7181c5e000281cce0d79246be000204e5e0007800188da8b035e00078001a051f8001c1157006d00c7194c9e00078001e000415ed4d36524e2218678001e0000b639a499186a7e0004a5aca0d0f8001a5807209f69a078001e00019445c0ec9134640f0f02b0c1b038652c9431061b19c35e4590147196560a0a5038e81a0d01872cc6681f981b9191b7b81b1047289f4f141a4070780014982f8001e000780011de3e82d8c0178e30c181d007180155ca34601a2023c6e06c78001e00068175e00078001e000780004832cb5f9e0004025a696bd8634c15c58784e4fef0660651998084a8f852550696ce017c20923140fc91b21791e00078001c54678001e0f5f8001e00078001e00078000a95fa8123451c41389e00070792a1509828f649bf8000b9eb281c6c60c78001e00078000c1ebf8001e00078000a1d8f8001e000604052506227f540226838604514850de000780006008c67bbe000780004a112e0d4243df8001e00028621e00011413e0005944be000290da6025e81efc1f4f170ec1c79266721610877be0006118ec0852059fe0001b7c3a19578000c04ba1721e0004e7258000f8000e584f8001c0aee60cd011b4678d218b8a362802a9a1b4410d684efe0369060ac015f8001e0007800109cb78001e00078000e5c9f8001e000605c48073d05e06987f800009f8487f3e000504be80118e3fbe98378001a0b36802964950a624ed51f80000595183e9e0001a508e46788271e961b05d5e000405b76147f8001e000383da411f0a644c5627e6b3e0004234c8) else (0x45d0f8001e0002045e21697800101446a524c9dc803c8811be856d646af07c300ebf8001a20a0a535e000301fde0001865c69242145301fd78001e0007811f446be86d5e0002000de0004c535c16b311382187f80002ca1503ede0005262fc1fb9873be000493bde000244f5e000780018026b0565c98f5146fe00019829e0003981ef8c178001615da06e600bb78001c15f887bbe000717e1e00078000819e003dfe000487d640bd62823a1c97800165bec0479e000100d1e000485d9017f4b817981a7800100523a696c19ee14c5a53582603e0005118b2088780008182381c901e5bb7f064f2a05efe000585ede000080206d95580608085a05db81fec032fe00078001e00078001219fb868b6420f8000a08278001e0007600af835e8834981dd0281f169d86b08078884fba172983714056a35a4616058157e4fad8119e00078001a9d12844d41084354a49a24264261be6965ae957916d198dcb10cfe0002a50459e7b864c220078001e0007800100b0e3539e0004913c046fb82afc0f40a07aa86a804dfa0f90255dc18cf8001ddf7602ee25b900465e00078001e0007a74020ef78001a464e85e3e000025baa020f8000005478001e00078001e00070497c98740013e117780008045f8000a106f8000c1852801d88dbc9377e00078001e00078000e1b2981ba05e3a850481a51026be00070589c152a00362533e05a70949b13736082f8000e1545248a696378000a105687816433187f6804d78000892b81821e0007800021c3f80002006f8611e0003e5c94110b03a2f8a2205790dccf800185b2607a35834514a18ccf9b0a46611466ab492ff8001e00078000c076680ec4d4d785c8780d68677e00078000a12d6a731e0001033c8212437d72149ae6c58c61d064b26021161fe000123dfe0004132b604ee66efc10ef80bfe0001235be0001852be0007800144cc51813e0007b77b2550f8001e00078001e0007033240a2107c9e0005079be00038155e0007800120ba78001e0006062ac50080139e00078000412af8001e0006827fa198f8001c127a8193e0005a481e0003a5e1e00079783e0000b603e000325078016a03f740ee78001e000123db60387026c418f74347e0001e011e0007a1b9e0007170be000780004059f8001e00078000e0a878001e000686a1e0007018980d2e65fd217d78001a12f20546c57ae855ba94a98779e00078001e00078001e00078001e00078001e00078000486a780005dc378001e0007800084cb7800168293837849f17800040af78001e0000a58be0000876f80b278001e0001882d092378000003c2024b8037780004c33904c5e9366850fe0002946b60b9f800029018142be0002045165d5f800045ec78001c44c78000a5e1182d24999281d0c038f800021bef8001e947500bde1f8f800121f34)) else (if j<6 then (0x7800160a0f800081dcb0777e4eaaa60fe00078000a090f8001e00018482e19d78001e00078001e000184a5e00032577e000215a6004081669e52e22675e0007a837e000436abe00078001e000584da2493aa33be000087a9e000624b0c1a478001e985780012004793cd6005507dbe0003830c81da78697c98d2b6c7a06478001c1b178001e000084599de33a19e0534f8001e00078001e00078001e0007800161ba78001e000106734170b22d40deef8000c01f2032240607674de01a932da205a301b9e0b8b83630450d24bd058278000ad18f800118311b279e088f8000190478001e00078001e0004165f219236729e00078001e0007800025ba78001e0000a61000770630fb8fa1180585c2010d3e15ef8000c181ca4f46146da30181b88b63fe00078001e000780014984f8001e0005029460a8f80008121f0437414ed374be00078001e00078000c1f429276693a083fce041e01dee5adf8000a0d49174769858e7cbe00078001e000205c1e00078000403378000c1e4405b0013878001e0007800081d66a41be0004802ee5c97800068685130e6205fa6e8c1ad780002861f011b08d808832604c580d5d9e478001a0eb105e6e55d602040916c26236602f8000e080f80000960f80016d13f8001e000213c321ffd023d694678001e0003250f80807800081e2c27e20844d8092e04af8000e0fe98715e000384f220b8607050c2b102512d4bf8001e00078001da00413e9e0007800145b37800161d1615abe000001208520981b6a2044256b40b02a7c3211e9e2e04209e8337c44d0e4456087184b06115e80b7e142f869a4461c83156a06287d94c32f270be00078001857158239800aa01630a05904fec0c940819814fc808621d97800005c0c0409e0005a813e00050613e00028647290ff8000cccef800120ce202a8c1d380535e000126546a0ef8001e00050026609378001e00078001e000780010513e66cb8d6b6113e60450076a5930c94cde000004e9e00070001e0d92847fe00078001c195a16a060ee9049141ee6075be0003248e0cd4733e4403e76323e00078001e0006012501905882b80b578000e952a85dde0003850105124846b4099f8001e000181bd4582f80004109f8001e00058601e9977e3090499f840be00078001a018f8001a14a4a5a5e00050447e00078001e0007800100673a3f7e00051795e0002948c40f7000984065f8001e0007800165387e79be0004266fed7578001409eda538a00f9171141aa284a7c211f8001e0007848ae8d3a835c251a78001e000396d320948358fe0001c811c01c78000082b204984023f8000012e727608011707f1e0007848de00078001e0002859960ad0063a81d078001009f78001e000304ec251e4b3172d7d88306a106406c6e9ccf8001a074f8000edbd78001cd077073f) else (0x1614ce978088d220176e04a482fc491ee218ec19f1a543417a2166a41bbf8001e000780004db86a56fe000585d1c15f584e200c0bf5c889f378001e0002a0bac09e283a1e00078001e00078001e00078001805e78001e00078001e00078001e00078001e00078000a0c07800180ae285f1e00078001e0007800141dc78001210078001a0903a80e4206a94d5e000507e9e00078001ea051076105c8b870141f1f8001e00d78000e0b2f8001e00051523e000380a7211a3a402a06a7800105cfaa687e00078001615d3001740f5586d72c1c8030ba1ed7800040868a483e000120a269e9e84d9e0a1b03fe61e7281f440f3c86a5e0007800065d278001e0005880de000780008173200e699f01240860cff8000e9b17247d215078001212eb01f060c63e1f441b7f8001e00078001ed52507ab800f02746c052c36cac0ed885d6e0dfa26f7e000780012ccf7826fe0004774de00078001e000616dfe000224ffc907f800141796e0ce286b7a1b6e05af800185bb4e0b841a600788316aa2849e000180a9e00023467e8f8f8001992af8001e00012723e0006b7c7e0f8222d364ba01332800c2023121baf800121102846218ddb839621eb28711e00078001e00078000893af80009948d6807e0001a677e00078001e0003600c8918e016ee1669353a58bdf2486c0ed78001e00078000419c6262c6c2d135e9e00061636f9dfb6337e000501e128d7f8000003b806cfad64f800140ab78001449878001c0c7f8001e0007800140dd1083e4db7f8001e0007800061448a555e00078001e0002256c099378001e00078001e0007282a4019d025fc1e3f800049a3780006944b872f603ff800041211b4540a0c6e5f6a1d9f87472542f033401646065f20d278001293ba9411ac63c83a4adf3681f265df686b81830780010e03a8813c95e78001e000687bde0005627de00078001c44cf32d5e00063601a91cf8001049a287e7e14c30837e00078001e00048391e0c45852ce8d4f8001a06ae058fe00079459e00078001e000124740e0578000417ce92e724f578001e000783c7e0007800160d878000c1d4b8183a10c6a497801a7800180e36007425f3632df61520a57c6cc028481e00051263e0003378960667127584e99b0a3682d7800081c378001e000))))
def genData9 (j : Nat) : Nat := if 15 ≤ j then 0 else (if j<7 then (if j<3 then (if j<1 then (0x5c42ff3acc17f9d630bfceb105fe75842ff3aa617f9d510bfcea305fe750c2ff3a8217f9d220bfce8905fe74082ff39ec37f9cf60bfce7885fe73986ff39cc17f9ce50bfce7105fe73842ff39a217f9cc61bfce6305fe73142ff398617f9cc10bfce5b0dfe72d82ff396617f9cb10bfce530dfe72982ff394a17f9ca31bfce5185fe72842ff392217f9c861bfce4305fe72142ff390617f9c810bfce3b05fe71cc2ff38cc37f9c660bfce3285fe718c6ff38c617f9c620bfce230dfe71182ff388a17f9c431bfce2185fe71082ff388217f9c361bfce130dfe70982ff384a17f9c231bfce1185fe70882ff384217f9c061bfce0305fe70142ff380637f9c030bfce0105fe70042febb6617f5db10bfaed30dfd76982febb4a17f5da31bfaed185fd76882febb4217f5d950bfaec98dfd764c2febb2417f5d910bfaec285fd760c6febb0617f5d820bfaec085fd75d82febae617f5d710bfaeb305fd75942febac617f5d620bfaeb085fd754c2febaa217f5d460bfaea185fd75042feba4417f5d120bfae8105fd73d86feb9ec17f5cf10bfae730dfd73982feb9ca17f5ce31bfae7185fd73882feb9c217f5cd10bfae630dfd73182feb98a17f5cc10bfae5b0dfd72d82feb96617f5cb10bfae530dfd72982feb94a17f5ca31bfae5185fd72882feb94217f5c910bfae430dfd72182feb90a17f5c830bfae4085fd71d82feb8e617f5c660bfae3285fd718c2feb8c417f5c610bfae2305fd71142feb88617f5c420bfae1b0dfd70986feb84637f5c061bfae018dfc76cc2fe3b6217f1da50bf8ed18dfc768c2fe3b4417f1da10bf8eca85fc764c6fe3b2617f1d920bf8ec885fc76142fe3b0637f1d830bf8ec105fc76042fe3ac617f1d620bf8eb085fc75582fe3aa617f1d510bf8ea185fc75042fe3a2417f1d020bf8e7885fc73842fe39ac37f1cd60bf8e6a85fc73442fe398217f1cb10bf8e5085fc72586fe392c17f1c950bf8e4985fc72442fe390217f1c560bf8e2a85fc714c2fe38a417f1c161bf8e098ff370443f988421fcc1910fe606887f302443f902a21fc41910fe206887f102443f802a21fac8220fb661187d732c43eb99221f5cc631faa648877b50943bca80a1dd9d710eeaeb886fb609837bb0cc37e9c061bf4e018df970186fcb80637ddd710beeea885f671982fb38ca17d9c630bece3105f671182fb388a17d9c430bece2105f671042fabae217d5d510beae3305f571942fab8c617d5c620beae3085f571182fab88a17d5c430beae2105ee72186f7390c17b9c850bdce4185ed72186f6b90c17b5c850bdae4185de73186ef398c1779cc50bbae630ddd73182eeb98a16f9d020b7ae81057e75c42bf3a8c15f9d430afaeb8857d75182beba8613f9d8509fcec18cfe760c27f3b0413f5d8509faec18cfd760c27ebb0415d5d710) else (if j<2 then (0xfdc0f10fee06887f702c43fb81221fd9db10fecec887f675c43fb3aa21fd9cf10fece6887f672c43fb39221fd9c660fece3287f6718c3fb38c41fd9c550fece2307f671143fb38861fd9c420feccb887f665443fb31e21fd98d10fecc5887f662443fb308c3fd94f10feca6887f652c43fb29221fd90b10fec84887f632443fb18863fd85b10fec2c887f615443fb09e21fd84d10fec25887f612443fb08221fd81b10fec0c887f605c43fb02a21fd80f10fec06887f602c43fb01221fd5db10feaec887f575c43fabaa21fd5cf10feae6887f572c43fab9221fd5c660feae3287f5718c3fab8c41fd5c550feae2307f571143fab8861fd5c420feacb887f565443fab1e21fd58d10feac5887f562443fab08c3fd54f10feaa6887f552c43faa9221fd50b10fea84887f532443fa8b621fd45a31fea2c98ff516443fa8aa21fd45410fea27887f513443fa89621fd44910fea20087f506c43fa83221fd41710fea0a887f503c43fa81a21fd40b10fea04887f476c43fa3b221fd1d710fe8ea887f473c43fa39a21fd1cb10fe8e4887f465c43fa32a21fd18f10fe8c6887f462c43fa31221fd14f10fe8a6887f452c43fa29221fd10b10fe884887f416c43fa0b221fd04f10fe826887f412c43fa09221fd01b10fe80c887f405c43fa02a21fd00f10fe806887f402c43fa01221fbc9120fde41107ee72187f7390c1fb9c850fdce4187ee20483f6b90c3fb5c860fdae4287ed720c3f692241fb48020fbe6d987df364c3ef9ae61f7cd530fbe65087df32443ef99021f7cc631fbe61187df300c3ef398c3f79cc60fbce6287de314c7ef18261f75cc61fbae6307dd73143ee9b661f74d930fba6a987dd32043ee98863f74c030f7ce8107bd74083bfa84a1df9d710efcea3077e750c3bf282a1df5d710efaea3077d750c3bea80a1bfd9760dfecab06ff63d877fb1ec1bfd8d61dfec6b06ff62d837fb12c1bfd8661dfec230eff609837fb00c1bf9d850dfcec18efe760c37f3b041bf98561dfcc0b06fd761437ebb063bf5d830dfaec106fd655837eb1ec1bf58d61dfac6b06fd625837eb08c3bf58060bfeed985ff76c42ffbb4a17fdda31bfeed185ff76882ffbb4217fdd950bfeec98dff764c2ffbb2417fdd910bfeec285ff760c6ffbb0617fdd820bfeec085ff75cc2ffbae217fdd560bfeea985ff75442ffba8617fdd410bfee9105ff74482ffba0417fdcf10bfee7085ff73586ffb9ac17fdcd50bfee6885ff73042ffb96217fdca10bfee4b0dff72582ffb92a17fdc930bfee4885ff72042ffb8ac17fdc550bfee2985ff71482ffb82c37fdc131bfced985fe76c42ff3b4a17f9da31bfced185fe76882ff3b4217f9d950bfcec98dfe764c2ff3b2417f9d910bfcec30dfe76182ff3b0a17f9d831bfcec185fe76082ff3b0217f9d760bfceb985fe7) else (0xdc96b44afd2559129e4945349f0a4dbd25d6925e48ed2455921a4904e47ee23d3d1d968e4746e1a34d919888c5245f022d9515c28a6644fa225c111ea887a440421e110e128697430e216610a4c84bd423c20ff50704833d41612091d03f2817e4081a02d500747fbf3fa21fb48fc787df73ed91f494f9c07c9b3e2b1eedcf6d27b1b3d429e8dcf3d2799b3c5e9dfa0ee1476473ac69d304e80e734d39499c818e29870b638149beb8ddd66e1636a09b1b0d72e6ad435089a4f0d12867e3339d99a4ccbd66555325f9905cc6cc62b53118986d8c240605d2fd197c7cbd485e292ed717484b93a5c222dd396cd4b5745a3f2ce216500b13058022bba95be8ad10561f2adb15510a9b654692a0014e80a65c52bc292994784a2cc50c7282613f689ebe4eed273d937dc9b0a4d132650930bc97564b3925639295493c6499e24ac92450919e488a2422920008f88478823a611c408da8468f2325118148b80457b22969137c8922442821f190e7886a04302215e909bc844241d320b5104048142405c20070ff007ee43f091f500f9007bc03d9b1ea68f39079083c241de20ed6c75f63a2f1cad0e2806fcc372c1b618da1c6c1835b51a7d8d09866a232b219128c54061f2303617be0bac05bc82d0f161d0ad94552029bb14730a0684f1a26c11303894ec48de239a116b88808425a20580fe587d883d501dee0e9a071e837801aeb0d140654c30fc17a90b6a058442a78146709c904b3c23f41125082803e341d700de306900312c16ec0aaa04ea824001068075f03450171c09e4041d01a400a14036000db000300003ffb2241ffd8520ffcec907fe72583ff312c1ff81920ffaec907fd72583feb2a21ff59220ffac8907fd62943feb1461ff58a10ffac4b07fd62543feb1261ff58910ffac4287fd61543feb0a41ff54910ffa84987fd26883fe83241fed8260ff6c0b07fb308c3fd98261fec4210ff620887fb06943fd83461fec1a20ff60d087fb06543fd83261fec1920ff60c887fb058c3fd82c41fec1530ff609107fb04483fd81c21fec0d10ff605087fb02443fd380c3fe9c031ff4c0307fa50143fd18061fe88020ff420087fa05843fd02a21fe5c061ff2e018ff960183fc98061fe44010ff20d287f9068c3fc83441fe41a10ff20ca87f9064c3fc83241fe41910ff20b187f905883fc82a61fe41120ff207087f903443fc81421fe40910ff00b087f805443fbbb621fddd910feeeb887f775443fbb9e21fddcd10feee5887f772443fbb8221fdd9710feeca887f763c43fbb1a21fdd8b10feec4887f761987fbb0ac3fdd4f10feea6887f752c43fba9221fdccb10fee64887f716c43fb8b463fdc5931fee2c887f715c43fb8ac21fdc5510fee2a087f713c43fb89a21fdc4b10fee24887f710843fb88021fdc1b10fee0c887f705c43fb82a21))) else (if j<5 then (if j<4 then (0x1609044200f05c28120802c1208038180802002e47210ec70371a8b04a2110078301309040160a040140803010017230ec6e3515890421f0f074301409040180a040180802002a48208e872371b0b448231007c2e150904416090401c0c05010057239107c3a1b8d45824110803c170a048200b048200e060200800b91c843b1c0dc6a2c12884401e0c04c24100582810050200c04005c0a5e5d2d66963b4aaba518526fa92f34919a441d1fda8ed346eea330d17768ad744f9a23f50f7e86db4304a1495078682cd40bea02acfe027e773eb79f394f7de7b653d6d9e944f38e793d3bf69dbdcec4a75413a5b9d0b4e69272bf38ff9c5d4e122700737919ba64dc1e6d85367d9b1c4d7ce6b5d35069a2acd042679732f6993dcc826629f309597edcbc865d292dfe96b8cb392588b2ba6958ccaa7a5459299f949fca31250ed280493db49dc64e4726de93484992e4bfb25b892884917e479323189138486fe425320549007c7de63dd91e568ee94755e39b91c8e8e24c6f3a36b91b0e8d40c681a333b194f8c7346262305f17e18bce45d5e2e2516cd8b444590e2bfd15b98aba4527e281313588961448fa2375113f8862441fe20750ff587d843cb21dcf0ea2872ec38621b5f0d3d866a4318a17f30b9085a5c2bae14f30a1984d3c251e11cf087e841cc1d920d9d063882da414c2096b043a81fac0c820497019a805e400e1ff44ff277f51bf739fab8fc877dfd3edd9f61afa927d1dbe7d9f362f96c7c93be3adf14cf8617c0e3df5dee28f67e7addbd44de8d6f3cc797bbc93de360f11a784b3c025def8eef87711bb55dd93aec1975c1babfdd4f6ea0074c2ba471d19ce81473ad39ac9cc14e58f728a392adc884e3fd71e0b8dcdc65ce2e0714db8935c410e1a8709fb837dc0ece0166fd6b7d35bdc8de846f0db76edbab6dd166e56b717db7ecdba86d9fb6be9b56ada676d0cb672db2fad92f6c70b6205b066d7ee6bd4b5d91ae3ed6da6b4ab5941ac16d5c66aa5b53f5a95ed43d69f7b4e19a628d27e690ab471da2f2d1346877b42a9a0cad02067edb3e599ea2cf0c6717336619a16cc996625b2ff59770cb736592b2b5d9524ca4d65043270d92fcc9396475b21558fa2c7296345317658a86c4ad6214b0f91873ec35a618ab0b418516c2466100b06f182eec1326076b02a180c6bfd65f8e2f9657b86bd245e6b2f2217886bbf55dd82edad764cbae15d4e2e9817448b9e85cdaae5c17256b8e65c50ae171702eb7c95bbdadc016d76b66d5b142d78d6b3cb5595a8a2d3196902b3e259af2cb8d653cb2595905ac7196260b0b55821abf8d5f3caf59576f2b9695be2ad91567dab2255768aadf550e2a4f950d2a794535fa98ed4b14a4eb522aa8efd45d4a21550a4a81893f089ea64ee427559394a9bf44da1a6a4933c299304c562607d2e) else (0x100602810050200800b118803a1c0d86a341609444200f06028120803014080301004005c8c3b1b8d456241087c3c1d0c05024100602810060200800a91c883e1d0dc6a2c12088401e0b85024100582410070301004005c8e421d8e06e351609442200f06026120802c1408028100602002e47208ec72361a8b04a220f8783014088401809040140802008017251208e32178b458291309446221007c3c79288e32178b0522712888401e2c8e3b1b8d45825110803c180a048200c050200c04010014238ec6e351609444200f0602812080301408030100400508e3b1b8d45825110803c180a048200c050200c04010014238ec6e351609444200f0602812080301408030100400508e3b1b8d45825110803c180a048200c050200c040100142310074381b0d4682c12888401e0c05024100602810060200800b91876371a8ac48210f8783a180a048200c050200c04010015239107c3a1b8d45824110803c170a048200b048200e060200800b91c843b1c0dc6a2c12884401e0c04c24100582810050200c04005c8c401d0e06c351a0b44c231007c3215090441a0a048180a0200ae46200e870361a8d05825110803c180a048200c050200c04010017230ec6e3515890421f0f074301409040180a040180802002a47220f874371a8b04822100782e140904016090401c0c040100172310074381b0d4682d1308c401f0c85424110682812060280802b918803a1c0d86a341609444200f06028120803014080301004005c8c3b1b8d456241087c3c1d0c05024100602810060200800a91c883e1d0dc6a2c12088401e0b85024100582410070301004005c8c401d0e06c351a0b44c231007c3215090441a0a048180a0200ae46200e870361a8d05825110803c180a048200c050200c04010017230ec6e3515890421f0f074301409040180a040180802002a46200e870361a8d05a26118803e190a848220d050240c050100572310074381b0d4682c12888401e0c05024100602810060200800b91876371a8ac48210f8783a180a048200c050200c040100152390876381b8d45825108803c1809848200b050200a040180800b91c843b1c0dc6a2c12884401e0c04c24100582810050200c04005c8e411e0e46e3616094441f0f0642a12088341409030140401588c401d0e06c351a0b04a2210078301409040180a040180802002e47220f874371a8b04822100782e140904016090401c0c040100172410478391b8d85a26118803e190a848220d050240c050100562310074381b0d4682c12888401e0c05024100602810060200800b91c883e1d0dc6a2c12088401e0b85024100582410070301004005c8c3b1b8d456241087c3c1d0c05024100602810060200800a920823a1c8dc6c2d1208c401f0b85424110582410070301404015c8e441f0e86e35)) else (if j<6 then (0x200802001035162ac4aa411284409f0f274b1d8793a18060281038dc3c9d090280c021c6a1e4e8400e040100081a8793a100401002002084220823c1806020e350f0411e08018080040d83e110421c0a020090350f0401087020080040d84ca40ca5c1a8b0502510872c6a25520612e0c45829120843963b0f0612e0c4582912084394371004810870300871a8782008438100200206c1f0882408830100481a87820080220c0400206c2350855260d458180a844196351128428930622c0c850220cb2387828930622c0c850220ca1d8894214498200c850220ca1b880240a0220c0438d43c100401106010010351027c2491052240c8501204b1b8782491052240c8501204a1b8813e12488200c8501204a1b8813e1248829120401204a1a8813c12480291006420090058dc409e09240100642009005120823c1c8dc6c2d1308c401f0c85424110682812060280802b11c823b1c8d86a2c128883e1e0c05022100602410050200802005c8e3b1b8d45825110803c180a048200c050200c04010014238ec6e351609444200f0602812080301408030100400508e3b1b8d45825110803c180a048200c050200c0401001464b1962ae55aa04ea4508813a59288e3d1d8dc6a31287a3b190a44e250d0601c0c05020d178a444160a03818060212c61d8dc6aab52284409d0c05024100602810060200800a11c843b1c0dc6a2c12884401e0c04c24100582810050200c04005c8e441f0e86e351609044200f05c28120802c1208038180802002e4a218ec722f1288c44180a8501809040180a0444943d1d8bc4e25110602c14060281006021e48208e872371b0b448231007c2e150904416090401c0c05010057178a444160a03818060212461d8dc6a2b120843e1e0e8602812080301408030100400548e3b1b8d45825110803c180a048200c050200c040100142390478391b8d858251107c3c190a848220d050240c050100562410478391b8d85a26118803e190a848220d050240c050100562310074381b0d4682c12888401e0c05024100602810060200800b918803a1c0d86a341689846200f8642a120883414090301404015c8c401d0e06c351a0b44c231007c3215090441a0a048180a0200ae48208e872371b0b448231007c2e150904416090401c0c050100572310074381b0d4682d1308c401f0c85424110682812060280802b920823a1c8dc6c2d1208c401f0b85424110582410070301404015c8e411e0e46e3616094441f0f0642a12088341409030140401588e3d1b8b04a22100783416090381406011e47208ec72361a8b04a2210078301409040180a040180802002c471d8dc6a2c128883e1e0c05024100602810060200800a11c8a3f1d8dc6a2c12888401e0c05024100602410060200800b11c863b1c8dc6a2c12888401e0c05024) else (0x18682c12888401e0c05024100602810060200800911c6a2c12088401e0b85024100582410070301004004c8e3516094441f0f060281108030120802810040100263516078301409040180a040180802001c42178a444160a04c2410070300c0434843516078301309040160a040140803010010249107c3c1d8e870361a8d0662a13898381a0c8381a0a04aa49220f8783b1d0e06c351a0c8522712868300e0602810a0f06c260f864220d050241006028080270f06c260f864220d050240c0501004d1d8d44a1e0c040180a040180802001a3b1a8943c180803014080301004003478361307c3211068281208038180a02009e3b1a8943c18080301408038180802001c3b1a8943c18080301408030100400347635128783010060281006020080068f46e2710068240e05024100601183a1a0983e19088341409030140401347434128783010060281006020080068ec6a240e860200c050200c0401000d1d8d44a1e0c040180904014080200800e239087c391c0d86a34180a8461c0b0541c0d030152210f872381b0d4682f148882c14070300c04407c3a1408836170a034180b048200e06021e391b08c3e150883412060281004013472361187c2a11068240c0501004c1a8883c14080301006020080058d4441e0a04018080301004002c72361187c2a11068240c0501004c1a8883c14080301006020080058d4441e0a0401808030100602001835110782810060200c0401000b1b8802c12070280c0502008a1c0d0461f0a8441a09030140401307034110782810060200c0401000c1a8843a14080301006020080058f86a220f050200b0381808020018391a8883c140803010050200802003490411e0e46e361a8d04e200d058240e050180488f06e2610064240d05024100703008d1b8d4401e090401408030100400306e351007c3c12080281006020080068dc6a200f048200a0401808020018371a8803c12080281006020080060dc6a200f8782410050200c04010040070d868200f048200a0401808020018371a87c3a12080281006020080060dc6a200f04820090381808020018371a8803c120802810050180800611c76371a8d04e200d058240e050180470dc6a200f848220a048180a020098371b0803e12088281006028080260d468200f848220a048180a020098371b0803e12088200e06028080260d448170582410071c6a1f088240a02008e350f04010040100071b07c2209028080238d43c100401004001c6a1e080200802000e350f04010040100071a8b04a221007861b098320d0502461a894300c0502061a888280c0301061a880240a0300861a8742008020080038d83e110381404011c6a1e0801c0802000e350f04010030100071a8782008020040038d43c9d0802008020010350f2742008020080040d43c9d08)))) else (if j<11 then (if j<9 then (if j<8 then (0x340f84412050100471b0d4401e090401408030100481001a371a87c3c12080281006020090200346c1f0881c0a02008e371a8803c12080241006020090200346e35100782410050200a04012040068d8681f088240a020090361a0803c12080281006020090200346e350f8742410050200c04012040068d83e110481c0a020090371a8803c12080240e06020090200346e35100782410050200a03012040068d86a1f0f044200904014080200800d1a8d0409e092401488032100480306a200fa78241148028128803015080200a0101a0782008020080038d43a100401004001c6e361007d3c1208a40100602a100401401e350f0400e040100071a8782008018080038d43c100401002001c6a341007d3c1208a401409440180a84010050088d4681e0802008020010350f0742008020080040dc6c200fa782411480200e0602a1004014020350f0401007020080040d43c100401006020010350f040100401004004124883e1e0ec74371a8c450261289036190c05c1a0c05828120803b048208f072371b0d45a26118803e190a848220d050240c050100572410478391b8d86a341689846200f8642a12088341409030140401608e3b1b8d4682c12888401e0c05024100602810060200800a91c76371a8b04a2210078301409040180a040180802002848208f072371b0b44c231007c3215090441a0a048180a0200ac471d8dc6a2c12888401e0c05024100602810060200800a11c76371a8b04a2210078301409040180a0401808020028471d8dc6a2c12888401e0c05024100602810060200800a1288e461d8dc6a32178b0522712888401e3c96451f8f4783a1c8dc6c331509c4c1c0d0641c0d050254250f4763a1b8d46429138943418070301408408e421d8e06e35178a444160a0381806021e3d1b8d86a27100682c12070280c02348c3b1b8d456241087c3c1d0c05024100602810060200800a920823a1c8dc6c2d1208c401f0b85424110582410070301404015c8e441f0e86e351609044200f05c28120802c1208038180802002e47210ec70371a8b04a2110078301309040160a0401408030100172390476391b0d458251107c3c180a044200c048200a040100400b924904723104803a1c8e06c351a0c85e2c1489c4a22100795248e862281309448221007836190c05c1a0c05828120803aa48238d85a2c1309446221007c3c190a848220d050240c05010057238d45825110803c180a048200c050200c04010012238d45825110803c1d0c05024100602810060200800991c6a2c12888401e0c05024100602810060200800911c6a2c12888401e0c05024100602810060200800911c6a2c12888401e0c05024100602810060200800912876321489c4a24110803c1a0c038180a0420471b8b04e25110803e1e0d058240e050180481) else (0x6ab4178a444160a0381806022047208ec72361aad04e200d058240e05018048118803a1c0d86a341689846200f8642a120883414090301404015c8c401d0e06c351a0b04a2210078301409040180a040180802002e461d8dc6ab415890421f0f074301409040180a040180802002c48208e872371b2d5682d1208c401f0b8542411058241007030140401648e441f0e86e355a0b04822100782e140904016090401c0c040100182390876381b8d5682c12884401e0c04c24100582810050200c0400608e411d8e46c355a0b04a220f8783014088401809040140802008018230d058ab12a9044a11027c3c9d308e3a1609044200f27436190c05c1a0c05828120803a6471b0b04a220f8793a190a848220d050240c05010053230d45825110803c9d0c05024100602810060200800991c6a2c12088401e4e86028120803014080301004004c8e351609442200f274301409040180a0401808020026471a8b04a220f8793a180a048200c050200c04010013238ec5824110803c9d0d0601c0c05020e238dc58251107c3c9d0d058240e05018047918682c12888401e4e86028120803014080301004004c8e351609044200f2742e140904016090401c0c04010014238d458251107c3c9d0c0502210060241005020080200508435160783013090411e0c050200c04010010210b0441809848208f070300c04308435160783013090411e0b050200a04018080088e86826520652e0d45828128843983a1a09548184b831160a448210e60ec6c250f860220c048210e06028080270e86c260f864220d0502510870301404013c743512878301006028108703010040038763512078301006028108703010040038763512878301005828108703010040038763512878301006024108703010040038763712880301206024108703008c1d0d04c1f0c8441a0a04a210e06028080278e868250f060200c050210e06020080070ec6a240e860200c050210e06020080070e86a240f05c200b048200e06020080070ec6a250f060200c048210e050200802003c703411a842a9306a2c0c054220cc1c0d044a10a24c188b032140883307c3a1128428930581c0c850220cc1c8d8441f0a0441809028110602009a381b08c3e1508834120602a110602009c381a8883c140803010060220c0400346a210f050200c04018088301000c1c8d8461f0a844160903015088301004e1f0d4441e0a0401608030110602001a391a8883c140803010050220c0400347237110802812060280a0441808c1c0d0461f0a8441a0903015088301004e1c0d0441e0a0401808030110602001a35108742810060200c04418080060f86a220f050200b03818088301000d1c8d4441e0a040180802811060200800e1b0d0409f092441489032140481306e204f8492209038190a024096)) else (if j<10 then (0x220471d8dc6a34178a444160a0381806021c360f84412050100471a07c2209028080238d43c100401004001c681e080200802000e350e84010040100071b07c2207028080238d43c100381004001c6a1e080200602000e360f84412050100471a8782008020080038d43a100401004001c6c1f0881c0a02008e350f0400e040100071a8782008018080039288e461d8dc6a32178b0522712888401e3c92441f0f0763a1c0d86a34190a44e250d0601c0c050214259147e3d1e0ec74391b8d8662a13898381a0c8381a0a04aa4a1e8ec74371a8c8522712868300e0602810811c843e1d8e470371a8bc52220b0501c0c0301111b0d03e11048140401206a340f04010040100081d0902e0b048200e38d86a1f088240a020090350f04010040100071b07c2209028080238d43c100401004001c6a1e080200802000e350f0401004010007238b04a221007861e098320d0502461d894300c050206110501806020a371a880240a0300871a8742008020080038d83e110381404011c6a1e0801c0802000e350f04010030100071a8782008020040038e8481e0b82c12080390360f87822090280802411c76371a8c85e2c1489c4a2210078d1d8943c18060281038dc401f0f04814060110350f0400e040100071a8782008020040038d43c100401004001c84220a0401806020e350f04010030100071b07c2209040140401206a1e080200802000e48208f072371b0cc5427130703419070341409448e3b1b8d46429138943418070301408388e3b1609444200f068300e060281068dc4012050200c021c6a1e080200801000e360f8441205020080240d43c100401004001c90411e0e46e36180a8461c0b0541c0d030150238ec6e35178a444160a0381806021a471609444200f058280e060180860ec4a220c050180a040180850dc40120501808021c6a1e080200801000e471d8dc6a27100682c12070280c02348e371609444200f0682c12070280c02387637128803012060281006011637110802812060280c04011448208f072371b0d44e200d058240e050180480f06e2610064240d050241006011847220f874371aad0622813094481b0c8602e0d0602c14090401d72390476391b0d5682d1308c401f0c85424110682812060280802b91876371aad05825110803c180a048200c050200c040100152410474391b8d96ab41689846200f8642a12088341409030140401608e441f0e86e355a0b04a2210078301409040180a040180802002e47210ec70371aad05825110803c180a048200c050200c040100172390476391b0d5682c12888401e0c05024100602810060200800b91876371aad0642f160a44e25110803c7120823a1c8dc6cb55a0cc54271307034190703414094c8e441f0e86e355a0c8522712868300e0602810891c843b1c0dc) else (0x80058d4441e0a04018080301004002c6a1f088240a02008e35100481406010c360f2742209028080240dc3c9d090280c021c6c1f088210e050100481b8802408438180438d83e110481106020090371004814044180871a8b1562552089421f0f274a1a8b156255208942200f8793a58d44aa40c25c188b048210e50d44aa40c25c188b0502410872c6a2250851260c458140883286a2250851260c458180a0441963b0f27430970622c120843943b0f27430970622c14090421cb1c8793a144983116050220ca238793a14498311606028110658e444a10823c188b028110650894210478311606028110650d43e110481404011c6a200f848220a048180a020096360f8441087028080240dc401f0904410870301404012c6c1f0882408830100481b8803e12088281204418080258d43c100401004001c6a1e080200802000e350f2742008020080040d43c9d0802008020010350f0401087020080040d43c100421c08020010350f0401004418080040d43c1004011060200102210850200c058180a040194350f0401004018080040d03e110481404011c681e080200802000e350e84010040100071a8782007020080038d43c100401004001c681f088240a02008e340f04010040100071a8742008020080038d43c100381004001c842f148882c1409848200e060180868d43c1004010060200103a1a8902e0b048200e40ec6a25120602e0c05828120803983a120782e0b048200e40ec4a1e0c05c180b0502410072c7639114782910040180a0481400c1e8ec72271188a40160a44814080301409024072228f05220080281205018016360f8441207028080240d43c100401c08020010350f0400e040100071a07c2209028080238d03c100401004001c6a1d080200802000e360f84412050100471a8782008020080038d03e110481404011c681e080200802000e350e8401004010007249107c3c1d8e86e35188a04c251206c32180b834180b05024100760943d1d8e86e35190a44e250d0601c0c050210250c852271289044200f068300e060281078e4451e0a44018080281205018018360f8441207028080240d43c100401c08020010350f04010030100071a8782008018080038d43c1d0802008020010360f8782209028080240d03c100401004001c6a1e0801c0802000e350f04010040100071b07c2209028080238d03c100401004001c6a1e0801c0802000e350f074200802008004118803a1c0d86a34190bc58291389444200f20471d8dc6a34190bc58291389444200f1c46200e870361a8d0662a13898381a0c8381a0a04a446200e870361a8d064291389434180703014084490411e0e46e361a8d0662a13898381a0c8381a0a04a647210ec6e351a0c8522712868300e06028108118803a1c0d86a34178a444160a0381806))) else (if j<13 then (if j<12 then (0x9a37112844014090301406028110602346a1e080200802000e47208ec72361aad05825110803c180a048200c050200c0401001723b1876371b0d5682c12888401e0c05024100602810060200800b91c6a2c128883e1e4e86028120803014080301004004c8ec61a8b156255208942200f8793a180a048200c050200c040100181d8d44a1e0c04018090421c0c0401000e1d8d44aa40f060200c050241087030100400407235110782810060200a04418080068d444a10f050200c040180a0441808007120823c1c8dc6c351689846200f8642a120883414090301404015c7a371a89c401a0b0481c0a03008c2411c6c2d160984a23110803e1e0c85424110682812060280802b91c6e2c1389444200f0682c12070280c023c78361307c3211068281208030140401387a371388034120702810060116391b08c3e15088341206028100401346e200b0481c0a030100448d43c100401004001c6a1e080200802000e350f04010040100071a87820080200800391c5825110803c30d03c100401004001c6a1d080200802000e350f0400e040100071a87820080180800392890476310476391b0d4642f168b052261288c44200f8795251208ec61d8dc6a32178b0522712888401e4094451f8f076ba1c8d86a32148984a1c0c8601a0c0502410a929923d1e0ed74371a8c8522712868300e0602810910c7e395c0d86a2f1488c441c0a8501a0c0301408911d84be1d8e570371a8bc52220b0501c0c0301112310074381b0d4682d1308c401f0c85424110682812060280802b9287632148984aa41107c3c1c0c8601a0c0502410912876321489c4c2552088401e0d0601c0c0502111c8bc5223112843e1e0e054280d060180a04408e2f1488c44a1100782c14070300c043886391788838150a24c2210068300c05021ec217ab852220b0542893090401c0c03010f1d8a550220c0501c0d0622c140803010e2410478391b8d86a2d1308c401f0c85424110682812060280802b920823c1c8dc6c2d1308c401f0c85424110682812060280802b12c8a3f1e8f074391b8d8662a13898381a0c8381a0a04a8481e8dc6c35138803416090381406011c471b8b04e25110803e1e0d058240e0501804811c58251107c3d188a4421908820060070f06c260f864220d050241006028080270f46e2713080341207028120803008d1c8d8461f0a8441a09030140802009a37118802c12070280c0502008b1a8782008020080200208e3b1b8d45825110803c180a048200c050200c04010014238ec6e351609444200f0602812080301408030100400508e351609444200f0602812080301408030100400488e351609444200f0602812080301408030100400487635128783010060281006020080068ec6a250f060200c050200c0401000d1a8883c140803010060200) else (0xb458291309446221007c3c991d8c3b1b8d86ab4190bc58291389444200f2047208ec72361aad064291309438190c034180a04821323b19843b1b8d86ab4190a44e250d0601c0c0502122390476391b0d5682f1488c441c0a8501a0c0301408991d8c3b1b8d86ab4178a444160a0381806022046200e870361a8d05a26118803e190a848220d050240c050100572310074381b0d468391c762c128883e1e4e87032180683014090420471d8b04a221007c3c9d0d0601c0c05020f238e458251107c3c9d0e054280d060180a04408e2c12888401f0f2742c14070300c04387639128883014060241087030140868ec4aa411060280c05024108703010d1b0d43e11048140401206c1f088240a02008e3c1b0983e19088341409030140401346e351007c2411050240c0501004c1b07c3c11048140401206e360f048231005026100602c100401801e371b0803e1e090441409030140401346c1e08c40130802c1004018016360f8441208028080240dc401f0904414080301404012c6c1f088240a040100481b8803e12088281206020080258d43c100401004010010350f04010040080071a8782008020080038d43c100401004001c6a1e080200802000e350f04010040100071a8782008020080038d43c100401004001c6a1e080200802000e350f04010040100072390476391b0d5682d1308c401f0c85424110682812060280802b91d8c3b1b8d86ab41388034160903814060120471b0b04a220f8793a190a848220d050240c05010053238dc5825110803e1e4e8682c12070280c024076361287c301106024108703014040138763712a9040180903014090421c0c023872361107c2811060240a04418080268dc44a110050240c050180a0441808d1a8782008020080038d43c100401004001c6a1e080200802000e350f0401004010007238dc5825110803c1a0b0481c0a03008e1a0782008020080038d43a100401004001c6a1e0801c0802000e350f0401003010007238d458ab12a9044a10f8793a591c6a2c558954822508803e1e4e983b1a89548184b83116090421cb1d8d44aa40c25c188b0502410873072351128428930622c0a044196351128428930622c0c050220cb1a07c2209028080238ec4a1e0c25c188b048210e50ec4aa40f0612e0c4582812084398391107828930622c0a04419447112843c14498311606028110660e444a10a040188b028110650894214080311606028110650ec44a10a24c18080301408832c6c1f0881c0a02008e47208ec72361aad05a26118803e190a848220d050240c0501005723b1876371b0d56827100682c12070280c02408e371609444200f8793a1a0b0481c0a0300901d8d84a1f0c04418090421c0c0501004e1d8dc4aa410060240c05024108703008e1c8d8441f0a044180902811060200)) else (if j<14 then (0x1c0c05c200c043472b81b8d4462290058291207032140602812048ae06a218e852200c8401809028018375b0d44e200fc78240a03008b1bad86a200b0481c0a030160802308e399b88c44a11007c3c160a4481c0c850180a0481263e9d8a44414498401c0c05c200c043472381a888431e0a04e200c05c200c050200e0500486a220f050200c040180802001646200e870361a8d05825110803c180a048200c050200c040100172310074381b0d46838e86a240f05c200b048200e06020080070e848170582410071c6c350f8782210048200a04010040068d83e110481404011c6a1e080200802000e350f04010040100071a8782008020080038d43c100401004001c8e351609444200f0602812080301408030100400487635128783010060281006020080068d4441e0a04018080301004002c6e35100782410050200c0401000c1a8782008020080038d43c100401004001c76250f060200c050200c0401000c1a8782008020080038883c14080301006020080050d43c100401004001c6e35100782410050200c0401000c1a8782008020080038dc6a200f048200a0401808020018340f84412050100471b07c2207028080238d03c100401004001c6a1d080200802000e350f0400e040100071a8782008018080038d43c100401002001c8e2c128883e1e4e86028120803014080301004004890c616aac4ca411a84401f0f27434160903814060126340f84412050100471b07c220702808023918803a1c0d86a341609444200f06028120803014080301004005c74240f05c200b048200e06020080068d83e1e0884012080281004010018471d8dc6a2c12888401e0c05024100602810060200800a11c76371a8b04a2210078301409040180a0401808020028471d8dc6a2c12888401e0c05024100602810060200800a11c76371a8b04a2210078301409040180a04018080200284a2391876371a8c85e2c1489c4a2210078f250f4763a1b8d46429138943418070301408408e421d8e06e35178a444160a0381806021e471e8ec6e361a89c401a0b0481c0a03008f238b04a2210078301409040180a0401808020022471609444200f06028120803014080301004004494321489c4a24110803c1a0c038180a041e42178a444160a04c2410070300c043476250f060200c050200c0401000c1e8ec4e25100683012070301409040180478883c14080301006020080050dc44200b050240e060280c0502008d1a8793a10040100400206e350fa742410050200c0401000c1b0d43e11048140401206e35100481406010e360f8782209028080240dc401e090280c021c6c1f0882410050100481b880240a040180438d83e110481408020090371004814060200871b8d86a200f87824110802812080301408020080122390476391b0d56832178) else (0x1d8d5682f1648830160a04c24108641a08791c6ab410058240e050180b04011835110501806020c3b1a8894214498311606428110660ec6a341128428930622c0c850220cd1aad0441e0a0401808030100400307035110501806020e471d8e06e3511050180602144823b186e351609c4a221007c3d128541a04810c84c01a8b23c180a04c24108441205003c84c01a8bc59220c0582813090421906821eb81a888431e0a4401908030120500347e3e5c0d4451e0a440180b840180902801e395c0d4451e0a4401908030140902801c47210ec70371a8d044140601808611d7035178a444218f050180602183e1dae06a291105)))))
def genIndex9 (j : Nat) : Nat := if 12 ≤ j then 0 else (if j<6 then (if j<3 then (if j<1 then (0x4ee03b2dc3e7223efc000f0003c000419260ef8b59a283a4d14ea920edb861565c213db02eb83304020220a9815859243c82f05368440a5b01690ee33132a0378406b6d580a15d7c000677d7c000424a7c000708e7c000f0003c000f0001026c9024bc000623ebc000716d89319833d73212416bd81774059bc000100c71007c11bcc3b847b9bc00051a0bc000f000101b9009e3c000e14c60253c3ae3c014f000331e7f0002916910d798635d01b7859d007a3c000f00033622f0001cdc5f0003c000f0003c000f0003c000f0003c00066777c000f000156e7f0003c000f0003c000f00004e0ff0003c000f0002ce66f00020608f0003c000f0003405ce092d02d7a026fc000618244687f0003c000f0003c000f0003c000c086bc000618cf830af3ac902adf0000c2e650320f279e1757c0001d9bbc000f000245dcf0003c000f00025dc730077c00070f920e6314a8a22020c20a360838006082970ca018f0c901082a0498302000001c0c086002d38000001010010a03283258000040800a002a40200507049c00228180000c08f39113e58300180010058b090a0c78c0010020020030002182010a0059b06041080809b171a14087061c480000c68d30a0380160850000040800000211020c380020008802000c4064808d002820f043018002080081e080810e3001f1c60001080dd89022820a0400188080130a3c000050e0c0010404286001840708189f6023804a181408006800052a0408110007100804300420451c060c08c04040190008208020003528251811a0420b0409683020200120040040c08100042808502026920c001810e0878004243000a0c402020538018242071a3818204043810a64200003808d06096091600400004c4011a288000008401020c004081109c002841a000c6831600000061400c08052060200001000820700000000e08c00149c28010406120010002001010e06a00030608c850a1038104000010a4c281302c0880200086141400008201800630001540c001000028104044800214200080828200045800e0c60106005810e14c82084c0120404106000c102080c580120c0000c000803e002870208194021008106183820210203070c2861a302822a1020102000020010181100c20b0404101047960000003121a000850038000000c083001022e3004004040858302300090008080080621d021810a0010283002c400040458a060088114cc002045050412000011e00304001c98510103af0400280080400000b0605084018704040000c1c080007c087020c18d0c0000600041800a0400108001961410084002008000000940000181020000008081800e280050634302000c01b004c2000a0030008200000c00000003400c0000280020408028003800208001620010f201440104040810250285) else (if j<2 then (0xd9346aff0001c02ef1443c000f0000c311f0003c000c0c7dd1baf00004e5c31a5c8cf14042bc000f0003c000000ce856c407c7c000f74ffc117f0003c0009023bc000f0000454a20ae3c00037b4fc000f0000c3fbf0003c000f0003c000512a0b3e3f00000640f0003c000449e99e7f11a83c000f0003c00091a4cb6e2015951d40f00028472f0003c0007586a4e80b66cf4322f00034ec3f0002c1c490c2f457ff0000836e977bcf51af0003c0009b95fc0002189551e5c1013c00047b403291e2b8c82157d172443ff08bec6b5647dbc00005a88068e708dbc00020c744516611030524717bc025b3d07b417a104b31dabf0001032bb128fc000c11e7c000f0003c000c100fc000f0003c000706f74ec420ca44d0511863c000e1ae3c000f00029433209263000f0003c000f0003c000c37ab16a8c10c7c000cc6dfc000a13a246c9b422bc000f0002853646768439ef0003c000bc83bc000f0003c000e49dfc000f0003c000f0001c56a93bf3c000f0003c0000058b4e42c49c9d96bb0c0fc000f00028595cd66ec203f000204d39073cc39980787c000a17c54419f13a8b289f00020025f0002135ef0001d2a8f0003c000f0003c000f00035578a194051d6f0003c000c5665529791107c000f0003c000f0001c081f0003c2fe50217c000f00010543437df842310ebd412465b7fc000f0001d5f393968c5b351b344058f000305a60c7a545aa976060652501334452d10d6537bc45dd0115f4a33c1f6318d846d5f00021e57f00025689f0003c00071119090553a07c0006139b863bf000315e0e364e80c661128860310bdbc000c351f4af925a728469f0002d5ddf0003c000f0003c000c37181376f00004cfba07d3c000f0003c000e24a2015740cd3c00004c4786a493b95c125c0907c000b66bd03e5204d112eff0000c116754f3c000f000184ccb1577ccb3f0003c00030607c000e130e8bc260b8fc00035b2bc00073ac68328f0001c4a0f000340c4f0003c0003c7114cf8b16c7c5de1023fc000f0001d6baf0001c8f93093bc000d004ccde63c7a1c614603364521a4887c0009026b42a320b1bc00061a2d332ee0dfd41aaf00010229413f371d4a3a0bc000b10944ae2f00030178f00000daaf0002c47bf00021a10f0003c000fcd26400851115b530f0003c0002176bc000ec8afc000acb83c000f0002452bf00034392d181fc000839872e2370d9bc000f0003c00064d935a11f0002423ce0ea546cff0003c000f0000c1eff0003c000f00014028f0003c000d0f489d57503cf0114417454105d4db58e6bf00021a6ac11e943cbf0000b65ee4abfc0007356ac4fff00018e4bc1257c31ac0aaddd58f0003034d9564281c0f0002cd7fd69ac93e52090d0b9e036820e62f0000442af0001c477f0003c000f0003c000f3a18f2f4f00024) else (0xc0b0f0003c0005141685948387612a4f0003c000d14cfc00030e4204b8f0003091dc0616135db2c8fc000157d3c000505c683caa0687c000010a3c00056023c0003cb77c0005248f0dd680be7c00090447c000f0003c0002124d4474f00029ef7d0b56b6e5bd5bf16b7806bc425cf00014e87b23ffc00010c3c0130a36ef05a5e144b03eff4a2c0443f0001d369f000241bbf000356058ce6fc0004499fc00082bbfc000f0003c000f000100d272f13c000f0003c000d059640ae81b6bc000a17ea0535002800ec65244695d3418704cb2f0003805b25883c00070560422543763c1aedc76e9028c4f624ae5f0003c000f0003c000f0003c00055963c000c00f3c00004c408604b1583414470e009a9960ba58ca3e0288936682443c000d1643c0003569483e9f00018eb47845a4657b16e7c000f0001402a7030cc19882bc9c414f000342d0f00000d068565115ed76a6bc00041b5c412180d1642a7504f692c3e487444c660cc6922074c5fc000f0003c0009117d4aeba1314115592bbbc00007a3681eaf0003c000f0003e630177f7c5eaf00038e6f81557c000f000283026cd3fc00022ffa12b35cd9fc000a148bc000f0000cc42f0002004fe56afc000f000006e985b3bc000f000282dc2114103ecf0000c643f0001818af00015e5e534a58231f00019363f0003f388f0003c000f0003c0008001806b2c562615916599ec342d5a10c2c9b06cfc0000069442967c7fac0bd10b47c000a797fc000c15d3431725bb3c00080a5582748c16a962cf0003c000e4abbc0003caae417b50cfbc0006381fc000f0003c000f000305caf0003c000f1bdbc000f0002c00f00f27422c40c13c32ecd9cc451a70d6f8c1d518e706964764e81d7719cf83c644c7d1eb24178b45e7f0003c000f00028209f684bc000f000352b7f0003c000f1ae7c00004a87c000dc78d4453f07f395871137bd5dc11743859af0002818073720c665b5a218307dce49c16f8176dc3d790d521acc4684ea5dcc01fd0e69d2dac040bb189d46d9010c8c1ebc1619d1e2039a89318c38de4476a462bde620581b0eb0c10f8f379909960169b006401ac8169fc000f0003c000d6b35090ef0003c01f51a0785a4f0003c00070f2201a8f00018d08355f740e501946b675a3900529080f1d0bffb14b9421b5d54fc000411f38ea62080583d8e04bcc1c7ad458c065a4a77067862e809682f0000c18f4084b92ff83928052aa0547c000f0001c4d4f0001831cb2467c000a15f309076160982f1cca0fc000e0e2b413220f3042b1f04e6c0df423c244e9c0f7a48fdccca6f2b96033c44489c793c000506a6ce9ff474dc0617055bc000e19a2490de099383c1f0003c000f00028374b11c7b331f187ac2d9f0003c000619217249610e38001957cb4250647efc000f00008638f0002f573c))) else (if j<4 then (0xf0003c000f000348eef00018259a2bdbc000e117656d5f00035a7bf0003c000f0003c00074ec7c000f0003c00000eff46ddf000299f684ac8345db0d7419e29079fc000a2b7bc000f0003c000234058c36f0003c000f0003c000f0003c00081671951fd1993c54f4c787c000e09fdc2989117bc000f67dfc000d3018c324f00030de2311d74cf3a3bb44381819074553b3b0bc000f1758116bf00014496b04a25a9ef0003c00000e09014a600ae86c532b73c0feb5b730567005b0c3bee0ab395fff000315af302bdc65d818d1c234219bbb6d8f0003c000e09cd19ecf0000c8efe0af41511d05301a72800884cf0bd5c15a738043a15ebf02a402c3d1bc7c000e0af0491660fd7c0001c856f5f120793864404a820ae8175e3c00000c519d79c4dc300eec5be340d180f4ff3614197edab4703f48af3f0003c63aa0e5c747cf0003c000414bd8eeaf00010655f0003c89df0002ddf33378c8047e6a7f52b620900d282f0003058561a23c913f00001ab59cbae85abf0003c000f0003c000355f2c5df018ac921eb029f5e8e50ade028d32406c05ff00038cc2f595ac384b0bf2c611f00014e4ef0000c27df34c7954480154f419712d2d66300f5bc000a4817c000b0420528ff0003812af0003c000f0003c000f33e49e8f1107235d6a4a72c5a894c709460a167fc000c19f242d2f0000c13685a5144d7f000352e2f0003c000f0002dd3c8cac6069486bbc8ba19019fc00093823c08cf0003f58b757a54c1183409826b10b9f42557188bc000f0003c0009126fc00014998c58cf0003c000e42735af0f000256b1f00020e1710c4c1d3d1cb5c51e670fdb45c2265a78e7c037bbc000803ffc000147a591fa00f68d5fe70e8c033af00038416f0001f343b1b1fc000f000040f1f163ac150f00009358f0002c219f0003c0009c5ca8c28b0f0195d164756c2caf0003c000f0003c000c1a2bc000f0003c000f00010afad131ef1fdf0002f26cf0003c000f0003c000d1bc3c000f0003c0005042e0261f0003c00093b07c0003010dc04a32b9e43b0705ffde1a90b07c000d022fc0007122bc00060a31c035703efc00050e4fc000f0003c000cc97dc216f0003c000c3957c000bcc21c47061934c6bff0003c5791150205be7cbdc84bb4163ec48d418b3c000f0001c0823d393c0007098f81a3c36cfc000f0003c0006c573c00081354861a70579c15373292722997973c0008cfcf9a0e51b87c0002014dc515f0003c000a116241f923b55c34675853c577f0002c044f000396a9f0003c000b028fc00001777c000199edb56720e3fc00040ad79276f361500249185a45bb2490b4914b19c046aa3683fc000f00024168f000371e0f000304bcf0000266cd0defc000a19ffc00086f8fc000f06f08546f00010d86f0000d2f6f000145a2f00001807857b3) else (if j<5 then (0x3c00036a2fc000f0003c000d148fc000f00000436b1b29042c8024605acf4dd4c235c4f4fc0005187d4da651b3bc000dd533c000001058420636e8c68c908bac489f0003c00086a3152c1f0003c000f0003c00063aa0c4df468b3021494c3431ce856a6c52561466859ec1593c000c0c3a0b8f51358c0bb4391f52e1f000141dfa18fbc000f000340b5f0003c000f0003c000f0003c000f3a8fc000f0003c000f0003c000f0003c000f0000c07cc0dc44c3a968b5c6ef9cc274d33a053bc000818f686ede1007c000877b7c000702b3c000f000355a1d14440c31712d4f2f1f0000c003408179b121098a92d201816006af00030bc34ce27c00085863c000f0003c000f0003c000719dbc000f0003c000859c7c00024d5fc00036c4fc000b4a23459bc040c4293417c276688cb8f45fe3f78c5644c0725c517f0002cebf04cdb84cfa08cdcb00f0003c00000fb9b1af44fc2441fa693fc000704ae006875ac195acf000306a8f0003069cf0000c11e314fbc00080f419eec0784fc000f0003c000f0003c000f000295d74242fc0008172c5e84249fe06d6f12c941fbf6940d6af26abbc000e240c802c808c944abe14c0850472be3c000f0001058a81793c000f00034500c00d815daecf8bc000f0003c000f0003c000f0003c00076abd7330f0001d4a94d406c2f560a74c615c1a8fc000f0003c21c714c88e3b21173c000f13d3c000b155a44f5f0003c000f0003c00000e73c000f0003c000f0003c000b059cc67ab02ebc0007cdfbde88a09f3c000f000031f9f0003c000717cfc00024907c000515738eeef0003c000f0003c000f00024ad6f0003449df00001d6c17a6773f9668c3424df0001908bf0003c0003120f8ca234bd70451f0002863cf0000464550d29558210d88426ff0002da31f0003c000416228699b3853c000f000135ceb1bd34277204b6cae1d082ec11ca2b838228f000045f43001cc0a661a42c2e0807bbc000f000356fa4d5d3c00013727939ec32c5c48084746c683f0003c3b367a08c07b1534c4365f00015327105cbc000f000345f663287c000f0001c5b563b3713e3533bd5637e150ac49a45b68c11010fe98612f0001c49ff00030afcd088e937cf476fc0008cc6e4b54f0003c000f000301d4e5b4686e64004905c6e179bc0002191d06ee40659c386f0003c00060aaa0547f0003c000d77dbc00036783c000558abc000f0000c4cef0002267c0dbe7c0008136c36ebd7781c039a1966001014779849ec1477c0005171c93655d479716df00024bc9859fbc00000fc9452cf0003c47ef000242bff0003cc00cc77f0513423d302a5fd39702ef7c7d34107a0ff3c0000db06823e41b83c000f000292c2912da037300c861a7ac1b47c00090655d316a35ca0e447103dcc3850a0bc000f0574846af0003c000f0003c000) else (0x9249fbc00010d63c000f0000c4ef2780fc000f0000400e49863c000f0001036ff0002a5cf61bdfc000f0003c0006027d00b2a12870cccc16dfc00051197c000f0003c000f0002c88e612e456fb6037bc000c58a58271f00018aea3011bc000c00eb1deb906648087f0003c000b0890812954c29c0b101193c000914e6089ef00000dfa70fb7c000f000301c87386d1aa0f00034660f000003f844f8bc0009118980d460dafc00063400c126f085fc000f000382e216ada8042f0003c00022bc432cfa0144d6b6c75f7c3695580a5aa121acd82d3f00014481f0003c000f0000880dd4263c000f0003c32df00014090713459ab731297c00081a6a509730d4840a8c39b2001a51b6fc0000097a86cc32bb5058751023c000f00013315775f092a78083604e5b0620d6cd4c82d02dbf798d5a8fc043e4466e7b879a9ce10f00387d14f58333c7a4984c9a47c5c316a008f96a5a196d0ea2f000271d2f0003c0007143bccee336f080bec4237c000a6a43c00020f570133008c3c000b2ff7c000b77a401c12d040da9d20437b5584066e83b9d10415a6663086c65461603d59f657bace9cf0003c000acb7fc000f00019669301d285cebc04bc000d977fc000b320f01e6f0000f535a3123b22af0003c00030177c00090f8284b3777f8c118a67ebc000f0001340ff000046be82c8785e1f0003416df0003c00084b71c2c514b1d0207e3605869d918ffc00041b41c06f90eefc10110343c000f67ed02081189b8e733057fc000817e18491679600305f0003109a73793441361584408df0003c000f0003c000f0003c000310d3c000f0003c000f000116e1f0001c4b7a04bb99653cbcc6ddc41a843502f0003c00073997c000f0003c000f0003c000f0003c000f00037306f02fdd1e075793c1dbf0002034ce0e8bc00080d13c000f389d4176f0003c00090e0fc000f0003c000f0003c6bdf000342bbf0000c46310a8ac1c3e33c8c9171c7ad4395c5a07c000c0c0655d5f0003c6ac92433c0004061dc24f53b258360fc02780261173e015ac6a914433b0f7d04ae313afc00020303c3196078bc00065805c482f01cfc000b0ac203aa71aedc09ebc5d68671e06feb51350eda06630134a40d7518bcc32561aad7173803e5828800c3704e1a4c9ad43f03ae7937dccfa71597577d18137769dc9a76ad79fc1d9c0f88f3a7b58c551dd25a2cd699e3679c418df9ce92bfc1bd5c221910180909102e14de95c5948e68a7b89054e3387843b190354f278231b4037560d8f1decd0df31a4dd0c414ada413410385a17ca8631a1264804b7dbd6c92230998cd9f36c104cd315b008677ccd104d6c4c92fc000155ee06d80777381f01693a8038f00000030f0003c000f000382af34a07c000bc18e8cc397444007af0001040703696044ef00024427f0001817df000)))) else (if j<9 then (if j<7 then (0xc4d463f0001447d501c44e6442f1a8e6d9159b45edf474bc000e335dc55220ecbc000f000081d5f00019ae2d4ccbc000f000303c414c8f829ff00020272f00000b3bb4e9682cdc068b4adb3caaa00e651af04685e3b310ef1637870e41511548292a479f86ae6691c88fecc77612db16ca2f2136168fc000f00030e26e30f3c194e23d48e4c1580052c622beef5eaf0000c0f8f0003c000a0b09936ef0003c000f000283adf0002da48f0003c000f0003c000f0003d691f6e5b865ef0003c00015a1900ddb1807d1f980eadc256f00028368f0003c000f00fb3335e005a0e5fa0d560d8af000245c4f0003c000338ea017ef000044874132fc00000537c0009015c82b3f000083c5c311a564021a9fc00040a13c2b6f000212a6f0003c000f000345a9f0001441a3058fc0000188fc000f000243cef0003c000f000356f2f0003c000f0002d9e78308d857ba0f0fc000f1867c000fd06fc00043897c0003cde174904199e817cf00020610d363fc000f535bc000f0003c000e5a6cc40cd0d6bc000c02e5168cc5ae57552f0001c017c1bebc000f0003c000d113e11a1c341e864b4c02bc000f00019b5f2388ec312009ab026741adc8280713ec058b10d27c000f0003c0009760bc000f000131678c76a41a4646220473f0003c00076bd684784152e92be823dcde31b6d81d26ff0003c000f0003c000b0747c000c5977c000306700599f0003c000bcae205ba032d6334eab73fc000f00018689f000141b2b13e20343c6bd9413fbd4dfc000f00038da230291438cf0002f1d94593fc000f03c8557af0003c000f3a0fc00080a1805e010797c000f0003c00060fc3c0008074c9685d12b5002d5158f046d00a2cb621156b7c000d5bd846d4607194dd54d4184ef0d18841e1830b02833ff0003c000f0003c000330f64027f0003c000f0003c000f0000d6f5f00030494f0003c000d23cfc000a584645780795bc000f000152c0c0c214573f0ffec53f83816425dd70431e7e8b9efc0005da7c0ea4f0001c1d25cdcdf5e5a16370cc060274c39f66947c00011a8a460680dfacad8f0000c20f901d7c000a06d546f3915db40966305ec00c0036cd666655dc9be9501f7c000f00004c498150496d92139001a0e0ddec4f7a0a295659307e181cee6b089ee9b694a0376f000382b4306c7c00044a03c000f0002c37df0003c000b68bbc000f00031ab2d385b811fb246916b5f0003c000f0000dac3b038293cc407fc1a2f10963c000d050fc11344ecfc66cf658c05ad21b4fc0001182ac597c3b1ed287a578b419204837c00081560c6a5e1b9e0421f0003c0004572fc000f00028405c5bb7c000305c3c000b069b021dfcb3845c1f0000d6983081040d3f0002862da32fc001c16acfc0008126300a1504efc000f0003c000f0003c000f0003c0001543dc07) else (if j<8 then (0x807a6b21af00025695f000344a6e15310630f0003c000f0003c000f0003c00090a87c000f0000d26b50cd942489780b8e3ef000081b8f000111b3e0ba0429af0003c00082c7e05eea0c26901255b7986ba4cd23c000a0643c000309a7c000b03bd56878cac275729182dd26e720298eb3c38f5d5a0f00020d87f00014389a15150cf7b1687c000f0003c000708478e76f0003c000119d7c0001d073c00032f2da08ef0003c000a174f4d8874cafc000d3bd4063764357c39b30769c415f00020ebb73567044bc0be0050734503c2ee505d3f292259845608000d2c4f1f0003c00051288da67f0003c000d156f450ff0003c000f0003c000f000083d1f00029deef0003c00000cd7c1fabc7f3c000f0000060df0003c000f000306b010e5af21ba01e04e0690fce9680530b3444cd032fc00091037c000c01a633e8924559670f0002d58fc3b584af7f0003c00002d0fc422f0003c000f0003c00063b3bc000f0003c00010183c000f00034c1cf00011ddaf0003c000f0002b20ff0003c000f0000029cf0001851fbc7aa44fef0003c000e775d957651b71ce151015bc0004063104d8f0003c000e1b8bc000f0003c0009c8a3c000413e4728a905cfc000b0b799334f0003c000000340048d0733c000f0003c000f0003c000f0000066f832f8449231407c000f00010447f000385f5f0003c00032b550485d08e8456f410ebc00004831ce7ab09b956e3e00a481b4709dac361b7792c59655aabf512b08de95e1ec51fc000f0003c000f0003c000e38f180bc60aa40581708290adfe0bebc000f000193e9f000046ec35957c000f000142dff0003c000f0001c15cf0003c000f0003c000356684391f00038e43e14d01e81b0a91d5d990153c00020f758109559cbc000824110e0c116d3c000500cbc000f0003c000f0003c000f039d8e1aa384985444cbf5c22260203c372f0000c4afe070ab2d1307728ced202cdc19f10dc3c000b036904fa71b21027b75be7c000106dbc000f00004dbdc4ebbc000f00013592119e40bf90d1b2b005f0003c000f0003ccff6160fc000f00010c53c3030350812b99443df0001465811a6fc000f0000c4e2a7806d69a67a2fc00040774867dd1732821eb0bfdb1d710e6105bcd0e2dc4baf000241617087f41ecb371f4246d4e65767430afb822776a3706ebc14ed423bc6a3b81cbf0002c06e8184fc000708aec3a8c33d80691352bbc48bf0003c000f0000c3c250bd1051ef0003891b00253c000b033bc000f00035be2d679a0ee00d39d0af5f0003c00011093c00081703c281f0003c000915b40550c13ca7170f07cd72fe805a980b4f00010add6050b5a26203d691f0f0003c00010a5c5ae11d97fc0007103b99e5311124cd6809fa4502112a745fb9094a35de015200290005b886282689fc000e1153c6f2237) else (0x143cff0001c24a8142fc000d33eb16cfa16b84e60316448646f0003444961a54807e16b73c00037a47c00070c9fc00070ae69ac7f00020642a4997c000f14dc02d433113c000e0d43c000f000275712cb7af6d0f0003c000679655e8617bcfc000f0003c000f00009e21608e0c149f3abbcc2656a03c0000c7e24508f000245fff0003c000f000202e1c15ad04c2f000371bef0003c000f0001cbfaf0003c00001213c5f79982e092bc04e3c0009c770820ce6747c0002382bc0001d6cfc0009174b0270f00029540f000246c0c2f05c53cf0003c000f000181e3f0003c460f0001065af0003c000f0003c000157f08040c0083c000f0003c000e396e8123407dfc000f0003c000f00000179f0003532df0003c000f0003c000f00010c10f0003c000f0003c00015b817303f0003c00082d17c000f0227c00020cc3c0004b77df39dc1427c1f5f00004624a10af9ac410ae986f8f186d80e272bf4b1bbd0cde1e8c90044441d07976559e2018c413111b944242816fcd2cbac71bc00095a0c83ba36b1442c4f00000c7af00018184e0819406670e9b442db0b93c000f0002c11a1249fc000f000275b1810c3c000575ebc000f0002331af000084e3f00018e88a14a1c2c7a0d5bc000f00013368f00038620655ff337ff00029d7bf0003c000f000182e540b23c5512c87f55f76180ac64e156dec33912f23c000f0003c000f06c3c000d1663c000118abd5b62123bc000f00020ea1e46650593f017bc0001032bc0006c7fcc6619146fc0004388340e8f00019e2c96b03c00081383c000b0d3fc00020ce3c60f710a7c000606de4341e6b05450ab2f1703515d40fc000e0c33c000f0002912d00d7c166b119accc8055b1bc000f0003c000f00030135f0003c00040c6d890281737c00090c604570f675bc0003198bf381601c016c800026d1da94e88fc10b1b2fc000f0002c3feac7b104fdf0001c2440760e46a9c39534eab00a1fc000c46e7c000f00038e1cf000240d6f00001374ccce219d250f37c000f0003c000f0003c000f00015586f0002841bdce03c00060fa00554f1b92891e60c18c33d20bec42ecf0003da87f00001eed1371385bd108800653f00034379f0003c000536e4c0dcd04ebc000e1537cad9909b5800bd24838656f47e383f141003bef546a230584c2da54924939df55b01c853ced8204f212a5e1233866de14a6f5f0019fb490af000243e1f00019596509e5c45780ab9cbfbf0003c000669fbc000f24ab5dd5f0003c000f00027676c0167836d1143083f7f0003c000bca10d211f0003c000c0f53c0007018bc0006199ada7f91794b48ff000000c5813cc44aaf2403c0004022b4520f0003c000f0000c24cc13c3c000b58424e1f90b618106115c6c4902571e463280fadc417f0a6f04b00049e0095f000356904c92bc0))) else (if j<10 then (0x2cc9007bc000f0003c0009483fc000017aec14730d0215a6069bfc00031323c000f0003c000f000300c750862041ea16263397b02135595c0edfc1a7f0003c000e0143c49c70f8fc00060266d9e9f0003c00030803c000900f68aecc36c7c00040d9f837af0003c000b37e48e5ef000100e401ab696beb110b415bf000302b2f0002d008b137745e9912b0c926f0003c000d13039e80f025fc00030366a6232074306a6019d3c000e0a0e31b8c048bc000002dc40f4d158a81cdf0387c000f0003c000377c513bfd156bc0006241b433c35ba1038df00019e64015e800fcf0003c4dae4cabc000f00034409f0003c000f000155d0f0003c00070d67c0008399d1581a75d985d9d047480ccf0003c000f5b5e93d5c3843c000b09d7c000c1463c000f0003b362f0003c000f0003dd77714704dbe93abed116d0e69c6e3f00008eefb11ba73983562101ab40e9d055e4075bc00050504c6df208b7035c5002ab1d863af1c30020cca0eb7f0003c000f0003c5eca054a32ecb03abc000f00008c4bf000284cdd095d1a0c407f7cd96e77c13307b0e3ad3cf90d3b529af00007c1cf0003c000f0001860eb2d1d423ff0002c6c351564167df19a7c000206fbc0002072ac66a4365fc000d0483c00096837c000703b7c000d1187108ef000100b62458fc000c175299d5e13058ee8f000082852024f410cf000300c2f00011ed891a4bc0003d5b643eaf0003c0008013b00aba0fd3cbc04388674e961723c000a0c8319b5f00020698c116bc000f0000d64b34840cea73192bc000f0003c000f0000c56ec0cb0064cb139c32d800e50d186a04f98e7d9084fc000f0003c000b1b1144d9f15f615050596e06e830262c2f2f0002d5a2d01b3c0003247cc50661a7dd333102b7c000f00014ad700b6bc000d083bc0003100940f6f0003c0002021bc000d03dfc000b014ab26d349aa96d3f0003045b92487d32c71bed0600e07fad9adf00010289a651d816ba0d4d84be706264de89052fc6c2f00028183c197340e3f000240185051bc000a0583c000f0003c000215a7c00002472c5a067b3e8686232daf412f0003c000f0003c000fd52bc000a481fc000c39154021f0002c064123e3c000f0003c000f00018186917e7c0002155fc00063934fe21f0000018be67f3c000f0000c0e98584e4629f00038119e14b5b2f834b3511adf00024e0e157d7c000f0003c00032b93c000f0001f305f00019657e2f28c19e758c3c000367f7c0001995c9583d125c02ce30e23c000c07b7c000332dfc000f00004154f0127c000017f40912f0003c000d3bdec357a19ed8dcabcf9fc00051a3ecb3ff0001846bf0000cde7f000306b6c6b6fc000f0003007653a174155e0fe60104523dbc000f44f793e8f00000ae910763c000f109b569ef00015e0056b1bc000f00008d03f0) else (if j<11 then (0xdabc00030a8256e6b227d0514d4a67c000f0003c000f000046ea00f99c0aa72bd3450df0003c000108434ed3f0002018ef0003c000f000083acf00004e53f0003c000f0003c000801c94348f00014527f0002c4ed349ecc9085116582f790bb400c1f0003c000f175dc5e8f0003c000f0003c000b69970ed0f0003428ef0003c000bd4dad68d01b7ac14f577f3c000c4ec315fdf0003c00050cefc000023f3425af0003c000f0003c000f0002c60cd0273c000a0637c00092f1d51f7f00038326c046fc00010ff4091864ebe0488f0002c5685562bc0000596bc0000140fc000f0003455ff0003c000f00018d0420ed1dacbf1bf0b2f200517c000f0003c000005d7c000f0003c000f0003c000e1312666d50b77c0003185fc000f0000c3a1f0003c000c104bc000d1047c00047aafc000f0000f56e61b4a44a720d2f0ce2a75fdf2e4309805df7811a046840674e003f74c848ee21741606f9900ed4347903ac95c5b49cfd131f00019dcbf000082547373a432380523960930e95c32a73aebcd83f0002052616dcbc000f000242cfd10efc000f00029206f0003c000f00000486f0003c000f00039ed7c55e506c1a676fde3064aa6819df00011298b03c3c000a0003c00000aa186b1f0003c000f0001807787913c000f0003c00034b33c000f0003c000f0003c000f0003c1c515ab9f515f000384dc41714457ef000045b0a598bc00010db3401b82c21404df0003c000f00010e18f0002168af00000549f0003c000d1137c5b8d3aa7c000f000043bce03eaddd941293c000f0003c000f0003c000d30b84e0df000142fdf0003c000f0003c000bd053c00080013827ab0223c00012d1b4456a3513032ff0003c0006077bc000f0003c000a0e77c000654f50bfcc03b14592f000104ec546d4d2f0539e685c95d3a945b2532d2d9de41ad300020587bc000f0002b5258064cd9f8812f64b410d51bc000e01af846ce249483d9f0001c245f0002c00576fa38191c06ebc0008089b4572c19c8ceebf17f0c61d867e7c0005102bc000d10e64164f000082cb108abc000f00031aa5d0a53c000400bfc000f0003c000178df0e13159fdf5e3547b3c000512ff5e95f00030140659aac538f0003c0008097cc47f4c82b0159f0003c00016a9a41f2f000082d6310ba0e8df0bce953f9119fc000f0003c00060f71831e17a43c62ee04480afef0003503e32a6fc000100dccb3d8735a8eac0c6c5c083f0003c000f0003c000a0a3fc000d2bc26607309470df030ef7c00041a01cb44f0003d697f0002c6c680eb88437010bf4045f17618e28f00004182f0003c000a9a5d15eff0003c000f0003c000d7ba3b557512c7c0006c7d7c000a1a370291f000300d8b69bbc000f0002029ed040bc00073007c23d8193fc000b0babc00010325819ab04013314f00010) else (0x3178d85c3f000303b5b0a6594d820783c247f0003c0003c93143dbf00020e75f0003c00027bbbc69ed09a3c000f0000937120057c0006065e848f50e8143150)))))
def genData10 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x49484746444241403e3c3b3a3938373635344925211d1911090500f8f0ece8e4e0dcd8d4d1249443e3c3b3a31282625241b1918170d0c0b0a090807592104f0e4dcd8b4988c807c6454484434282418140805648413c3937362d2623201f191512110d0a0906050201591cecdcd4b09488807860504840302820181008014473b37352c2522201e181412100c0a0806040200512104f0e4dcd8b4988c807c64544844342824181408056473b37352c2522201e181412100c0a0806040200511cecdcd4b09488807860504840302820181008014473b37352c2522201e181412100c0a0806040200512d21150d04fcf4f0e4dcd8b4a473d3b373519291cc8bcb0a49c94888078b4b453f3d3c332a27261c1a190e0d0a094128f4ecc8a49c94686038302820d2f292216140e0c060424f4dc9c8068584838281808b46403a383635342d2623201f191512110d0a09060502015d1900e8e0d8d4d0b09488807860504840302820181008017463b37352b24211f1e1d181412100c0a0806040200552104e8e4dcd8b4908c807c5c5448442c24201c18140805747443e3a37352c2422201e171412100b090807060402005d1d08ece0dcd4b094848078604c48402c282014100c0801747413b3936352c25221f1e181411100c090805040201005c0039b375b4831aaed2c3a9a26ca432199f01d89cb1b399217696314b91c0ec8c10918620328030018003ff61ffd83ff30ffc43fe61ff983fe50ff8c7fe30ff883fe10ff587fd60ff543fd31ff4c3fd20ff443fc61ff183fc50ff0c7fc30ff083fc10fdc43f510)
def genIndex10 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (0x5dd31dca1efc00001ec30524367bc001e00084c978003c001e280f4720074ac45164c5f000287e18192c19cd017712427ccc8810f0007800202d901cee14cf80011c3a223bf000780014203e22bc11150063c00069d9c0e11097fc0010884f00078003c393e000524ef8003c3e1e0000032f80008287e0000c3eb068103e619dbf00058382c11bc537e022ae9964c244a787087eb82fc0014020d0e5b20dfc2bd609a0148104e189e6867ef0007800240c88032c0c3f83bfc001e000704578003c001e23ff00078003c000487aa00bf009fc000c95f90ac326d7c001e000b43cf80007d59804e4d3ea8487c001e000f000101cf8d39428d227b4802ad39f16adf0006005b8210a4f0f0007b18fc001b959f00041693c001e000900080a0ec0bebe99f000780000231e0009035ae81b02374442b14e181c3c0000e7cf000587a7c0006dbd002c4070f4b55e000914278000d3be45a7a27df9a33c001e00080d6f8001c27de000f00078003b37b42a40528f8003c0018c7ed4a1882cfc0012db710ad2e753c001012c4cdbf8000928ce2307527cbaa7c001a151f0003845fc00081caf000706de44cbe000c0c0b8a5bc0004c4fd0abf800113d9e00010d878003c001e000f000780034453e000f000709a183a1cdd8a0a07800104a66031f095f8003c2a061d19cf3a26d805244202f0002a4c19553e000f000183e3c00080e4f000102dfc0000498b116688671bd729d0f0003b1e70cc1e000e065704b7c001e000f00078003c0014206249e1082fc0012071107e78707c00065a930ae405cec420c15ff000509b58495e00050b8a2a59c037ed99f0000834484110979530dd89ed9438a044e52978001427fe99bf0bb10733c001e000108af80028180a10286e2605870133cdc2f0002e20680ab2196814a901d903c9003df50578787c00081f9c4b28b50d54a141c7f000331898191e000834178003c001e0e6f00078003f4e8818bd2f378001c3b3406012cda81ab014640a8f0007800093dbe0000036f8003c000645810c4b9a22f37de0008c22c83daca761c5340e5410308188010004195280c0055a4400b04019000600c1b043460b022018408040130210e801cac40a086a0b0060400224141030200007027c4000a1c401080000a6a0c10102000801634731001c38a1a00202220000104042040404697020420f046c2960840203884000500504800828083081468002045002c0c105041010132141800a04780000c88102342000a000841d0408c043c00802000050e005980628297080028100040800830880004801700100000010d86280410012300830200102000800106044010610580060008106040012618401002400e02043010a046180a00280040c0810048082000440a021458a0060082180c0000008c8300040002204205000c182) else (0x79c4a52046f0006885f89fc2061910678003c00022763012687ee8ac5e00090b4f184d80a5623ef00028026848fe000743878003c001e000f00078000011e400660b6c8a8581a525bdf00078001186fe000f00068127d3b5e000c32568661c2c5e000f00038010c1bbca0df0007062b50a22195c10f101ebc001e000810b408ab9ab7e00086df7825d02fe29512011b8a6bc000c27880f4215d64bd7e06ef0002868e9c7706563452780008c2c2240474e7880e92b44043f0000086bc001e000e6dc585f3d52fe000f000784bf04dcba17f00028989f0bac1eb622d78003b4ebe000f00078003c001e00022d7203a51427201cf000483c3c001e00040a919943039b00f7f000200a70156266d8048f8003c001e0006027f8003c001e00036ecd216fc001ba4aa0edb0257c000045bf000380508073e000f0000838600a7e000f0007800113c6e072f000680b111aba0c4874bae2024473e000cd0fc354780f28a20408a6a76ea548a456954130208b106199cfd3b482800512e0ff1140f80010251669f80487800380260125f000782ee80b2e109f0daf800398fee124c0ccf80014bc40aadf00071723c001c1634b5278003c001e000f000788db11c5a04b0c3740a7fc001e00040a6f8003847be000f324ba9a7c001e000609ed09458cffe000b04278003c001811d324fcb83052b700c3f000322c3c001e0003c6f8968b3248e03ef4cc81a8002df041800de083f89429c04d1126a68f4c23f0214d01b9112bc3a9463cd0f6d6143c001c05bb10ad003f0035e000f00028097c001e000f0007800081605a18f0000e4c7c4b1e000832bf800248afe000d41a880ebc001e00024f278001b515e0006148b1250f229e000f00068a830bd5c23cf0007800308abe000d14ba83a2c4c161e7f000293e549ebe000f00078002935be000f000780008448a615f000689c94113e0005d3e780038227a98c66cdc81a643d5266946db78003c001e27552d6f80025bcde000fd399893bc391a69bf00078003c00009b7b02ea93f7c00069abf09a709661bb5e000f0003193fc000e58af000009b3c0005a7a5078f8001431b299854ec6876a954479da105092a6d0111f87fa14dc86b10273e0005c6af8003c001c159d08e78003c001c661f00008445851181d7f00018153009041dcf000780004325e000f047739495ca1e000f4cf081d78255e00056a2f8003c001e00066c628713c001d9154004500d75c27e0000069d924882f6c945f000286bbc001e000605e78000846a3a3e8407c3a8219ea4ded103f6804989e9a103f0007835fc0014446f000586e35ab508558d02f8002418be000962ec26bbc0004294f0007800058b7e00022a8726e35422498af0005884fc001e936d6326b78c44a841d3f071f800102e82036a1564674f423461bb11547800013e0b9)) else (if j<3 then (0xff0005051fc001e000603b903e50221806392e7f84b9c373e00080579e717c001e000dcdcf8003c001e00030f778003c001e00010e34836fc0016e12a043e895d83cac491f000189e9c49ef878f24c80200041361f1f0007025813c5e000f0003683b0310660ac0a15854dc87fe000a469f8003c001e000f0007030b428be000524d280cc8d3bc82b80715868a920be000c094f800100dfe000f0001842fc001e000f000780030215213050109635ac3e862453cbef80038291417af00078003c001e000f14e9848e98ab8497f00078003c0002179f000436efc000211e30dee2807c001e000a323f80028245e000f0007800003be416abc6e2001f4363ed30f00019278f363c178f02878003c001e000f00078003c0015948b50d3833dc9f46190f000767bfc001e0006723f3837c001e000f000696d65335e000f00078003c000426ab12a8ba614224400df0a7e35dfc0003a40f00078003c00120e7f000783efc001e0006083a06a0daea827970ffd970adce7e00070b5f8003c001e5c7f000780038335e000f00078002706fe000f0007800252ef59ba20c98358c338ca0a9f000088bd9559e000f00020075c1e409753c1a90910434ae232f00078003c001e000d0ff5002d045de00066bcb834352c66011e116d8103c001e000f000308e385046241d2bb78000547660bdf00060189d8b85a417131f8003c1dd4a02f0007543d083901a7227e0363784e081c5329c53595813b4116206a6b76e8431e000a2a2daa7294c1e49cf64a4a86fc000a191b30a1811cf54be000f0000331bc001e0008151984c7c001e0006106b8923c00011a1cc24a2637c001e000020de1667c001e000509078000c2a9e00002fca022d8b7c403070adf80564835e000554af8000c03de0000cd978000401c4d9ff000584dfc0010539f314a243fc001e000f0004887fc001e000dd35f8001c2d18204f0154069880afe0002156f8003c14de000b0cf206afc0004e14c11031aa9415be09ce12130977c001e000f00020592c44b0298f0005024ccb47e00070bed860812f1a21b70b2b267c050ae14a40ee906765bc5e155b0fae827883ef0269700c9020f03c5ea3c21535a1fcc1364de4eca4c063f924d481f90aeeba8848d9e000f1471b1c08068a2a5f00000999594886a6f000780004283e000122cf1707c001e0000506780019a0ae086f00078003c001e000101c6e4fa41b9e000f00078003c000c274900ff80015c2b58d86132405dfc001e0000d24f8a2bc001e000f00078000419de000f00020a4e8463e000f0001e50e51ea4d9af0004088d1c35e0009427f80030159e00020a7606dbc00120c7f00068987c0017882f00078001016ca20e911bf8003c001e000fd0f78aa71533e000f00078002824dca88d076f8002f0c7e170c350f8001802180cc3017983) else (if j<4 then (0x18d525985043f5a107c000406c05501a877451fe5d9f530a83b39342014c6d1fc81335b79cdb5f04650701553cc45ca27fc98a9c926b9e8f000004cef0f881a130d7c88d389e30a7336f2b835b50bb82059cdffb0d7ad4746ac101db17ebc000598180e7c2a77b3ca26a8f000185badc91e000d093f34f21265e000f00020807c001e000f0006282fd5460862e34c800b7c0002212f000102bbc001e0007d564613fc000e0bae319504640277003cf00078877c001ad3d0065f4ab583c7e0008728a082b118de000e08356290da6de000f0007b93f4306053d1caf78003441e453abd4cb07ebc000e61a3d07c0925040f29c3d4f52041603182d8af00078003108de000904c5694c432e2e9dc6f678002891e21de6060a03afc0012042d4c37088710b9e000f0d4f8001f3bc805ef000007cbc001a211f00078003c00160282034289cfd382852590ec78003c001a13cf00079797c001e00044d078003c000c2abf00078003c001e000729e78003c001e0002509780018289e00090635028bc000e05c214378002817fe000f000780014497e000f00078003c001e00034578357ec2c1e00070cff80039c39e0002113f8003c001e000f0004075a530fe000f0001099e0045e0009d21f1694c48739dc10b3700ff41b4d9c0563d306164c04e685f0005e799021ce9c430fe7800142ebe000f0007800274bd4271a0ca686fd8056ee0ab6585a7ac09f101aaf00011763b071e000733378003c001e000f00078003c00182332079f8000b496c5d0f487206e901fb41b4f000610644d458989266a983ab831de000f4ddf166bc0000479f00078000c3cde5a8f000780004d3de00013188a9f3c001e0000d083e95104a1a9c2c13f60356417ce41ea033e88e8d0c7e000e15178003548e060be0b3f651344b9e00020d24029ec50e010d207ae926d1883e000210e3219544ac019bf0007800133c3e0004066f8003c000c27d00b95385971c0c100f00078002b4bfe000e14f007be4ab4c95cf0007800242086180003ef905dc0ccc0b22d337631044dfa003c020ee4c25c376e960d4c78003c000e64800df78003c00141b2f00078003c001a864f00038a32da8e40e53052f800044b50695f00078003c00101564887ea6f2092a0536405a083d3c001613aa2db4825300f0226bf0005061004ef494745324d684c0a3e0562750b691bc0012146f0002027d026ab2a330a5f800200f7edac720ef8000000be000f00078003c00040b8227be02e7c000cdeaf00078003f4cf0074f00078003c001e000a086291be0001e000f0005a922c3abe000fd2678003c00039ee86e089a60527a402650497800001f5e000d05a904dbdb43e0003155481ffc3ece0aa10f0780028163e2a7f0007b8f2706c29a6c300f8003c000aa4426e1f8003c001e000b12df80034367994) else (0xe13fc8032b2f6ad26f0c3280088499608570fe9aaa39359e000c220da250048de000006c78000c265e000f0007897b451619b8f0001aa87c00020d9e03e305fbc001e000a0257816a04f9e000106fe0898010244f230a4f080))))
def genData11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def genIndex11 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x3c03c03c03c03064186435306c3fc03c0006b51a6c7c00590c51d66428763d36dbbc0083a53bc56127c0293d508f01644147c00ea9b43c0104e0334593c69afc03c0371f103c03c00dcbc03816c5fc01a2ad57c0155db57c03c019e7c03c03c03c0199fc03c011511d7c00442027c01113c1234944942fc03c02506f0bc03a8ec1c0075419a4c23c02c63744367c0012114b58bc03c03c02f2d08ff2455b5dcd1e983c03c03c01968b10d4fb3bc030aadc035e60f40040d845c1bc00dc680892fc009d34c6b53d62de3c03c03c03c00a0d82041850800004a10c504b0484d6101)
def generatedLevels : Nat → Packing
  | 3 => (7,8,7,0,0,6,0,genData3)
  | 4 => (87,7,7,0,0,10,0,genData4)
  | 5 => (195,6,7,0,0,13,0,genData5)
  | 6 => (462,5,7,0,0,15,0,genData6)
  | 7 => (1061,4,7,0,0,17,0,genData7)
  | 8 => (1789,3,7,0,0,18,0,genData8)
  | 9 => (686,2,7,0,0,17,0,genData9)
  | 10 => (27,1,7,0,0,12,0,genData10)
  | 11 => (1,0,7,0,0,0,0,genData11)
  | _ => emptyPacking
def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 2 13 2 8 3 1 genIndex4
  | 5 => lookupWord 37 224 5 13 7 2 genIndex5
  | 6 => lookupWord 86 521 6 15 8 3 genIndex6
  | 7 => lookupWord 227 1359 6 16 9 3 genIndex7
  | 8 => lookupWord 485 2911 7 18 11 3 genIndex8
  | 9 => lookupWord 788 4728 7 18 11 3 genIndex9
  | 10 => lookupWord 307 1843 7 17 10 3 genIndex10
  | 11 => lookupWord 23 138 6 12 5 3 genIndex11
  | _ => fun _ => none
def qF_ : Forest := ⟨507,11,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[], [83], [48,65,101], [48,65,99,101], [80,65,83,101], [80,65,99], [96], [96,83]],generatedLevels,generatedIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP3_0 : block qF_ 3 0 7 = true := by
  apply cellsBlock (ar := 4) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB3 : block qF_ 3 0 7 = true := genP3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP4_0 : block qF_ 4 0 87 = true := by
  apply cellsBlock (ar := 5) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB4 : block qF_ 4 0 87 = true := genP4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_0 : block qF_ 5 0 6 = true := by
  apply cellsBlock (ar := 4) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_6 : block qF_ 5 6 21 = true := by
  apply cellsBlock (ar := 5) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_27 : block qF_ 5 27 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_123 : block qF_ 5 123 72 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB5 : block qF_ 5 0 195 = true := (@block_merge qF_ 5 0 27 168 (@block_merge qF_ 5 0 6 21 genP5_0 genP5_6) (@block_merge qF_ 5 27 96 72 genP5_27 genP5_123))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_0 : block qF_ 6 0 82 = true := by
  apply cellsBlock (ar := 5) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_82 : block qF_ 6 82 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_178 : block qF_ 6 178 19 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_197 : block qF_ 6 197 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_293 : block qF_ 6 293 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_389 : block qF_ 6 389 73 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB6 : block qF_ 6 0 462 = true := (@block_merge qF_ 6 0 197 265 (@block_merge qF_ 6 0 82 115 genP6_0 (@block_merge qF_ 6 82 96 19 genP6_82 genP6_178)) (@block_merge qF_ 6 197 96 169 genP6_197 (@block_merge qF_ 6 293 96 73 genP6_293 genP6_389)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_0 : block qF_ 7 0 5 = true := by
  apply cellsBlock (ar := 5) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_5 : block qF_ 7 5 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_101 : block qF_ 7 101 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_197 : block qF_ 7 197 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_293 : block qF_ 7 293 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_389 : block qF_ 7 389 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_485 : block qF_ 7 485 6 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_491 : block qF_ 7 491 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_587 : block qF_ 7 587 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_683 : block qF_ 7 683 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_779 : block qF_ 7 779 65 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_844 : block qF_ 7 844 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_940 : block qF_ 7 940 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1036 : block qF_ 7 1036 25 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB7 : block qF_ 7 0 1061 = true := (@block_merge qF_ 7 0 491 570 (@block_merge qF_ 7 0 197 294 (@block_merge qF_ 7 0 5 192 genP7_0 (@block_merge qF_ 7 5 96 96 genP7_5 genP7_101)) (@block_merge qF_ 7 197 192 102 (@block_merge qF_ 7 197 96 96 genP7_197 genP7_293) (@block_merge qF_ 7 389 96 6 genP7_389 genP7_485))) (@block_merge qF_ 7 491 288 282 (@block_merge qF_ 7 491 96 192 genP7_491 (@block_merge qF_ 7 587 96 96 genP7_587 genP7_683)) (@block_merge qF_ 7 779 161 121 (@block_merge qF_ 7 779 65 96 genP7_779 genP7_844) (@block_merge qF_ 7 940 96 25 genP7_940 genP7_1036))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_0 : block qF_ 8 0 17 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_17 : block qF_ 8 17 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_113 : block qF_ 8 113 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_209 : block qF_ 8 209 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_305 : block qF_ 8 305 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_401 : block qF_ 8 401 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_497 : block qF_ 8 497 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_593 : block qF_ 8 593 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_689 : block qF_ 8 689 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_785 : block qF_ 8 785 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_881 : block qF_ 8 881 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_977 : block qF_ 8 977 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1073 : block qF_ 8 1073 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1169 : block qF_ 8 1169 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1265 : block qF_ 8 1265 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1361 : block qF_ 8 1361 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1457 : block qF_ 8 1457 8 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1465 : block qF_ 8 1465 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1561 : block qF_ 8 1561 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1657 : block qF_ 8 1657 86 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1743 : block qF_ 8 1743 46 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB8 : block qF_ 8 0 1789 = true := (@block_merge qF_ 8 0 881 908 (@block_merge qF_ 8 0 401 480 (@block_merge qF_ 8 0 113 288 (@block_merge qF_ 8 0 17 96 genP8_0 genP8_17) (@block_merge qF_ 8 113 96 192 genP8_113 (@block_merge qF_ 8 209 96 96 genP8_209 genP8_305))) (@block_merge qF_ 8 401 192 288 (@block_merge qF_ 8 401 96 96 genP8_401 genP8_497) (@block_merge qF_ 8 593 96 192 genP8_593 (@block_merge qF_ 8 689 96 96 genP8_689 genP8_785)))) (@block_merge qF_ 8 881 480 428 (@block_merge qF_ 8 881 192 288 (@block_merge qF_ 8 881 96 96 genP8_881 genP8_977) (@block_merge qF_ 8 1073 96 192 genP8_1073 (@block_merge qF_ 8 1169 96 96 genP8_1169 genP8_1265))) (@block_merge qF_ 8 1361 200 228 (@block_merge qF_ 8 1361 96 104 genP8_1361 (@block_merge qF_ 8 1457 8 96 genP8_1457 genP8_1465)) (@block_merge qF_ 8 1561 96 132 genP8_1561 (@block_merge qF_ 8 1657 86 46 genP8_1657 genP8_1743)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_0 : block qF_ 9 0 1 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_1 : block qF_ 9 1 78 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_79 : block qF_ 9 79 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_175 : block qF_ 9 175 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_271 : block qF_ 9 271 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_367 : block qF_ 9 367 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_463 : block qF_ 9 463 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_559 : block qF_ 9 559 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_655 : block qF_ 9 655 6 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_661 : block qF_ 9 661 25 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB9 : block qF_ 9 0 686 = true := (@block_merge qF_ 9 0 367 319 (@block_merge qF_ 9 0 79 288 (@block_merge qF_ 9 0 1 78 genP9_0 genP9_1) (@block_merge qF_ 9 79 96 192 genP9_79 (@block_merge qF_ 9 175 96 96 genP9_175 genP9_271))) (@block_merge qF_ 9 367 192 127 (@block_merge qF_ 9 367 96 96 genP9_367 genP9_463) (@block_merge qF_ 9 559 96 31 genP9_559 (@block_merge qF_ 9 655 6 25 genP9_655 genP9_661))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_0 : block qF_ 10 0 2 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_2 : block qF_ 10 2 25 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB10 : block qF_ 10 0 27 = true := (@block_merge qF_ 10 0 2 25 genP10_0 genP10_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP11_0 : block qF_ 11 0 1 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB11 : block qF_ 11 0 1 = true := genP11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genTables : checkedTables qF_ 11 := by
  intro k hk
  interval_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact genB3
  · exact genB4
  · exact genB5
  · exact genB6
  · exact genB7
  · exact genB8
  · exact genB9
  · exact genB10
  · exact genB11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genGeometry : graphValid qF_ (boundsBefore generatedKnown) = true := by
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowGenerated : Lower true (varsX 507) (qG_ 507) 12 :=
  lower_forest (g := qF_) (i := 0) (hints := 51)
    (before_sound generatedKnown generatedPrior) genGeometry genTables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_55659.ForestCore
namespace PEqualNP.Outside.L_meta_55659
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0,3,1,3,0,4,1,4,0,5,1,5,2,5,3,5,0,6,2,6,3,6,4,6,5,6,0,7,1,7,2,7,3,7,4,7,5,7,6,7] : List ℕ).length / 2,(List.ofFn x).getD (([0,3,1,3,0,4,1,4,0,5,1,5,2,5,3,5,0,6,2,6,3,6,4,6,5,6,0,7,1,7,2,7,3,7,4,7,5,7,6,7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0,3,1,3,0,4,1,4,0,5,1,5,2,5,3,5,0,6,2,6,3,6,4,6,5,6,0,7,1,7,2,7,3,7,4,7,5,7,6,7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0,1,2,3,4,5,6,7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffffffffffffffffffefffffffffffffffafffefffeeeeeee00fffffffffffffffffffffffffffffffefffffffffffffffafffefffeeeeeee00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 2 zero,32,36)]) (by decide +kernel) (qP_ _ (by decide +kernel))
    (qP_ _ (by decide +kernel)) lowGenerated
  have count : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [count] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def sampleInput (r : Row) (i : Fin 8) : Bool := bit r (inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampledInput (r : Row) : List.ofFn (sampleInput r) = roots.map (bit r) := by
  rw [roots, List.map_ofFn]
  rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampleCorrect : ∀ r : Row, bit r codedGraph = graph (sampleInput r) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def signedNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem binaryLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    13 ≤ C.gates.countP (fun g => !signedNot g) := by
  have goalEq : (execute C.gates roots).getD C.output zero = codedGraph := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInput]
    exact (comp (sampleInput r)).trans (sampleCorrect r).symm
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [goalEq] at out
  unfold ForestCore.Repr at out
  have pg : bit 0 codedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  have properGoal : proper codedGraph := by unfold proper; decide +kernel
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates roots fit (by simp) properGoal
    (out.resolve_right (fun h => h properGoal))
  change k ≤ C.gates.countP (fun g => !signedNot g) at hk
  rw [nrm_map (by decide +kernel : roots.all plainWord = true)] at sub
  have step := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have ready : supply true (roots.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, paid⟩ := contraction (observe_proper properGoal) step _ Reach.start ready
  have lower := wholeBound q bank reach hit
  omega
def upperGates : List Gate := [⟨.or, [7,5]⟩, ⟨.or, [3,2]⟩, ⟨.or, [9,0]⟩, ⟨.or, [5,4]⟩, ⟨.or, [11,3]⟩, ⟨.or, [6,1]⟩, ⟨.or, [13,0]⟩, ⟨.or, [14,7]⟩, ⟨.or, [14,10]⟩, ⟨.and, [12,15]⟩, ⟨.and, [16,8]⟩, ⟨.and, [10,6]⟩, ⟨.or, [17,18]⟩, ⟨.or, [20,19]⟩]
theorem upper_shape : ∀ g ∈ upperGates,(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates,21⟩ (List.ofFn x) = graph x := by
  decide +kernel
end PEqualNP.Outside.L_meta_55659
open PEqualNP.Outside.L_meta_55659 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_55659 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, hg, eq⟩ := neg
    have fan : FanInTwo ⟨gs, o⟩ := fun t ht => ⟨(legal t ht).1,(legal t ht).2⟩
    have low := binaryLower ⟨gs, o⟩ fan computes
    change 13 ≤ gs.countP (fun g => !signedNot g) at low
    have lt : gs.countP (fun g => !signedNot g) < gs.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hg, by simp [eq, signedNot]⟩
    refine ⟨upperGates,21, upper_shape, ?_, upper_sem⟩
    change 14 ≤ gs.length
    omega
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g, hg, eq⟩)), cap⟩
