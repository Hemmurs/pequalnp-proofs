import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_34788.Contraction
abbrev Forest := Nat → Nat × Nat
def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)
def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)
def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start
theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)
theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩
abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
abbrev CutCheck := RowState → Bool
def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token
def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])
def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws
abbrev Bound := Nat × List Word × Nat × Word
def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask
def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words
def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))
def WordBuilds (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws
def Lower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length
theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp
def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j
def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask
def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b
variable {mask : Nat} {target : Word}
def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w
def Masked (mask word : Nat) : Prop := word &&& mask = word
theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]
theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩
theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]
theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]
def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w
theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd
theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h
theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]
theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h
theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb
theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _
theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]
theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h
variable {rows : Nat}
def fullMask (rows : Nat) : Nat := 2 ^ rows - 1
theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl
theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))
abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m
def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m
theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]
theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]
theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..
theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]
theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp
theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]
def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))
theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]
abbrev PointWire (rows : Nat) := Fin rows → Bool
def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat
def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val
theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]
theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))
theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]
theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]
theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq
theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i
theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)
theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]
namespace PackedRect
def full : ℕ := 22300745198530623141535718272648361505980415
def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')
def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)
end PackedRect
abbrev Witness := Word × Nat × Nat
def witnessWord (w : Witness) : Word := w.1
def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)
def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes
def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal
abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep
def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right
def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true
theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]
theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩
theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩
theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩
theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih
def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w
theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]
theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩
theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)
def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0
theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩
theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]
theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩
theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]
theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]
def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word
theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl
def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont
theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]
abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink
def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws
theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢
theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail
abbrev DagSample := Nat × Nat
abbrev DagSignals := Word × Word
abbrev DagCounts := Word × Word × Word
def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use
theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]
def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2
def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))
def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use
theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl
def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)
abbrev DagTagged := Word × DagSignals
def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0
def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token
def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank
def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank
def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)
theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩
theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]
theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]
theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h
theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd
theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)
def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w
abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)
def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray
def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal
def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)
theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok
theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩
def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices
theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)
def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)
def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)
theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0
theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp
theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c
theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0
def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]
theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp
theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]
theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]
theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]
theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]
def GateWordMono (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b)
def WordBuildsMono (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWordMono mask roots w ∧ WordBuildsMono mask (w :: roots) ws
def MonoLower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuildsMono mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length
theorem gateMonoOfAvailable {mask : Nat} {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWordMono mask bank w :=
  ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩
def maskFlatF (mask word : Word) : Bool :=
  dagForceWord (word &&& mask) (fun v => v == 0 || v == mask)
theorem maskFlatF_eq (mask word : Word) : maskFlatF mask word = maskFlat mask word := by
  simp [maskFlatF, maskFlat, dagForceWordEq]
def flatCountF (mask : Word) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlatF mask word then count + 1 else count) words
theorem flatCountF_eq (mask : Word) (words : List Word) : flatCountF mask words = flatCount mask words := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    change (if maskFlatF mask w then flatCountF mask ws + 1 else flatCountF mask ws) =
      (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws)
    rw [maskFlatF_eq, ih]
def dagBoundHeaderOK (target : Word) (bound : Bound) : Bool :=
  let (mask, _, _, goal) := bound
  (target &&& mask) == goal && goal != 0 && goal != mask
abbrev DagLinkList := Nat → List (Nat × Nat × Nat)
def dagUnpackLinksGo (data width tokenBits destBits tokMask destMask : Nat) : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, pos =>
      dagForceWord (unpack data width pos) (fun code =>
        dagForceWord (code &&& tokMask) (fun tk =>
          dagForceWord ((code >>> tokenBits) &&& destMask) (fun ds =>
            dagForceWord (code >>> (tokenBits + destBits)) (fun au =>
              (tk, ds, au) :: dagUnpackLinksGo data width tokenBits destBits tokMask destMask n (pos + 1)))))
def dagExtractLinks (index data indexWidth sizeBits tokenBits destBits autoBits : Nat) : DagLinkList :=
  fun parent =>
    dagForceWord (unpack index indexWidth parent) (fun entry =>
      dagForceWord (entry &&& fullMask sizeBits) (fun size =>
        dagForceWord (entry >>> sizeBits) (fun offset =>
          dagUnpackLinksGo data (tokenBits + destBits + autoBits) tokenBits destBits
            (fullMask tokenBits) (fullMask destBits) size offset)))
def dagFindLink : List (Nat × Nat × Nat) → Nat → Option DagLink
  | [], _ => none
  | (tk, ds, au) :: rest, token =>
      if Nat.beq tk token then some (ds, au) else dagFindLink rest token
def dagForceLinkList (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun e _ next k =>
      dagForceWord e.1 (fun tk =>
        dagForceWord e.2.1 (fun ds =>
          dagForceWord e.2.2 (fun au =>
            next (fun rest => k ((tk, ds, au) :: rest)))))) ls) cont
theorem dagForceLinkListEq (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) :
    dagForceLinkList ls cont = cont ls := by
  induction ls generalizing cont with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨tk, ds, au⟩ := e
    change dagForceWord tk (fun tk' => dagForceWord ds (fun ds' => dagForceWord au (fun au' =>
      dagForceLinkList es (fun rest => cont ((tk', ds', au') :: rest))))) = _
    rw [dagForceWordEq, dagForceWordEq, dagForceWordEq, ih]
def dagHighest7 (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset + shift))) 7) value 0
def dagSamplePairOK (mask goal : Word) (code : Nat) : Bool :=
  let p := code &&& 511
  let n := code >>> 9
  goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 256 && Nat.blt n 256
def dagSampleValid (mask goal : Word) (sample : DagSample) : Bool :=
  treeBlock 0 sample.2 (fun k => dagSamplePairOK mask goal (unpack sample.1 18 k))
def dagPackWords256 (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 256) ||| (tail <<< 256)) ws
def dagLaneMarks256 (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 256)) n
def dagOmitted256 (aBit bBit : Word) (left right : Bool) : Word :=
  (if left then 0 else aBit) ||| (if right then 0 else bBit)
theorem dagPackBits256 {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 256) :
    (dagPackWords256 ws).testBit (256 * i + row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 256) ||| (dagPackWords256 ws <<< 256)).testBit (256 * i + row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 256 ≤ 256 * i.succ + row := by omega
      have offset : 256 * i.succ + row - 256 = 256 * i + row := by omega
      have past : ¬ 256 * i.succ + row < 256 := by omega
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [crossed, offset, past, ih hi]
theorem dagMarkBits256 {length i : Nat} (inside : i < length) :
    (dagLaneMarks256 length).testBit (256 * i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks256 length <<< 256)).testBit (256 * i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 256 ≤ 256 * i.succ := by omega
      have offset : 256 * i.succ - 256 = 256 * i := by omega
      simp [crossed, offset, ih hi]
def dagPackedPair256 (packed marks erased out : Word) (directed : Bool) (code : Nat) : Bool :=
  dagForceWord (code &&& 511) (fun p =>
    dagForceWord (code >>> 9) (fun n =>
      let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
      gateOK &&
        dagForceWord ((packed >>> p) &&& marks) (fun up =>
          dagForceWord ((packed >>> n) &&& marks) (fun down =>
            let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
            Nat.beq (contrast &&& (marks ^^^ erased)) 0))))
theorem dagPackedPair256Sound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {code a b : Nat} {left right : Bool}
    (nd : ws.Nodup) (pairOK : dagSamplePairOK mask goal code = true)
    (checked : dagPackedPair256 (dagPackWords256 ws) (dagLaneMarks256 ws.length)
      (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right) out directed code = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) [code] = true := by
  apply List.any_eq_true.mpr
  refine ⟨code, List.mem_cons_self, ?_⟩
  simp only [dagSamplePairOK, Bool.and_eq_true, Nat.blt_eq] at pairOK
  obtain ⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩ := pairOK
  simp only [dagPackedPair256, dagForceWordEq, Bool.and_eq_true] at checked
  obtain ⟨output, closure⟩ := checked
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp, hn⟩, neg⟩, List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i, inside, eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right).testBit (256 * i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (256 * j)).testBit (256 * i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 256 * j ≠ 256 * i by omega]
    simp [dagOmitted256, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks256 ws.length
  let signal := dagPackWords256 ws
  have mark : marks.testBit (256 * i) = true := dagMarkBits256 inside
  have test {j : Nat} (within : j < 256) :
      ((signal >>> j) &&& marks).testBit (256 * i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits256 inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (256 * i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right)).testBit (256 * i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px, nx, pt, nt, Nat.testBit_and, Nat.testBit_xor, mark, omitted, p, n] at h ⊢
def dagSampleKill256 (sample : DagSample) (full : Word) (counts : DagCounts)
    (xC yC outC packed marks aBit bBit out : Word) (directed ka kb : Bool) : Bool :=
  let dx := if ka then 0 else xC
  let dy := if kb then 0 else yC
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| outC) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then false
    else dagForceWord (dagHighest7 missing) (fun idx =>
      if Nat.blt idx sample.2 then
        dagForceWord (unpack sample.1 18 idx) (fun code =>
          dagPackedPair256 packed marks (dagOmitted256 aBit bBit ka kb) out directed code)
      else false))
def dagNodeBoundsGo (bounds : Array Bound) (dataPacked cutBits : Nat) : Nat → Nat → List Bound
  | 0, _ => []
  | n + 1, pos =>
      match bounds[unpack dataPacked cutBits pos]? with
      | none => dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)
      | some b => b :: dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)
theorem dagNodeBoundsGo_mem {bounds : Array Bound} {dataPacked cutBits : Nat} :
    ∀ cnt off b, b ∈ dagNodeBoundsGo bounds dataPacked cutBits cnt off → b ∈ bounds.toList := by
  intro cnt
  induction cnt with
  | zero => intro _ _ h; cases h
  | succ n ih =>
    intro off b h
    unfold dagNodeBoundsGo at h
    split at h
    · exact ih _ _ h
    next x hx =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx)
      · exact ih _ _ h
def dagNodeBounds (bounds : Array Bound) (idxPacked dataPacked indexWidth sizeBits cutBits i : Nat) : List Bound :=
  let entry := unpack idxPacked indexWidth i
  dagNodeBoundsGo bounds dataPacked cutBits (entry &&& fullMask sizeBits) (entry >>> sizeBits)
theorem dagNodeBounds_mem {bounds : Array Bound} {idxPacked dataPacked indexWidth sizeBits cutBits i : Nat} :
    ∀ b ∈ dagNodeBounds bounds idxPacked dataPacked indexWidth sizeBits cutBits i, b ∈ bounds.toList :=
  fun b h => dagNodeBoundsGo_mem _ _ b h
def normWord (mask w : Word) : Word :=
  if w < mask ^^^ w then w else mask ^^^ w
theorem xor_cancel_left (mask w : Word) : mask ^^^ (mask ^^^ w) = w := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
theorem normWord_symm (mask w : Word) : normWord mask (mask ^^^ w) = normWord mask w := by
  unfold normWord
  rw [xor_cancel_left]
  by_cases h : w < mask ^^^ w
  · have h' : ¬(mask ^^^ w < w) := Nat.lt_asymm h
    simp [h, h']
  · by_cases h' : mask ^^^ w < w
    · simp [h, h']
    · have eq : w = mask ^^^ w := Nat.le_antisymm (Nat.le_of_not_lt h') (Nat.le_of_not_lt h)
      rw [if_neg h', if_neg h]; exact eq
theorem normWord_eq_or (mask w : Word) : normWord mask w = w ∨ normWord mask w = mask ^^^ w := by
  unfold normWord; split <;> simp
theorem normWord_idem (mask w : Word) : normWord mask (normWord mask w) = normWord mask w := by
  rcases normWord_eq_or mask w with h | h
  · rw [h, h]
  · rw [h, normWord_symm, h]
theorem normWord_zero (mask : Word) : normWord mask 0 = 0 := by
  unfold normWord
  rw [Nat.xor_zero]
  by_cases h : 0 < mask
  · rw [if_pos h]
  · have hm : mask = 0 := Nat.eq_zero_of_not_pos h
    rw [hm]; rfl
theorem normWord_mask (mask : Word) : normWord mask mask = 0 := by
  have h : normWord mask (mask ^^^ 0) = normWord mask 0 := normWord_symm mask 0
  rwa [Nat.xor_zero, normWord_zero] at h
theorem masked_xor {mask w : Word} (hw : Masked mask w) : Masked mask (mask ^^^ w) := by
  apply Nat.eq_of_testBit_eq; intro i
  have bit := congrArg (fun n : Nat => n.testBit i) hw
  simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
  cases hm : mask.testBit i <;> simp_all
theorem masked_norm {mask w : Word} (hw : Masked mask w) : Masked mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; exact masked_xor hw
theorem proper_xor {mask w : Word} (hp : properWord mask w) : properWord mask (mask ^^^ w) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_zero] at this
    exact hp.2 this
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_self] at this
    exact hp.1 this
theorem proper_norm {mask w : Word} (hp : properWord mask w) : properWord mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hp
  · rw [h]; exact proper_xor hp
theorem demorgan_and {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
theorem demorgan_or {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a ||| b) = (mask ^^^ a) &&& (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
theorem masked_and_self_xor {mask a : Word} (ma : Masked mask a) : a &&& (mask ^^^ a) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem masked_or_self_xor {mask a : Word} (ma : Masked mask a) : a ||| (mask ^^^ a) = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem masked_or_mask {mask a : Word} (ma : Masked mask a) : a ||| mask = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all
def AvBin (mask : Word) (bank : List Word) (w : Word) : Prop :=
  w = 0 ∨ w = mask ∨ w ∈ bank ∨ (mask ^^^ w) ∈ bank
theorem avBin_not {mask : Word} {bank : List Word} {w : Word}
    (h : AvBin mask bank w) : AvBin mask bank (mask ^^^ w) := by
  rcases h with rfl | hmask | hm | hm
  · exact Or.inr (Or.inl (Nat.xor_zero mask))
  · rw [hmask]; exact Or.inl (Nat.xor_self mask)
  · exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  · exact Or.inr (Or.inr (Or.inl hm))
theorem avBin_weaken {mask : Word} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (av : AvBin mask small w) : AvBin mask big w := by
  rcases av with rfl | rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
  · simpa [xor_cancel_left] using avBin_not (sub (mask ^^^ w) h)
theorem avBin_of_av {mask : Word} {bank : List Word} {w : Word}
    (h : AvailableWord mask bank w) : AvBin mask bank w := by
  rcases h with rfl | rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl hm))
theorem masked_avBin {mask : Word} {bank : List Word} {w : Word}
    (all : ∀ x ∈ bank, Masked mask x) (av : AvBin mask bank w) : Masked mask w := by
  rcases av with rfl | rfl | hm | hm
  · simp [Masked]
  · simp [Masked]
  · exact all _ hm
  · simpa [xor_cancel_left] using masked_xor (all _ hm)
def GateBin (mask : Word) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvBin mask bank a ∧ AvBin mask bank b ∧ (out = a &&& b ∨ out = a ||| b)
theorem gateBin_weaken {mask : Word} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (g : GateBin mask small out) : GateBin mask big out := by
  rcases g with ⟨a, b, ha, hb, eq⟩
  exact ⟨a, b, avBin_weaken sub ha, avBin_weaken sub hb, eq⟩
theorem masked_gateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ x ∈ bank, Masked mask x) (g : GateBin mask bank out) : Masked mask out := by
  rcases g with ⟨a, b, ha, hb, rfl | rfl⟩
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    simp only [Masked] at ma mb ⊢; rw [Nat.land_assoc, mb]
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    apply Nat.eq_of_testBit_eq; intro i
    have ba := congrArg (fun n : Nat => n.testBit i) ma
    have bb := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at ba bb ⊢
    cases hm : mask.testBit i <;> simp_all
def WordBuildsBin (mask : Word) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateBin mask roots w ∧ WordBuildsBin mask (w :: roots) ws
def BinLower (mask : Word) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuildsBin mask roots values →
    AvBin mask (values ++ roots) target → minimum ≤ values.length
theorem buildsBin_weaken {mask : Word} {small big values : List Word}
    (supply : ∀ w ∈ small, AvBin mask big w) (build : WordBuildsBin mask small values) :
    WordBuildsBin mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateBin_weaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
    · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)
theorem buildsBin_append {mask : Word} {roots first second : List Word}
    (left : WordBuildsBin mask roots first)
    (right : WordBuildsBin mask (first ++ roots) second) :
    WordBuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    exact buildsBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) right
def binOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  if op == 0 then a &&& b
  else if op == 1 then a ||| b
  else if op == 2 then a &&& (mask ^^^ b)
  else (mask ^^^ a) &&& b
def normBinOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  normWord mask (binOp4 mask op a b)
def swapOp4 (op : Nat) : Nat :=
  if op == 2 then 3 else if op == 3 then 2 else op
theorem swapOp4_lt {op : Nat} (h : op < 4) : swapOp4 op < 4 := by
  unfold swapOp4
  split
  · decide
  · split
    · decide
    · exact h
theorem binOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask (swapOp4 op) b a = binOp4 mask op a b := by
  have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp [binOp4, swapOp4, Nat.land_comm, Nat.lor_comm]
theorem normBinOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    normBinOp4 mask (swapOp4 op) b a = normBinOp4 mask op a b := by
  unfold normBinOp4; rw [binOp4_swap mask hop]
theorem gateBin_normBinOp4 {mask : Word} {bank : List Word} {op : Nat} {a b : Word}
    (hop : op < 4) (ma : Masked mask a) (mb : Masked mask b)
    (ha : AvBin mask bank a) (hb : AvBin mask bank b) :
    GateBin mask bank (normBinOp4 mask op a b) := by
  have hna := avBin_not ha
  have hnb := avBin_not hb
  have mna := masked_xor ma
  have mnb := masked_xor mb
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  unfold normBinOp4
  rcases normWord_eq_or mask (binOp4 mask op a b) with heq | heq
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨a, b, ha, hb, Or.inl rfl⟩
    · exact ⟨a, b, ha, hb, Or.inr rfl⟩
    · exact ⟨a, mask ^^^ b, ha, hnb, Or.inl rfl⟩
    · exact ⟨mask ^^^ a, b, hna, hb, Or.inl rfl⟩
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inr (demorgan_and ma mb)⟩
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inl (demorgan_or ma mb)⟩
    · refine ⟨mask ^^^ a, b, hna, hb, Or.inr ?_⟩
      change mask ^^^ (a &&& (mask ^^^ b)) = (mask ^^^ a) ||| b
      rw [demorgan_and ma mnb, xor_cancel_left]
    · refine ⟨a, mask ^^^ b, ha, hnb, Or.inr ?_⟩
      change mask ^^^ ((mask ^^^ a) &&& b) = a ||| (mask ^^^ b)
      rw [demorgan_and mna mb, xor_cancel_left]
def LiveBin (mask target : Word) : Nat → Finset Word → Prop
  | 0, S => S = {normWord mask target} ∧ properWord mask target
  | k + 1, S =>
    ∃ (U : Finset Word) (a b : Word) (op : Nat),
      op < 4 ∧ S = insert a (insert b U) ∧
      properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      normWord mask a = a ∧ normWord mask b = b ∧
      normBinOp4 mask op a b ∉ insert a (insert b U) ∧
      LiveBin mask target k (insert (normBinOp4 mask op a b) U)
theorem LiveBin.stop {mask target : Word} (hp : properWord mask target) :
    LiveBin mask target 0 {normWord mask target} := ⟨rfl, hp⟩
theorem LiveBin.step {mask target : Word} {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
    (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (na : normWord mask a = a) (nb : normWord mask b = b)
    (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)) :
    LiveBin mask target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hfresh, tail⟩
theorem LiveBin.ind {mask target : Word}
    {motive : ∀ (k : Nat) (S : Finset Word), LiveBin mask target k S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 {normWord mask target} (LiveBin.stop hp))
    (step : ∀ {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
      (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (na : normWord mask a = a) (nb : normWord mask b = b)
      (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
      (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)),
      motive k (insert (normBinOp4 mask op a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (LiveBin.step hop ha hb hab na nb hfresh tail))
    {k : Nat} {S : Finset Word} (h : LiveBin mask target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hf, tail⟩ := h
    exact step hop ha hb hab na nb hf tail (ih tail)
theorem liveBinProps {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : ∀ a ∈ S, properWord mask a ∧ normWord mask a = a := by
  induction h using LiveBin.ind with
  | stop hp =>
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact ⟨proper_norm hp, normWord_idem mask target⟩
  | step hop ha hb hab na nb hf tail ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha, na⟩, ⟨hb, nb⟩, fun w hw => ih w (Finset.mem_insert_of_mem hw)⟩
theorem liveBinSize {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : S.card ≤ k + 1 := by
  induction h using LiveBin.ind with
  | stop => simp
  | @step k U a b op hop ha hb hab na nb hf tail ih =>
    have hu : normBinOp4 mask op a b ∉ U := fun hm =>
      hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
def binWitness (mask : Word) (nws : List Word) (w : Word) : Prop :=
  ∃ op a b, op < 4 ∧ a ∈ nws ∧ b ∈ nws ∧ properWord mask a ∧ properWord mask b ∧
    normWord mask a = a ∧ normWord mask b = b ∧ a ≠ b ∧ w = normBinOp4 mask op a b
theorem classifyGateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateBin mask bank out) :
    wordRep mask (bank.map (normWord mask)) (normWord mask out) ∨
    binWitness mask (bank.map (normWord mask)) (normWord mask out) := by
  let nbank := bank.map (normWord mask)
  have c0 : wordRep mask nbank 0 := Or.inr fun h => h.1 rfl
  have cnorm (x : Word) (hx : AvBin mask bank x) :
      x = 0 ∨ x = mask ∨ (normWord mask x ∈ nbank ∧ properWord mask (normWord mask x)) := by
    by_cases hz : x = 0
    · exact Or.inl hz
    by_cases hm : x = mask
    · exact Or.inr (Or.inl hm)
    have hp : properWord mask x := ⟨hz, hm⟩
    refine Or.inr (Or.inr ⟨?_, proper_norm hp⟩)
    rcases (hx.resolve_left hz).resolve_left hm with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  rcases g with ⟨a, b, ha, hb, eq⟩
  have ma := masked_avBin all ha
  have mb := masked_avBin all hb
  have trivial_word (w : Word) (hw : AvBin mask bank w) : wordRep mask nbank (normWord mask w) := by
    rcases cnorm w hw with rfl | rfl | ⟨hm, _⟩
    · rw [normWord_zero]; exact c0
    · rw [normWord_mask]; exact c0
    · exact Or.inl hm
  rcases cnorm a ha with rfl | rfl | ⟨hma, pa⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.zero_and, normWord_zero]; exact Or.inl c0
    · simp only [Nat.zero_or]; exact Or.inl (trivial_word b hb)
  · rcases eq with rfl | rfl
    · rw [Nat.land_comm, mb]; exact Or.inl (trivial_word b hb)
    · rw [Nat.lor_comm, masked_or_mask mb, normWord_mask]; exact Or.inl c0
  rcases cnorm b hb with rfl | rfl | ⟨hmb, pb⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.and_zero, normWord_zero]; exact Or.inl c0
    · simp only [Nat.or_zero]; exact Or.inl (trivial_word a ha)
  · rcases eq with rfl | rfl
    · rw [ma]; exact Or.inl (trivial_word a ha)
    · rw [masked_or_mask ma, normWord_mask]; exact Or.inl c0
  let na := normWord mask a
  let nb := normWord mask b
  have mna : Masked mask na := masked_norm ma
  have mnb : Masked mask nb := masked_norm mb
  by_cases same : na = nb
  · have hrel : b = a ∨ b = mask ^^^ a := by
      rcases normWord_eq_or mask a with ea | ea <;> rcases normWord_eq_or mask b with eb | eb
      · left; exact eb.symm.trans (same.symm.trans ea)
      · right
        have h1 : a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left] at this; exact this.symm
      · right; exact eb.symm.trans (same.symm.trans ea)
      · left
        have h1 : mask ^^^ a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left, xor_cancel_left] at this; exact this.symm
    rcases hrel with rfl | rfl <;> rcases eq with rfl | rfl
    · rw [Nat.and_self]; exact Or.inl (Or.inl hma)
    · rw [Nat.or_self]; exact Or.inl (Or.inl hma)
    · rw [masked_and_self_xor ma, normWord_zero]; exact Or.inl c0
    · rw [masked_or_self_xor ma, normWord_mask]; exact Or.inl c0
  have ea : a = na ∨ a = mask ^^^ na := by
    rcases normWord_eq_or mask a with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have eb : b = nb ∨ b = mask ^^^ nb := by
    rcases normWord_eq_or mask b with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have mkWit (op : Nat) (hop : op < 4) (heq : normWord mask out = normBinOp4 mask op na nb) :
      binWitness mask nbank (normWord mask out) :=
    ⟨op, na, nb, hop, hma, hmb, pa, pb, normWord_idem mask a, normWord_idem mask b, same, heq⟩
  right
  rcases eq with hout | hout <;> rcases ea with hea | hea <;> rcases eb with heb | heb
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 2 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb, ← demorgan_or mna mnb, normWord_symm]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by
      have h1 : mask ^^^ ((mask ^^^ na) &&& nb) = na ||| (mask ^^^ nb) := by
        rw [demorgan_and (masked_xor mna) mnb, xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 2 (by decide) (by
      have h1 : mask ^^^ (na &&& (mask ^^^ nb)) = (mask ^^^ na) ||| nb := by
        rw [demorgan_and mna (masked_xor mnb), xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb, ← demorgan_and mna mnb, normWord_symm]; rfl)
theorem pullBin {mask target : Word} {nws : List Word} {z : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S)
    (hz : wordRep mask nws z ∨ binWitness mask nws z) (sub : ∀ a ∈ S, a ∈ nws ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ LiveBin mask target k' S' ∧ ∀ a ∈ S', a ∈ nws := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ nws
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ nws ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := (liveBinProps h z hm).1
      rcases hz with hr | ⟨op, a, b, hop, ha, hb, pa, pb, na, nb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (normBinOp4 mask op a b)
        have ht : LiveBin mask target k (insert (normBinOp4 mask op a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ nws := by
          intro v hv
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hmem
        have hf : normBinOp4 mask op a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k + 1, insert a (insert b U), Nat.le_refl _,
          LiveBin.step hop pa pb hab na nb hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
theorem extractBinLive {mask target : Word} {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuildsBin mask roots values)
    (hit : AvBin mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveBin mask target k S ∧ ∀ w ∈ S, w ∈ roots.map (normWord mask) := by
  have hm : normWord mask target ∈ (values ++ roots).map (normWord mask) := by
    rcases (hit.resolve_left p.1).resolve_left p.2 with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {normWord mask target}, Nat.zero_le _, LiveBin.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact masked_gateBin all builds.1
      · exact all _ hv
    have ht : AvBin mask (ws ++ w :: roots) target := by
      rcases hit with rfl | rfl | hmem | hmem
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
    have hm' : normWord mask target ∈ (ws ++ w :: roots).map (normWord mask) := by
      rcases (ht.resolve_left p.1).resolve_left p.2 with hmem | hmem
      · exact List.mem_map_of_mem hmem
      · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
    obtain ⟨k, S, hk, live, sub⟩ := ih next builds.2 ht hm'
    have available : ∀ v ∈ S, v ∈ roots.map (normWord mask) ++ [normWord mask w] := by
      intro v h
      simpa [List.map_cons, or_comm] using sub v h
    obtain ⟨k', S', hk', hl, hsub⟩ := pullBin live (classifyGateBin all builds.1) available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩
theorem agreesNorm {i j mask w : Word} (m : AgreesAt i j mask) (hw : AgreesAt i j w) :
    AgreesAt i j (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; simp only [AgreesAt, Nat.testBit_xor] at m hw ⊢; rw [m, hw]
theorem liveBinAgrees {mask target : Word} {i j k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveBin.ind with
  | stop =>
    have hn := all _ (Finset.mem_singleton_self _)
    rcases normWord_eq_or mask target with h | h
    · rwa [h] at hn
    · rw [h] at hn
      change mask.testBit i = mask.testBit j at m
      change (mask ^^^ target).testBit i = (mask ^^^ target).testBit j at hn
      rw [Nat.testBit_xor, Nat.testBit_xor, m] at hn
      change target.testBit i = target.testBit j
      cases hmj : mask.testBit j <;> cases hti : target.testBit i <;> cases htj : target.testBit j <;> simp_all
  | @step k U a b op hop pa pb hab na nb hf tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · unfold normBinOp4
      apply agreesNorm m
      have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have mm : mask.testBit i = mask.testBit j := m
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl <;>
        simp [binOp4, AgreesAt, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, aa, bb, mm]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
theorem dagPartitionLiveBin {mask goal : Word} {ws : List Word} {k : Nat}
    (goalMask : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPartition false ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition false ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition false ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  have same := liveBinAgrees live (pm.trans nm.1.symm) (fun w hw => by
    simpa [AgreesAt] using agree w (List.mem_toFinset.mp hw))
  simp [AgreesAt, hp, nm.2] at same
theorem dagPairsOpenBin {mask goal : Word} {ws : List Word} {pairs : List Nat} {k : Nat}
    (masked : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPairReject mask goal false ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code, _, check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  have h := liveBinAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
    have pair := bank _ (List.mem_toFinset.mp hw)
    simpa [AgreesAt] using pair)
  simp [AgreesAt, hp, neg] at h
theorem essentialRequiredBin {mask target : Word} {stock : List Word} {entry : Witness}
    {S : Finset Word} {k : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    normWord mask (witnessWord entry) ∈ S := by
  obtain ⟨w, p, n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp, mn⟩, tp⟩, tn⟩, unequal⟩, rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
    have horig : orig ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    have h := List.all_eq_true.mp rest orig omem
    have hag : AgreesAt p n orig := by simpa [horig, AgreesAt] using h
    exact agreesNorm (mp.trans mn.symm) hag
  have agree := liveBinAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree
theorem essentialWordsInBin {mask target : Word} {stock : List Word} {witnesses : List Witness}
    {S : Finset Word} {k : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequiredBin (List.all_eq_true.mp ok entry mem) sub live
theorem essentialLowerBin {mask target : Word} {stock : List Word} {witnesses : List Witness} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset.card - 1) :
    BinLower mask stock target minimum := by
  intro values build hit
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsInBin ok sub live)
  have size := liveBinSize live
  omega
def buildableBin (m g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s ∨ (m ^^^ g) ∈ s
  | n + 1, s => buildableBin m g n s ∨
      ∃ a b, (a ∈ s ∨ m ^^^ a ∈ s) ∧ (b ∈ s ∨ m ^^^ b ∈ s) ∧
        ∃ d : Bool, buildableBin m g n (insert (binWord d a b) s)
theorem supplyPoolBin {m g : Word} {n : Nat} {s q : Finset Word}
    (sub : ∀ w ∈ s, w ∈ q ∨ m ^^^ w ∈ q) (h : buildableBin m g n s) : buildableBin m g n q := by
  induction n generalizing s q with
  | zero =>
    rcases h with h1 | h1
    · exact sub g h1
    · rcases sub (m ^^^ g) h1 with h2 | h2
      · exact Or.inr h2
      · rw [xor_cancel_left] at h2; exact Or.inl h2
  | succ n ih =>
    have subPair {x : Word} (hx : x ∈ s ∨ m ^^^ x ∈ s) : x ∈ q ∨ m ^^^ x ∈ q := by
      rcases hx with h1 | h1
      · exact sub x h1
      · rcases sub (m ^^^ x) h1 with h2 | h2
        · exact Or.inr h2
        · rw [xor_cancel_left] at h2; exact Or.inl h2
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · exact Or.inl (ih sub h)
    · refine Or.inr ⟨a, b, subPair ha, subPair hb, d, ih ?_ h⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Or.inl (Finset.mem_insert_self _ _)
      · rcases sub w hw with hq | hq
        · exact Or.inl (Finset.mem_insert_of_mem hq)
        · exact Or.inr (Finset.mem_insert_of_mem hq)
theorem buildableBinWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildableBin mask goal n pool) (supply : ∀ w ∈ pool, AvBin mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuildsBin mask bank values ∧
      AvBin mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero =>
    refine ⟨[], Nat.le_refl _, trivial, ?_⟩
    rcases h with h1 | h1
    · exact supply goal h1
    · simpa [xor_cancel_left] using avBin_not (supply _ h1)
  | succ n ih =>
    have supPair {w : Word} (hw : w ∈ pool ∨ mask ^^^ w ∈ pool) : AvBin mask bank w := by
      rcases hw with h1 | h1
      · exact supply w h1
      · simpa [xor_cancel_left] using avBin_not (supply _ h1)
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · let w := binWord d a b
      have g : GateBin mask bank w :=
        ⟨a, b, supPair ha, supPair hb, by cases d <;> simp [w, binWord]⟩
      have growing : ∀ v ∈ insert w pool, AvBin mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun _ hh => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hh)))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih h growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
        simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)))) hit
theorem cofBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask op a b &&& m = binOp4 m op (a &&& m) (b &&& m) := by
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact cofBinary m a b false
  · exact cofBinary m a b true
  · change (a &&& (mask ^^^ b)) &&& m = (a &&& m) &&& (m ^^^ (b &&& m))
    rw [← cofNot sub b]; exact cofBinary m a (mask ^^^ b) false
  · change ((mask ^^^ a) &&& b) &&& m = (m ^^^ (a &&& m)) &&& (b &&& m)
    rw [← cofNot sub a]; exact cofBinary m (mask ^^^ a) b false
theorem flNorm {mask m : Word} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (normWord mask a) ↔ maskedFlat m a := by
  rcases normWord_eq_or mask a with h | h
  · rw [h]
  · rw [h]; exact flNot sub a
theorem flBothOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (ha : maskedFlat m a) (hb : maskedFlat m b) : maskedFlat m (normBinOp4 mask op a b) := by
  rw [normBinOp4, flNorm sub]
  unfold maskedFlat at *
  rw [cofBinOp4 sub hop]
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [binOp4, ha, hb]
theorem simpleBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (h : maskedFlat m a ∨ maskedFlat m b) :
    binOp4 mask op a b &&& m = 0 ∨ binOp4 mask op a b &&& m = m ∨
    binOp4 mask op a b &&& m = a &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (a &&& m) ∨
    binOp4 mask op a b &&& m = b &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (b &&& m) := by
  rw [cofBinOp4 sub hop]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]; simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by rw [Nat.lor_comm]; exact masked_or_mask (restrictWord m x)
  have top3 (x : Word) : (m ^^^ (x &&& m)) &&& m = m ^^^ (x &&& m) :=
    masked_xor (restrictWord m x)
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  have right3 (x : Word) : m &&& (m ^^^ (x &&& m)) = m ^^^ (x &&& m) := by
    rw [Nat.land_comm]; exact top3 x
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;> rcases h with (ha | ha) | (hb | hb) <;>
    simp [binOp4, *, top1, top2, top3, right1, right2, right3]
theorem maskedBuildBin {mask goal : Word} {k : Nat} {s : Finset Word}
    (run : LiveBin mask goal k s) (m : Word) (submask : mask &&& m = m)
    (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n + (flatSet m s).card ≤ k ∧ buildableBin m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveBin.ind with
  | stop =>
    refine ⟨0, ?_, ?_⟩
    · have pgn : ¬ maskedFlat m (normWord mask goal) := by rwa [flNorm submask]
      simp only [flatSet, Finset.filter_singleton, pgn, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · rcases normWord_eq_or mask goal with h | h
      · left; simp [projectedStock, visibleWords, h]
      · right; rw [← cofNot submask goal, ← h]; simp [projectedStock, visibleWords]
  | @step k u a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    obtain ⟨n, cap, built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n + (flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    have hv_rel : v &&& m = binOp4 mask op a b &&& m ∨
        v &&& m = m ^^^ (binOp4 mask op a b &&& m) := by
      rcases normWord_eq_or mask (binOp4 mask op a b) with h | h
      · left; simp [v, normBinOp4, h]
      · right; simp [v, normBinOp4, h, cofNot submask]
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k + 1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa, fb, ite_true, ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBothOp4 submask hop fa fb; simp only [vf, ite_true] at cap; omega | omega | tauto
      refine ⟨n, budget, supplyPoolBin ?_ built⟩
      intro w hw
      simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
      rcases hw with rfl | rfl | rfl | h
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · have sc := simpleBinOp4 submask hop simple
        rcases hv_rel with e | e <;> rw [e]
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr (Or.inl rfl))
          · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inr (Or.inl (Nat.xor_zero m)))
          · exact Or.inl (Or.inl (Nat.xor_self m))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa, fb, ite_false] at ca cb
      have ha_in : a &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hb_in : b &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hna_in : m ^^^ (m ^^^ (a &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have hnb_in : m ^^^ (m ^^^ (b &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have mkStep {a' b' : Word} {d : Bool}
          (ha' : a' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ a' ∈ projectedStock m (insert a (insert b u)))
          (hb' : b' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ b' ∈ projectedStock m (insert a (insert b u)))
          (heq : binOp4 mask op a b &&& m = binWord d a' b') :
          ∃ n', n' + (flatSet m (insert a (insert b u))).card ≤ k + 1 ∧
            buildableBin m (goal &&& m) n' (projectedStock m (insert a (insert b u))) := by
        refine ⟨n + 1, by omega, Or.inr ⟨a', b', ha', hb', d, supplyPoolBin ?_ built⟩⟩
        intro w hw
        simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
        rcases hw with rfl | rfl | rfl | h
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hv_rel with e | e
          · exact Or.inl (Or.inl (e.trans heq))
          · exact Or.inr (by rw [e, xor_cancel_left]; exact Or.inl heq)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 0) submask (by decide) a b)
      · exact mkStep (d := true) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 1) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inr hnb_in) (cofBinOp4 (op := 2) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inr hna_in) (Or.inl hb_in) (cofBinOp4 (op := 3) submask (by decide) a b)
theorem essentialLiftBin {mask target : Word} {stock cutStock : List Word} {witnesses : List Witness}
    {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvBin cut cutStock (w &&& cut))
    (known : BinLower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset).card) :
    BinLower mask stock target minimum := by
  intro values build hit
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive masked build hit proper
  have subW := essentialWordsInBin ok sub live
  have subFlat : flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuildBin live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvBin cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x, hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
      rcases normWord_eq_or mask orig with e | e
      · rw [e]; exact supplies _ omem
      · rw [e, cofNot submask]; exact avBin_not (supplies _ omem)
  obtain ⟨ys, len, built', out⟩ := buildableBinWords built starts
  have lower := known ys built' out
  omega
def normWordFast (mask w : Word) : Word :=
  dagForceWord (mask ^^^ w) (fun c => if Nat.blt w c then w else c)
theorem normWordFast_eq (mask w : Word) : normWordFast mask w = normWord mask w := by
  simp [normWordFast, normWord, dagForceWordEq, Nat.blt_eq]
def normBinOp4Fast (mask op x y : Word) : Word :=
  normWordFast mask (binOp4 mask op x y)
theorem normBinOp4Fast_eq (mask op x y : Word) : normBinOp4Fast mask op x y = normBinOp4 mask op x y :=
  normWordFast_eq mask (binOp4 mask op x y)
def availableNormB (bank : List Word) (v : Word) : Bool :=
  v == 0 || bank.contains v
theorem availableNormB_spec {mask : Word} {orig bank : List Word} {w : Word}
    (mw : Masked mask w) (hbank : ∀ x ∈ bank, AvBin mask orig x)
    (h : availableNormB bank (normWord mask w) = true) : AvBin mask orig w := by
  simp only [availableNormB, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with hz | hm
  · rcases normWord_eq_or mask w with e | e
    · exact Or.inl (e.symm.trans hz)
    · have : mask ^^^ w = 0 := e.symm.trans hz
      have h1 : w = mask := by
        have h2 := congrArg (fun z => mask ^^^ z) this
        rw [xor_cancel_left, Nat.xor_zero] at h2
        exact h2
      exact Or.inr (Or.inl h1)
  · have hav := hbank _ hm
    rcases normWord_eq_or mask w with e | e
    · rwa [e] at hav
    · rw [e] at hav
      have := avBin_not hav
      rwa [xor_cancel_left] at this
def stockWordBinF (mask : Word) (nstock needed : List Word) (word : Word) : List Word :=
  dagForceWord (normWordFast mask (word &&& mask)) (fun v =>
    if availableNormB nstock v || needed.contains v then needed else v :: needed)
def recipeStartBinF (mask : Word) (nstock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBinF mask nstock seen word)) words) []
def recipeClosureBinF (mask : Word) (nstock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (dagForceWord (normWordFast mask (out &&& mask)) (fun vo =>
        if seen.contains vo then
          stockWordBinF mask nstock (stockWordBinF mask nstock seen a) b else seen)))
    history start
def recipeGateBinNorm (mask : Word) (nbank : List Word) (v ma mb : Word) : Bool :=
  availableNormB nbank (normWordFast mask ma) && availableNormB nbank (normWordFast mask mb) &&
    (v == normWordFast mask (ma &&& mb) || v == normWordFast mask (ma ||| mb) ||
     v == normWordFast mask (ma &&& (mask ^^^ mb)) || v == normWordFast mask ((mask ^^^ ma) &&& mb))
theorem recipeGateBinNorm_spec {mask : Word} {orig nbank : List Word} {v ma mb : Word}
    (hma : Masked mask ma) (hmb : Masked mask mb)
    (hbank : ∀ x ∈ nbank, AvBin mask orig x)
    (h : recipeGateBinNorm mask nbank v ma mb = true) : GateBin mask orig v := by
  simp only [recipeGateBinNorm, normWordFast_eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  have havA := availableNormB_spec hma hbank ha
  have havB := availableNormB_spec hmb hbank hb
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 1) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 2) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 3) (by decide) hma hmb havA havB
def replayRecipesBinF (mask : Word) (needed : List Word) : List (Word × Word × Word) → List Word → List Word
  | [], _ => []
  | (w, a, b) :: rs, nbank =>
      dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
        if needed.contains v && !availableNormB nbank v then
          dagForceWord (a &&& mask) (fun ma =>
            dagForceWord (b &&& mask) (fun mb =>
              if recipeGateBinNorm mask nbank v ma mb then
                v :: replayRecipesBinF mask needed rs (v :: nbank)
              else replayRecipesBinF mask needed rs nbank))
        else replayRecipesBinF mask needed rs nbank)
theorem replayRecipesBinFBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (orig nbank : List Word) (hbank : ∀ x ∈ nbank, AvBin mask orig x) :
    WordBuildsBin mask orig (replayRecipesBinF mask needed recipes nbank) ∧
      ∀ x ∈ replayRecipesBinF mask needed recipes nbank, x ∈ replayRecipesBinF mask needed recipes nbank := by
  refine ⟨?_, fun _ h => h⟩
  induction recipes generalizing orig nbank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask orig (dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
      if needed.contains v && !availableNormB nbank v then
        dagForceWord (a &&& mask) (fun ma =>
          dagForceWord (b &&& mask) (fun mb =>
            if recipeGateBinNorm mask nbank v ma mb then
              v :: replayRecipesBinF mask needed recipes (v :: nbank)
            else replayRecipesBinF mask needed recipes nbank))
      else replayRecipesBinF mask needed recipes nbank))
    simp only [dagForceWordEq, normWordFast_eq]
    split
    · split
      · rename_i h1 h2
        refine ⟨recipeGateBinNorm_spec (restrictWord mask a) (restrictWord mask b) hbank h2, ?_⟩
        apply ih (normWord mask (w &&& mask) :: orig) (normWord mask (w &&& mask) :: nbank)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hy)))) (hbank x hx)
      · exact ih orig nbank hbank
    · exact ih orig nbank hbank
def dagBoundClosesBinNoHdr (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, _) := bound
  let (fuel, ws, history) := state
  dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
    if Nat.blt remaining lower then
      dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
        if Nat.blt (start.length + remaining) lower then
          dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
            if Nat.blt (needed.length + remaining) lower then
              dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                Nat.blt (replay.length + remaining) lower &&
                  ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                    availableNormB (replay ++ nstock) v)))
            else false)
        else false)
    else false)
def dagKnownClosesBinNoHdr (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBinNoHdr state bound || later) bounds
def dagFilterForceBoundsBin (target : Word) (bounds : List Bound) (cont : List Bound → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Bound → Bool) → Bool) (fun k => k [])
    (fun b _ next k =>
      dagForceWord b.1 (fun m' =>
        dagForceWord b.2.2.2 (fun g' =>
          if (target &&& m') == g' && g' != 0 && g' != m' then
            dagForceWords (b.2.1.map (fun w => normWordFast m' w)) (fun nst' =>
              next (fun rest => k ((m', nst', b.2.2.1, g') :: rest)))
          else next k))) bounds) cont
theorem dagFilterForceBoundsBinEq (target : Word) (bounds : List Bound) (cont : List Bound → Bool) :
    dagFilterForceBoundsBin target bounds cont =
      cont ((bounds.filter (dagBoundHeaderOK target)).map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) := by
  induction bounds generalizing cont with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨m, st, lo, g⟩ := b
    change dagForceWord m (fun m' => dagForceWord g (fun g' =>
      if (target &&& m') == g' && g' != 0 && g' != m' then
        dagForceWords (st.map (fun w => normWordFast m' w)) (fun nst' =>
          dagFilterForceBoundsBin target bs (fun rest => cont ((m', nst', lo, g') :: rest)))
      else dagFilterForceBoundsBin target bs cont)) = _
    simp only [dagForceWordEq, dagForceWordsEq, List.filter_cons, dagBoundHeaderOK]
    have hm : st.map (fun w => normWordFast m w) = st.map (normWord m) := by
      congr 1; funext w; exact normWordFast_eq m w
    by_cases hc : ((target &&& m) == g && g != 0 && g != m) = true
    · simp only [hc, ite_true, hm, List.map_cons]; exact ih _
    · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, ite_false]; exact ih _
def dagBoundClosesBinFast (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                  Nat.blt (replay.length + remaining) lower &&
                    ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                      availableNormB (replay ++ nstock) v)))
              else false)
          else false)
      else false)
def availableBinB (mask : Word) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w || bank.contains (mask ^^^ w)
theorem availableBinB_spec {mask : Word} {bank : List Word} {v : Word} :
    availableBinB mask bank v = true ↔ AvBin mask bank v := by
  simp [availableBinB, AvBin, or_assoc]
def stockWordBin (mask : Word) (stock needed : List Word) (word : Word) : List Word :=
  let v := normWord mask (word &&& mask)
  if availableBinB mask stock v || needed.contains v then needed else v :: needed
def recipeStartBin (mask : Word) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBin mask stock seen word)) words) []
def recipeClosureBin (mask : Word) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (normWord mask (out &&& mask)) then
        stockWordBin mask stock (stockWordBin mask stock seen a) b else seen))
    history start
def recipeGateBin (mask : Word) (bank : List Word) (w a b : Word) : Bool :=
  availableBinB mask bank a && availableBinB mask bank b &&
    (w == normWord mask (a &&& b) || w == normWord mask (a ||| b) ||
     w == normWord mask (a &&& (mask ^^^ b)) || w == normWord mask ((mask ^^^ a) &&& b))
theorem recipeGateBin_spec {mask : Word} {bank : List Word} {v a b : Word}
    (ma : Masked mask a) (mb : Masked mask b)
    (h : recipeGateBin mask bank v a b = true) : GateBin mask bank v := by
  simp only [recipeGateBin, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableBinB_spec] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 1) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 2) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 3) (by decide) ma mb ha hb
def replayRecipesBin (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := normWord mask (w &&& mask)
      if needed.contains v && !availableBinB mask bank v &&
          recipeGateBin mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank
theorem replayRecipesBinBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuildsBin mask bank (replayRecipesBin mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask bank
      (if needed.contains (normWord mask (w &&& mask)) && !availableBinB mask bank (normWord mask (w &&& mask)) &&
          recipeGateBin mask bank (normWord mask (w &&& mask)) (a &&& mask) (b &&& mask) then
        normWord mask (w &&& mask) :: replayRecipesBin mask needed recipes (normWord mask (w &&& mask) :: bank)
      else replayRecipesBin mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGateBin_spec (restrictWord mask a) (restrictWord mask b) (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _
def dagBoundClosesBin (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBin mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBin mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBin mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableBinB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)
def dagKnownClosesBin (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBin target state bound || later) bounds
def KnownBin (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1
theorem extendKnownBin {bound : Bound} {bounds : List Bound}
    (old : KnownBin bounds)
    (new : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    KnownBin (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h
def BinViable (mask target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k, k ≤ state.1 ∧ LiveBin mask target k state.2.1.toFinset
theorem boundClosesBinSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBin target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let needed := recipeClosureBin cut stock history (recipeStartBin cut stock ws)
  let replay := replayRecipesBin cut needed history.reverse stock
  simp only [dagBoundClosesBin, dagForceWordEq, dagForceWordsEq, Nat.blt_eq,
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableBinB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append (replayRecipesBinBuilds cut needed history.reverse stock) built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega
theorem knownClosesBinSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : BinViable mask target state) :
    dagKnownClosesBin target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBin target state bound || dagKnownClosesBin target bounds state) = false
    rw [boundClosesBinSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))
theorem boundClosesBinFastSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let nstock := stock.map (normWord cut)
  let needed := recipeClosureBinF cut nstock history (recipeStartBinF cut nstock ws)
  let replay := replayRecipesBinF cut needed history.reverse nstock
  simp only [dagBoundClosesBinFast, dagForceWordEq, dagForceWordsEq, flatCountF_eq, normWordFast_eq,
    Nat.blt_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := Nat.blt_eq.mp length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have hnst : ∀ x ∈ nstock, AvBin cut stock x := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    rcases normWord_eq_or cut s with e | e
    · rw [e]; exact Or.inr (Or.inr (Or.inl hs))
    · rw [e]; exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  have hrep := (replayRecipesBinFBuilds cut needed history.reverse stock nstock hnst).1
  have hbank : ∀ x ∈ replay ++ nstock, AvBin cut (replay ++ stock) x := by
    intro x hx
    rcases List.mem_append.mp hx with hr | hs
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left stock hr)))
    · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_append_right replay hy)))) (hnst x hs)
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableNormB_spec (restrictWord cut v) hbank (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append hrep built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega
theorem knownClosesBinNoHdrSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hdr : ∀ b ∈ bounds, dagBoundHeaderOK target b = true)
    (viable : BinViable mask target state) :
    dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) ||
      dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state) = false
    have h1 := boundClosesBinFastSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable
    have hh := hdr bound List.mem_cons_self
    have heq : dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) =
        dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) := by
      obtain ⟨f, ws, hist⟩ := state
      obtain ⟨m, st, lo, g⟩ := bound
      simp only [dagBoundHeaderOK] at hh
      simp only [dagBoundClosesBinNoHdr, dagBoundClosesBinFast, hh, Bool.true_and]
    rw [heq, h1]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))
      (fun b hb => hdr b (List.mem_cons_of_mem _ hb))
theorem buildsBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    {values : List Word} (h : WordBuildsBin m roots values) :
    WordBuildsBin n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvBin n bank (f v))
      (h : AvBin m roots v) : AvBin n bank (f v) := by
    rcases h with rfl | rfl | hv | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
    · have h1 := src _ hv; rw [invert] at h1; simpa [xor_cancel_left] using avBin_not h1
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, b, ha, hb, eq | eq⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)
theorem lowerBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    (bound : BinLower n bank (f goal) minimum) :
    BinLower m roots goal minimum := by
  intro values build hit
  suffices AvBin n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsBinMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ (List.mem_map_of_mem hv))))
    · exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw)))) (supply _ hr)
  · rcases List.mem_append.mp mem with hv | hr
    · have h1 : f (m ^^^ goal) ∈ values.map f ++ bank := List.mem_append_left _ (List.mem_map_of_mem hv)
      rw [invert] at h1
      exact Or.inr (Or.inr (Or.inr h1))
    · have h1 := supply _ hr
      rw [invert] at h1
      exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw))))
        (by simpa [xor_cancel_left] using avBin_not h1)
theorem suppliesBinOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableBinB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvBin oldMask old (rename w) := by
  intro w hw
  exact availableBinB_spec.mp (List.all_eq_true.mp h w hw)
def dagShiftCheckBin (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableBinB oldMask old (dagShift mask move w))
theorem dagShiftLowerBin {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : BinLower oldMask old oldGoal min)
    (ok : dagShiftCheckBin width mask goal oldMask oldGoal stock old move = true) :
    BinLower mask stock goal min := by
  simp only [dagShiftCheckBin, Bool.and_eq_true, Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded, unique⟩, masks⟩, goals⟩, supply⟩ := ok
  obtain ⟨andG, orG, xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr; rw [dagShiftLinear]; simp
  apply lowerBinMap (dagShift mask move) zero masks (fun w => by rw [xorG, masks]) andG orG (suppliesBinOfCheck supply)
  rwa [goals]
def gateTokenBin (a b op keep : Nat) : Nat := ((a * 64 + b) * 4 + op) * 4 + keep
theorem gateTokenBinFields {a b op keep : Nat} (hb : b < 64) (ho : op < 4) (hk : keep < 4) :
    gateTokenBin a b op keep % 4 = keep ∧
    gateTokenBin a b op keep / 4 % 4 = op ∧
    gateTokenBin a b op keep / (4 * 4 * 64) = a ∧
    gateTokenBin a b op keep / (4 * 4) % 64 = b := by
  unfold gateTokenBin; omega
def normStock (mask : Word) (stock : List Word) : List Word :=
  List.rec [] (fun w _ rest => insertWord (normWord mask w) rest) stock
theorem normStockSet (mask : Word) (stock : List Word) :
    (normStock mask stock).toFinset = (stock.map (normWord mask)).toFinset := by
  induction stock with
  | nil => simp [normStock]
  | cons w ws ih =>
    change (insertWord (normWord mask w) (normStock mask ws)).toFinset = _
    rw [insertWordSet, ih]; simp
def childStateBin (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 4
  let a := token / (4 * 4 * 64)
  let b := (token / (4 * 4)) % 64
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := normBinOp4 mask op x y
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)
def dagDirectChildBin (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    some (fuel - 1, insertWord out rest, (out, x, y) :: history)
theorem dagDirectChildBinEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 4) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChildBin mask state a b op keep x y (normBinOp4 mask op x y) =
      childStateBin mask (gateTokenBin a b op keep) state := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨keepEq, opEq, aEq, bEq⟩ := gateTokenBinFields (a := a) hb hop hk
  simp only [childStateBin, dagDirectChildBin, keepWord, keepEq, opEq, aEq, bEq]
def dagTraceBin (mask : Word) (nstock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ nstock.length then some (rootState nstock fuel token) else none
      else (previous (parent - 1)).bind (childStateBin mask token)) (fuel + 1)) i
def dagMoveWordsBin (mask : Word) (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (normWord mask (mixMove m w)) next) ws
theorem dagMoveSetBin {mask : Word} {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWordsBin mask m ws).toFinset = ws.toFinset.image (fun w => normWord mask (relabel select w)) := by
  induction ws with
  | nil => simp [dagMoveWordsBin]
  | cons w ws ih =>
    change (insertWord (normWord mask (mixMove m w)) (dagMoveWordsBin mask m ws)).toFinset = _
    rw [insertWordSet, ih (fun u hu => agree _ (List.mem_cons_of_mem _ hu)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]
def dagRefBin (mask : Word) (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto - 1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWordsBin mask m state.2.1
theorem liveBinMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k : Nat} {S : Finset Word} (live : LiveBin mask goal k S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveBin mask goal k (S.image (fun w => normWord mask (relabel select w))) := by
  let g := relabel select
  let f := fun w => normWord mask (g w)
  have hmask : g mask = mask := auto.2.1
  have hxor (w : Word) : g (mask ^^^ w) = mask ^^^ g w := by dsimp only [g]; rw [relabelXor, auto.2.1]
  have fnrm (w : Word) : f (normWord mask w) = f w := by
    rcases normWord_eq_or mask w with h | h
    · rw [h]
    · simp only [f, h, hxor, normWord_symm]
  have injG {a b : Word} (ma : Masked mask a) (mb : Masked mask b) : g a = g b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have injF {a b : Word} (ma : Masked mask a) (mb : Masked mask b)
      (na : normWord mask a = a) (nb : normWord mask b = b) (eq : f a = f b) : a = b := by
    have hrel : g a = g b ∨ g a = mask ^^^ g b := by
      rcases normWord_eq_or mask (g a) with ea | ea <;> rcases normWord_eq_or mask (g b) with eb | eb
      · left; exact ea.symm.trans (eq.trans eb)
      · right; exact ea.symm.trans (eq.trans eb)
      · right
        have h1 : mask ^^^ g a = g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left] at this; exact this
      · left
        have h1 : mask ^^^ g a = mask ^^^ g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left, xor_cancel_left] at this; exact this
    rcases hrel with h1 | h1
    · exact injG ma mb h1
    · rw [← hxor] at h1
      have h2 := injG ma (masked_xor mb) h1
      rw [← na, h2, normWord_symm, nb]
  have properF {a : Word} (ma : Masked mask a) (ha : properWord mask a) : properWord mask (f a) := by
    apply proper_norm
    exact ⟨fun eq => ha.1 (injG ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (injG ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {T : Finset Word} {v : Word} (hv : v ∉ T) (mv : Masked mask v) (nv : normWord mask v = v)
      (ms : ∀ w ∈ T, Masked mask w) (ns : ∀ w ∈ T, normWord mask w = w) : f v ∉ T.image f := by
    intro hw
    obtain ⟨w, hs, eq⟩ := Finset.mem_image.mp hw
    exact hv (injF (ms w hs) mv (ns w hs) nv eq ▸ hs)
  have opImage {a b : Word} (ma : Masked mask a) (mb : Masked mask b) {op : Nat} (hop : op < 4) :
      ∃ op', op' < 4 ∧ f (normBinOp4 mask op a b) = normBinOp4 mask op' (f a) (f b) := by
    have mfa : Masked mask (f a) := masked_norm (maskedTransfer hmask ma)
    have mfb : Masked mask (f b) := masked_norm (maskedTransfer hmask mb)
    have ga_rel : g a = f a ∨ g a = mask ^^^ f a := by
      rcases normWord_eq_or mask (g a) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have gb_rel : g b = f b ∨ g b = mask ^^^ f b := by
      rcases normWord_eq_or mask (g b) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have hstep : f (normBinOp4 mask op a b) = normWord mask (binOp4 mask op (g a) (g b)) := by
      rw [normBinOp4, fnrm]
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · simp [f, binOp4, g, relabelAnd]
      · simp [f, binOp4, g, relabelOr]
      · simp [f, binOp4, g, relabelAnd, hxor]
      · simp [f, binOp4, g, relabelAnd, hxor]
    rw [hstep]
    have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;> rcases ga_rel with hga | hga <;> rcases gb_rel with hgb | hgb
    · exact ⟨0, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by
        rw [hga, hgb]; change normWord mask (f a ||| (mask ^^^ f b)) = _
        have h1 : mask ^^^ ((mask ^^^ f a) &&& f b) = f a ||| (mask ^^^ f b) := by
          rw [demorgan_and (masked_xor mfa) mfb, xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by
        rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| f b) = _
        have h1 : mask ^^^ (f a &&& (mask ^^^ f b)) = (mask ^^^ f a) ||| f b := by
          rw [demorgan_and mfa (masked_xor mfb), xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| (mask ^^^ f b)) = _; rw [← demorgan_and mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask (f a &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& f b) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& (mask ^^^ f b)) = _; rw [xor_cancel_left]; rfl⟩
  induction live using LiveBin.ind with
  | stop hp =>
    rw [Finset.image_singleton]
    have hfg : f (normWord mask goal) = normWord mask goal := by
      rw [fnrm]; simp only [f, g, auto.2.2]
    change LiveBin mask goal 0 {f (normWord mask goal)}
    rw [hfg]
    exact LiveBin.stop hp
  | @step k U a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply masked_norm
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, mask ^^^ b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨mask ^^^ a, b, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have hns : ∀ w ∈ insert a (insert b U), normWord mask w = w := fun w hw =>
      (liveBinProps (LiveBin.step hop pa pb ab na nb fresh tail) w hw).2
    obtain ⟨op', hop', fve⟩ := opImage ma mb hop
    have ht := ih hnew
    have hf := freshImage fresh mv (normWord_idem mask _) masked hns
    change LiveBin mask goal (k + 1) ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveBin mask goal k (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveBin.step hop' (properF ma pa) (properF mb pb)
      (fun h => ab (injF ma mb na nb h)) (normWord_idem mask _) (normWord_idem mask _) hf ht
theorem dagLinkedBin {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRefBin mask count states moves links parent token state = true)
    {k : Nat} (live : LiveBin mask goal k state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveBin mask goal k saved.2.1.toFinset := by
  unfold dagRefBin at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination, saved, hd, eq, finish.1, ?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select, hauto, agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWordsBin mask m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSetBin (fun w hw => agree w (masked w hw))]
          exact liveBinMaskedImage hauto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))
def dagLocalBinFast (mask goal ngoal negGoal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains ngoal &&
      (fuel == 0 || cut state || !dagPartition false ws goal negGoal))
def dagLocalBin (mask goal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains (normWord mask goal) &&
      (fuel == 0 || cut state || !dagPartition false ws goal (mask ^^^ goal)))
theorem dagLocalBinFast_eq (mask goal : Word) (cut : CutCheck) (state : RowState) :
    dagLocalBinFast mask goal (normWord mask goal) (mask ^^^ goal) cut state =
      dagLocalBin mask goal cut state := rfl
theorem dagLocalBinOpen {mask goal : Word} {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (viable : BinViable mask goal state) (noCut : cut state = false) :
    dagLocalBin mask goal cut state = false := by
  obtain ⟨fuel, ws, history⟩ := state
  have ⟨nd, k, cap, live⟩ := viable
  change k ≤ fuel at cap
  have card := liveBinSize live
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨eq, _⟩ := live
    have hm : normWord mask goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocalBin, fit, hm]
  have sep := dagPartitionLiveBin masked live
  simp [dagLocalBin, fit, hz, sep, noCut]
def dagSizeFloorBin (n keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1)) + 1
def dagTooWideBin (n fuel token : Nat) : Bool :=
  dagSizeFloorBin n (token % 4) > (fuel - 1) + 1
theorem dagWideChildBin {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (wide : dagTooWideBin state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let i := token / (4 * 4 * 64)
  let j := token / (4 * 4) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := normBinOp4 mask op x y
  let a := keep.testBit 0
  let b := keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || i ≥ j
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega
def dagTagStepBin (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 4
  let x := bank.getD (token / (4 * 4 * 64)) (0, 0, 0)
  let y := bank.getD (token / (4 * 4) % 64) (0, 0, 0)
  let raw := binOp4 mask op x.1 y.1
  let comp := mask ^^^ raw
  let up0 := binOp4 full op x.2.1 y.2.1
  let dn0 := binOp4 full op x.2.2 y.2.2
  let tag := if raw < comp then (raw, up0, dn0) else (comp, full ^^^ up0, full ^^^ dn0)
  dagTagInsert tag (dagTagKeep (keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))
def dagTraceTagsBin (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStepBin mask (fullMask width) token (previous (parent - 1))) (fuel + 1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags
def dagCheckChildrenBin (mask goal : Word) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  dagForceWord (normWordFast mask goal) (fun ngoal =>
  dagForceWord (mask ^^^ goal) (fun negGoal =>
  (n ≤ 64) && !state.2.1.contains ngoal &&
  dagForceWord (dagPackWords256 state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks256 n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        treeBlock 0 n (fun a =>
          dagForceWord (state.2.1.getD a 0) (fun x =>
            dagForceWord (1 <<< (256 * a)) (fun aBit =>
              let xs := tags.getD a (0, 0)
              dagForceWord (dagSignalContrast false full xs) (fun xC =>
                treeBlock (a + 1) (n - (a + 1)) (fun b =>
                  dagForceWord (state.2.1.getD b 0) (fun y =>
                    dagForceWord (1 <<< (256 * b)) (fun bBit =>
                      let ys := tags.getD b (0, 0)
                      dagForceWord (dagSignalContrast false full ys) (fun yC =>
                        treeBlock 0 4 (fun op =>
                          dagForceWord (normBinOp4Fast mask op x y) (fun out =>
                            if out == 0 || out == mask || state.2.1.contains out then true else
                            dagForceWord (binOp4 full op xs.1 ys.1) (fun up =>
                              dagForceWord (binOp4 full op xs.2 ys.2) (fun down =>
                                dagForceWord (dagSignalContrast false full (up, down)) (fun outC =>
                                  treeBlock 0 4 (fun keep =>
                                    let ka := keep.testBit 0
                                    let kb := keep.testBit 1
                                    let nAfter := n - (if ka then 0 else 1) - (if kb then 0 else 1) + 1
                                    if Nat.blt state.1 nAfter then true
                                    else if dagSampleKill256 sample full normal xC yC outC packed marks aBit bBit out false ka kb then true
                                    else match dagDirectChildBin mask state a b op keep x y out with
                                    | none => true
                                    | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                                      let child := (fuel, forced, history)
                                      let token := gateTokenBin a b op keep
                                      reference token child || dagLocalBinFast mask goal ngoal negGoal cut child))))))))))))))))))))))
theorem dagEarlyOpenBin256 {mask goal a b op keep out : Nat} {state child : RowState}
    {sample : DagSample} (full : Word) (counts : DagCounts) (xC yC outC : Word)
    (masked : Masked mask goal) (viable : BinViable mask goal child)
    (parent : state.2.1.Nodup) (svalid : dagSampleValid mask goal sample = true)
    (eval : dagDirectChildBin mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) :
    dagSampleKill256 sample full counts xC yC outC
      (dagPackWords256 state.2.1) (dagLaneMarks256 state.2.1.length)
      (1 <<< (256 * a)) (1 <<< (256 * b)) out false (keep.testBit 0) (keep.testBit 1) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  unfold dagSampleKill256 at closed
  simp only [dagForceWordEq] at closed
  generalize hmiss :
    (((counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& (if keep.testBit 0 then 0 else xC) &&& (if keep.testBit 1 then 0 else yC))) |||
       (counts.1 ^^^ (counts.1 &&& ((if keep.testBit 0 then 0 else xC) ||| (if keep.testBit 1 then 0 else yC))))) ||| outC) ^^^ full) = missing at closed
  by_cases hm : Nat.beq missing 0 = true
  · simp only [hm, ite_true] at closed; cases closed
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ite_false] at closed
    by_cases hlt : Nat.blt (dagHighest7 missing) sample.2 = true
    · simp only [hlt, ite_true] at closed
      have hidx : dagHighest7 missing < sample.2 := Nat.blt_eq.mp hlt
      have pairOK := treeBlock_at svalid (Nat.zero_le _) (by simpa using hidx)
      have closed' := dagPackedPair256Sound parent pairOK closed
      let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
      let stale : Bool := out == 0 || out == mask || ws.contains out
      let bank := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
      change (if bad then none else if stale then none else
        some (fuel - 1, insertWord out bank, (out, x, y) :: history)) = some child at eval
      by_cases h : bad = true
      · simp [h] at eval
      by_cases h' : stale = true
      · simp [h, h'] at eval
      have eq : (fuel - 1, insertWord out bank, (out, x, y) :: history) = child := by simpa [h, h'] using eval
      subst child
      obtain ⟨nd, k, cap, live⟩ := viable
      have same : (out :: bank).toFinset = (insertWord out bank).toFinset := by
        ext w
        simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
      have refuses := dagPairsOpenBin (pairs := [unpack sample.1 18 (dagHighest7 missing)]) masked
        (show LiveBin mask goal k (out :: bank).toFinset by rwa [same])
      exact Bool.noConfusion (closed'.symm.trans refuses)
    · simp only [Bool.not_eq_true] at hlt
      simp only [hlt, Bool.false_eq_true, ite_false] at closed
theorem dagChildAtBin {mask goal : Word} {cut : CutCheck} {ref : Nat → RowState → Bool}
    {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildrenBin mask goal cut ref state sample tags = true)
    (svalid : dagSampleValid mask goal sample = true)
    (ha : a < state.2.1.length) (hab : a < b) (hb : b < state.2.1.length) (hop : op < 4) (hk : keep < 4)
    (eval : childStateBin mask (gateTokenBin a b op keep) state = some child)
    (masked : Masked mask goal) (viable : BinViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocalBin mask goal cut child = false) :
    ref (gateTokenBin a b op keep) child = true := by
  have narrow : Nat.blt state.1 (state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hlt : state.1 < state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1 := Nat.blt_eq.mp h
    have hb64 : b < 64 := by
      simp only [dagCheckChildrenBin, dagForceWordEq, dagForceCacheEq, dagCountSignsEq, normWordFast_eq,
        Bool.and_eq_true, decide_eq_true_eq] at checked
      omega
    obtain ⟨ke, _, _, _⟩ := gateTokenBinFields (a := a) hb64 hop hk
    have hpos : 0 < state.1 := by
      rcases state with ⟨sf, sws, shist⟩
      by_contra! hz
      have h0 : sf = 0 := by omega
      subst h0
      simp [childStateBin] at eval
    have hwide : dagTooWideBin state.2.1.length state.1 (gateTokenBin a b op keep) = true := by
      simp only [dagTooWideBin, dagSizeFloorBin, ke, decide_eq_true_eq]
      omega
    have tooMany := dagWideChildBin eval hwide
    obtain ⟨f, w, path⟩ := child
    simp [dagLocalBin, tooMany] at openChild
  simp only [dagCheckChildrenBin, dagForceCacheEq, dagForceWordEq, dagCountSignsEq, normWordFast_eq, normBinOp4Fast_eq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  have atB := treeBlock_at atA (i := b) (by omega) (by omega)
  have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
  have fields := dagDirectChildBinEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
    (keep := keep) (by omega) hop hk
  have direct := fields.trans eval
  have notStale : (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == 0 ||
      normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == mask ||
      state.2.1.contains (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0))) = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    rcases state with ⟨f, ws, hist⟩
    dsimp only [dagDirectChildBin] at hs direct
    by_cases hbad : (f == 0 || b ≥ ws.length || a ≥ b) = true
    · simp only [hbad, ite_true] at direct; cases direct
    · simp only [Bool.not_eq_true] at hbad
      simp only [hbad, Bool.false_eq_true, ite_false, hs, ite_true] at direct
      cases direct
  simp only [notStale, Bool.false_eq_true, ite_false] at atOp
  have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
  have early := fun full counts xC yC outC => dagEarlyOpenBin256 full counts xC yC outC masked viable nd svalid direct
  rcases child with ⟨fuel, ws, history⟩
  simpa only [narrow, Bool.false_eq_true, ite_false, fields, eval, dagForceWordsEq, early,
    dagLocalBinFast_eq, openChild, Bool.or_false] using atKeep
def HasChildBin (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧ a < b ∧ b < state.2.1.length ∧ op < 4 ∧ keep < 4 ∧
    childStateBin mask (gateTokenBin a b op keep) state = some child
theorem binaryChildBin {mask fuel a b op : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (hop : op < 4) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (normBinOp4 mask op x y)) (fresh : normBinOp4 mask op x y ∉ ws) :
    childStateBin mask (gateTokenBin a b op keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (normBinOp4 mask op x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (normBinOp4 mask op x y, x, y) :: history) := by
  obtain ⟨ke, ope, aa, bb⟩ := gateTokenBinFields (a := a) hb64 hop hk
  simp only [childStateBin, ke, ope, aa, bb, hx, hy]
  simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, properWord]
theorem stepProgressBin {mask fuel k op : Nat} {x y target : Word} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel) (hop : op < 4)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : normBinOp4 mask op x y ∉ insert x (insert y U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op x y) U)) :
    ∃ child, HasChildBin mask (fuel, ws, history) child ∧ BinViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := normBinOp4 mask op x y
  have p := (liveBinProps tail v (Finset.mem_insert_self _ _)).1
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep; cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, op, keep, ha, hab, hb, hop, keepLt, ?_⟩, ?_⟩
  · have eq := binaryChildBin (fuel := fuel) (history := history) hop hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveBin mask target k (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail
theorem wordProgressBin {mask target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : BinViable mask target state) :
    normWord mask target ∈ state.2.1 ∨ ∃ child, HasChildBin mask state child ∧ BinViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨eq, _⟩ := live
    left
    change ws.toFinset = {normWord mask target} at eq
    rw [← List.mem_toFinset, eq]; simp
  | succ k =>
    right
    obtain ⟨U, x, y, op, hop, eq, px, py, xy, nx, ny, fresh, tail⟩ := live
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same; apply xy; rw [← getWord xm, same, getWord ym]
    by_cases hord : ws.idxOf x < ws.idxOf y
    · exact stepProgressBin nd width cap hop eq xy hord fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : normBinOp4 mask (swapOp4 op) y x ∉ insert y (insert x U) := by
        rw [normBinOp4_swap mask hop, Finset.insert_comm]; exact fresh
      have tail' : LiveBin mask target k (insert (normBinOp4 mask (swapOp4 op) y x) U) := by
        rw [normBinOp4_swap mask hop]; exact tail
      exact stepProgressBin nd width cap (swapOp4_lt hop) eq' xy.symm (by omega) fresh' tail'
theorem childStateBinData {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let a := token / (4 * 4 * 64)
  let b := token / (4 * 4) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := normBinOp4 mask op x y
  let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega, ?_⟩
  have mx : Masked mask x := readWordMasked masked a
  have my : Masked mask y := readWordMasked masked b
  have hm : Masked mask z := by
    apply masked_norm
    unfold binOp4
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, mask ^^^ y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨mask ^^^ x, y, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (keep.testBit 1) y _ w other
def dagCheckNodeBin (mask goal : Word) (nodeBounds : Nat → List Bound)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (linkList : DagLinkList)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) =>
    dagForceWord goal (fun goal' =>
      dagFilterForceBoundsBin goal' (nodeBounds i) (fun activeBounds =>
        dagForceLinkList (linkList (i + 1)) (fun nlinks =>
          dagForceWords ws (fun forced =>
            dagStateOK mask forced && dagCheckChildrenBin mask goal' (dagKnownClosesBinNoHdr activeBounds)
              (dagRefBin mask count states moves (fun _ tok => dagFindLink nlinks tok) 0)
              (fuel, forced, history) sample (tags i)))))
def dagAllowedRootBin (mask : Word) (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (normWord mask (witnessWord entry)))
def dagCheckRootsBin (mask goal : Word) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (nstock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ nstock.length) fun token =>
    let state := rootState nstock fuel token
    !dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal cut state || reference token state
theorem dagAllNodesBin {mask goal : Word} {width fuel count : Nat}
    {nstock : List Word} {nodeBounds : Nat → List Bound} {forest : Forest} {moves : Array WordMove}
    {linkList : DagLinkList} {sample : DagSample} {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (cutSound : ∀ i s, BinViable mask goal s →
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds count
      (dagTraceBin mask nstock fuel forest) moves linkList sample tags) = true) :
    ∀ cap i saved, i < count → dagTraceBin mask nstock fuel forest i = some saved →
      saved.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTraceBin mask nstock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNodeBin mask goal nodeBounds count states moves linkList sample tags i = true at checked
    simp only [dagCheckNodeBin, stateEq, dagForceWordEq, dagFilterForceBoundsBinEq, dagForceLinkListEq,
      dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd, masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : BinViable mask goal s := ⟨nd, k, sFuel ▸ kBound, live⟩
    have scanned := ok
    simp only [dagCheckChildrenBin, dagForceWordEq, normWordFast_eq, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgressBin wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a, b, op, keep, ha, hab, hb, hop, hk, eval⟩ := possible
    have r := dagChildAtBin ok svalid ha hab hb hop hk eval goalMask cv nd
      (dagLocalBinOpen goalMask cv (cutSound i _ cv))
    have ⟨less, cm⟩ := childStateBinData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_, k', fits, clive⟩ := cv
    obtain ⟨j, dest, bound, restore, fuelEq, tail⟩ := dagLinkedBin maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' fits tail
theorem lowerDagBin {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {forest : Forest} {moves : Array WordMove} {linkList : DagLinkList}
    {sample : DagSample} {tags : Nat → List DagSignals}
    {bounds : List Bound} {nodeBounds : Nat → List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w)
    (nstockNd : (normStock mask stock).Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : KnownBin bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nodeSub : ∀ i b, b ∈ nodeBounds i → b ∈ bounds)
    (rootCheck : dagCheckRootsBin mask goal (dagKnownClosesBin goal bounds) witnesses
      (dagRefBin mask count (dagTraceBin mask (normStock mask stock) fuel forest) moves
        (fun p tok => dagFindLink (linkList p) tok) 0)
      (normStock mask stock) fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds
      count (dagTraceBin mask (normStock mask stock) fuel forest) moves linkList sample tags) = true) :
    BinLower mask stock goal (fuel + 1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive stockMasked build hit proper
  let nstock := normStock mask stock
  have included : S ⊆ nstock.toFinset := by
    intro w hw
    rw [normStockSet, List.mem_toFinset]
    exact sub w hw
  obtain ⟨token, tokenBound, eq⟩ := rootToken nstock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState nstock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : BinViable mask goal state := by
    refine ⟨(rootWordSublist nstock token).nodup nstockNd, k, ?_, ?_⟩
    · change k ≤ fuel; omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : BinViable mask goal s) : dagKnownClosesBin goal bounds s = false :=
    knownClosesBinSound known submasks h
  have nodeCutOpen (i : Nat) (s : RowState) (h : BinViable mask goal s) :
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false :=
    knownClosesBinNoHdrSound
      (fun b hb => known b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => submasks b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => (List.mem_filter.mp hb).2) h
  have openRoot := dagLocalBinOpen goalMask v (cutOpen _ v)
  have allowed : dagAllowedRootBin mask witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequiredBin (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) state ||
    dagRefBin mask count (dagTraceBin mask nstock fuel forest) moves
      (fun p tok => dagFindLink (linkList p) tok) 0 token state) = true at checked
  simp only [allowed, openRoot, Bool.not_true, Bool.false_or] at checked
  have finish := dagAllNodesBin maskBounds goalMask svalid nodeCutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveBin mask goal k state.2.1.toFinset := by rwa [eq']
  have nstockMasked : ∀ w ∈ nstock, Masked mask w := by
    intro w hw
    have h1 : w ∈ nstock.toFinset := List.mem_toFinset.mpr hw
    rw [normStockSet, List.mem_toFinset] at h1
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp h1
    exact masked_norm (stockMasked orig omem)
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact nstockMasked _ ((rootWordSublist nstock token).subset hw)
  obtain ⟨i, s, hi, restore, cap, plan⟩ := dagLinkedBin maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k fits plan
theorem hcsGateWordMono {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    GateWordMono (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) := Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
def isNotOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.not => true
  | _ => false
def countNonNot : List PEqualNP.CircuitLowerBounds.Gate → Nat
  | [] => 0
  | g :: rest => (if isNotOp g.op then 0 else 1) + countNonNot rest
theorem countNonNot_le_sub {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (h : ∃ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) :
    countNonNot gs + 1 ≤ gs.length := by
  induction gs with
  | nil => obtain ⟨_, hm, _⟩ := h; simp at hm
  | cons g gs ih =>
    have hle : ∀ l, countNonNot l ≤ l.length := by
      intro l; induction l with
      | nil => simp [countNonNot]
      | cons x xs ihx => simp only [countNonNot, List.length_cons]; cases isNotOp x.op <;> simp <;> omega
    obtain ⟨g', hm, hop⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [countNonNot, hop, isNotOp, ite_true, Nat.zero_add, List.length_cons]
      have := hle gs; omega
    · have := ih ⟨g', hm, hop⟩
      simp only [countNonNot, List.length_cons]
      cases isNotOp g.op <;> simp <;> omega
theorem hcsBuildsBin {rows : Nat} (raw : List (BitVec rows)) (bank : List Word)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (sub0 : ∀ v ∈ raw, AvBin (fullMask rows) bank v.toNat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length ≤ countNonNot gs ∧ WordBuildsBin (fullMask rows) bank vs ∧
      ∀ v ∈ gs.foldl hcsStep raw, AvBin (fullMask rows) (vs ++ bank) v.toNat := by
  induction gs generalizing raw bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, fun v hv => sub0 v hv⟩
  | cons g gs ih =>
    let v := hcsGateVal raw g
    have hg := hfan g List.mem_cons_self
    have hop := hg.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have avRaw (i : Nat) : AvBin (fullMask rows) bank (raw.getD i 0).toNat := by
      rw [List.getD_eq_getElem?_getD]
      cases h : raw[i]? with
      | none => exact Or.inl rfl
      | some a => exact sub0 a (List.mem_of_getElem? h)
    rcases hop with h_and | h_or | h_not
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inl h_and) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_and, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inr h_or) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_or, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have hv : AvBin (fullMask rows) bank v.toNat := by
        obtain ⟨op, ins⟩ := g
        simp only at h_not; subst op
        cases ins with
        | nil =>
          have : v.toNat = fullMask rows ^^^ 0 := by simpa [v, hcsGateVal] using notNat (0 : BitVec rows)
          rw [this]; exact avBin_not (Or.inl rfl)
        | cons a _ =>
          have : v.toNat = fullMask rows ^^^ (raw.getD a 0).toNat := by
            simpa [v, hcsGateVal] using notNat (raw.getD a 0)
          rw [this]; exact avBin_not (avRaw a)
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) bank u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact sub0 u hu
        · exact hv
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) bank sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨xs, ?_, built, reach⟩
      simp only [countNonNot, h_not, isNotOp, ite_true, Nat.zero_add]; exact len

def memB (l : List Word) (x : Word) : Bool :=
  List.rec false (fun a _ r => Nat.beq x a || r) l
theorem natBeqEq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · have hne : a ≠ b := Nat.ne_of_beq_eq_false h
    simp [hne]
  · have he : a = b := Nat.eq_of_beq_eq_true h
    simp [he]
theorem memBEq (l : List Word) (x : Word) : memB l x = l.contains x := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change (Nat.beq x a || memB t x) = (a :: t).contains x
    rw [ih, natBeqEq, List.contains_cons]
def availFast (bank : List Word) (v : Word) : Bool :=
  Nat.beq v 0 || memB bank v
theorem availFastEq (bank : List Word) (v : Word) : availFast bank v = availableNormB bank v := by
  simp only [availFast, availableNormB, natBeqEq, memBEq]
def maskFlatFast (mask word : Word) : Bool :=
  dagForceWord (word &&& mask) (fun v => Nat.beq v 0 || Nat.beq v mask)
theorem maskFlatFastEq (mask word : Word) : maskFlatFast mask word = maskFlatF mask word := by
  simp only [maskFlatFast, maskFlatF, natBeqEq]
def flatCountFast (mask : Word) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlatFast mask word then count + 1 else count) words
theorem flatCountFastEq (mask : Word) (words : List Word) : flatCountFast mask words = flatCountF mask words := by
  simp only [flatCountFast, flatCountF, maskFlatFastEq]
def stockWordFast (mask : Word) (nstock needed : List Word) (word : Word) : List Word :=
  dagForceWord (normWordFast mask (word &&& mask)) (fun v =>
    if availFast nstock v || memB needed v then needed else v :: needed)
theorem stockWordFastEq (mask : Word) (nstock needed : List Word) (word : Word) :
    stockWordFast mask nstock needed word = stockWordBinF mask nstock needed word := by
  simp only [stockWordFast, stockWordBinF, availFastEq, memBEq]
def recipeStartFast (mask : Word) (nstock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordFast mask nstock seen word)) words) []
theorem recipeStartFastEq (mask : Word) (nstock words : List Word) :
    recipeStartFast mask nstock words = recipeStartBinF mask nstock words := by
  simp only [recipeStartFast, recipeStartBinF, stockWordFastEq]
def recipeClosureFast (mask : Word) (nstock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (dagForceWord (normWordFast mask (out &&& mask)) (fun vo =>
        if memB seen vo then
          stockWordFast mask nstock (stockWordFast mask nstock seen a) b else seen)))
    history start
theorem recipeClosureFastEq (mask : Word) (nstock : List Word) (history : List (Word × Word × Word))
    (start : List Word) :
    recipeClosureFast mask nstock history start = recipeClosureBinF mask nstock history start := by
  simp only [recipeClosureFast, recipeClosureBinF, stockWordFastEq, memBEq]
def recipeGateFast (mask : Word) (nbank : List Word) (v ma mb : Word) : Bool :=
  availFast nbank (normWordFast mask ma) && availFast nbank (normWordFast mask mb) &&
    (Nat.beq v (normWordFast mask (ma &&& mb)) || Nat.beq v (normWordFast mask (ma ||| mb)) ||
     Nat.beq v (normWordFast mask (ma &&& (mask ^^^ mb))) || Nat.beq v (normWordFast mask ((mask ^^^ ma) &&& mb)))
theorem recipeGateFastEq (mask : Word) (nbank : List Word) (v ma mb : Word) :
    recipeGateFast mask nbank v ma mb = recipeGateBinNorm mask nbank v ma mb := by
  simp only [recipeGateFast, recipeGateBinNorm, availFastEq, natBeqEq]
def replayFast (mask : Word) (needed : List Word) : List (Word × Word × Word) → List Word → List Word
  | [], _ => []
  | (w, a, b) :: rs, nbank =>
      dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
        if memB needed v && !availFast nbank v then
          dagForceWord (a &&& mask) (fun ma =>
            dagForceWord (b &&& mask) (fun mb =>
              if recipeGateFast mask nbank v ma mb then
                v :: replayFast mask needed rs (v :: nbank)
              else replayFast mask needed rs nbank))
        else replayFast mask needed rs nbank)
theorem replayFastEq (mask : Word) (needed : List Word) :
    ∀ (rs : List (Word × Word × Word)) (nbank : List Word),
      replayFast mask needed rs nbank = replayRecipesBinF mask needed rs nbank := by
  intro rs
  induction rs with
  | nil => intro nbank; rfl
  | cons r rs ih =>
    intro nbank
    obtain ⟨w, a, b⟩ := r
    simp only [replayFast, replayRecipesBinF, memBEq, availFastEq, recipeGateFastEq, ih]
def boundClosesFast (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, _) := bound
  let (fuel, ws, history) := state
  dagForceWord (fuel - flatCountFast mask ws) (fun remaining =>
    if Nat.blt remaining lower then
      dagForceWords (recipeStartFast mask nstock ws) (fun start =>
        if Nat.blt (start.length + remaining) lower then
          dagForceWords (recipeClosureFast mask nstock history start) (fun needed =>
            if Nat.blt (needed.length + remaining) lower then
              dagForceWords (replayFast mask needed history.reverse nstock) (fun replay =>
                Nat.blt (replay.length + remaining) lower &&
                  dagForceWords (replay ++ nstock) (fun bank =>
                    ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                      availFast bank v))))
            else false)
        else false)
    else false)
theorem boundClosesFastEq (state : RowState) (bound : Bound) :
    boundClosesFast state bound = dagBoundClosesBinNoHdr state bound := by
  simp only [boundClosesFast, dagBoundClosesBinNoHdr, flatCountFastEq, recipeStartFastEq,
    recipeClosureFastEq, replayFastEq, availFastEq, dagForceWordsEq]
def knownClosesFast (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => boundClosesFast state bound || later) bounds
theorem knownClosesFastEq (bounds : List Bound) :
    knownClosesFast bounds = dagKnownClosesBinNoHdr bounds := by
  funext state
  simp only [knownClosesFast, dagKnownClosesBinNoHdr, boundClosesFastEq]
def dagLocalFast (_mask goal ngoal negGoal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!memB ws ngoal &&
      (Nat.beq fuel 0 || cut state || !dagPartition false ws goal negGoal))
theorem dagLocalFastEq (mask goal ngoal negGoal : Word) (cut : CutCheck) (state : RowState) :
    dagLocalFast mask goal ngoal negGoal cut state = dagLocalBinFast mask goal ngoal negGoal cut state := by
  simp only [dagLocalFast, dagLocalBinFast, memBEq, natBeqEq]
def dagDirectChildFast (mask : Word) (state : RowState) (a b _op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else if Nat.beq out 0 || Nat.beq out mask || memB ws out then none
  else
    let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    some (fuel - 1, insertWord out rest, (out, x, y) :: history)
theorem dagDirectChildFastEq (mask : Word) (state : RowState) (a b op keep x y out : Nat) :
    dagDirectChildFast mask state a b op keep x y out = dagDirectChildBin mask state a b op keep x y out := by
  simp only [dagDirectChildFast, dagDirectChildBin, memBEq, natBeqEq]
theorem bitAgree (out p n : Nat) :
    Nat.beq (((out >>> p) ^^^ (out >>> n)) &&& 1) 0 = (out.testBit p == out.testBit n) := by
  have hp : out.testBit p = (out >>> p).testBit 0 := by simp
  have hn : out.testBit n = (out >>> n).testBit 0 := by simp
  rw [hp, hn, natBeqEq]
  generalize out >>> p = a
  generalize out >>> n = b
  have hx : ((a ^^^ b) &&& 1) = if (a.testBit 0 ^^ b.testBit 0) then 1 else 0 := by
    rw [← Nat.testBit_xor, Nat.and_one_is_mod, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one (a ^^^ b) with h | h <;> simp [h]
  rw [hx]
  cases a.testBit 0 <;> cases b.testBit 0 <;> rfl
def ppF (packed marks erased out : Word) (code : Nat) : Bool :=
  dagForceWord (code &&& 511) (fun p =>
    dagForceWord (code >>> 9) (fun n =>
      Nat.beq (((out >>> p) ^^^ (out >>> n)) &&& 1) 0 &&
        Nat.beq ((((packed >>> p) ^^^ (packed >>> n)) &&& marks) &&& (marks ^^^ erased)) 0))
theorem ppFEq (packed marks erased out : Word) (code : Nat) :
    ppF packed marks erased out code = dagPackedPair256 packed marks erased out false code := by
  simp only [ppF, dagPackedPair256, dagForceWordEq, Bool.false_eq_true, ↓reduceIte]
  rw [bitAgree, Nat.and_xor_distrib_right]
def skF (sample : DagSample) (full : Word) (counts : DagCounts)
    (xC yC outC packed marks aBit bBit out : Word) (ka kb : Bool) : Bool :=
  let dx := if ka then 0 else xC
  let dy := if kb then 0 else yC
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| outC) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then false
    else dagForceWord (dagHighest7 missing) (fun idx =>
      if Nat.blt idx sample.2 then
        dagForceWord (unpack sample.1 18 idx) (fun code =>
          ppF packed marks (dagOmitted256 aBit bBit ka kb) out code)
      else false))
theorem skFEq (sample : DagSample) (full : Word) (counts : DagCounts)
    (xC yC outC packed marks aBit bBit out : Word) (ka kb : Bool) :
    skF sample full counts xC yC outC packed marks aBit bBit out ka kb =
      dagSampleKill256 sample full counts xC yC outC packed marks aBit bBit out false ka kb := by
  simp only [skF, dagSampleKill256, ppFEq]
def dagCheckChildrenFast (mask goal : Word) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  dagForceWord (normWordFast mask goal) (fun ngoal =>
  dagForceWord (mask ^^^ goal) (fun negGoal =>
  (n ≤ 64) && !memB state.2.1 ngoal &&
  dagForceWord (dagPackWords256 state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks256 n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        treeBlock 0 n (fun a =>
          dagForceWord (state.2.1.getD a 0) (fun x =>
            dagForceWord (1 <<< (256 * a)) (fun aBit =>
              let xs := tags.getD a (0, 0)
              dagForceWord (dagSignalContrast false full xs) (fun xC =>
                treeBlock (a + 1) (n - (a + 1)) (fun b =>
                  dagForceWord (state.2.1.getD b 0) (fun y =>
                    dagForceWord (1 <<< (256 * b)) (fun bBit =>
                      let ys := tags.getD b (0, 0)
                      dagForceWord (dagSignalContrast false full ys) (fun yC =>
                        treeBlock 0 4 (fun op =>
                          dagForceWord (normBinOp4Fast mask op x y) (fun out =>
                            if Nat.beq out 0 || Nat.beq out mask || memB state.2.1 out then true else
                            dagForceWord (binOp4 full op xs.1 ys.1) (fun up =>
                              dagForceWord (binOp4 full op xs.2 ys.2) (fun down =>
                                dagForceWord (dagSignalContrast false full (up, down)) (fun outC =>
                                  treeBlock 0 4 (fun keep =>
                                    let ka := keep.testBit 0
                                    let kb := keep.testBit 1
                                    let nAfter := n - (if ka then 0 else 1) - (if kb then 0 else 1) + 1
                                    if Nat.blt state.1 nAfter then true
                                    else if skF sample full normal xC yC outC packed marks aBit bBit out ka kb then true
                                    else match dagDirectChildFast mask state a b op keep x y out with
                                    | none => true
                                    | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                                      let child := (fuel, forced, history)
                                      let token := gateTokenBin a b op keep
                                      reference token child || dagLocalFast mask goal ngoal negGoal cut child))))))))))))))))))))))
theorem dagCheckChildrenFastEq (mask goal : Word) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) :
    dagCheckChildrenFast mask goal cut reference state sample tags =
      dagCheckChildrenBin mask goal cut reference state sample tags := by
  simp only [dagCheckChildrenFast, dagCheckChildrenBin, memBEq, natBeqEq, dagDirectChildFastEq, dagLocalFastEq, skFEq]
def dagCheckNodeFast (mask goal : Word) (nodeBounds : Nat → List Bound)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (linkList : DagLinkList)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) =>
    dagForceWord goal (fun goal' =>
      dagFilterForceBoundsBin goal' (nodeBounds i) (fun activeBounds =>
        dagForceLinkList (linkList (i + 1)) (fun nlinks =>
          dagForceWords ws (fun forced =>
            dagStateOK mask forced && dagCheckChildrenFast mask goal' (knownClosesFast activeBounds)
              (dagRefBin mask count states moves (fun _ tok => dagFindLink nlinks tok) 0)
              (fuel, forced, history) sample (tags i)))))
theorem dagCheckNodeFastEq (mask goal : Word) (nodeBounds : Nat → List Bound)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (linkList : DagLinkList)
    (sample : DagSample) (tags : Nat → List DagSignals) :
    dagCheckNodeFast mask goal nodeBounds count states moves linkList sample tags =
      dagCheckNodeBin mask goal nodeBounds count states moves linkList sample tags := by
  funext i
  simp only [dagCheckNodeFast, dagCheckNodeBin, dagCheckChildrenFastEq, knownClosesFastEq]

end PEqualNP.Outside.L_meta_34788.Contraction

namespace PEqualNP.Outside.L_meta_34788.Cert
open PEqualNP.Outside.L_meta_34788.Contraction

def qS0 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def qS1 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def qS2 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def qS3 : WordMoveStep := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def qS4 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def qS5 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def qS6 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def qS7 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def qS8 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def qS9 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def qS10 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def qS11 : WordMoveStep := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def qS12 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def qS13 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def qS14 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 4)])
def qS15 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 16)])
def qS16 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 64)])
def qS17 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 1)])
def qS18 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 8)])
def qS19 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def qS20 : WordMoveStep := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0)], [(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 32)])
def qS21 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def qS22 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 0)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def qS23 : WordMoveStep := ([(0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555, 0), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x5555000055550000555500005555000055550000555500005555000055550000, 15)])
def qS24 : WordMoveStep := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def qS25 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def qS26 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 16)], [])
def qS27 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 4)], [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 4)])
def qS28 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def qS29 : WordMoveStep := ([(0xffffffffffffffffffffffffffffffff, 0)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])
def qS30 : WordMoveStep := ([(0x5555555555555555555555555555555555555555555555555555555555555555, 1)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 1)])
def qS31 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def qS32 : WordMoveStep := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 32)], [(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 32)])
def qS33 : WordMoveStep := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def qS34 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def qS35 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000, 120)])
def qS36 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def qS37 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 64)], [])
def qS38 : WordMoveStep := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def qS39 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def qS40 : WordMoveStep := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333, 0), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0x3333333333333333000000000000000033333333333333330000000000000000, 62)])
def qS41 : WordMoveStep := ([(0x3333333333333333333333333333333333333333333333333333333333333333, 2)], [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 2)])
def qS42 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 60)])
def qS43 : WordMoveStep := ([(0x3333333333333333333333333333333333333333333333333333333333333333, 0)], [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 2)])
def qS44 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff, 0), (0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000, 112)])
def qS45 : WordMoveStep := ([(0xcccccccccccccccccccccccccccccccc33333333333333333333333333333333, 0), (0xcccccccccccccccccccccccccccccccc, 126)], [(0x3333333333333333333333333333333300000000000000000000000000000000, 126)])
def qBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def qGoal : Word := 0xfffffffffffffffffffffffffffefffefffffffefffffefcffeeffeeeeccaa00
def q0M : Word := 0x30300000303
abbrev q0G : Word := qGoal &&& q0M
abbrev q0W : List Word := projectDAGStock q0M qBase [0, 3, 5]
def q0F : Bound := (q0M, q0W, 4, q0G)
def q0E := unpackWitnesses q0W [16928, 282656, 544776]
abbrev q0N : List Word := normStock q0M q0W
def q0C : List Bound := []
def q0S : DagSample := (0x40244021008840209100a01028, 6)
def q0L : DagLinkList := dagExtractLinks 0x9 0x7 2 1 3 1 1
def q0D : Forest := fun i => decodeNode 1 4 0xe i
def q0T := dagTraceTagsBin q0M 6 (dagTagBases q0N 0x3624 0x337ad 6) 3 q0D
def q0St := dagTraceBin q0M q0N 3 q0D
def q0Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0A : DagMovesOK q0M q0G 256 q0Mv := dagMovesOfCheck (by decide +kernel)
def q0NB : Nat → List Bound := dagNodeBounds q0C.toArray 0x0 0x0 2 1 1
def q0Ck := dagCheckNodeFast q0M q0G q0NB 1 q0St q0Mv q0L q0S q0T
def q0RA (token : Nat) : Bool :=
  let s := rootState q0N 3 token
  !dagAllowedRootBin q0M q0E s.2.1 || dagLocalBin q0M q0G (dagKnownClosesBin q0G q0C) s ||
  dagRefBin q0M 1 q0St q0Mv (fun p tok => dagFindLink (q0L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0RB0 : treeBlock 0 8 q0RA = true := by decide +kernel
theorem q0R : dagCheckRootsBin q0M q0G (dagKnownClosesBin q0G q0C) q0E (dagRefBin q0M 1 q0St q0Mv (fun p tok => dagFindLink (q0L p) tok) 0) q0N 3 = true := q0RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0B0 : treeBlock 0 1 q0Ck = true := by decide +kernel
theorem q0Bf : treeBlock 0 1 q0Ck = true := q0B0
theorem q0Bk : treeBlock 0 1 (dagCheckNodeBin q0M q0G q0NB 1 q0St q0Mv q0L q0S q0T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q0Bf
theorem q0K : KnownBin q0C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0Bin : BinLower q0M q0W q0G 4 := by
  apply lowerDagBin _ _ _ _ q0A _ _ _ q0K _ (fun _ b hb => dagNodeBounds_mem b hb) q0R q0Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q0C.all (fun b => q0M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q1M : Word := 0xf0f00
abbrev q1G : Word := qGoal &&& q1M
abbrev q1W : List Word := projectDAGStock q1M qBase [0, 1, 3]
def q1E := unpackWitnesses q1W [5642, 271889, 533514]
abbrev q1N : List Word := normStock q1M q1W
def q1C : List Bound := []
def q1S : DagSample := (0x1009080481409088241412, 5)
def q1L : DagLinkList := dagExtractLinks 0x9 0x7 2 1 3 1 1
def q1D : Forest := fun i => decodeNode 1 4 0xe i
def q1T := dagTraceTagsBin q1M 5 (dagTagBases q1N 0x26d6 0x7755 5) 2 q1D
def q1St := dagTraceBin q1M q1N 2 q1D
def q1Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1A : DagMovesOK q1M q1G 256 q1Mv := dagMovesOfCheck (by decide +kernel)
def q1NB : Nat → List Bound := dagNodeBounds q1C.toArray 0x0 0x0 2 1 1
def q1Ck := dagCheckNodeFast q1M q1G q1NB 1 q1St q1Mv q1L q1S q1T
def q1RA (token : Nat) : Bool :=
  let s := rootState q1N 2 token
  !dagAllowedRootBin q1M q1E s.2.1 || dagLocalBin q1M q1G (dagKnownClosesBin q1G q1C) s ||
  dagRefBin q1M 1 q1St q1Mv (fun p tok => dagFindLink (q1L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1RB0 : treeBlock 0 8 q1RA = true := by decide +kernel
theorem q1R : dagCheckRootsBin q1M q1G (dagKnownClosesBin q1G q1C) q1E (dagRefBin q1M 1 q1St q1Mv (fun p tok => dagFindLink (q1L p) tok) 0) q1N 2 = true := q1RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1B0 : treeBlock 0 1 q1Ck = true := by decide +kernel
theorem q1Bf : treeBlock 0 1 q1Ck = true := q1B0
theorem q1Bk : treeBlock 0 1 (dagCheckNodeBin q1M q1G q1NB 1 q1St q1Mv q1L q1S q1T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q1Bf
theorem q1K : KnownBin q1C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1Bin : BinLower q1M q1W q1G 3 := by
  apply lowerDagBin _ _ _ _ q1A _ _ _ q1K _ (fun _ b hb => dagNodeBounds_mem b hb) q1R q1Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q1C.all (fun b => q1M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q2M : Word := 0x500050000000000050005
abbrev q2G : Word := qGoal &&& q2M
abbrev q2W : List Word := projectDAGStock q2M qBase [1, 4, 6]
def q2F : Bound := (q2M, q2W, 4, q2G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q2Bin : BinLower q2M q2W q2G 4 := dagShiftLowerBin (width := 256) [qS0, qS1, qS2] q0Bin (by decide +kernel)
def q3M : Word := 0x30300000000000000000000000000000303
abbrev q3G : Word := qGoal &&& q3M
abbrev q3W : List Word := projectDAGStock q3M qBase [0, 3, 7]
def q3F : Bound := (q3M, q3W, 4, q3G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q3Bin : BinLower q3M q3W q3G 4 := dagShiftLowerBin (width := 256) [qS3, qS4] q0Bin (by decide +kernel)
def q4M : Word := 0x30000000300000000000000000000000300000003
abbrev q4G : Word := qGoal &&& q4M
abbrev q4W : List Word := projectDAGStock q4M qBase [0, 5, 7]
def q4F : Bound := (q4M, q4W, 4, q4G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q4Bin : BinLower q4M q4W q4G 4 := dagShiftLowerBin (width := 256) [qS5, qS6, qS3, qS4] q0Bin (by decide +kernel)
def q5M : Word := 0x50000000500000000000000000000000500000005
abbrev q5G : Word := qGoal &&& q5M
abbrev q5W : List Word := projectDAGStock q5M qBase [1, 5, 7]
def q5F : Bound := (q5M, q5W, 4, q5G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5Bin : BinLower q5M q5W q5G 4 := dagShiftLowerBin (width := 256) [qS0, qS5, qS6, qS3, qS4] q0Bin (by decide +kernel)
def q6M : Word := 0x1010000010100000000000000000000010100000101
abbrev q6G : Word := qGoal &&& q6M
abbrev q6W : List Word := projectDAGStock q6M qBase [3, 5, 7]
def q6F : Bound := (q6M, q6W, 4, q6G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6Bin : BinLower q6M q6W q6G 4 := dagShiftLowerBin (width := 256) [qS7, qS8, qS9, qS5, qS6, qS3, qS4] q0Bin (by decide +kernel)
def q7M : Word := 0x5000000000000000500000000000000050000000000000005
abbrev q7G : Word := qGoal &&& q7M
abbrev q7W : List Word := projectDAGStock q7M qBase [1, 6, 7]
def q7F : Bound := (q7M, q7W, 4, q7G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q7Bin : BinLower q7M q7W q7G 4 := dagShiftLowerBin (width := 256) [qS0, qS10, qS11, qS3] q0Bin (by decide +kernel)
def q8M : Word := 0x11000000000000001100000000000000110000000000000011
abbrev q8G : Word := qGoal &&& q8M
abbrev q8W : List Word := projectDAGStock q8M qBase [2, 6, 7]
def q8F : Bound := (q8M, q8W, 4, q8G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8Bin : BinLower q8M q8W q8G 4 := dagShiftLowerBin (width := 256) [qS12, qS13, qS10, qS11, qS3] q0Bin (by decide +kernel)
def q9M : Word := 0x303000003030
abbrev q9G : Word := qGoal &&& q9M
abbrev q9W : List Word := projectDAGStock q9M qBase [0, 3, 5]
def q9F : Bound := (q9M, q9W, 4, q9G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q9Bin : BinLower q9M q9W q9G 4 := dagShiftLowerBin (width := 256) [qS14] q0Bin (by decide +kernel)
def q10M : Word := 0x303000003030000
abbrev q10G : Word := qGoal &&& q10M
abbrev q10W : List Word := projectDAGStock q10M qBase [0, 3, 5]
def q10F : Bound := (q10M, q10W, 4, q10G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q10Bin : BinLower q10M q10W q10G 4 := dagShiftLowerBin (width := 256) [qS15] q0Bin (by decide +kernel)
def q11M : Word := 0x303000003030000000000000000
abbrev q11G : Word := qGoal &&& q11M
abbrev q11W : List Word := projectDAGStock q11M qBase [0, 3, 5]
def q11F : Bound := (q11M, q11W, 4, q11G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q11Bin : BinLower q11M q11W q11G 4 := dagShiftLowerBin (width := 256) [qS16] q0Bin (by decide +kernel)
def q12M : Word := 0xa000a00000000000a000a
abbrev q12G : Word := qGoal &&& q12M
abbrev q12W : List Word := projectDAGStock q12M qBase [1, 4, 6]
def q12F : Bound := (q12M, q12W, 4, q12G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12Bin : BinLower q12M q12W q12G 4 := dagShiftLowerBin (width := 256) [qS17, qS0, qS1, qS2] q0Bin (by decide +kernel)
def q13M : Word := 0x50005000000000005000500
abbrev q13G : Word := qGoal &&& q13M
abbrev q13W : List Word := projectDAGStock q13M qBase [1, 4, 6]
def q13F : Bound := (q13M, q13W, 4, q13G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q13Bin : BinLower q13M q13W q13G 4 := dagShiftLowerBin (width := 256) [qS18, qS0, qS1, qS2] q0Bin (by decide +kernel)
def q14M : Word := 0x303000000000000000000000000000003030000
abbrev q14G : Word := qGoal &&& q14M
abbrev q14W : List Word := projectDAGStock q14M qBase [0, 3, 7]
def q14F : Bound := (q14M, q14W, 4, q14G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14Bin : BinLower q14M q14W q14G 4 := dagShiftLowerBin (width := 256) [qS15, qS3, qS4] q0Bin (by decide +kernel)
def q15M : Word := 0x300000003000000000000000000000003000000030000
abbrev q15G : Word := qGoal &&& q15M
abbrev q15W : List Word := projectDAGStock q15M qBase [0, 5, 7]
def q15F : Bound := (q15M, q15W, 4, q15G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15Bin : BinLower q15M q15W q15G 4 := dagShiftLowerBin (width := 256) [qS15, qS5, qS6, qS3, qS4] q0Bin (by decide +kernel)
def q16M : Word := 0xa0005000a0005
abbrev q16G : Word := qGoal &&& q16M
abbrev q16W : List Word := projectDAGStock q16M qBase [0, 1, 5]
def q16F : Bound := (q16M, q16W, 4, q16G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16Bin : BinLower q16M q16W q16G 4 := dagShiftLowerBin (width := 256) [qS19, qS13, qS9] q0Bin (by decide +kernel)
def q17M : Word := 0x500000505000005
abbrev q17G : Word := qGoal &&& q17M
abbrev q17W : List Word := projectDAGStock q17M qBase [1, 3, 5]
def q17F : Bound := (q17M, q17W, 4, q17G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17Bin : BinLower q17M q17W q17G 4 := dagShiftLowerBin (width := 256) [qS19, qS0] q0Bin (by decide +kernel)
def q18M : Word := 0x5000050000000000500005
abbrev q18G : Word := qGoal &&& q18M
abbrev q18W : List Word := projectDAGStock q18M qBase [1, 2, 6]
def q18F : Bound := (q18M, q18W, 4, q18G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q18Bin : BinLower q18M q18W q18G 4 := dagShiftLowerBin (width := 256) [qS19, qS0, qS9, qS2] q0Bin (by decide +kernel)
def q19M : Word := 0x50000000050000005000000005
abbrev q19G : Word := qGoal &&& q19M
abbrev q19W : List Word := projectDAGStock q19M qBase [1, 2, 6]
def q19F : Bound := (q19M, q19W, 4, q19G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q19Bin : BinLower q19M q19W q19G 4 := dagShiftLowerBin (width := 256) [qS20, qS0, qS9, qS2] q0Bin (by decide +kernel)
def q20M : Word := 0xc0300000000000000000000000000000c03
abbrev q20G : Word := qGoal &&& q20M
abbrev q20W : List Word := projectDAGStock q20M qBase [0, 1, 7]
def q20F : Bound := (q20M, q20W, 4, q20G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q20Bin : BinLower q20M q20W q20G 4 := dagShiftLowerBin (width := 256) [qS21, qS13, qS9, qS3, qS4] q0Bin (by decide +kernel)
def q21M : Word := 0xa0005000000000000000000000000000a0005
abbrev q21G : Word := qGoal &&& q21M
abbrev q21W : List Word := projectDAGStock q21M qBase [0, 1, 7]
def q21F : Bound := (q21M, q21W, 4, q21G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q21Bin : BinLower q21M q21W q21G 4 := dagShiftLowerBin (width := 256) [qS19, qS13, qS9, qS3, qS4] q0Bin (by decide +kernel)
def q22M : Word := 0xa0000000000000005000000000000000a0000000000000005
abbrev q22G : Word := qGoal &&& q22M
abbrev q22W : List Word := projectDAGStock q22M qBase [0, 1, 7]
def q22F : Bound := (q22M, q22W, 4, q22G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q22Bin : BinLower q22M q22W q22G 4 := dagShiftLowerBin (width := 256) [qS22, qS13, qS9, qS3, qS4] q0Bin (by decide +kernel)
def q23M : Word := 0x22000000000000001100000000000000220000000000000011
abbrev q23G : Word := qGoal &&& q23M
abbrev q23W : List Word := projectDAGStock q23M qBase [0, 2, 7]
def q23F : Bound := (q23M, q23W, 4, q23G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q23Bin : BinLower q23M q23W q23G 4 := dagShiftLowerBin (width := 256) [qS22, qS9, qS3, qS4] q0Bin (by decide +kernel)
def q24M : Word := 0x50000500000000000000000000000000500005
abbrev q24G : Word := qGoal &&& q24M
abbrev q24W : List Word := projectDAGStock q24M qBase [1, 2, 7]
def q24F : Bound := (q24M, q24W, 4, q24G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24Bin : BinLower q24M q24W q24G 4 := dagShiftLowerBin (width := 256) [qS19, qS0, qS9, qS3, qS4] q0Bin (by decide +kernel)
def q25M : Word := 0x500000500000000000000000000000005000005
abbrev q25G : Word := qGoal &&& q25M
abbrev q25W : List Word := projectDAGStock q25M qBase [1, 3, 7]
def q25F : Bound := (q25M, q25W, 4, q25G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25Bin : BinLower q25M q25W q25G 4 := dagShiftLowerBin (width := 256) [qS19, qS0, qS3, qS4] q0Bin (by decide +kernel)
def q26M : Word := 0x20001000000000002000100000000000200010000000000020001
abbrev q26G : Word := qGoal &&& q26M
abbrev q26W : List Word := projectDAGStock q26M qBase [0, 6, 7]
def q26F : Bound := (q26M, q26W, 4, q26G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26Bin : BinLower q26M q26W q26G 4 := dagShiftLowerBin (width := 256) [qS19, qS10, qS11, qS3] q0Bin (by decide +kernel)
def q27M : Word := 0x1000000000001000100000000000100010000000000010001000000000001
abbrev q27G : Word := qGoal &&& q27M
abbrev q27W : List Word := projectDAGStock q27M qBase [4, 6, 7]
def q27F : Bound := (q27M, q27W, 4, q27G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27Bin : BinLower q27M q27W q27G 4 := dagShiftLowerBin (width := 256) [qS20, qS23, qS24, qS25, qS10, qS3] q0Bin (by decide +kernel)
def q28M : Word := 0xf0000000000000f00
abbrev q28G : Word := qGoal &&& q28M
abbrev q28W : List Word := projectDAGStock q28M qBase [0, 1, 3]
def q28F : Bound := (q28M, q28W, 3, q28G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q28Bin : BinLower q28M q28W q28G 3 := dagShiftLowerBin (width := 256) [qS22, qS26] q1Bin (by decide +kernel)
def q29M : Word := 0x500050000000000500050
abbrev q29G : Word := qGoal &&& q29M
abbrev q29W : List Word := projectDAGStock q29M qBase [1, 2, 4]
def q29F : Bound := (q29M, q29W, 4, q29G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q29Bin : BinLower q29M q29W q29G 4 := dagShiftLowerBin (width := 256) [qS22, qS27, qS0, qS9, qS6] q0Bin (by decide +kernel)
def q30M : Word := 0x300030000000003000300
abbrev q30G : Word := qGoal &&& q30M
abbrev q30W : List Word := projectDAGStock q30M qBase [0, 3, 4]
def q30F : Bound := (q30M, q30W, 3, q30G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Bin : BinLower q30M q30W q30G 3 := dagShiftLowerBin (width := 256) [qS22, qS24, qS25, qS26] q1Bin (by decide +kernel)
def q31M : Word := 0x500050000000005000500
abbrev q31G : Word := qGoal &&& q31M
abbrev q31W : List Word := projectDAGStock q31M qBase [1, 3, 4]
def q31F : Bound := (q31M, q31W, 4, q31G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Bin : BinLower q31M q31W q31G 4 := dagShiftLowerBin (width := 256) [qS22, qS28, qS0, qS6] q0Bin (by decide +kernel)
def q32M : Word := 0x3000000030000030000000300
abbrev q32G : Word := qGoal &&& q32M
abbrev q32W : List Word := projectDAGStock q32M qBase [0, 3, 5]
def q32F : Bound := (q32M, q32W, 4, q32G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Bin : BinLower q32M q32W q32G 4 := dagShiftLowerBin (width := 256) [qS22] q0Bin (by decide +kernel)
def q33M : Word := 0x11000000000000001100000000000000220000000000000022
abbrev q33G : Word := qGoal &&& q33M
abbrev q33W : List Word := projectDAGStock q33M qBase [0, 2, 6]
def q33F : Bound := (q33M, q33W, 4, q33G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Bin : BinLower q33M q33W q33G 4 := dagShiftLowerBin (width := 256) [qS29, qS30, qS9, qS2] q0Bin (by decide +kernel)
def q34M : Word := 0x30300000000000003030000000000000000
abbrev q34G : Word := qGoal &&& q34M
abbrev q34W : List Word := projectDAGStock q34M qBase [0, 3, 6]
def q34F : Bound := (q34M, q34W, 4, q34G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Bin : BinLower q34M q34W q34G 4 := dagShiftLowerBin (width := 256) [qS29, qS31, qS2] q0Bin (by decide +kernel)
def q35M : Word := 0x11000000000000001100000000000011000000000000001100
abbrev q35G : Word := qGoal &&& q35M
abbrev q35W : List Word := projectDAGStock q35M qBase [2, 3, 6]
def q35F : Bound := (q35M, q35W, 4, q35G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35Bin : BinLower q35M q35W q35G 4 := dagShiftLowerBin (width := 256) [qS29, qS28, qS12, qS13, qS2] q0Bin (by decide +kernel)
def q36M : Word := 0x3000300000000000300030000000000000000
abbrev q36G : Word := qGoal &&& q36M
abbrev q36W : List Word := projectDAGStock q36M qBase [0, 4, 6]
def q36F : Bound := (q36M, q36W, 3, q36G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q36Bin : BinLower q36M q36W q36G 3 := dagShiftLowerBin (width := 256) [qS29, qS31, qS24, qS25, qS10, qS2, qS26] q1Bin (by decide +kernel)
def q37M : Word := 0x101010100000000010101010000000000000000
abbrev q37G : Word := qGoal &&& q37M
abbrev q37W : List Word := projectDAGStock q37M qBase [3, 4, 6]
def q37F : Bound := (q37M, q37W, 3, q37G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q37Bin : BinLower q37M q37W q37G 3 := dagShiftLowerBin (width := 256) [qS29, qS31, qS7, qS24, qS9, qS10, qS2, qS26] q1Bin (by decide +kernel)
def q38M : Word := 0x30000000300000003000000030000000000000000
abbrev q38G : Word := qGoal &&& q38M
abbrev q38W : List Word := projectDAGStock q38M qBase [0, 5, 6]
def q38F : Bound := (q38M, q38W, 4, q38G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q38Bin : BinLower q38M q38W q38G 4 := dagShiftLowerBin (width := 256) [qS29, qS31, qS5, qS6, qS2] q0Bin (by decide +kernel)
def q39M : Word := 0x11000000000000001100000011000000000000001100000000
abbrev q39G : Word := qGoal &&& q39M
abbrev q39W : List Word := projectDAGStock q39M qBase [2, 5, 6]
def q39F : Bound := (q39M, q39W, 4, q39G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q39Bin : BinLower q39M q39W q39G 4 := dagShiftLowerBin (width := 256) [qS29, qS32, qS12, qS13, qS5, qS6, qS2] q0Bin (by decide +kernel)
def q40M : Word := 0x100010001000100010001000100010000000000000000
abbrev q40G : Word := qGoal &&& q40M
abbrev q40W : List Word := projectDAGStock q40M qBase [4, 5, 6]
def q40F : Bound := (q40M, q40W, 3, q40G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Bin : BinLower q40M q40W q40G 3 := dagShiftLowerBin (width := 256) [qS29, qS23, qS33, qS25, qS10, qS6, qS26] q1Bin (by decide +kernel)
def q41M : Word := 0x11000000000011000000000000000000110000000000110000
abbrev q41G : Word := qGoal &&& q41M
abbrev q41W : List Word := projectDAGStock q41M qBase [2, 4, 7]
def q41F : Bound := (q41M, q41W, 4, q41G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Bin : BinLower q41M q41W q41G 4 := dagShiftLowerBin (width := 256) [qS22, qS34, qS12, qS13, qS1, qS3, qS4] q0Bin (by decide +kernel)
def q42M : Word := 0xa000a0000000000a000a0
abbrev q42G : Word := qGoal &&& q42M
abbrev q42W : List Word := projectDAGStock q42M qBase [1, 2, 4]
def q42F : Bound := (q42M, q42W, 4, q42G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Bin : BinLower q42M q42W q42G 4 := dagShiftLowerBin (width := 256) [qS17, qS22, qS27, qS0, qS9, qS6] q0Bin (by decide +kernel)
def q43M : Word := 0x3030000030300000000000000000000030300000303
abbrev q43G : Word := qGoal &&& q43M
abbrev q43W : List Word := projectDAGStock q43M qBase [0, 3, 5, 7]
def q43F : Bound := (q43M, q43W, 7, q43G)
def q43E := unpackWitnesses q43W [66176, 331904, 606336, 868384]
abbrev q43N : List Word := normStock q43M q43W
def q43C : List Bound := [q3F, q0F, q4F, q6F]
def q43S : DagSample := (0x100844028040a0100940204020940220108800a0402214028040a0, 12)
def q43L : DagLinkList := dagExtractLinks 0x884420300789e02c01 0x68300a098b2108641924442088648c13910210303e04065060cdca1999423620664408c08098000f 9 4 12 3 4
def q43D : Forest := fun i => decodeNode 3 15 0x10614131a19203e4064804c8078 i
def q43T := dagTraceTagsBin q43M 12 (dagTagBases q43N 0x63388f1f8f44 0xfb3cef3fef5d 12) 6 q43D
def q43St := dagTraceBin q43M q43N 6 q43D
def q43Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q43Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q43Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q43Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q43Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 3, 6, 5] 0 i.val)
def q43Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 7, 6, 3] 0 i.val)
def q43Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q43Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q43Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q43Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q43Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q43Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q43Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 0, 6, 5] 0 i.val)
def q43Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 7, 6, 3] 0 i.val)
def q43Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q43Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q43Mv := dagMoves ([([qS3], q43Mp0, q43Mi0), ([qS5], q43Mp1, q43Mi1), ([qS35, qS3], q43Mp2, q43Mi2), ([qS7], q43Mp3, q43Mi3), ([qS7, qS3], q43Mp4, q43Mi4), ([qS7, qS5], q43Mp5, q43Mi5), ([qS7, qS35, qS3], q43Mp6, q43Mi6), ([qS36, qS35], q43Mp7, q43Mi7)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43A : DagMovesOK q43M q43G 256 q43Mv := dagMovesOfCheck (by decide +kernel)
def q43NB : Nat → List Bound := dagNodeBounds q43C.toArray 0x16ac4a9105204 0x63e1e1 7 3 2
def q43Ck := dagCheckNodeFast q43M q43G q43NB 7 q43St q43Mv q43L q43S q43T
def q43RA (token : Nat) : Bool :=
  let s := rootState q43N 6 token
  !dagAllowedRootBin q43M q43E s.2.1 || dagLocalBin q43M q43G (dagKnownClosesBin q43G q43C) s ||
  dagRefBin q43M 7 q43St q43Mv (fun p tok => dagFindLink (q43L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43RB0 : treeBlock 0 16 q43RA = true := by decide +kernel
theorem q43R : dagCheckRootsBin q43M q43G (dagKnownClosesBin q43G q43C) q43E (dagRefBin q43M 7 q43St q43Mv (fun p tok => dagFindLink (q43L p) tok) 0) q43N 6 = true := q43RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43B0 : treeBlock 0 7 q43Ck = true := by decide +kernel
theorem q43Bf : treeBlock 0 7 q43Ck = true := q43B0
theorem q43Bk : treeBlock 0 7 (dagCheckNodeBin q43M q43G q43NB 7 q43St q43Mv q43L q43S q43T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q43Bf
theorem q43K : KnownBin q43C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q6Bin) q4Bin) q0Bin) q3Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Bin : BinLower q43M q43W q43G 7 := by
  apply lowerDagBin _ _ _ _ q43A _ _ _ q43K _ (fun _ b hb => dagNodeBounds_mem b hb) q43R q43Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q43C.all (fun b => q43M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q44M : Word := 0xf000f000000000f000f00
abbrev q44G : Word := qGoal &&& q44M
abbrev q44W : List Word := projectDAGStock q44M qBase [0, 1, 3, 4]
def q44F : Bound := (q44M, q44W, 6, q44G)
def q44E := unpackWitnesses q44W [12824, 296513, 565272, 827969]
abbrev q44N : List Word := normStock q44M q44W
def q44C : List Bound := [q31F, q28F, q30F]
def q44S : DagSample := (0x414082192090c140b0502482510c064300904024301a201081442050688209201403050, 16)
def q44L : DagLinkList := dagExtractLinks 0x8888888179785c4a3a0e01 0x483c4830bc3eb4323c2e3422444c38403440283c24231831902f8823101f0813000f 8 3 11 4 1
def q44D : Forest := fun i => decodeNode 4 15 0x18344c3080710081e14231062207c409880f0 i
def q44T := dagTraceTagsBin q44M 16 (dagTagBases q44N 0x807bcf8739b45bcc 0x9bfbe7e7fcbe9bd9 16) 5 q44D
def q44St := dagTraceBin q44M q44N 5 q44D
def q44Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q44Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q44Mv := dagMoves ([([qS24], q44Mp0, q44Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44A : DagMovesOK q44M q44G 256 q44Mv := dagMovesOfCheck (by decide +kernel)
def q44NB : Nat → List Bound := dagNodeBounds q44C.toArray 0x39ce7399ac5a3 0x10a4 5 2 2
def q44Ck := dagCheckNodeFast q44M q44G q44NB 10 q44St q44Mv q44L q44S q44T
def q44RA (token : Nat) : Bool :=
  let s := rootState q44N 5 token
  !dagAllowedRootBin q44M q44E s.2.1 || dagLocalBin q44M q44G (dagKnownClosesBin q44G q44C) s ||
  dagRefBin q44M 10 q44St q44Mv (fun p tok => dagFindLink (q44L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44RB0 : treeBlock 0 16 q44RA = true := by decide +kernel
theorem q44R : dagCheckRootsBin q44M q44G (dagKnownClosesBin q44G q44C) q44E (dagRefBin q44M 10 q44St q44Mv (fun p tok => dagFindLink (q44L p) tok) 0) q44N 5 = true := q44RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B0 : treeBlock 0 10 q44Ck = true := by decide +kernel
theorem q44Bf : treeBlock 0 10 q44Ck = true := q44B0
theorem q44Bk : treeBlock 0 10 (dagCheckNodeBin q44M q44G q44NB 10 q44St q44Mv q44L q44S q44T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q44Bf
theorem q44K : KnownBin q44C := (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q30Bin) q28Bin) q31Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Bin : BinLower q44M q44W q44G 6 := by
  apply lowerDagBin _ _ _ _ q44A _ _ _ q44K _ (fun _ b hb => dagNodeBounds_mem b hb) q44R q44Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q44C.all (fun b => q44M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q45M : Word := 0x30300000303000000000000000000000303000003030000
abbrev q45G : Word := qGoal &&& q45M
abbrev q45W : List Word := projectDAGStock q45M qBase [0, 3, 5, 7]
def q45F : Bound := (q45M, q45W, 7, q45G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45Bin : BinLower q45M q45W q45G 7 := dagShiftLowerBin (width := 256) [qS15] q43Bin (by decide +kernel)
def q46M : Word := 0x30300000030300000000000000000000303000000303
abbrev q46G : Word := qGoal &&& q46M
abbrev q46W : List Word := projectDAGStock q46M qBase [0, 2, 3, 7]
def q46F : Bound := (q46M, q46W, 7, q46G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Bin : BinLower q46M q46W q46G 7 := dagShiftLowerBin (width := 256) [qS20, qS25, qS1, qS6] q43Bin (by decide +kernel)
def q47M : Word := 0xa0005000a00050000000000000000000a0005000a0005
abbrev q47G : Word := qGoal &&& q47M
abbrev q47W : List Word := projectDAGStock q47M qBase [0, 1, 5, 7]
def q47F : Bound := (q47M, q47W, 7, q47G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q47Bin : BinLower q47M q47W q47G 7 := dagShiftLowerBin (width := 256) [qS19, qS13, qS9] q43Bin (by decide +kernel)
def q48M : Word := 0xa0000000a00000005000000050000000a0000000a0000000500000005
abbrev q48G : Word := qGoal &&& q48M
abbrev q48W : List Word := projectDAGStock q48M qBase [0, 1, 5, 7]
def q48F : Bound := (q48M, q48W, 7, q48G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48Bin : BinLower q48M q48W q48G 7 := dagShiftLowerBin (width := 256) [qS22, qS13, qS9] q43Bin (by decide +kernel)
def q49M : Word := 0x50000050500000500000000000000000500000505000005
abbrev q49G : Word := qGoal &&& q49M
abbrev q49W : List Word := projectDAGStock q49M qBase [1, 3, 5, 7]
def q49F : Bound := (q49M, q49W, 7, q49G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49Bin : BinLower q49M q49W q49G 7 := dagShiftLowerBin (width := 256) [qS19, qS0] q43Bin (by decide +kernel)
def q50M : Word := 0xa000500000000000a000500000000000a000500000000000a0005
abbrev q50G : Word := qGoal &&& q50M
abbrev q50W : List Word := projectDAGStock q50M qBase [0, 1, 6, 7]
def q50F : Bound := (q50M, q50W, 7, q50G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q50Bin : BinLower q50M q50W q50G 7 := dagShiftLowerBin (width := 256) [qS19, qS13, qS9, qS2] q43Bin (by decide +kernel)
def q51M : Word := 0x500005000000000050000500000000005000050000000000500005
abbrev q51G : Word := qGoal &&& q51M
abbrev q51W : List Word := projectDAGStock q51M qBase [1, 2, 6, 7]
def q51F : Bound := (q51M, q51W, 7, q51G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q51Bin : BinLower q51M q51W q51G 7 := dagShiftLowerBin (width := 256) [qS19, qS0, qS9, qS2] q43Bin (by decide +kernel)
def q52M : Word := 0x5000000005000000500000000500000050000000050000005000000005
abbrev q52G : Word := qGoal &&& q52M
abbrev q52W : List Word := projectDAGStock q52M qBase [1, 2, 6, 7]
def q52F : Bound := (q52M, q52W, 7, q52G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q52Bin : BinLower q52M q52W q52G 7 := dagShiftLowerBin (width := 256) [qS20, qS0, qS9, qS2] q43Bin (by decide +kernel)
def q53M : Word := 0x5000005000000000500000500000000050000050000000005000005
abbrev q53G : Word := qGoal &&& q53M
abbrev q53W : List Word := projectDAGStock q53M qBase [1, 3, 6, 7]
def q53F : Bound := (q53M, q53W, 7, q53G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q53Bin : BinLower q53M q53W q53G 7 := dagShiftLowerBin (width := 256) [qS19, qS0, qS2] q43Bin (by decide +kernel)
def q54M : Word := 0x5000000000005000500000000000500050000000000050005000000000005
abbrev q54G : Word := qGoal &&& q54M
abbrev q54W : List Word := projectDAGStock q54M qBase [1, 4, 6, 7]
def q54F : Bound := (q54M, q54W, 7, q54G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q54Bin : BinLower q54M q54W q54G 7 := dagShiftLowerBin (width := 256) [qS20, qS0, qS1, qS2] q43Bin (by decide +kernel)
def q55M : Word := 0x30303030c0c0c0c
abbrev q55G : Word := qGoal &&& q55M
abbrev q55W : List Word := projectDAGStock q55M qBase [0, 1, 3, 4]
def q55F : Bound := (q55M, q55W, 6, q55G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q55Bin : BinLower q55M q55W q55G 6 := dagShiftLowerBin (width := 256) [qS20, qS23, qS24, qS1, qS37] q44Bin (by decide +kernel)
def q56M : Word := 0x30303030000000000000000000000000c0c0c0c
abbrev q56G : Word := qGoal &&& q56M
abbrev q56W : List Word := projectDAGStock q56M qBase [0, 1, 3, 4]
def q56F : Bound := (q56M, q56W, 6, q56G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q56Bin : BinLower q56M q56W q56G 6 := dagShiftLowerBin (width := 256) [qS29, qS23, qS24, qS1, qS37] q44Bin (by decide +kernel)
def q57M : Word := 0xf0000000f00000f0000000f00
abbrev q57G : Word := qGoal &&& q57M
abbrev q57W : List Word := projectDAGStock q57M qBase [0, 1, 3, 5]
def q57F : Bound := (q57M, q57W, 6, q57G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q57Bin : BinLower q57M q57W q57G 6 := dagShiftLowerBin (width := 256) [qS22, qS28, qS0, qS6, qS37] q44Bin (by decide +kernel)
def q58M : Word := 0x3030000030300000000000000000000303000003030
abbrev q58G : Word := qGoal &&& q58M
abbrev q58W : List Word := projectDAGStock q58M qBase [0, 2, 3, 5]
def q58F : Bound := (q58M, q58W, 7, q58G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q58Bin : BinLower q58M q58W q58G 7 := dagShiftLowerBin (width := 256) [qS29, qS27, qS25, qS1, qS11, qS2, qS4] q43Bin (by decide +kernel)
def q59M : Word := 0x30003000300030300030003000300
abbrev q59G : Word := qGoal &&& q59M
abbrev q59W : List Word := projectDAGStock q59M qBase [0, 3, 4, 5]
def q59F : Bound := (q59M, q59W, 6, q59G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q59Bin : BinLower q59M q59W q59G 6 := dagShiftLowerBin (width := 256) [qS22, qS28, qS23, qS24, qS25, qS6, qS37] q44Bin (by decide +kernel)
def q60M : Word := 0x50005000500050500050005000500
abbrev q60G : Word := qGoal &&& q60M
abbrev q60W : List Word := projectDAGStock q60M qBase [1, 3, 4, 5]
def q60F : Bound := (q60M, q60W, 6, q60G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q60Bin : BinLower q60M q60W q60G 6 := dagShiftLowerBin (width := 256) [qS22, qS36, qS38, qS37] q44Bin (by decide +kernel)
def q61M : Word := 0x30300000c0c0000030300000c0c
abbrev q61G : Word := qGoal &&& q61M
abbrev q61W : List Word := projectDAGStock q61M qBase [0, 1, 3, 6]
def q61F : Bound := (q61M, q61W, 6, q61G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q61Bin : BinLower q61M q61W q61G 6 := dagShiftLowerBin (width := 256) [qS20, qS39, qS40, qS10, qS11, qS2, qS37] q44Bin (by decide +kernel)
def q62M : Word := 0x30003000c000c00030003000c000c
abbrev q62G : Word := qGoal &&& q62M
abbrev q62W : List Word := projectDAGStock q62M qBase [0, 1, 4, 6]
def q62F : Bound := (q62M, q62W, 6, q62G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q62Bin : BinLower q62M q62W q62G 6 := dagShiftLowerBin (width := 256) [qS20, qS41, qS24, qS1, qS11, qS2, qS37] q44Bin (by decide +kernel)
def q63M : Word := 0x303030300000000030303030000000000000000
abbrev q63G : Word := qGoal &&& q63M
abbrev q63W : List Word := projectDAGStock q63M qBase [0, 3, 4, 6]
def q63F : Bound := (q63M, q63W, 6, q63G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63Bin : BinLower q63M q63W q63G 6 := dagShiftLowerBin (width := 256) [qS29, qS23, qS24, qS25, qS10, qS11, qS2, qS37] q44Bin (by decide +kernel)
def q64M : Word := 0x3030000030300000303000003030000000000000000
abbrev q64G : Word := qGoal &&& q64M
abbrev q64W : List Word := projectDAGStock q64M qBase [0, 3, 5, 6]
def q64F : Bound := (q64M, q64W, 7, q64G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64Bin : BinLower q64M q64W q64G 7 := dagShiftLowerBin (width := 256) [qS29, qS31, qS4] q43Bin (by decide +kernel)
def q65M : Word := 0x300030003000300030003000300030000000000000000
abbrev q65G : Word := qGoal &&& q65M
abbrev q65W : List Word := projectDAGStock q65M qBase [0, 4, 5, 6]
def q65F : Bound := (q65M, q65W, 6, q65G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q65Bin : BinLower q65M q65W q65G 6 := dagShiftLowerBin (width := 256) [qS29, qS23, qS24, qS25, qS10, qS6, qS37] q44Bin (by decide +kernel)
def q66M : Word := 0x10101010101010101010101010101010000000000000000
abbrev q66G : Word := qGoal &&& q66M
abbrev q66W : List Word := projectDAGStock q66M qBase [3, 4, 5, 6]
def q66F : Bound := (q66M, q66W, 6, q66G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q66Bin : BinLower q66M q66W q66G 6 := dagShiftLowerBin (width := 256) [qS29, qS23, qS8, qS25, qS10, qS6, qS2, qS37] q44Bin (by decide +kernel)
def q67M : Word := 0xf0f0f0f0f0f0f0f
abbrev q67G : Word := qGoal &&& q67M
abbrev q67W : List Word := projectDAGStock q67M qBase [0, 1, 3, 4, 5]
def q67F : Bound := (q67M, q67W, 7, q67G)
def q67E := unpackWitnesses q67W [25136, 287792, 553008, 799754, 1077272]
abbrev q67N : List Word := normStock q67M q67W
def q67C : List Bound := [q0F, q10F, q16F, q17F]
def q67S : DagSample := (0xa030280884c140b05024060b0c06806090184c30190c024141a088642209040244021080480422100886012008241028100a01422008840412088c42221, 28)
def q67L : DagLinkList := dagExtractLinks 0xe38e31341 0x405c3843a04f9043202f1023001f 6 3 12 3 1
def q67D : Forest := fun i => decodeNode 3 15 0x2e2843205e408c80f8 i
def q67T := dagTraceTagsBin q67M 28 (dagTagBases q67N 0xc210f74c96f0eb2081f1fdd276f93ffe984 0xda73f74e26fbeba58dfaf9d936fcfffecdf 28) 6 q67D
def q67St := dagTraceBin q67M q67N 6 q67D
def q67Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q67Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q67Mv := dagMoves ([([qS7], q67Mp0, q67Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q67A : DagMovesOK q67M q67G 256 q67Mv := dagMovesOfCheck (by decide +kernel)
def q67NB : Nat → List Bound := dagNodeBounds q67C.toArray 0x4072a9084 0x9378 7 3 2
def q67Ck := dagCheckNodeFast q67M q67G q67NB 5 q67St q67Mv q67L q67S q67T
def q67RA (token : Nat) : Bool :=
  let s := rootState q67N 6 token
  !dagAllowedRootBin q67M q67E s.2.1 || dagLocalBin q67M q67G (dagKnownClosesBin q67G q67C) s ||
  dagRefBin q67M 5 q67St q67Mv (fun p tok => dagFindLink (q67L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q67RB0 : treeBlock 0 32 q67RA = true := by decide +kernel
theorem q67R : dagCheckRootsBin q67M q67G (dagKnownClosesBin q67G q67C) q67E (dagRefBin q67M 5 q67St q67Mv (fun p tok => dagFindLink (q67L p) tok) 0) q67N 6 = true := q67RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q67B0 : treeBlock 0 5 q67Ck = true := by decide +kernel
theorem q67Bf : treeBlock 0 5 q67Ck = true := q67B0
theorem q67Bk : treeBlock 0 5 (dagCheckNodeBin q67M q67G q67NB 5 q67St q67Mv q67L q67S q67T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q67Bf
theorem q67K : KnownBin q67C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q17Bin) q16Bin) q10Bin) q0Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q67Bin : BinLower q67M q67W q67G 7 := by
  apply lowerDagBin _ _ _ _ q67A _ _ _ q67K _ (fun _ b hb => dagNodeBounds_mem b hb) q67R q67Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q67C.all (fun b => q67M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q68M : Word := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
abbrev q68G : Word := qGoal &&& q68M
abbrev q68W : List Word := projectDAGStock q68M qBase [0, 1, 3, 6, 7]
def q68F : Bound := (q68M, q68W, 8, q68G)
def q68E := unpackWitnesses q68W [66176, 328832, 594048, 884864, 1151048]
abbrev q68N : List Word := normStock q68M q68W
def q68C : List Bound := [q7F, q3F, q34F, q20F, q22F]
def q68S : DagSample := (0x30082c12432082430502c14090182c904a01824064324124900905128824920824100940204804201209008201a0402090422100880520802810110880c0403008281, 30)
def q68L : DagLinkList := dagExtractLinks 0x1c0e070363b0d86c36165923543801 0x170b8980c430108701d1403224055c22f374521087c1d0c9b42906832680bc14130201f43c4327066cd10c1a11d204fa2086480fc8819a202f420460807c08098001f 9 4 12 4 3
def q68D : Forest := fun i => decodeNode 4 16 0x85c90194015443e34323832204c203e2423101f1013101f0 i
def q68T := dagTraceTagsBin q68M 30 (dagTagBases q68N 0x28421ceee4b78f5f4103e3f0e93bfc47ffd108 0x2b4e7ceef137d75f4b1bf5f8ec9bfebfffdbbd 30) 7 q68D
def q68St := dagTraceBin q68M q68N 7 q68D
def q68Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q68Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q68Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 4, 5, 3, 7] 0 i.val)
def q68Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 4, 5, 3, 7] 0 i.val)
def q68Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q68Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q68Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q68Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q68Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 6, 4, 5, 0, 7] 0 i.val)
def q68Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 0, 2, 1, 4, 5, 3, 7] 0 i.val)
def q68Mv := dagMoves ([([qS40], q68Mp0, q68Mi0), ([qS0, qS10], q68Mp1, q68Mi1), ([qS7], q68Mp2, q68Mi2), ([qS7, qS40], q68Mp3, q68Mi3), ([qS0, qS8, qS10], q68Mp4, q68Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68A : DagMovesOK q68M q68G 256 q68Mv := dagMovesOfCheck (by decide +kernel)
def q68NB : Nat → List Bound := dagNodeBounds q68C.toArray 0x90907469685a5858432b1302 0x2304028140a041 8 3 3
def q68Ck := dagCheckNodeFast q68M q68G q68NB 12 q68St q68Mv q68L q68S q68T
def q68RA (token : Nat) : Bool :=
  let s := rootState q68N 7 token
  !dagAllowedRootBin q68M q68E s.2.1 || dagLocalBin q68M q68G (dagKnownClosesBin q68G q68C) s ||
  dagRefBin q68M 12 q68St q68Mv (fun p tok => dagFindLink (q68L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68RB0 : treeBlock 0 32 q68RA = true := by decide +kernel
theorem q68R : dagCheckRootsBin q68M q68G (dagKnownClosesBin q68G q68C) q68E (dagRefBin q68M 12 q68St q68Mv (fun p tok => dagFindLink (q68L p) tok) 0) q68N 7 = true := q68RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68B0 : treeBlock 0 12 q68Ck = true := by decide +kernel
theorem q68Bf : treeBlock 0 12 q68Ck = true := q68B0
theorem q68Bk : treeBlock 0 12 (dagCheckNodeBin q68M q68G q68NB 12 q68St q68Mv q68L q68S q68T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q68Bf
theorem q68K : KnownBin q68C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q22Bin) q20Bin) q34Bin) q3Bin) q7Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68Bin : BinLower q68M q68W q68G 8 := by
  apply lowerDagBin _ _ _ _ q68A _ _ _ q68K _ (fun _ b hb => dagNodeBounds_mem b hb) q68R q68Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q68C.all (fun b => q68M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q69M : Word := 0xf000f000f000f0f000f000f000f00
abbrev q69G : Word := qGoal &&& q69M
abbrev q69W : List Word := projectDAGStock q69M qBase [0, 1, 3, 4, 5]
def q69F : Bound := (q69M, q69W, 8, q69G)
def q69E := unpackWitnesses q69W [49760, 312416, 544864, 843872, 1098305]
abbrev q69N : List Word := normStock q69M q69W
def q69C : List Bound := [q31F, q32F, q44F, q57F, q59F, q60F]
def q69S : DagSample := (0x2090c140b0502482510c0643009050a8c062050a03038301c0302804024c0610c068804205108141a201403050040a0820920984c028, 24)
def q69L : DagLinkList := dagExtractLinks 0x9 0x1f 2 1 5 1 1
def q69D : Forest := fun i => decodeNode 1 6 0x3e i
def q69T := dagTraceTagsBin q69M 24 (dagTagBases q69N 0x3f3f93cfc3fe79d8ffc0bf46eda4d 0x6ffff99d7f3ff3adeffedbfe6edad8 24) 7 q69D
def q69St := dagTraceBin q69M q69N 7 q69D
def q69Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69A : DagMovesOK q69M q69G 256 q69Mv := dagMovesOfCheck (by decide +kernel)
def q69NB : Nat → List Bound := dagNodeBounds q69C.toArray 0x6 0x23a88 6 3 3
def q69Ck := dagCheckNodeFast q69M q69G q69NB 1 q69St q69Mv q69L q69S q69T
def q69RA (token : Nat) : Bool :=
  let s := rootState q69N 7 token
  !dagAllowedRootBin q69M q69E s.2.1 || dagLocalBin q69M q69G (dagKnownClosesBin q69G q69C) s ||
  dagRefBin q69M 1 q69St q69Mv (fun p tok => dagFindLink (q69L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69RB0 : treeBlock 0 32 q69RA = true := by decide +kernel
theorem q69R : dagCheckRootsBin q69M q69G (dagKnownClosesBin q69G q69C) q69E (dagRefBin q69M 1 q69St q69Mv (fun p tok => dagFindLink (q69L p) tok) 0) q69N 7 = true := q69RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69B0 : treeBlock 0 1 q69Ck = true := by decide +kernel
theorem q69Bf : treeBlock 0 1 q69Ck = true := q69B0
theorem q69Bk : treeBlock 0 1 (dagCheckNodeBin q69M q69G q69NB 1 q69St q69Mv q69L q69S q69T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q69Bf
theorem q69K : KnownBin q69C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q60Bin) q59Bin) q57Bin) q44Bin) q32Bin) q31Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69Bin : BinLower q69M q69W q69G 8 := by
  apply lowerDagBin _ _ _ _ q69A _ _ _ q69K _ (fun _ b hb => dagNodeBounds_mem b hb) q69R q69Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q69C.all (fun b => q69M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q70M : Word := 0x30303030303030303030303030303030000000000000000
abbrev q70G : Word := qGoal &&& q70M
abbrev q70W : List Word := projectDAGStock q70M qBase [0, 3, 4, 5, 6]
def q70F : Bound := (q70M, q70W, 9, q70G)
def q70E := unpackWitnesses q70W [74384, 340112, 581728, 876688, 1130592]
abbrev q70N : List Word := normStock q70M q70W
def q70C : List Bound := [q11F, q65F, q66F, q63F, q34F, q64F, q36F, q40F, q37F, q38F]
def q70S : DagSample := (0x2422500a120a8500a8401a100894814480684816080a0481c0825148244825024161209824140c061301a09068482c0c07030140904940204828120925008824220805020985205040280c0a0, 34)
def q70L : DagLinkList := dagExtractLinks 0x3460d183460d183460d00f3e1cf833c1cf033c0ce873a0ce833a0ce07380ce03361cd83360cd83360cd83360cd83341cd03340cd03340cd03340cd03340cd03340cd03340cd03321cc83320cc07300cc03300cc032a3c90f221c8071e1c41f0c2c3030c0c287081c203042c087001bd96ee4b992e03b786d83b586d22b406ce1b28ac24af8abc1ae0ab23aa92a43a712963a40e8e1a20e823a0067a39b9a6c1998e587929e44390864208f8a3c18e863628d063218c06265880e1e1870616385061028385fc97e85f817d09ec47911e027421c657181ba66c15a656791793592952952154234f0d26b43b10453f10ea936a0c0d2e10a69279084d1a384af0f1c17300a8001 0x72444052443012442092244c92204c12644c122424122428524040124430124c4092204c32003c12002c92204c32203c12202c12202012004412002071e0496d604111c03151e0294d602111e0190d601111a4308c205c11803011f0501164308c205c11403011203011d0508f24502f24404d04300d042090845c11a4482f04300f04208ee4502ee4400ee4300c442031844c11843c11642c11642c11405c31204c11203c11002c2ec84010e44010ec402ea44010c05c10a02c0c24248fc0502fc0401080309000501060201040200c24381020208fe0502fe0406d403010883850645c10644c10243c106c4210484e1028424fa4506d24400f24304d60504fc45c0f84300f04204f64500f64400ee4301004500fe4424e604e4d4042100c5c0fe8380fc44c0f48400fb0500f6840ad24500f884e0f68426e444e6d24424e404e4d20420f48400f4c400d883c2d804c4f28500f28400ee8308d00502d00400e003c0c40300f2c420f084e0ee8420ec4314de04e4d00420e803d0ecc400ea43c0dc04c0e84300e88402c00400e20200e00200e40500de0200e64480e44502d84400e284e0e08422c083d0de4420dc0312c044c0da05c0d803c0da4300d84300d70500d24500d04300d48482d30500d28500ca05c2d0c420d08420ce04e0cc04d0c804c0c60450c40422c003d0c002d0ce0200cc4300ca0210c80200c64308c205c2be04c0be02c0c44308c205c2c204c0c202c0c04300be0540bd0508840512840410a80314b202944e0210b201904e01189205d0ba0492820310a60210820118800512800410a40310800210b801903c0112b445c0b644c0b443c0ae42c0a20402b30520b28520a04310b005e0ae01e09e4400ac06c2aa05c0aa03c2a90520a8c520a685e0a485288845e86e45227244126c44007243106c4300a242e0a042909e42204842104642029a04109a03109c02909402149ac5209ac4286a85226a84249845209844249605e49405209604e09404209284849046c09045c08c44c08a43c87a06027a05064c04008803009105208ec5e08cc5287e05208602008ac4387c04227c032088c4348644e08643e48486008485008084087646027645064a44006e43084e06024e05006004c03c04008505208285e08085247a45e47645207844107444007243106c43045e05e44e05206804d07ec5e07c83807a45245c05e44c052078c5007084005043c25005c27705207685207484065a45e64a45226642d45a05e44a05206604d472c52072c4247085207084245805e44805205804e04804206ec4346c84206c83246a44306a43346404f45604e45404344604206403f05603e05403304603206885006645006443023a050062c5e060c5223ac4d05e45205c05e05a05225004105802105602005484023a45c05206c05003c24f05204e85204c45e04a45204843104643004405e04205d04005c03e05503c05223a04d03a02d23905203885203645e03445303245282605f81e05321c04102a03101c02103001f02e01902c01300a01162ac4342a84302a83382044e81444381244222043e21443321243202042e01442301242282804322803302802302705342445e02444e02243c81a05221a04202003001f05341c85201c84241a45e41845341645201a44e01844301644201443101243041005f40e05e40c05340a05201004f00e04e00c04300a042608c4340844300843380404f80204320403f20203300602100401f00201300001f 14 5 13 8 3
def q70D : Forest := fun i => decodeNode 8 21 0x22644b101a4040c4020608282d414154890a843c5221628817140078a002c4f6202681712c05896838456212221391108488c5c3e41c1f1130fa0a07884e3b4211db100e58846e84e374211bb100d88786c84033224179140b909c588422c2211600c4b086054430298281421209d0a04c842240101190c08804242020212181010c07c0583e4301e02a0f414074092380191a2260c90f0650a43005e1800f0c01b05c0782ec521642f0b21485885c2c429162110b00a4598842a442150270a810855090290521362f09b1484d88624c431121f08c1483d0bc1e8520f62f0720e0388a41cc500d42906210031884168420b6218520c82886614850092280490c0258bc10c5208229040178200a410021080100421001c0d80e03c07429031178188a40c43106218030178180ba0c05c0602a8301481805a0c8520522f02914c148a40a01f0500c82804c1506608023048298191380c87806030038298121080889c04443022210110c4088600404f0202701010c08084044330101080807c040260201f00 i
def q70T := dagTraceTagsBin q70M 34 (dagTagBases q70N 0x679ef877627ccec7ff501c7eb869f83fd02edbdc9c 0x37faffe777ffd6ef7ff55bdffbffff99ffa855bddb9 34) 8 q70D
def q70St := dagTraceBin q70M q70N 8 q70D
def q70Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q70Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q70Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q70Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q70Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q70Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q70Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q70Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q70Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q70Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q70Mv := dagMoves ([([qS5], q70Mp0, q70Mi0), ([qS7], q70Mp1, q70Mi1), ([qS36, qS5], q70Mp2, q70Mi2), ([qS7, qS5], q70Mp3, q70Mi3), ([qS36], q70Mp4, q70Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70A : DagMovesOK q70M q70G 256 q70Mv := dagMovesOfCheck (by decide +kernel)
def q70NB : Nat → List Bound := dagNodeBounds q70C.toArray 0xe00e00e00e00e00de2de0de0de0dd1dd0dd0db2db0db0db0db0db0db0db0db0db0db0db0db0da1da0da0da0d91d90d90d90d90d81d71d61d51d50d50d41d40d31d30d30d30d30d30d30d30d30d30d30cf4cf0ce1cd1cc1cb1cb0ca1c91c81c62c51c41c31c30c12c10be3bc2ba2b91b90b81b80b80b62b33b03af1af0ae1ae0ab3ab0a83a80a44a22a119f29c39939819719529419319219209119018c48b18b08a18918818718618338308218118108108017a67647246a86736436045b55655154d44944544143c53843443042c42842532141e31951360e5095045004 0x14340442120262513534623421003301404040221014013070103540501301314401904600121221201320226213025086542125067386782061353462562630240132143015407213021032103140765041613050135013213021034012531261613252061352513025130251302135 12 4 4
def q70Ck := dagCheckNodeFast q70M q70G q70NB 148 q70St q70Mv q70L q70S q70T
def q70RA (token : Nat) : Bool :=
  let s := rootState q70N 8 token
  !dagAllowedRootBin q70M q70E s.2.1 || dagLocalBin q70M q70G (dagKnownClosesBin q70G q70C) s ||
  dagRefBin q70M 148 q70St q70Mv (fun p tok => dagFindLink (q70L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70RB0 : treeBlock 0 32 q70RA = true := by decide +kernel
theorem q70R : dagCheckRootsBin q70M q70G (dagKnownClosesBin q70G q70C) q70E (dagRefBin q70M 148 q70St q70Mv (fun p tok => dagFindLink (q70L p) tok) 0) q70N 8 = true := q70RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B0 : treeBlock 0 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B16 : treeBlock 16 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B32 : treeBlock 32 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B48 : treeBlock 48 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B64 : treeBlock 64 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B80 : treeBlock 80 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B96 : treeBlock 96 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B112 : treeBlock 112 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B128 : treeBlock 128 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B144 : treeBlock 144 4 q70Ck = true := by decide +kernel
theorem q70Bf : treeBlock 0 148 q70Ck = true := (@treeBlock_merge 0 80 68 q70Ck (@treeBlock_merge 0 48 32 q70Ck (@treeBlock_merge 0 32 16 q70Ck (@treeBlock_merge 0 16 16 q70Ck q70B0 q70B16) q70B32) (@treeBlock_merge 48 16 16 q70Ck q70B48 q70B64)) (@treeBlock_merge 80 48 20 q70Ck (@treeBlock_merge 80 32 16 q70Ck (@treeBlock_merge 80 16 16 q70Ck q70B80 q70B96) q70B112) (@treeBlock_merge 128 16 4 q70Ck q70B128 q70B144)))
theorem q70Bk : treeBlock 0 148 (dagCheckNodeBin q70M q70G q70NB 148 q70St q70Mv q70L q70S q70T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q70Bf
theorem q70K : KnownBin q70C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q38Bin) q37Bin) q40Bin) q36Bin) q64Bin) q34Bin) q63Bin) q66Bin) q65Bin) q11Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70Bin : BinLower q70M q70W q70G 9 := by
  apply lowerDagBin _ _ _ _ q70A _ _ _ q70K _ (fun _ b hb => dagNodeBounds_mem b hb) q70R q70Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q70C.all (fun b => q70M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q71M : Word := 0xf0f00000f0f00000f0f00000f0f
abbrev q71G : Word := qGoal &&& q71M
abbrev q71W : List Word := projectDAGStock q71M qBase [0, 1, 3, 5, 6]
def q71F : Bound := (q71M, q71W, 7, q71G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71Bin : BinLower q71M q71W q71G 7 := dagShiftLowerBin (width := 256) [qS11] q67Bin (by decide +kernel)
def q72M : Word := 0xf000f000f000f000f000f000f000f
abbrev q72G : Word := qGoal &&& q72M
abbrev q72W : List Word := projectDAGStock q72M qBase [0, 1, 4, 5, 6]
def q72F : Bound := (q72M, q72W, 7, q72G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q72Bin : BinLower q72M q72W q72G 7 := dagShiftLowerBin (width := 256) [qS23, qS33, qS10] q67Bin (by decide +kernel)
def q73M : Word := 0x5050505050505050505050505050505
abbrev q73G : Word := qGoal &&& q73M
abbrev q73W : List Word := projectDAGStock q73M qBase [1, 3, 4, 5, 6]
def q73F : Bound := (q73M, q73W, 7, q73G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q73Bin : BinLower q73M q73W q73G 7 := dagShiftLowerBin (width := 256) [qS23, qS33, qS25, qS10, qS11] q67Bin (by decide +kernel)
def q74M : Word := 0xf0f0f0f0000000000000000000000000f0f0f0f
abbrev q74G : Word := qGoal &&& q74M
abbrev q74W : List Word := projectDAGStock q74M qBase [0, 1, 3, 4, 7]
def q74F : Bound := (q74M, q74W, 7, q74G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q74Bin : BinLower q74M q74W q74G 7 := dagShiftLowerBin (width := 256) [qS3, qS4] q67Bin (by decide +kernel)
def q75M : Word := 0x3333000000000000333300000000000033330000000000003333
abbrev q75G : Word := qGoal &&& q75M
abbrev q75W : List Word := projectDAGStock q75M qBase [0, 2, 3, 6, 7]
def q75F : Bound := (q75M, q75W, 8, q75G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q75Bin : BinLower q75M q75W q75G 8 := dagShiftLowerBin (width := 256) [qS13] q68Bin (by decide +kernel)
def q76M : Word := 0x3030303000000000303030300000000030303030000000003030303
abbrev q76G : Word := qGoal &&& q76M
abbrev q76W : List Word := projectDAGStock q76M qBase [0, 3, 4, 6, 7]
def q76F : Bound := (q76M, q76W, 7, q76G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q76Bin : BinLower q76M q76W q76G 7 := dagShiftLowerBin (width := 256) [qS40, qS42, qS3] q67Bin (by decide +kernel)
def q77M : Word := 0x3300000033000000330000003300000033000000330000003300000033
abbrev q77G : Word := qGoal &&& q77M
abbrev q77W : List Word := projectDAGStock q77M qBase [0, 2, 5, 6, 7]
def q77F : Bound := (q77M, q77W, 8, q77G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q77Bin : BinLower q77M q77W q77G 8 := dagShiftLowerBin (width := 256) [qS13, qS5, qS6] q68Bin (by decide +kernel)
def q78M : Word := 0x111100001111000011110000111100001111000011110000111100001111
abbrev q78G : Word := qGoal &&& q78M
abbrev q78W : List Word := projectDAGStock q78M qBase [2, 3, 5, 6, 7]
def q78F : Bound := (q78M, q78W, 8, q78G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q78Bin : BinLower q78M q78W q78G 8 := dagShiftLowerBin (width := 256) [qS12, qS8, qS10, qS11, qS2] q68Bin (by decide +kernel)
def q79M : Word := 0x3000300030003000300030003000300030003000300030003000300030003
abbrev q79G : Word := qGoal &&& q79M
abbrev q79W : List Word := projectDAGStock q79M qBase [0, 4, 5, 6, 7]
def q79F : Bound := (q79M, q79W, 7, q79G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q79Bin : BinLower q79M q79W q79G 7 := dagShiftLowerBin (width := 256) [qS40, qS42, qS5, qS3] q67Bin (by decide +kernel)
def q80M : Word := 0xf0f0f0f00000000000000000f0f0f0f
abbrev q80G : Word := qGoal &&& q80M
abbrev q80W : List Word := projectDAGStock q80M qBase [0, 1, 3, 4, 5]
def q80F : Bound := (q80M, q80W, 8, q80G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q80Bin : BinLower q80M q80W q80G 8 := dagShiftLowerBin (width := 256) [qS22, qS11, qS3] q68Bin (by decide +kernel)
def q81M : Word := 0xf0f000000000f0f0f0f000000000f0f
abbrev q81G : Word := qGoal &&& q81M
abbrev q81W : List Word := projectDAGStock q81M qBase [0, 1, 3, 4, 6]
def q81F : Bound := (q81M, q81W, 8, q81G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q81Bin : BinLower q81M q81W q81G 8 := dagShiftLowerBin (width := 256) [qS20, qS6, qS3] q68Bin (by decide +kernel)
def q82M : Word := 0xf0f0000000000000f0f00000000000000000f0f0000000000000f0f
abbrev q82G : Word := qGoal &&& q82M
abbrev q82W : List Word := projectDAGStock q82M qBase [0, 1, 3, 4, 6]
def q82F : Bound := (q82M, q82W, 8, q82G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q82Bin : BinLower q82M q82W q82G 8 := dagShiftLowerBin (width := 256) [qS29, qS6, qS3] q68Bin (by decide +kernel)
def q83M : Word := 0xcc330000cc330000cc330000cc33
abbrev q83G : Word := qGoal &&& q83M
abbrev q83W : List Word := projectDAGStock q83M qBase [0, 1, 2, 5, 6]
def q83F : Bound := (q83M, q83W, 7, q83G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q83Bin : BinLower q83M q83W q83G 7 := dagShiftLowerBin (width := 256) [qS21, qS40, qS9, qS5, qS6, qS2] q67Bin (by decide +kernel)
def q84M : Word := 0x9999000099990000999900009999
abbrev q84G : Word := qGoal &&& q84M
abbrev q84W : List Word := projectDAGStock q84M qBase [0, 2, 3, 5, 6]
def q84F : Bound := (q84M, q84W, 7, q84G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q84Bin : BinLower q84M q84W q84G 7 := dagShiftLowerBin (width := 256) [qS43, qS7, qS40, qS42, qS5, qS11] q67Bin (by decide +kernel)
def q85M : Word := 0x22221111222211112222111122221111
abbrev q85G : Word := qGoal &&& q85M
abbrev q85W : List Word := projectDAGStock q85M qBase [0, 2, 3, 5, 6]
def q85F : Bound := (q85M, q85W, 7, q85G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q85Bin : BinLower q85M q85W q85G 7 := dagShiftLowerBin (width := 256) [qS19, qS7, qS40, qS42, qS5, qS11] q67Bin (by decide +kernel)
def q86M : Word := 0xc030c030c030c030c030c030c030c03
abbrev q86G : Word := qGoal &&& q86M
abbrev q86W : List Word := projectDAGStock q86M qBase [0, 1, 4, 5, 6]
def q86F : Bound := (q86M, q86W, 8, q86G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q86Bin : BinLower q86M q86W q86G 8 := dagShiftLowerBin (width := 256) [qS21, qS24, qS5, qS6, qS3] q68Bin (by decide +kernel)
def q87M : Word := 0x9090909090909090909090909090909
abbrev q87G : Word := qGoal &&& q87M
abbrev q87W : List Word := projectDAGStock q87M qBase [0, 3, 4, 5, 6]
def q87F : Bound := (q87M, q87W, 8, q87G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87Bin : BinLower q87M q87W q87G 8 := dagShiftLowerBin (width := 256) [qS43, qS7, qS24, qS25, qS5, qS3] q68Bin (by decide +kernel)
def q88M : Word := 0x5050505050505050a0a0a0a0a0a0a0a
abbrev q88G : Word := qGoal &&& q88M
abbrev q88W : List Word := projectDAGStock q88M qBase [0, 1, 3, 4, 5]
def q88F : Bound := (q88M, q88W, 8, q88G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88Bin : BinLower q88M q88W q88G 8 := dagShiftLowerBin (width := 256) [qS22, qS30, qS0, qS8, qS6, qS37] q69Bin (by decide +kernel)
def q89M : Word := 0x30303030c0c0c0c030303030c0c0c0c
abbrev q89G : Word := qGoal &&& q89M
abbrev q89W : List Word := projectDAGStock q89M qBase [0, 1, 3, 4, 6]
def q89F : Bound := (q89M, q89W, 8, q89G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q89Bin : BinLower q89M q89W q89G 8 := dagShiftLowerBin (width := 256) [qS20, qS41, qS24, qS1, qS11, qS2, qS37] q69Bin (by decide +kernel)
def q90M : Word := 0xf0f00000f0f00000f0f00000f0f00
abbrev q90G : Word := qGoal &&& q90M
abbrev q90W : List Word := projectDAGStock q90M qBase [0, 1, 3, 5, 6]
def q90F : Bound := (q90M, q90W, 8, q90G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90Bin : BinLower q90M q90W q90G 8 := dagShiftLowerBin (width := 256) [qS19, qS11, qS37] q69Bin (by decide +kernel)
def q91M : Word := 0x5050a0a05050a0a05050a0a05050a0a
abbrev q91G : Word := qGoal &&& q91M
abbrev q91W : List Word := projectDAGStock q91M qBase [0, 1, 3, 5, 6]
def q91F : Bound := (q91M, q91W, 8, q91G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91Bin : BinLower q91M q91W q91G 8 := dagShiftLowerBin (width := 256) [qS19, qS30, qS0, qS8, qS6, qS2, qS37] q69Bin (by decide +kernel)
def q92M : Word := 0x5000a0005000a0005000a0005000a0005000a0005000a0005000a0005000a
abbrev q92G : Word := qGoal &&& q92M
abbrev q92W : List Word := projectDAGStock q92M qBase [0, 1, 5, 6, 7]
def q92F : Bound := (q92M, q92W, 8, q92G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92Bin : BinLower q92M q92W q92G 8 := dagShiftLowerBin (width := 256) [qS19, qS30, qS0, qS33, qS5, qS44, qS2, qS37] q69Bin (by decide +kernel)
def q93M : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev q93G : Word := qGoal &&& q93M
abbrev q93W : List Word := projectDAGStock q93M qBase [0, 1, 3, 4, 5, 6]
def q93F : Bound := (q93M, q93W, 10, q93G)
def q93E := unpackWitnesses q93W [49760, 312416, 577632, 843872, 1101896, 1368112]
abbrev q93N : List Word := normStock q93M q93W
def q93C : List Bound := [q0F, q11F, q73F, q67F, q72F, q12F, q71F, q13F, q55F, q80F, q81F, q86F, q87F, q69F, q88F, q89F, q90F, q91F]
def q93S : DagSample := (0x50a8c068000a06038180c8002200108824324128c0623008882512416022510c1602050241a022130502c14090182c301a0182406130c0643009050682219088244021010884022180481028100a01422088c4c0700888410090190c9049240242012201080209051288249208240412201400442008846070209848221, 56)
def q93L : DagLinkList := dagExtractLinks 0x1602c0580ac3582a0d219c511620440843081c2ac644a88018001 0x112360801103c078dc87c0e02636b14d3c8be9c4530f21f8710cc350f8cf0634c437c5a18c3109ed684366831a5a1bd290c61684f0a4218480f0220c68e86f4643183a13c190870305362629b0b10c91096468438422fc1914d9489e0a44b6421fb190cc848460804b0302181008c040260003f 11 5 13 5 3
def q93D : Forest := fun i => decodeNode 5 18 0x2363c088d21fa8866a43e1d09e542791086401e120c634278d08632258409610218404610098407e0 i
def q93T := dagTraceTagsBin q93M 56 (dagTagBases q93N 0xfeeb8423f41a74701f92dc6f65af0f7541079e987fe7e0ba4f73ef9b039f7ff881fff0bc207ffffb34c9 0xfeebb4e7f57a747fffc4ddef7daf7f754b1fae9dffe7f8bb2775effba79ffffa5bfffbbe077ffffb965c 56) 9 q93D
def q93St := dagTraceBin q93M q93N 9 q93D
def q93Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q93Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q93Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q93Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q93Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 0, 1, 3, 7] 0 i.val)
def q93Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 0, 1, 3, 7] 0 i.val)
def q93Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 3, 1, 0, 7] 0 i.val)
def q93Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 0, 1, 3, 7] 0 i.val)
def q93Mv := dagMoves ([([qS11], q93Mp0, q93Mi0), ([qS7], q93Mp1, q93Mi1), ([qS23, qS33, qS10], q93Mp2, q93Mi2), ([qS23, qS33, qS10, qS11], q93Mp3, q93Mi3)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93A : DagMovesOK q93M q93G 256 q93Mv := dagMovesOfCheck (by decide +kernel)
def q93NB : Nat → List Bound := dagNodeBounds q93C.toArray 0xf83e0f83d1f07a2dcf34c0ec4a4e54851b6595153500d 0x43280c10184100880190201840310408394083904501844080622040039431839ac5a92f30c44 10 4 5
def q93Ck := dagCheckNodeFast q93M q93G q93NB 18 q93St q93Mv q93L q93S q93T
def q93RA (token : Nat) : Bool :=
  let s := rootState q93N 9 token
  !dagAllowedRootBin q93M q93E s.2.1 || dagLocalBin q93M q93G (dagKnownClosesBin q93G q93C) s ||
  dagRefBin q93M 18 q93St q93Mv (fun p tok => dagFindLink (q93L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93RB0 : treeBlock 0 64 q93RA = true := by decide +kernel
theorem q93R : dagCheckRootsBin q93M q93G (dagKnownClosesBin q93G q93C) q93E (dagRefBin q93M 18 q93St q93Mv (fun p tok => dagFindLink (q93L p) tok) 0) q93N 9 = true := q93RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B0 : treeBlock 0 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B16 : treeBlock 16 2 q93Ck = true := by decide +kernel
theorem q93Bf : treeBlock 0 18 q93Ck = true := (@treeBlock_merge 0 16 2 q93Ck q93B0 q93B16)
theorem q93Bk : treeBlock 0 18 (dagCheckNodeBin q93M q93G q93NB 18 q93St q93Mv q93L q93S q93T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q93Bf
theorem q93K : KnownBin q93C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q91Bin) q90Bin) q89Bin) q88Bin) q69Bin) q87Bin) q86Bin) q81Bin) q80Bin) q55Bin) q13Bin) q71Bin) q12Bin) q72Bin) q67Bin) q73Bin) q11Bin) q0Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93Bin : BinLower q93M q93W q93G 10 := by
  apply lowerDagBin _ _ _ _ q93A _ _ _ q93K _ (fun _ b hb => dagNodeBounds_mem b hb) q93R q93Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q93C.all (fun b => q93M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q94M : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev q94G : Word := qGoal &&& q94M
abbrev q94W : List Word := projectDAGStock q94M qBase [0, 1, 3, 4, 5, 7]
def q94F : Bound := (q94M, q94W, 10, q94G)
def q94E := unpackWitnesses q94W [74384, 337040, 602256, 799754, 1138832, 1400880]
abbrev q94N : List Word := normStock q94M q94W
def q94C : List Bound := [q5F, q74F, q45F, q16F, q67F, q43F, q47F, q49F, q0F, q21F, q17F, q25F]
def q94S : DagSample := (0x1029100a400280022006220c0e03028180e1209101a080683180c4142a48260148a0c2603088482c120a0182c060a00884c140b05024060b0c06806090184c30190c024141a088642209100840422100886012040a0402805088223108884100940204201201209008248048020904221008805208041208a44228100a0402214028040a0, 59)
def q94L : DagLinkList := dagExtractLinks 0x9e09e09e09e09e09e09e09e09e09e09e09b39659339309219029008f18f08e18e08e08b38838268117f27f07f07f07e17e07c27a27a07a07a07827627516f66695f75875535505054d34b241a3983633152f22691f714b07d016001 0xe086168420740183d2106e485d68422390171a0088ed8c0f4860b32181b8080e98c06c430390301cc180e10c0ec840b40301c4181d90816c4607742f3b2148dc8bc6c452b502f598148dc8616c860364201a9181d10c0684603483019a182c80d86204cb2036190130c40c8608616b420979180908445202e1a0111851c1b98a0d6850ae2381190c26484156070590180a0081b98c4d886e6b431171188888605806e2b03117c182b90c25c841a72174c90889c05c320222d22c9610c484025568612b420901088a805c28022298311411b89c0c44c07c2502e7221c1910a0c0840a423812114080881340701a0280e8130500804906223431112100848dc404629c0374c81887c09abe8501f228098140798dc3ac6213626ae1188700c42645c1b03e0d4189650c432462180370b81b4580d82a06514031098137488c2a44414c218c90184480821803109009894188450c6208410f231041088380dc1a0630c0310580b8280460802209831e421892108510462082214381be180dd0a0638403103813c1809c0a0430402101b14f088a684433820298100cc040260003f 12 4 13 6 2
def q94D : Forest := fun i => decodeNode 6 19 0x6305ec60b20c144182421844840848c0ec181a4303404c540c8a51c1283020841408b2790c4f4209a02e360c4611b8c0311807c2c0b85c188943112840248dc49188922810c6e1d8c438188703e0d062148c4281b850368a06c140ca2818850268b0620d0c61a10432310606e0c0c6181883017060230e0c61110820278404e080861010826298203304026080fc0 i
def q94T := dagTraceTagsBin q94M 59 (dagTagBases q94N 0xfd3fe108fc3de1fbcafc96e37873f08f07c1079df1fff4d55749eeede7c439e1ffe20fffc778c03fffff4c44 0x3de7fed39fcfde1fbcafe26ef7df3f79f47cb1fadfafff0d40764ee6df3efbbf9ffe97ffff7fbdcffffff66fd 59) 9 q94D
def q94St := dagTraceBin q94M q94N 9 q94D
def q94Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q94Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q94Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q94Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q94Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q94Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q94Mv := dagMoves ([([qS3], q94Mp0, q94Mi0), ([qS7], q94Mp1, q94Mi1), ([qS7, qS3], q94Mp2, q94Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94A : DagMovesOK q94M q94G 256 q94Mv := dagMovesOfCheck (by decide +kernel)
def q94NB : Nat → List Bound := dagNodeBounds q94C.toArray 0x8410821041983104608409811022044017d6fa1f0bd97a2f25e0bc0780f01dcbb8762e35c0b796e2da5ad351676cc594b28642c4988310612bb16d2ae50a99125a1e3f878cde98e2ca4d87f8c713a19c1b006 0x310382011120031256411872674250002504320b3935014a32801230a30a143200153093162402385611425617265479462539630145164206231405271645721465 11 3 4
def q94Ck := dagCheckNodeFast q94M q94G q94NB 60 q94St q94Mv q94L q94S q94T
def q94RA (token : Nat) : Bool :=
  let s := rootState q94N 9 token
  !dagAllowedRootBin q94M q94E s.2.1 || dagLocalBin q94M q94G (dagKnownClosesBin q94G q94C) s ||
  dagRefBin q94M 60 q94St q94Mv (fun p tok => dagFindLink (q94L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94RB0 : treeBlock 0 64 q94RA = true := by decide +kernel
theorem q94R : dagCheckRootsBin q94M q94G (dagKnownClosesBin q94G q94C) q94E (dagRefBin q94M 60 q94St q94Mv (fun p tok => dagFindLink (q94L p) tok) 0) q94N 9 = true := q94RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B0 : treeBlock 0 16 q94Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B16 : treeBlock 16 16 q94Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B32 : treeBlock 32 16 q94Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B48 : treeBlock 48 12 q94Ck = true := by decide +kernel
theorem q94Bf : treeBlock 0 60 q94Ck = true := (@treeBlock_merge 0 32 28 q94Ck (@treeBlock_merge 0 16 16 q94Ck q94B0 q94B16) (@treeBlock_merge 32 16 12 q94Ck q94B32 q94B48))
theorem q94Bk : treeBlock 0 60 (dagCheckNodeBin q94M q94G q94NB 60 q94St q94Mv q94L q94S q94T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q94Bf
theorem q94K : KnownBin q94C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q25Bin) q17Bin) q21Bin) q0Bin) q49Bin) q47Bin) q43Bin) q67Bin) q16Bin) q45Bin) q74Bin) q5Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94Bin : BinLower q94M q94W q94G 10 := by
  apply lowerDagBin _ _ _ _ q94A _ _ _ q94K _ (fun _ b hb => dagNodeBounds_mem b hb) q94R q94Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q94C.all (fun b => q94M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q95M : Word := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
abbrev q95G : Word := qGoal &&& q95M
abbrev q95W : List Word := projectDAGStock q95M qBase [0, 1, 2, 4, 6, 7]
def q95F : Bound := (q95M, q95W, 9, q95G)
def q95E := unpackWitnesses q95W [74384, 337040, 600208, 827969, 1155216, 1409601]
abbrev q95N : List Word := normStock q95M q95W
def q95C : List Bound := [q8F, q12F, q2F, q21F, q26F, q41F, q50F, q24F, q42F, q18F, q51F]
def q95S : DagSample := (0x6810aa1400440a1400e44000488281029142a160a84c2a120291000422090c8242031100c460014082510894422500a1500a854824806830321828940a21000c04834082c10884c22122091482440a05828120184d2091018480c16482500c120190c06422010808440814080500a1110081080480482402092012201100884402100a8101048229108a0402810110880c0403012050, 67)
def q95L : DagLinkList := dagExtractLinks 0xfc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fb1fb0fb0fb0fb0fa1fa0fa0fa0fa0fa0fa0fa0fa0fa0f91f72f70f43f31f30f12f01f00f00ee2ed1ec1eb1ea1e91e90e63e60e51e32e30e21e20e20e20e11e10e10e10e10e10e01e00e00de2de0dd1dd0dc1dc0db1da1da0da0da0d73d52d50d50d32d30d12c7ac52c32c12bc5ba2b82b71b34af4a87a62a15a01a009c49a29829719619609249028a68558328308218117f27d27b27a17827807357216f36d26d06586326126015e25e05e053b5034c440c3d33a33372d62d02941eb1a40fb01e001 0x4721411c84846c1411a449441105128504411411644c45b10118c4e45b10914c5044a1611045844c1411105043a1510cc504200c1064304090810a02442b1010842e40908908c404110c10643041a1010204041b101048404090c102c403d9144fe44d4010e4ff0603f3170f48513e9138c24303e0130f70513d2144f24513c10f4ce05d3000c4a8029288084e6019240044f54603a9130f34603ba130f10503b9180ec85d3a9144c805d3a00a4be02139c140be0302c10c0e404c2a90c0e0c50341144e2449329104e105837b164dc459339104dd05234a178cc852369178ca452361134d644c354190d24683451a0cf0503321a0ca4683210f0c68642e90c0a04223100b8900222e11009e430314140b60302c10e0aa428302104ba440271088b404d3091209a420304140b84502610c08e4202f80a0bc0242eb100b88412d90b88e4222c8134b4c502c9140964302c00b0aec50251080ac05c2a80b0a8850298170a905029b140a484828a140a04502710c0900502201309a42028c1409e4502610c0a105027a1409cc4226a138988422590b4944252481388e0422300f488c40248080910502390c08c43022b13888c4221b1447e4511e11048443f2090cc6605d168104800331380843a01b0c804c7f0521da14c7c45e1881b47a049130084300111e4140768611d11847243d1c10f06006d1601444a0310e00a42e0211b8064240111781b4540311b00a45c06d1480c46a0191a416466c421911646244f18110c5e42f17108c5b050162144484300b10885602e0900885483d14a0c42a4221400b84ec4213213c4a8431211082842211813c440431080bc4002b0f809c3c0230ec148388520d81783403e0cc1483085e0ba1482c4520a90c828430098178240520881342004c0780f81d05106b1081845105913c144430490bc104230381740c0430280a4080230180840401b00804c0003f 12 4 13 8 1
def q95D : Forest := fun i => decodeNode 8 21 0x2121f0892e2c4e6c621363141ae0a0cf0506642a32b14191880bec405c62026a1012d880904394483021b1710c89c8004c3e8289ed180f28c0770503a2301d2174e48a272029398281c0130dc8926b0583462c9a4148cc8bc6644d3322619c190c88d0654683182818a1a0c48d06243c31432184140b08904f05026014130090998804a8412521712b140908a04802c216281001707c0583f0501d6280e2120720a031050174280bb1085509c2a842152168a90945404029050132180990c04989c22c42116288710fc388661c0330e82906917834092190500b4308591842c87a1643c0b00c8580a42803213059086210411642089e104430821784108c220a00e8510701703a0f4150620a02e0562102213c11086084420402782010c1005e0802b0401382008c120a4068520302f0180f80e0a40485e0242901114808864044300202f0101480809a0404c0201f01414405884024510122780910c0485e024230102e80810c04052020230101080806c040260203f00 i
def q95T := dagTraceTagsBin q95M 67 (dagTagBases q95N 0xf2ef35f2e7bf7f47fd88bf1f3121f0f77966e798f8f3dbe3ffd63f05b4c03cdbcfb1b800fc67f80fbf81efffe00fedfe9889 0xd02715f06b9fff47bbff3f9ffd23fbf77a60e798fe75dbf5ff5e3fc594cb7d5be7bf7e77ff67fedfbfdffffff7dfedfecdfc 67) 8 q95D
def q95St := dagTraceBin q95M q95N 8 q95D
def q95Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95A : DagMovesOK q95M q95G 256 q95Mv := dagMovesOfCheck (by decide +kernel)
def q95NB : Nat → List Bound := dagNodeBounds q95C.toArray 0x18a314628c518a314628c518a310e20c418830ce11c13806fcdf8bc7766e8dc9b83702e05c0b736e2dc5b1b536a2d45a8b43682d05a0b33662c8d90b21642c8590b21626bd571ae15a6b0d60ac1582b0560ab3562a8d49a834e698d29a4344a885029f33c6784f09a930a524929051ae2d44a8750aa10c12804fc9f13d2784ee5d8ba2732e61be3716c4d49a4b3a654c69852fa5d4b6961ab25289ed352614a49411da31452869051f33c4710d91a2340648bd95c286490858ec1b42f0550850d613012804 0x22014020000022208010101041111119102014210125310210170112407070060101212020222022410211212212101212101010102129102082101104101110101021250821212014206301130361013020650231020153102102310253102602a 11 3 4
def q95Ck := dagCheckNodeFast q95M q95G q95NB 143 q95St q95Mv q95L q95S q95T
def q95RA (token : Nat) : Bool :=
  let s := rootState q95N 8 token
  !dagAllowedRootBin q95M q95E s.2.1 || dagLocalBin q95M q95G (dagKnownClosesBin q95G q95C) s ||
  dagRefBin q95M 143 q95St q95Mv (fun p tok => dagFindLink (q95L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95RB0 : treeBlock 0 64 q95RA = true := by decide +kernel
theorem q95R : dagCheckRootsBin q95M q95G (dagKnownClosesBin q95G q95C) q95E (dagRefBin q95M 143 q95St q95Mv (fun p tok => dagFindLink (q95L p) tok) 0) q95N 8 = true := q95RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B0 : treeBlock 0 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B16 : treeBlock 16 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B32 : treeBlock 32 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B48 : treeBlock 48 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B64 : treeBlock 64 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B80 : treeBlock 80 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B96 : treeBlock 96 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B112 : treeBlock 112 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B128 : treeBlock 128 15 q95Ck = true := by decide +kernel
theorem q95Bf : treeBlock 0 143 q95Ck = true := (@treeBlock_merge 0 80 63 q95Ck (@treeBlock_merge 0 48 32 q95Ck (@treeBlock_merge 0 32 16 q95Ck (@treeBlock_merge 0 16 16 q95Ck q95B0 q95B16) q95B32) (@treeBlock_merge 48 16 16 q95Ck q95B48 q95B64)) (@treeBlock_merge 80 32 31 q95Ck (@treeBlock_merge 80 16 16 q95Ck q95B80 q95B96) (@treeBlock_merge 112 16 15 q95Ck q95B112 q95B128)))
theorem q95Bk : treeBlock 0 143 (dagCheckNodeBin q95M q95G q95NB 143 q95St q95Mv q95L q95S q95T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q95Bf
theorem q95K : KnownBin q95C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q51Bin) q18Bin) q42Bin) q24Bin) q50Bin) q41Bin) q26Bin) q21Bin) q2Bin) q12Bin) q8Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95Bin : BinLower q95M q95W q95G 9 := by
  apply lowerDagBin _ _ _ _ q95A _ _ _ q95K _ (fun _ b hb => dagNodeBounds_mem b hb) q95R q95Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q95C.all (fun b => q95M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q96M : Word := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
abbrev q96G : Word := qGoal &&& q96M
abbrev q96W : List Word := projectDAGStock q96M qBase [0, 1, 3, 4, 6, 7]
def q96F : Bound := (q96M, q96W, 10, q96G)
def q96E := unpackWitnesses q96W [74384, 337040, 602256, 831560, 1155216, 1413192]
abbrev q96N : List Word := normStock q96M q96W
def q96C : List Bound := [q74F, q2F, q68F, q13F, q14F, q3F, q50F, q53F, q76F, q12F, q7F, q56F, q63F, q82F]
def q96S : DagSample := (0x4824882432412830580022120980522830980c22000c04834082c12432022130502c14090182c301a0182406130c064300905068221908824064324124900920108144a20924820920140205004025008108048048240209201200824108840220148201048229108a0402810110880c0403012050, 52)
def q96L : DagLinkList := dagExtractLinks 0xe83a0e83a0e4790e4390e0771d8706c02c4a4e729866098260945f6785b3649364850207c01 0x388343606c3643c3443c34c53b005fa80533003f28033320296f06c2e8482a4483043c2e8522c45e2a4522884c2607c2644324453250632243c9e06f9a0631e04f1a0432045e5cc5e1e4531c4391a8531806c5644e54443524421642e1442312422160301443112430cd05310c534cc438c4530e4430c4338a05f880534404f420430a03f08033060210401f020130003f 10 4 13 5 2
def q96D : Forest := fun i => decodeNode 5 18 0x1069921e518a72014c887904293c8bcf2293d098e221b60c6821e208bc7229988726429940d850180c8622218098a6122184866101f8406610108403e10098407e0 i
def q96T := dagTraceTagsBin q96M 52 (dagTagBases q96N 0xbfe8420ccf78f1df92db3f0e77c0741048df1ff6adba4ff36f3e8f87ff913fff07007ffffe9889 0xbfeb4e3cff78ffdfc4dbbfbe77cc74b1cbdfaff6a5bb27fb6f9e9fe7ffc47fffb7bdfffffecdfc 52) 9 q96D
def q96St := dagTraceBin q96M q96N 9 q96D
def q96Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q96Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q96Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q96Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q96Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q96Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q96Mv := dagMoves ([([qS40], q96Mp0, q96Mi0), ([qS7], q96Mp1, q96Mi1), ([qS7, qS40], q96Mp2, q96Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96A : DagMovesOK q96M q96G 256 q96Mv := dagMovesOfCheck (by decide +kernel)
def q96NB : Nat → List Bound := dagNodeBounds q96C.toArray 0x600c017c6f0dd1b83702d1591ae54d281ce292b15202bc4744e09a9b054b6850e296622a2d82b005 0x655545702603a7655302415045170231802114149348603ac702943b6156a43d802187012329314db024193012c87602 11 4 4
def q96Ck := dagCheckNodeFast q96M q96G q96NB 29 q96St q96Mv q96L q96S q96T
def q96RA (token : Nat) : Bool :=
  let s := rootState q96N 9 token
  !dagAllowedRootBin q96M q96E s.2.1 || dagLocalBin q96M q96G (dagKnownClosesBin q96G q96C) s ||
  dagRefBin q96M 29 q96St q96Mv (fun p tok => dagFindLink (q96L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96RB0 : treeBlock 0 64 q96RA = true := by decide +kernel
theorem q96R : dagCheckRootsBin q96M q96G (dagKnownClosesBin q96G q96C) q96E (dagRefBin q96M 29 q96St q96Mv (fun p tok => dagFindLink (q96L p) tok) 0) q96N 9 = true := q96RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B0 : treeBlock 0 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B16 : treeBlock 16 13 q96Ck = true := by decide +kernel
theorem q96Bf : treeBlock 0 29 q96Ck = true := (@treeBlock_merge 0 16 13 q96Ck q96B0 q96B16)
theorem q96Bk : treeBlock 0 29 (dagCheckNodeBin q96M q96G q96NB 29 q96St q96Mv q96L q96S q96T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q96Bf
theorem q96K : KnownBin q96C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q82Bin) q63Bin) q56Bin) q7Bin) q12Bin) q76Bin) q53Bin) q50Bin) q3Bin) q14Bin) q13Bin) q68Bin) q2Bin) q74Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96Bin : BinLower q96M q96W q96G 10 := by
  apply lowerDagBin _ _ _ _ q96A _ _ _ q96K _ (fun _ b hb => dagNodeBounds_mem b hb) q96R q96Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q96C.all (fun b => q96M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q97M : Word := 0x333300003333000033330000333300003333000033330000333300003333
abbrev q97G : Word := qGoal &&& q97M
abbrev q97W : List Word := projectDAGStock q97M qBase [0, 2, 3, 5, 6, 7]
def q97F : Bound := (q97M, q97W, 11, q97G)
def q97E := unpackWitnesses q97W [66176, 329856, 594048, 868480, 1147008, 1425504]
abbrev q97N : List Word := normStock q97M q97W
def q97C : List Bound := [q8F, q11F, q0F, q43F, q77F, q75F, q39F, q3F, q78F, q9F, q35F, q33F, q4F, q64F, q6F, q23F, q46F, q58F]
def q97S : DagSample := (0x4002400a8402a41029402250021400a440684028402a1402a10028201a0402900a249028042240a8402a140028041a010c824300908812094c0610022040a80623040e030300c0a0120b0182c301a090680028048a40030082c124320c0e020914180d060240a0d241300a09100840a25301900a21100a0102802914904924024184c20924820912190826120884100940204804402211008402a0402090422100880621002211028100a01221002810211080c0403008281, 82)
def q97L : DagLinkList := dagExtractLinks 0xea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea01ea00ea00ea00ea00ea00ea00e943e901e900e900e8c1e8c0e881e880e841e801e800e800e7c1e781e780e741e740e740e701e6c1e6c0e681e680e641e601e5c1e581e580e502e500e500e500e4c1e4c0e442e440e440e401e3c1e381e380e341e340e340e340e340e340e340e340e340e340e340e340e340e340e340e340e340e340e301e243e201e200e200e200e1c1e181e180e180e141e140e140e140e140e140e140e140e140e101e100e100e100e043df83df41df01df00df00dec1dec0dec0dec0dec0dec0dec0de81de80de80de41de01ddc1ddc0ddc0ddc0dd81dd41dd40dd01dd00db47da44da40da40d944d901d8c1d881d841d840d840d7c2d703d586d502d500d4c1d4c0d346d283d280d280d280d280d184d102d082cd4dcc83cc80cc41cc01cb82cb80cb41cb40cac2ca81ca80c945c7c6c6c4c642c5c2c503c404c3c1c303c243c201c143c101c0c1c0c0c003bf04bbcdbb81bac3b985b590b541b3c6b3c0b381b380b302b300b300b282b202b1c1b1c0b1c0b142b083b041af44af40ae83ae02adc1adc0ad42ac44ab83ab02a947a805a743a701a682a680a680a641a5c2a581a541a501a443a383a380a245a144a0449f839f419e839e419e019dc19d819cc39b07994798c2978596c39489938492c39242918391419101908290028f828f418f408f018f008ec18e428dc28d428d018c828a8888888880888088418609838a818881417f877c4d7b057a43774c75097482730672c1728171456d116b8669c7694268c2684263d25dd85c0759c95846568751d34c954a88465144873f553e443bca3b033ac13613340830cd30032d8a2a4d290526c9254624051d9a1a0e15530c25084f050d00530001 0x29f0604a6918029a4400a710e029ac480a61131e940600a591702968384a3918068c4404a311812924600a52130294c5d0a4a1b02908600a4b1b02910602a3b14428e8510a3c1b028cc585a211b02880600a2817028a8600a211702808385a1117128444c0a110f1e814607a021b02868604a131802850607a021b068284c0a0a0f1e8086c1a0213028083c0a0a1902804340a020e027e06c09f017027a05c09fc18027c44009f310027a06c27a817c9a4053583010520c03108300841ea01f069004e6654617992185e5846d77f81b0278460193814024e04009c80c027685c193010427446c77f81b027242409b01f066a05c09a813026603c19c4188270c6209ba188a6c85209b108426602d09a81f026805c09981f1e4a061192810426403906880841b801d0988055e4806109100841a0011098b121260470098114025e440098418825e462097117c25a453495b1b4a52c5e26e3148256c4d58020d81fe83409490e41b843178f8185e3806018f810463804009600a4256c4809521f1e3c07058031202550707900185e3a06007fa0e0252c4809411b0250c5348d918522c46058291056084404830181a4b061492a18523e46d48e11b023443108a90c123246148a118023244108a1100226450093909024cc5c089114024b05c48891c062045009231a061e44048601f02460641871141220470088114160644009131b921e46209080d4240c7009041f023ec5c48c11c023c87008ea18023cc6d08eb1b023884c08dd1c023305048ba1c220a47008d41b823306208c21b822e86226b217899e85208921381ac83e067a0c961646e582918921606e4828188230c4058bd1c122f07008bc14022d0603884148228c401882106208460288c14c22ac5e08a3148a26c43088a14c226833584917960845237d913c22443f17d90bd21205e48201489f604f08900fc1f602f088c140221062087a1b961046e581918821c425086813421a450286b14821a8310858184212060086117021007007d1170216c700850170a11461084a18021046108381f0a0ec52083a0c49f205e07c80b820d060082918420846008191c020407c08001f060b470082c1c0a074611824180208c60081a184a05061081118420006d27e81781fa02e280c14c202453080017c9a804f267010c1a801f067004ddfe06c27e01785fc04c07f00f01f802e77f81b05fe04c07f80f01fc06407e81f01f807407d91401aec4807d01701f705007d11701f207c47c11f01f045c07b11301f106207bb1b81ecc6207ad1c1dd847c17611711c644c07190f1db847007a11905d644c07590f1dd447c17511701d444c06f10f01e687c17921701e484c07810f05e245c07891301e043c07780901da45c17211701dcc7c076b1401c8c4817221711d8c7007631401d4c40771a1c05c6850073a1301bc84007641891ccc6e471b1881d2c4d075a1b81d486216c01041d2c5016ea1401d0c6e073b1885bac4d07321885ae04116eb1701ca87c07221305c7062071b1881c486e070a1b41c086c06fa1941bc86216ea1341ba83d06e31211b647c06d91701b244c06dc1881b4c6e06cb1881b085c06b11401b0c5006bb1201aa05c06b41401aa45c06a01f01a602406951c019a06c768a1c019805c06581b019406c068b1201a0c6e76281b819e85006481b019f05006401b018e06c06711f018c06c166c18819ac6206621b8196862164810419203106500a418c021464b188192c42464118819044246381b918c062063813818c04206291b818906074e81848bc05f223014c53a04143a80c40ea02102f007c08c0139594185d6446175481b418605922e813c88a04314e00c413802102e807c08a01374d81848b805f222014c53604104d80c40d602102e007c088013061117053405104d010417203102180840b201d060806418001525ea1b88b286215fa17457c85c05fa13417c84c05a20f417883c05e90a40b242114c814413204105a00c48b045f221114c0b042f021108c17801e05da18097485005d1080972c6205ca0c416843d05c01f416e07c25981b856c05d15a817016c04d05a813016803d05980b8164c4874c01c453005153a010412a031020008409a01d056806415801555821b916046e058b1b816046274b818c15e03904a008407e01105711b815b063056418d15646245511801564420551100152c4845421f514887c25021b889a862054217414885c053213414484c05010a409a42174901c5d1c070149014451c05053981054e404005451c814f07e05341c814a87e03420f1d220720524188146c6e051318913c06e749818dd20062034008414286e747818814106304f917053cc6e04f11b913ac7024ab18813ac5004db10012a83174691c5d12470146914451245004791314e24415381101cea07023081b84ea05004001300d604003080b993146304ec188138c6e04db188934c5344c218c13483344911bd11c46e446918d112462225917c87c453046110411044004c90fc09642f01f108d0fe06e43a81888cc05f042813413203f03300bc13107204ba1f910e47214311410fc07e43a01c812c02504ac18d12886e04a213910c462043110910806f43c018c10804f03c010c12707e04931c911647213391410f807e43981c8122c6f04831b811ec62133b13411c86243d81b90e4062146d1c811b072046414011687e04521c889286e21ea1884ce85c033a13009283e01ea0c94f447e53891c850644d03b11310f407e43881c810605d13b017090f463144c188d0d052044b18890cc52044310010e863143210410c83153c91b94e0462332117c4ce44d14110f44c842f43c81b90e0062232017c10404d03380f40c802f242318810ac5004220c410645104111408c606e13501400c602e23f518c102c6e04031888fac5313531340fe86203f118c0fa43303e01bc0f606e03d018c0f2062224017c87805313b010409001f01e004c8f106203c31048c446e13511700c443e03b81f00ec04c23a518c4eb06203ab1880e886303991bc0e446e038918c0e0462223917c87645302390bc07642303781b80dc06d03681b00d806503581888d205f13501340d403d03480bd0d0c6e03431390ce46203391090cd07203341490ca87e032a1790c847203211490c607e43101c80c605e03101480c306343011b80c044e02f81b04bd47202f41c80bac7e02e31c9ca647e72691c84ae45d12911700ae44d02911300b643e02a90f409c43c02d10d40b2432125814409604102c00e408e03142bc1c80af05242b31f90aac7202b31780aac5242a11f80a845e029c18d0a4c6202931090a286f42821b909e86342721880a284f028213809e8430272109c94063125010c09b06342611b809844e425c1c809705242521f809485e42491c809245242401f908e072024017808e05212351c808d072022b1f8088c7272021c808683211f114407c44102110e407643171c01f807406c02080f808106341fa1b807e84e71b01b846c04e41f41c807d05241ea1c807a85241e11f907647201e117807645201c81b1474c5341d214c07483371c814c47203301c808c07106341ba1b806e84e41b118806c442916518c46b06201ab18806886e019a18886485e218a14c852852716118c064429018908c05242171301bdc40063208017c81605310f810403e03101800bc04602d01780a405c025016808c02a021008007c016013016418d056862015a10905446e414918805444e0149109c3c06310f010c03a031005008401a01d014006404e015013418d04a86f41221b9046862211217881a852012a13c04884e011a10802883d01110a401a42141081b9c3806370d818804204e10e010c43604200a00c583d463010418c83d05340fb18883ac5200fb10903c86300f210c03a83140e11bd03646e40d118d032462206117c81245300e113c03644e00d110c03244200a10f401842f004908d03006f40b81b902c06340a818882605f209017882205300c013c02e04e00b010c02a04200a00f402602f00900b8022023508418d020c63008310dc1e46f70711b9c1a462107913c41c44e106910801e43f00710f801a432706018c41804300600cd417063405b18c016c43705218841484200520c9c12463104910c01243370381b801005c103813800e03e902c14d40cc53302b10d00c853202a10c00c833702914c40a433002908dc0805f701814c80404f200810c40803f10180cc00802f001808c00401f000804c00003f 16 6 13 9 4
def q97D : Forest := fun i => decodeNode 9 22 0x8304e4871326244c48992e41c4a58bb1d6364660c1188364498b11043042c8b9094303c20c0e4432379070da830339880c903631c8c0c142e3008d8be2122e98c4b84312e0842b803e2dc0b8b703e2d4072b36242b60c4ac2312b08beab229aac052aa6242a60e0a66242858a6a021226d8b89a82e2658d0980322618dc9501aa560f89362e24d8da8f63623d0988fa3823a0dc8d8312358808c82822e0c08a62f2258a489419a2407e898282220c48743721c84a87418a0c8b87f6381ec0b87b4301e88c27a4189e20c0768381c98c0714309c48c2702299b80be6e01e1b00c86b03e1a80e86a8281948b86403e18e0c4616371858c461a3817c8c85e43e1710985c2261688785a0121658f8566281560c45343714d0c4536281498dc516311450c45143e1410985063113d0dc4f43693d0d84f43293d0c44f41e93d8904e8311358dc4d6311358a04b62412e0a04a22e1240f8480121228e0476241058dc408280f88f83c6310ed0dc3b4310ec0523b6210e88843a0270e80843a2370de0c03602c8d48b83300c8c802a324268c5098312148c403c304300bc8402f4188b80fa2e03e0b809a2e0260b807a2e0170b98902d6370ac8c42b01c8ac8dc2a8318a60c6282210a08802862409e8e42683f09a0e42643f09a0c4256370958c4254370920c62322e08c8dc228310818dc206310810662001f8820e41f43f07c04a1f83187909c1e83f0758e41d6378718dc1c6310710c41c83906e0a01b43f06d0e41b6310698801a4318690621a628065062192288648a0196370618c4184310608c6182198600de180370600c6180310618821703e05c098176310590c6162378588dc162318588c4160370580da160360580ca1603105807a1601785989c152210560a41442f0508a41402f0500a41483184c89c1303604a0e41163f0458e41121f04486a11219044072118290418bc106290408bc1083183d8840f42783d09c0f42183d0840f83183889c0e8290350bc0d2290340bc0d0290360e40c63f0318e40c4190308720c01f0320c60b42702e0a40a4290288bc0a229029066090118260c6084270208840863101d0dc0743101c8520721181c05e0701481c04a0701181e0c60642101889c062210180320600a81a0c60542781509c05421014852050270160c6046210110860441881089e042270108860422101009e040270100860402101007a0401781005c040118118860321f80c87c0321900c06603621809064022198080b80201f0090660121180405e0101180403e0100980407e00 i
def q97T := dagTraceTagsBin q97M 82 (dagTagBases q97N 0x41395f3ffec22c4873bbbfffe7ddcef2676de3dd704c062c70f60f20ef8ffe200b9ca80efc0fc7fe3ffef7f1b9cc1ddc93bffc65c746303c0fffffd1108 0xffbd9ffffedaadc9f3bbbfffe7ddcef8ab6df5dd7effe70f7af65fa3efd7fffbeffca16efd5fdfff5ffff6fcbcce1dde49bffe9453ffffffffffffdbbbd 82) 10 q97D
def q97St := dagTraceBin q97M q97N 10 q97D
def q97Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q97Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q97Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q97Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q97Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 5, 4, 3, 2, 7] 0 i.val)
def q97Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 5, 4, 3, 2, 7] 0 i.val)
def q97Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q97Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q97Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q97Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q97Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 0, 4, 5, 2, 7] 0 i.val)
def q97Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 0, 4, 5, 2, 7] 0 i.val)
def q97Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q97Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q97Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q97Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q97Mp8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 5, 4, 0, 2, 7] 0 i.val)
def q97Mi8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 0, 4, 3, 2, 7] 0 i.val)
def q97Mv := dagMoves ([([qS5], q97Mp0, q97Mi0), ([qS42], q97Mp1, q97Mi1), ([qS42, qS5], q97Mp2, q97Mi2), ([qS7], q97Mp3, q97Mi3), ([qS36, qS5], q97Mp4, q97Mi4), ([qS7, qS42], q97Mp5, q97Mi5), ([qS7, qS5], q97Mp6, q97Mi6), ([qS36], q97Mp7, q97Mi7), ([qS7, qS42, qS5], q97Mp8, q97Mi8)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97A : DagMovesOK q97M q97G 256 q97Mv := dagMovesOfCheck (by decide +kernel)
def q97NB : Nat → List Bound := dagNodeBounds q97C.toArray 0xe447910e443910e443910e443910e443910e443910e443901e403900e38b8d1e3438c1e2c78a1e247881e1c7870e187851e143850e0cb812e007800df8b7d1df077a2de83782dd8b751dd43741dcc7730dcc3703dbc76d2da8f691da07671d94b632d84b601d6d7583d54f541d48b511d4074f1d3874d1d2cb4a1d1cf470d187442d0c7412d0073f1cfc33f0cfc33e1cf833e0cf0b3b1cec33a1ce83391cd8f360cd47341ccc7321cc47301cb8b2d1cb432c1cac72a1ca47281ca03271c987260c947232c8c3230c887220c847210c8431f2c7871c2c6c71b0c6c3183c58b151c453101c38b0e0c3830e0c3470c1c3030b1c2c3074c097002be9af46bcc6ef4bb0ee75b94ae32b796dc2b612d71b54ad32b40ece2b256c63b10ac22afceba5ad56b23ac46ae3aacea92a952a05a65e936a44a8c5a212862a10a8049f4e7949e067629c927029a9a67398965f3970e584958a515938e49591524148f163578cca2f48b4a294898e22486de13883d20c3828a073810e0047f11f757d0df047b89eb37a85e737949e237719d8474d5d0372d5c9271c9c5270c9c126f8dbc26e89b826d4db146bc9ac36a89a82694da506905a4068119d3668d982654d905638988661898155f517945d8d7335c496f25b856b3599563357955c2564d53654494d4525146350cd3e54e913554cc93034b1127548951f3461d13543d1096409cfc63e10f443bd4eb4391cdd73650d273390c863110bd72d9caf72a94a6427dc98724988b720e07b81ce07031a9866418545a715544f612d04560f603850c982d50a50245075c16704180a60118004 0x61ce5015e00001001c0f41c001008779c020284002849080001004011966524260242061c00080210842a0016600cc001800100e21004c01ca00000d38802020881000d18802208e21306700ce309c437318771065024220182051427019ec288e0024a1014234844030802018a008ca0198a001405014611814611c0009ce60bc813c083381e2410e838806101660180b5080a498205a4c110149304025096419c22410a2100c049820484063b000081810186120c27008813ad46101420296649820101493040a301232840a3080b5180a484c04946151801000640980309c40119260a90a4844032d4448402321460382608d6a02d405a1405a0c04102018ca6484063002e32d6602c0b301690986028c0620065318604840231801188c23104408ce11990c20404280260b9801004028045680446808d7018521c0d11c64111a412065411a42806438804280472084721c47239c362c6008861130a338023514c418041384ec1844309c43089c11b881115cc28944088c252c2240c8048c22024611006103585184e049423024230208518811698451808609c6028c012040728ce00a0813c0a21a087224c508c042804a224251008500903204a221402224a130c0928c2430086614030a0e418485008c54848200d21008855188328123090453212628464020892846032089098a3008a6410a018504284671182d7088500da82144d120851a085139870144e0904028da8190a173065089042844821448214606a08509c690a06428a2d410a36a08510d042886d410a3 14 4 5
def q97Ck := dagCheckNodeFast q97M q97G q97NB 336 q97St q97Mv q97L q97S q97T
def q97RA (token : Nat) : Bool :=
  let s := rootState q97N 10 token
  !dagAllowedRootBin q97M q97E s.2.1 || dagLocalBin q97M q97G (dagKnownClosesBin q97G q97C) s ||
  dagRefBin q97M 336 q97St q97Mv (fun p tok => dagFindLink (q97L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97RB0 : treeBlock 0 64 q97RA = true := by decide +kernel
theorem q97R : dagCheckRootsBin q97M q97G (dagKnownClosesBin q97G q97C) q97E (dagRefBin q97M 336 q97St q97Mv (fun p tok => dagFindLink (q97L p) tok) 0) q97N 10 = true := q97RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B0 : treeBlock 0 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B16 : treeBlock 16 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B32 : treeBlock 32 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B48 : treeBlock 48 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B64 : treeBlock 64 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B80 : treeBlock 80 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B96 : treeBlock 96 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B112 : treeBlock 112 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B128 : treeBlock 128 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B144 : treeBlock 144 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B160 : treeBlock 160 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B176 : treeBlock 176 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B192 : treeBlock 192 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B208 : treeBlock 208 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B224 : treeBlock 224 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B240 : treeBlock 240 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B256 : treeBlock 256 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B272 : treeBlock 272 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B288 : treeBlock 288 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B304 : treeBlock 304 16 q97Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97B320 : treeBlock 320 16 q97Ck = true := by decide +kernel
theorem q97Bf : treeBlock 0 336 q97Ck = true := (@treeBlock_merge 0 176 160 q97Ck (@treeBlock_merge 0 96 80 q97Ck (@treeBlock_merge 0 48 48 q97Ck (@treeBlock_merge 0 32 16 q97Ck (@treeBlock_merge 0 16 16 q97Ck q97B0 q97B16) q97B32) (@treeBlock_merge 48 32 16 q97Ck (@treeBlock_merge 48 16 16 q97Ck q97B48 q97B64) q97B80)) (@treeBlock_merge 96 48 32 q97Ck (@treeBlock_merge 96 32 16 q97Ck (@treeBlock_merge 96 16 16 q97Ck q97B96 q97B112) q97B128) (@treeBlock_merge 144 16 16 q97Ck q97B144 q97B160))) (@treeBlock_merge 176 80 80 q97Ck (@treeBlock_merge 176 48 32 q97Ck (@treeBlock_merge 176 32 16 q97Ck (@treeBlock_merge 176 16 16 q97Ck q97B176 q97B192) q97B208) (@treeBlock_merge 224 16 16 q97Ck q97B224 q97B240)) (@treeBlock_merge 256 48 32 q97Ck (@treeBlock_merge 256 32 16 q97Ck (@treeBlock_merge 256 16 16 q97Ck q97B256 q97B272) q97B288) (@treeBlock_merge 304 16 16 q97Ck q97B304 q97B320))))
theorem q97Bk : treeBlock 0 336 (dagCheckNodeBin q97M q97G q97NB 336 q97St q97Mv q97L q97S q97T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q97Bf
theorem q97K : KnownBin q97C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q58Bin) q46Bin) q23Bin) q6Bin) q64Bin) q4Bin) q33Bin) q35Bin) q9Bin) q78Bin) q3Bin) q39Bin) q75Bin) q77Bin) q43Bin) q0Bin) q11Bin) q8Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97Bin : BinLower q97M q97W q97G 11 := by
  apply lowerDagBin _ _ _ _ q97A _ _ _ q97K _ (fun _ b hb => dagNodeBounds_mem b hb) q97R q97Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q97C.all (fun b => q97M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q98M : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev q98G : Word := qGoal &&& q98M
abbrev q98W : List Word := projectDAGStock q98M qBase [0, 1, 4, 5, 6, 7]
def q98F : Bound := (q98M, q98W, 10, q98G)
def q98E := unpackWitnesses q98W [74384, 337040, 581728, 876688, 1155216, 1425504]
abbrev q98N : List Word := normStock q98M q98W
def q98C : List Bound := [q2F, q15F, q12F, q65F, q62F, q5F, q4F, q7F, q47F, q72F, q79F, q21F, q48F, q16F, q50F, q54F, q92F]
def q98S : DagSample := (0x3020820a02090c023118088603220908c02230188062320944225148301209101a09209201a0d20b0182c060a03030120d020b04c0e00884c22120184c6031018480422100886012088c4c07008884064330184c021201088050181c0826120884402140204201201209008248048041208a4422810088500a01028002810110880c0403012050, 60)
def q98L : DagLinkList := dagExtractLinks 0xbe0be0be0be0be0be0bc1ba1b81b80b80b80b61b60b60b60b60b60b03ac2a82a80a80a80a80a61a41a02a009e19649419028a38248017e17e07e07c162d5e24c94634413862c6263032001 0x6045060c4060c505e44cd0c60504405a02cd7870cec605c43e5a4325845044430590505643f4a07c54c40c885c524604807c4607c54c525045252851508314e43d4d0594ac434844346433444404483222033b5469ad4619ac52a0852c245ec04533c053340492c041200311a02142019400133f053a6853ab4609e8513c8332a4401e432ba03fb803e3a02f3802e37059b1051348333203e310592f0512c8332a442184222803f270532485322843208311e4521c06c1a832184401603e8b05989053870518ec43928538284394833144538444312433104230e0530c0430a039080330603104023020130003f 12 5 13 6 1
def q98D : Forest := fun i => decodeNode 6 19 0x314292264a43e74864ec141621facc52450a2820c5021ea10593d8867910cf2199e832340324804c9829908331c05e380b8782c8c8331807c2c16448288883310884200fc4829868530d0861a0c432290606c0d06411100201f04453048660908c10298204304072080cc10188202304026080fc0 i
def q98T := dagTraceTagsBin q98M 60 (dagTagBases q98N 0xcf8b7d4f4387c6f503c7f10edf83f7ebca9b063e7b1fea23f8ee9130ff1fdd47f0ffa43fff03ff000fffff4c89 0xcd8d7d174f9fc6fffbd7fd3effdbf7b3e28b2e5f7b4fe727fc6ecb36ffdf5c5ff4ffb09fffbfff2bbfffff67bc 60) 9 q98D
def q98St := dagTraceBin q98M q98N 9 q98D
def q98Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 7, 2, 3, 0, 6, 5, 1] 0 i.val)
def q98Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 7, 2, 3, 0, 6, 5, 1] 0 i.val)
def q98Mv := dagMoves ([([qS23, qS45, qS2], q98Mp0, q98Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98A : DagMovesOK q98M q98G 256 q98Mv := dagMovesOfCheck (by decide +kernel)
def q98NB : Nat → List Bound := dagNodeBounds q98C.toArray 0xa50a50a32a30a129f29d29b29839719619609519509238d58948728257f37a57827627427227026e26a46826536055e25685154d44944634153f23b43292e42682061c41660d9076007 0x20082411ca41ac82100e30042600d6d1880202c8110c60088c3004c001820080410808200420284c3394800956728824400830a84a41c0130c031042600da22a4e12b9641a0e1115422812410d4130124030461300161049081ea20c4809c09404a21c1ee52588 12 4 5
def q98Ck := dagCheckNodeFast q98M q98G q98NB 49 q98St q98Mv q98L q98S q98T
def q98RA (token : Nat) : Bool :=
  let s := rootState q98N 9 token
  !dagAllowedRootBin q98M q98E s.2.1 || dagLocalBin q98M q98G (dagKnownClosesBin q98G q98C) s ||
  dagRefBin q98M 49 q98St q98Mv (fun p tok => dagFindLink (q98L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98RB0 : treeBlock 0 64 q98RA = true := by decide +kernel
theorem q98R : dagCheckRootsBin q98M q98G (dagKnownClosesBin q98G q98C) q98E (dagRefBin q98M 49 q98St q98Mv (fun p tok => dagFindLink (q98L p) tok) 0) q98N 9 = true := q98RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98B0 : treeBlock 0 16 q98Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98B16 : treeBlock 16 16 q98Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98B32 : treeBlock 32 16 q98Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98B48 : treeBlock 48 1 q98Ck = true := by decide +kernel
theorem q98Bf : treeBlock 0 49 q98Ck = true := (@treeBlock_merge 0 32 17 q98Ck (@treeBlock_merge 0 16 16 q98Ck q98B0 q98B16) (@treeBlock_merge 32 16 1 q98Ck q98B32 q98B48))
theorem q98Bk : treeBlock 0 49 (dagCheckNodeBin q98M q98G q98NB 49 q98St q98Mv q98L q98S q98T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q98Bf
theorem q98K : KnownBin q98C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q92Bin) q54Bin) q50Bin) q16Bin) q48Bin) q21Bin) q79Bin) q72Bin) q47Bin) q7Bin) q4Bin) q5Bin) q62Bin) q65Bin) q12Bin) q15Bin) q2Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98Bin : BinLower q98M q98W q98G 10 := by
  apply lowerDagBin _ _ _ _ q98A _ _ _ q98K _ (fun _ b hb => dagNodeBounds_mem b hb) q98R q98Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q98C.all (fun b => q98M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q99M : Word := 0x55005500550055005500550055005500550055005500550055005500550055
abbrev q99G : Word := qGoal &&& q99M
abbrev q99W : List Word := projectDAGStock q99M qBase [1, 2, 4, 5, 6, 7]
def q99F : Bound := (q99M, q99W, 9, q99G)
def q99E := unpackWitnesses q99W [74896, 338064, 581728, 876688, 1155216, 1425504]
abbrev q99N : List Word := normStock q99M q99W
def q99C : List Bound := [q2F, q5F, q8F, q19F, q29F, q7F, q27F, q39F, q41F, q51F, q52F, q54F]
def q99S : DagSample := (0xc022302806050480480c460321860a048340c0e00a058281203059209403048402203098c0640308920b0301c0c0502010820502014028441219048440804900822011100840104828940a21004221028100a01221004820110880c0403012050, 43)
def q99L : DagLinkList := dagExtractLinks 0x4508a11062043186100e003d3782e11b8b52682d01a0304600a9939a163c66ccc917220e1e40b001 0x360401b6202cb141e48a0324301a4280ca0c1dc0a035050196210c01385c0842c03d182103bc1405d0602c8301582929b149cc8a4224309243019a0c2c88c0264408f030060172ca8c0288603241809c148490a4228301002f0781483809a19050302100800c23e8c05e8300f2201720c0388801b05e0c82935c149250a61683167229039089a80a61402309a311421889d06010462072200301b8140c40805d0302e414149048a644421610298100c4040260003f 11 4 13 5 3
def q99D : Forest := fun i => decodeNode 5 18 0x620620a1362148841141841060f829310c09829210a4841820060722018880582f120a444188c0463a31088c42220080dc2031080ba202e0806210098407e0 i
def q99T := dagTraceTagsBin q99M 43 (dagTagBases q99N 0x18e22ef9b73f9d33f8c9dfce83c4ee7fc7af81f7f8ff59fd806ff85c3beffa909 0x3cfaafffb73f9c55f8f9dfcc97dd6f3fc3afacf3fd7cfdfd8beffdf77beffafbc 43) 8 q99D
def q99St := dagTraceBin q99M q99N 8 q99D
def q99Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 5, 4, 7, 6] 0 i.val)
def q99Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 5, 4, 7, 6] 0 i.val)
def q99Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 5, 2, 1, 6] 0 i.val)
def q99Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 2, 4, 7, 1] 0 i.val)
def q99Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 4, 2, 1, 7] 0 i.val)
def q99Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 4, 2, 1, 7] 0 i.val)
def q99Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q99Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q99Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 2, 4, 7, 1] 0 i.val)
def q99Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 5, 2, 1, 6] 0 i.val)
def q99Mv := dagMoves ([([qS6, qS4], q99Mp0, q99Mi0), ([qS45, qS25, qS6, qS4], q99Mp1, q99Mi1), ([qS40, qS38], q99Mp2, q99Mi2), ([qS45, qS25], q99Mp3, q99Mi3), ([qS40, qS38, qS6, qS4], q99Mp4, q99Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q99A : DagMovesOK q99M q99G 256 q99Mv := dagMovesOfCheck (by decide +kernel)
def q99NB : Nat → List Bound := dagNodeBounds q99C.toArray 0x80402010080402010080401f2f878bc1e0f07134992c155a850879351306606 0x1104161301087450103210210ba9210 9 3 4
def q99Ck := dagCheckNodeFast q99M q99G q99NB 28 q99St q99Mv q99L q99S q99T
def q99RA (token : Nat) : Bool :=
  let s := rootState q99N 8 token
  !dagAllowedRootBin q99M q99E s.2.1 || dagLocalBin q99M q99G (dagKnownClosesBin q99G q99C) s ||
  dagRefBin q99M 28 q99St q99Mv (fun p tok => dagFindLink (q99L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q99RB0 : treeBlock 0 64 q99RA = true := by decide +kernel
theorem q99R : dagCheckRootsBin q99M q99G (dagKnownClosesBin q99G q99C) q99E (dagRefBin q99M 28 q99St q99Mv (fun p tok => dagFindLink (q99L p) tok) 0) q99N 8 = true := q99RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q99B0 : treeBlock 0 16 q99Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q99B16 : treeBlock 16 12 q99Ck = true := by decide +kernel
theorem q99Bf : treeBlock 0 28 q99Ck = true := (@treeBlock_merge 0 16 12 q99Ck q99B0 q99B16)
theorem q99Bk : treeBlock 0 28 (dagCheckNodeBin q99M q99G q99NB 28 q99St q99Mv q99L q99S q99T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q99Bf
theorem q99K : KnownBin q99C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q54Bin) q52Bin) q51Bin) q41Bin) q39Bin) q27Bin) q7Bin) q29Bin) q19Bin) q8Bin) q5Bin) q2Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q99Bin : BinLower q99M q99W q99G 9 := by
  apply lowerDagBin _ _ _ _ q99A _ _ _ q99K _ (fun _ b hb => dagNodeBounds_mem b hb) q99R q99Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q99C.all (fun b => q99M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q100M : Word := 0x55555555000000005555555500000000555555550000000055555555
abbrev q100G : Word := qGoal &&& q100M
abbrev q100W : List Word := projectDAGStock q100M qBase [1, 2, 3, 4, 6, 7]
def q100F : Bound := (q100M, q100W, 9, q100G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q100Bin : BinLower q100M q100W q100G 9 := dagShiftLowerBin (width := 256) [qS7] q95Bin (by decide +kernel)
def q101M : Word := 0x505050505050505050505050505050505050505050505050505050505050505
abbrev q101G : Word := qGoal &&& q101M
abbrev q101W : List Word := projectDAGStock q101M qBase [1, 3, 4, 5, 6, 7]
def q101F : Bound := (q101M, q101W, 10, q101G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q101Bin : BinLower q101M q101W q101G 10 := dagShiftLowerBin (width := 256) [qS7, qS9] q98Bin (by decide +kernel)
def q102M : Word := 0xf0f0f0f0f0f0f0ff0f0f0f0f0f0f0f0
abbrev q102G : Word := qGoal &&& q102M
abbrev q102W : List Word := projectDAGStock q102M qBase [0, 1, 2, 3, 4, 5]
def q102F : Bound := (q102M, q102W, 10, q102G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102Bin : BinLower q102M q102W q102G 10 := dagShiftLowerBin (width := 256) [qS22, qS27, qS42, qS11] q93Bin (by decide +kernel)
def q103M : Word := 0xf0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0
abbrev q103G : Word := qGoal &&& q103M
abbrev q103W : List Word := projectDAGStock q103M qBase [0, 1, 2, 3, 4, 5]
def q103F : Bound := (q103M, q103W, 10, q103G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q103Bin : BinLower q103M q103W q103G 10 := dagShiftLowerBin (width := 256) [qS29, qS27, qS42, qS2, qS4] q94Bin (by decide +kernel)
def q104M : Word := 0x333300003333333300003333000000003333000033333333000033330000
abbrev q104G : Word := qGoal &&& q104M
abbrev q104W : List Word := projectDAGStock q104M qBase [0, 2, 3, 4, 5, 7]
def q104F : Bound := (q104M, q104W, 11, q104G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q104Bin : BinLower q104M q104W q104G 11 := dagShiftLowerBin (width := 256) [qS22, qS34, qS11] q97Bin (by decide +kernel)
def q105M : Word := 0xaaaaffffaaaaffffaaaaffffaaaaffff
abbrev q105G : Word := qGoal &&& q105M
abbrev q105W : List Word := projectDAGStock q105M qBase [0, 1, 2, 3, 4, 5, 6]
def q105F : Bound := (q105M, q105W, 10, q105G)
def q105E := unpackWitnesses q105W [49760, 312416, 575584, 839776, 1090113, 1364040, 1624100]
abbrev q105N : List Word := normStock q105M q105W
def q105C : List Bound := [q0F, q12F, q11F, q61F, q85F, q83F, q71F, q84F]
def q105S : DagSample := (0x2130a84c0e0f0a8342a2503118184c0a9540a4502110482612088060b24128060902834904c028240e170384c221908824140b0884c140906034824506024041302894c064028841028100a01422088c422210108840211008880422011002090512882492082406130894482510a91410090190c9049240240442008844864209848221, 59)
def q105L : DagLinkList := dagExtractLinks 0xc8c8c1b9b1b0a9a1a0a08b7a5c43320d01 0x1ec507c181f460711b5d4706c1858c42490c5b8705b14194625c1894863381753462411bcc05d3b108c4312d18890631b108443108174007f 8 3 13 4 1
def q105D : Forest := fun i => decodeNode 5 18 0xa30328e09c38168c44831110c64a310c8de3621088622a31060c6162104862102e840fe0 i
def q105T := dagTraceTagsBin q105M 59 (dagTagBases q105N 0x378799efb4dbdbf00797e67fefefde6f818979fe1e9f3effc6f7effc7fe0ce90005cba0053df3fffe003fff87c1dbfeeff93129 0x1b7eb9aefb7dbdbe003a3eabfffefdfefdbe97aff7e9fa6fff2ffe7febfe0ce905b5cfa05d3ff3ffff6f3fffdfffdbfeeff99b9c 59) 9 q105D
def q105St := dagTraceBin q105M q105N 9 q105D
def q105Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q105A : DagMovesOK q105M q105G 256 q105Mv := dagMovesOfCheck (by decide +kernel)
def q105NB : Nat → List Bound := dagNodeBounds q105C.toArray 0x994c245127dbc5c4d9652e946923a1507607 0x4822900864110822a05a0611e3588 9 3 3
def q105Ck := dagCheckNodeFast q105M q105G q105NB 16 q105St q105Mv q105L q105S q105T
def q105RA (token : Nat) : Bool :=
  let s := rootState q105N 9 token
  !dagAllowedRootBin q105M q105E s.2.1 || dagLocalBin q105M q105G (dagKnownClosesBin q105G q105C) s ||
  dagRefBin q105M 16 q105St q105Mv (fun p tok => dagFindLink (q105L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q105RB0 : treeBlock 0 64 q105RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q105RB64 : treeBlock 64 64 q105RA = true := by decide +kernel
theorem q105R : dagCheckRootsBin q105M q105G (dagKnownClosesBin q105G q105C) q105E (dagRefBin q105M 16 q105St q105Mv (fun p tok => dagFindLink (q105L p) tok) 0) q105N 9 = true := (@treeBlock_merge 0 64 64 q105RA q105RB0 q105RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q105B0 : treeBlock 0 16 q105Ck = true := by decide +kernel
theorem q105Bf : treeBlock 0 16 q105Ck = true := q105B0
theorem q105Bk : treeBlock 0 16 (dagCheckNodeBin q105M q105G q105NB 16 q105St q105Mv q105L q105S q105T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q105Bf
theorem q105K : KnownBin q105C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q84Bin) q71Bin) q83Bin) q85Bin) q61Bin) q11Bin) q12Bin) q0Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q105Bin : BinLower q105M q105W q105G 10 := by
  apply lowerDagBin _ _ _ _ q105A _ _ _ q105K _ (fun _ b hb => dagNodeBounds_mem b hb) q105R q105Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q105C.all (fun b => q105M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q106M : Word := 0xffffffffffffffffaaaaaaaaaaaaaaaa
abbrev q106G : Word := qGoal &&& q106M
abbrev q106W : List Word := projectDAGStock q106M qBase [0, 1, 2, 3, 4, 5, 6]
def q106F : Bound := (q106M, q106W, 10, q106G)
def q106E := unpackWitnesses q106W [49760, 312416, 575584, 839776, 1106016, 1364040, 1616405]
abbrev q106N : List Word := normStock q106M q106W
def q106C : List Bound := [q11F, q12F, q88F]
def q106S : DagSample := (0xa31201842a45009448051089408243209402a35029100e470a954c021009848245209102a170a84c060b24128060902834904c028240e170384c905808864220924124c0610188cc062018840a25301900a21301a09068088c4c0700888490090884c80420291480440082482492082406130894480500190c0221209848221, 57)
def q106L : DagLinkList := dagExtractLinks 0x740e81d03a0721e03c0323640c81886f15c1b8168663cc080cf85d1381510a0019801 0x2f0602d0606ec4f6cc432e43b2c4336a04e2a01e2ac502ac682803d28c5022c5020c506684f648432642b244235a04e1a01e22c6a20c685ec421e4315804e1801e1ec505c03e1c01e1c05c9b469990521a869188419605f940531602f140239346b914698f4618d052cac531286b108690e8610c8414a8338a4530a4230804d4603f4403e420320601f0401e020120007f 11 5 13 5 2
def q106D : Forest := fun i => decodeNode 5 18 0x21dc48671634358a0c215a484696351d8d07628180b844348d08230178c0463435850d214308508212118409a100f8403c1009040fe0 i
def q106T := dagTraceTagsBin q106M 57 (dagTagBases q106N 0x2a089104b45043f77c3cf9ff9f6fbe18f2ff9ff3ffffffc0c3f9de3fb1379f87ff37e3cfdcffff000fff10111dbb2d2e2c5 0x240409134b55043ff7f5cfaffff6ebe1e747faff7ffffffeddbfddfffedb79ff3ff57f7fffdffff5adffff69e9dbb2d2aa6c 57) 9 q106D
def q106St := dagTraceBin q106M q106N 9 q106D
def q106Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q106Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q106Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q106Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q106Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def q106Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def q106Mv := dagMoves ([([qS5], q106Mp0, q106Mi0), ([qS24], q106Mp1, q106Mi1), ([qS24, qS5], q106Mp2, q106Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q106A : DagMovesOK q106M q106G 256 q106Mv := dagMovesOfCheck (by decide +kernel)
def q106NB : Nat → List Bound := dagNodeBounds q106C.toArray 0xa8a8a29d99958e867e766e66615d564e463b32271e160e03 0x415110504111244910464 8 2 2
def q106Ck := dagCheckNodeFast q106M q106G q106NB 24 q106St q106Mv q106L q106S q106T
def q106RA (token : Nat) : Bool :=
  let s := rootState q106N 9 token
  !dagAllowedRootBin q106M q106E s.2.1 || dagLocalBin q106M q106G (dagKnownClosesBin q106G q106C) s ||
  dagRefBin q106M 24 q106St q106Mv (fun p tok => dagFindLink (q106L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q106RB0 : treeBlock 0 64 q106RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q106RB64 : treeBlock 64 64 q106RA = true := by decide +kernel
theorem q106R : dagCheckRootsBin q106M q106G (dagKnownClosesBin q106G q106C) q106E (dagRefBin q106M 24 q106St q106Mv (fun p tok => dagFindLink (q106L p) tok) 0) q106N 9 = true := (@treeBlock_merge 0 64 64 q106RA q106RB0 q106RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q106B0 : treeBlock 0 16 q106Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q106B16 : treeBlock 16 8 q106Ck = true := by decide +kernel
theorem q106Bf : treeBlock 0 24 q106Ck = true := (@treeBlock_merge 0 16 8 q106Ck q106B0 q106B16)
theorem q106Bk : treeBlock 0 24 (dagCheckNodeBin q106M q106G q106NB 24 q106St q106Mv q106L q106S q106T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q106Bf
theorem q106K : KnownBin q106C := (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q88Bin) q12Bin) q11Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q106Bin : BinLower q106M q106W q106G 10 := by
  apply lowerDagBin _ _ _ _ q106A _ _ _ q106K _ (fun _ b hb => dagNodeBounds_mem b hb) q106R q106Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q106C.all (fun b => q106M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q107M : Word := 0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa
abbrev q107G : Word := qGoal &&& q107M
abbrev q107W : List Word := projectDAGStock q107M qBase [0, 1, 2, 3, 4, 6, 7]
def q107F : Bound := (q107M, q107W, 9, q107G)
def q107E := unpackWitnesses q107W [74384, 337040, 600208, 864400, 1090113, 1417360, 1671745]
abbrev q107N : List Word := normStock q107M q107W
def q107C : List Bound := [q12F, q33F, q42F]
def q107S : DagSample := (0xe47482480243039140251483402a170a84c060b018240a0d0282520910385d20944821022190882500812090c0a452092482090894482514830006820884c0683402080681209140a85402100a810082500880184c229108a0402810190c82c1403008281, 45)
def q107L : DagLinkList := dagExtractLinks 0xbc5e2f178bc5e2f178b8d8ac14ba0d026529944a2351184c05f2dc5e21ce44d209001e01 0xf5181e22cb2451690c0c9181c22e39050760bce4149b83034868648d0d51819a30308645e0c0ac180d230ac459288a2ad1a14834a6469308a29d188e43716862488dc51189122ea045c3e8e8711e0dc3c194602d0f0511e0921e108741e8d23414852348845f0c8a6110bc12118007f 9 3 13 5 1
def q107D : Forest := fun i => decodeNode 5 18 0x8b3682f460a51830428c0ca302d0c8a830248b28a341e0d27a31188dc622e988b86a3a148f05c3c128c0443c108f0421e110e83a34860a41234848be12298485e1211840fe0 i
def q107T := dagTraceTagsBin q107M 45 (dagTagBases q107N 0x22018032240871efbf0feeedbb1effc7ffff0f39ffe7fd878bf37fcfd0fff88fbfe377e9bf22288 0x220590222409bcefff57eeed997effebfffffffffffffdc7a1f57fe7fffffa5fbff577e9bf776fd 45) 8 q107D
def q107St := dagTraceBin q107M q107N 8 q107D
def q107Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q107A : DagMovesOK q107M q107G 256 q107Mv := dagMovesOfCheck (by decide +kernel)
def q107NB : Nat → List Bound := dagNodeBounds q107C.toArray 0x10204081020408101eb970e1c3568d1a3160b562c4c78c951c24402 0x1910104 7 2 2
def q107Ck := dagCheckNodeFast q107M q107G q107NB 31 q107St q107Mv q107L q107S q107T
def q107RA (token : Nat) : Bool :=
  let s := rootState q107N 8 token
  !dagAllowedRootBin q107M q107E s.2.1 || dagLocalBin q107M q107G (dagKnownClosesBin q107G q107C) s ||
  dagRefBin q107M 31 q107St q107Mv (fun p tok => dagFindLink (q107L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q107RB0 : treeBlock 0 64 q107RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q107RB64 : treeBlock 64 64 q107RA = true := by decide +kernel
theorem q107R : dagCheckRootsBin q107M q107G (dagKnownClosesBin q107G q107C) q107E (dagRefBin q107M 31 q107St q107Mv (fun p tok => dagFindLink (q107L p) tok) 0) q107N 8 = true := (@treeBlock_merge 0 64 64 q107RA q107RB0 q107RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q107B0 : treeBlock 0 16 q107Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q107B16 : treeBlock 16 15 q107Ck = true := by decide +kernel
theorem q107Bf : treeBlock 0 31 q107Ck = true := (@treeBlock_merge 0 16 15 q107Ck q107B0 q107B16)
theorem q107Bk : treeBlock 0 31 (dagCheckNodeBin q107M q107G q107NB 31 q107St q107Mv q107L q107S q107T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q107Bf
theorem q107K : KnownBin q107C := (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q42Bin) q33Bin) q12Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q107Bin : BinLower q107M q107W q107G 9 := by
  apply lowerDagBin _ _ _ _ q107A _ _ _ q107K _ (fun _ b hb => dagNodeBounds_mem b hb) q107R q107Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q107C.all (fun b => q107M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q108M : Word := 0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000
abbrev q108G : Word := qGoal &&& q108M
abbrev q108W : List Word := projectDAGStock q108M qBase [0, 1, 2, 3, 5, 6, 7]
def q108E := unpackWitnesses q108W [66176, 328832, 592000, 856192, 1130624, 1409152, 1687648]
abbrev q108N : List Word := normStock q108M q108W
def q108C : List Bound := [q39F]
def q108S : DagSample := (0x120944821120984822120b0482830184c02130188c022301a0c02840280402140204402240208c064122910084100a100881221040a012190c0e040300c0a0, 28)
def q108L : DagLinkList := dagExtractLinks 0x1007cbc5e0d4612ad427d2e10c1e01 0x2c8985a101a427308422885241084a6281244ce60a14a140942010c501d8a0b213944210c42910843b518266300cc5014899a5182463008c50ce8c11b18036282484e45084110a412108007f 9 3 13 4 2
def q108D : Forest := fun i => decodeNode 4 17 0x42053141d080cc50562823140c8986c502628090a44842207f0 i
def q108T := dagTraceTagsBin q108M 28 (dagTagBases q108N 0x3cf9fffcf3e7ff57ff8d7f3cff3f0002962fd5fbf1fff5488 0xffffffffffffff03ffdd7fffffff000a942fc0fbfafff56bd 28) 7 q108D
def q108St := dagTraceBin q108M q108N 7 q108D
def q108Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q108Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q108Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def q108Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def q108Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 0, 2, 1, 4, 5, 6, 7] 0 i.val)
def q108Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 0, 4, 5, 6, 7] 0 i.val)
def q108Mv := dagMoves ([([qS42], q108Mp0, q108Mi0), ([qS0], q108Mp1, q108Mi1), ([qS7, qS8], q108Mp2, q108Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q108A : DagMovesOK q108M q108G 256 q108Mv := dagMovesOfCheck (by decide +kernel)
def q108NB : Nat → List Bound := dagNodeBounds q108C.toArray 0xdb6b24691 0x0 3 1 1
def q108Ck := dagCheckNodeFast q108M q108G q108NB 12 q108St q108Mv q108L q108S q108T
def q108RA (token : Nat) : Bool :=
  let s := rootState q108N 7 token
  !dagAllowedRootBin q108M q108E s.2.1 || dagLocalBin q108M q108G (dagKnownClosesBin q108G q108C) s ||
  dagRefBin q108M 12 q108St q108Mv (fun p tok => dagFindLink (q108L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q108RB0 : treeBlock 0 64 q108RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q108RB64 : treeBlock 64 64 q108RA = true := by decide +kernel
theorem q108R : dagCheckRootsBin q108M q108G (dagKnownClosesBin q108G q108C) q108E (dagRefBin q108M 12 q108St q108Mv (fun p tok => dagFindLink (q108L p) tok) 0) q108N 7 = true := (@treeBlock_merge 0 64 64 q108RA q108RB0 q108RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q108B0 : treeBlock 0 12 q108Ck = true := by decide +kernel
theorem q108Bf : treeBlock 0 12 q108Ck = true := q108B0
theorem q108Bk : treeBlock 0 12 (dagCheckNodeBin q108M q108G q108NB 12 q108St q108Mv q108L q108S q108T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q108Bf
theorem q108K : KnownBin q108C := (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q39Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q108Bin : BinLower q108M q108W q108G 8 := by
  apply lowerDagBin _ _ _ _ q108A _ _ _ q108K _ (fun _ b hb => dagNodeBounds_mem b hb) q108R q108Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q108C.all (fun b => q108M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q109M : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000
abbrev q109G : Word := qGoal &&& q109M
abbrev q109W : List Word := projectDAGStock q109M qBase [0, 1, 2, 4, 5, 6, 7]
def q109F : Bound := (q109M, q109W, 8, q109G)
def q109E := unpackWitnesses q109W [74384, 337040, 600208, 843872, 1138832, 1417360, 1687648]
abbrev q109N : List Word := normStock q109M q109W
def q109C : List Bound := [q39F]
def q109S : DagSample := (0x3030120d01a21048251208448261208860311808460321808920944821120b030184c02130188c022181c100a01008500811008900823019048a440210c070182c060a01221040a012190c0e040300c0a0, 36)
def q109L : DagLinkList := dagExtractLinks 0x280a02719866094650906318c221809f1785e0781685093144901388c22c4a106401 0x65060cb101842030c40620a0ba0d178282c83054898ac14146212684e49084820f4f21e9a4292c842500c54a30228404e8c0951811620214603e8c0720d0da301844c2e8c0551809a3010c421d09c32108541e8843d0c8521108410188007f 10 4 13 5 1
def q109D : Forest := fun i => decodeNode 5 18 0x6205e0a128283d060f828368c09a30228c076201e8c06a30150685a30108984a300e8c02a3005884142705084141e8487a1214848421018840fe0 i
def q109T := dagTraceTagsBin q109M 36 (dagTagBases q109N 0xe67cf3ffff99f3cfffcbe7ff1d7beabdfe7fe018052223ffd5f6f11fe3ea908 0xffffffffffffffffffc1ffffbd79e03dff3f401c152027ffc3f6fabfe3eadfd 36) 7 q109D
def q109St := dagTraceBin q109M q109N 7 q109D
def q109Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q109A : DagMovesOK q109M q109G 256 q109Mv := dagMovesOfCheck (by decide +kernel)
def q109NB : Nat → List Bound := dagNodeBounds q109C.toArray 0x88888888888888875444444431 0x0 4 1 1
def q109Ck := dagCheckNodeFast q109M q109G q109NB 26 q109St q109Mv q109L q109S q109T
def q109RA (token : Nat) : Bool :=
  let s := rootState q109N 7 token
  !dagAllowedRootBin q109M q109E s.2.1 || dagLocalBin q109M q109G (dagKnownClosesBin q109G q109C) s ||
  dagRefBin q109M 26 q109St q109Mv (fun p tok => dagFindLink (q109L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q109RB0 : treeBlock 0 64 q109RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q109RB64 : treeBlock 64 64 q109RA = true := by decide +kernel
theorem q109R : dagCheckRootsBin q109M q109G (dagKnownClosesBin q109G q109C) q109E (dagRefBin q109M 26 q109St q109Mv (fun p tok => dagFindLink (q109L p) tok) 0) q109N 7 = true := (@treeBlock_merge 0 64 64 q109RA q109RB0 q109RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q109B0 : treeBlock 0 16 q109Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q109B16 : treeBlock 16 10 q109Ck = true := by decide +kernel
theorem q109Bf : treeBlock 0 26 q109Ck = true := (@treeBlock_merge 0 16 10 q109Ck q109B0 q109B16)
theorem q109Bk : treeBlock 0 26 (dagCheckNodeBin q109M q109G q109NB 26 q109St q109Mv q109L q109S q109T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q109Bf
theorem q109K : KnownBin q109C := (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q39Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q109Bin : BinLower q109M q109W q109G 8 := by
  apply lowerDagBin _ _ _ _ q109A _ _ _ q109K _ (fun _ b hb => dagNodeBounds_mem b hb) q109R q109Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q109C.all (fun b => q109M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q110M : Word := 0xff00ffffff00ffffff00ffffff00ffff
abbrev q110G : Word := qGoal &&& q110M
abbrev q110W : List Word := projectDAGStock q110M qBase [0, 1, 2, 3, 4, 5, 6]
def q110F : Bound := (q110M, q110W, 10, q110G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q110Bin : BinLower q110M q110W q110G 10 := dagShiftLowerBin (width := 256) [qS7] q105Bin (by decide +kernel)
def q111M : Word := 0xffffffffffffffffff00ff00ff00ff00
abbrev q111G : Word := qGoal &&& q111M
abbrev q111W : List Word := projectDAGStock q111M qBase [0, 1, 2, 3, 4, 5, 6]
def q111F : Bound := (q111M, q111W, 10, q111G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q111Bin : BinLower q111M q111W q111G 10 := dagShiftLowerBin (width := 256) [qS7] q106Bin (by decide +kernel)
def q112M : Word := 0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00
abbrev q112G : Word := qGoal &&& q112M
abbrev q112W : List Word := projectDAGStock q112M qBase [0, 1, 2, 3, 4, 6, 7]
def q112F : Bound := (q112M, q112W, 9, q112G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q112Bin : BinLower q112M q112W q112G 9 := dagShiftLowerBin (width := 256) [qS7] q107Bin (by decide +kernel)
def q113M : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa
abbrev q113G : Word := qGoal &&& q113M
abbrev q113W : List Word := projectDAGStock q113M qBase [0, 1, 2, 4, 5, 6, 7]
def q113F : Bound := (q113M, q113W, 9, q113G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q113Bin : BinLower q113M q113W q113G 9 := dagShiftLowerBin (width := 256) [qS5] q107Bin (by decide +kernel)
def q114M : Word := 0x5555555555555555555555555555555555005500550055005500550055005500
abbrev q114G : Word := qGoal &&& q114M
abbrev q114W : List Word := projectDAGStock q114M qBase [1, 2, 3, 4, 5, 6, 7]
def q114F : Bound := (q114M, q114W, 9, q114G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q114Bin : BinLower q114M q114W q114G 9 := dagShiftLowerBin (width := 256) [qS7, qS5] q107Bin (by decide +kernel)
def q115M : Word := 0x5555555555555555555555555555555555555555000000005555555500000000
abbrev q115G : Word := qGoal &&& q115M
abbrev q115W : List Word := projectDAGStock q115M qBase [1, 2, 3, 4, 5, 6, 7]
def q115F : Bound := (q115M, q115W, 8, q115G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q115Bin : BinLower q115M q115W q115G 8 := dagShiftLowerBin (width := 256) [qS0, qS8] q109Bin (by decide +kernel)
def q116M : Word := 0xff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f000
abbrev q116G : Word := qGoal &&& q116M
abbrev q116W : List Word := projectDAGStock q116M qBase [0, 1, 2, 4, 5, 6, 7]
def q116F : Bound := (q116M, q116W, 8, q116G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q116Bin : BinLower q116M q116W q116G 8 := dagShiftLowerBin (width := 256) [qS18, qS33, qS38, qS35, qS44, qS4] q108Bin (by decide +kernel)
def q117M : Word := 0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0
abbrev q117G : Word := qGoal &&& q117M
abbrev q117W : List Word := projectDAGStock q117M qBase [1, 2, 3, 4, 5, 6, 7]
def q117F : Bound := (q117M, q117W, 8, q117G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q117Bin : BinLower q117M q117W q117G 8 := dagShiftLowerBin (width := 256) [qS17, qS7, qS33, qS38, qS35, qS44, qS4] q108Bin (by decide +kernel)
def q118M : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev q118G : Word := qGoal &&& q118M
abbrev q118W : List Word := projectDAGStock q118M qBase [0, 1, 2, 3, 4, 5, 6, 7]
def q118E := unpackWitnesses q118W [74384, 337040, 600208, 864400, 1106016, 1400976, 1679504, 1949792]
abbrev q118N : List Word := normStock q118M q118W
def q118C : List Bound := [q97F, q12F, q95F, q111F, q93F, q45F, q94F, q70F, q13F, q51F, q100F, q99F, q11F, q106F, q74F, q113F, q98F, q107F, q114F, q96F, q112F, q109F, q67F, q72F, q101F, q116F, q47F, q80F, q71F, q103F, q105F, q110F, q102F, q104F, q115F, q117F]
def q118S : DagSample := (0x201a09028300a0c0210894406220188d209101a08068302a144825180c4c061008c40a45031180c860a250482c180e0142a060b03038301a0184c0c1609068181c1209805228188c0c26028840c22120b01229060b01828120d020b0490c83038022130502c140920914180d0602428160a048060b0c068060902834904c0282406130c064300903059209403048141a08864220910084042210088601202894c064028841028100a01422088c4c07008884064324124900920108144a2092482090814080500a1104864209848221040250081080480482402092012201100884402100a8100824108840220148201048229108a0402211028100a01221002810110880c0403012050, 118)
def q118L : DagLinkList := dagExtractLinks 0x25c097025c097025c096865a096825a096825a096825a0960656195065409502540940a500940250094025009402500940250094024e19306482910a3c48e0a3618d063218c062e18b822a2898a241888622088061c2860a123838a083810a00280020008001fe17f05fa17e05f807d09ee37b05ea17891dc37685da07605d807601d807395c456e95ba06d89b226b89a0767099826585941638d8265e156e559915a6550d54054094e150993a44d89341499d1a6431d0063f08f633c88f013c00f003c00e273614d043210c232f88bc12a2894a22946ee162c4c60ac418900ac001 0x1fc844fe4507f8403fd201e8082e4013792203f1201f4900f04407c2483b9101f58a2f8833fb21f3d80f9fa100fac807cc483b00c1d4060f60807ba403d4201c4844f548070211379089b8861f2480f82403c1143dc920ee460796403c3141dd062f3480786283c31c9d88fde807e77a413a9239d9080ea421740403a2201cc138e683172848389141cb120e04506d03e379141b8881e2c8171628b7b105b9064e34827084137b209ba0e6dac826c64070820554082a003140009b6520380102c0051540209f804f7c102be05153020a780c4f8027d283e6921f35a1e5a0844d488e692416f0245780c2a40414e0189e808590032c6013684477312399e11ccc4826524f32520d8f127c409e6203730b2057d8a2bc8335d2402690c96007cc3890608302fb1837092098440608412fb20970904964405a0472f62496c924944405904f2ed20371902b8c515b419eb90f95c07cb484159211a4808962904ae0825621f6ab205558a2a6c41524199e10894407eab4825484129b208ec844a54833a21828d20f41920a0c604f6282720c7349209a4604602e2852093d905984824b228628239200ba9d483ca24125114b1c11f860834702fa1814d3690498c824b6282520c52491d8808e4863023a0c51a1048a8824404121b105081388208cc0648a03184f98a27a8323c2201c81f0d407c818923f8491f3248ec8a07007c3da419d1102d811c6c05e3c839ddb1cced8867483239839dc21cce10866e849362111ad20ed1102688513242096908e9c1024e051210208f00c4680461e01334a4119b208c910562483a604192814474082320311301087004cc5906608822c419179238b887c5b483ac44116214aac91d544832b22f15114e90106480531c0208c00c434042520192800993d208999064ac51244199192085c8644408e210411000f84c0643e02e1e839ceb1cc75886388330c2110d80fc6a90732c82196290c20c65c9042e45296047ca823a50107260821602f8a8178500a626052120178880b8400461f4838e64187314c35064184408a0470581b0280bc1203e08839c3a1cc1d0870c4730622182908e100e6080430301881008c04026000ff 14 5 13 7 1
def q118D : Forest := fun i => decodeNode 8 21 0xa4038c20175900bb8905ca402c5201569009ac724ca4125a101288429488045418a1e24102904790823c6411e41cced904734803443c982238bc9045e88e2d847161208b093c574832ac499481b8a71204f082266411362489690048c51244199221048c84647482210411090f8829043d0821e6410f520c76906394821a6410d520c6690430c82186280c20c46091c30c60174188bc208591042c082166208a827054118298920f84907b2483e9061d0730d62186a0c8360e6188430c4248590882e9061548208641042208219060e882072470390f81e9060c8520622f03114c180320c01306a4102b20c158a20a83305241028238141040a03e0501702c1cc11886088330401f82520c0d8a4068310322901817c0c0bc06053030290180bc0c05c0602303a4181314c0906404440020360101780807c050730142180910c04846020430101880808c04026020ff00 i
def q118T := dagTraceTagsBin q118M 118 (dagTagBases q118N 0xe480ffffff60690f1d7433c3f9e3bfe4fceff7ff9e1ed38fbb3ff0fe7f7ffce0dbeb7fcbcf3fcffff3fc7ff7c7fff80217ec98138fe7c8fdff1ffff6f5d6d36aef97907bf3fcfdbfcff82787819f877fffff1007fe3fffe3f77fa7f07fe1dfefffefa441fdfffc3f87e7fe0007fffefffffffe988909 0xf11cffffff6de93f3d74f3cff9e3bfe4fceff7ffcfaed3bfbbbffbfe7f7ffce0dbeb7fe1d75fd7fff3febff7effffe2317ec9db3bfebcbfdffaffff6f7d6d308ef97cb3bf5fd7dbfe7fb3f8f9ddfc77fffff4b6ffefffff5f0ffbff6fff1dfefffefb12cfdfffeffbffffefbbffffefffffffecddfbc 118) 13 q118D
def q118St := dagTraceBin q118M q118N 13 q118D
def q118Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q118Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q118Mv := dagMoves ([([qS7], q118Mp0, q118Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118A : DagMovesOK q118M q118G 256 q118Mv := dagMovesOfCheck (by decide +kernel)
def q118NB : Nat → List Bound := dagNodeBounds q118C.toArray 0xb3d2cd2b28ec64b10ac04af8abb3ae0eb62acceb12ab8ea95a952a14a78e995a5528d8a28e873a10e8049f4e7a39dce7259b1a6939916604974e59494624d4925246390923f38f0e3848d123048b122848912204874e16784920e48129fc87e4df637c55ec57a4de637855de37619d3573d1ca57155bf66e59b186a61a36680d9c465d5907625d8275edd7565c156b5586959855154f5521d4264edd3384b1d20c45e512542dd0654018f883c20e883898d8a3420c6a2f64b762b68a6727a0995246087a1f2c7391a6862716a053712a44370f1c3660b2822a06280f901a4006 0x21c504004c00114b00100108014100130004c00100100804004e0016421c00470850421c504714108714b0590800523d108118024100824004c00120500104020100820c04230e0017560872c104c2123c90013d10082400452c005210f0c600b04f20005a00804200114020124004800100530100b14108014100914108b1410891413d10012400513825802413c900144100854f0c40541820080d438040130808004900150201504214c00128004a0012820150550010842060016421c00421c00591c90010851cb0500c21cb1432811c214d0ce30a0851e34191840072d918400708600814100808958005244605800948f0860402510d310600928035a24520d18b0c00490c005a2430086912ce1c308400624d38c1830802090c020e68938230d0ca08400e74a6c238c0c648400b0523d15c90012035011000880d724110e18041430834319210f00b0460804971c52c444004804051734904601740370008510b0dc00a04414234338c2821057de28270548f1c41510890013c35411000886cd0ca38400218c3c35411140022045150800553c21031920100542970950012871421004888466c004d0c52460406e03968841950011d00d61803021051cb0d628404600708d0ca3821444cc1d83434131c51c46104c65803cd1c900859444d0c72820164031844c02c34c61180022c21800d03433872821060132cd0ca5c61140107de60d0d04c01053431ca0861004cd0d84131060076104c6100 14 4 6
def q118Ck := dagCheckNodeFast q118M q118G q118NB 128 q118St q118Mv q118L q118S q118T
def q118RA (token : Nat) : Bool :=
  let s := rootState q118N 13 token
  !dagAllowedRootBin q118M q118E s.2.1 || dagLocalBin q118M q118G (dagKnownClosesBin q118G q118C) s ||
  dagRefBin q118M 128 q118St q118Mv (fun p tok => dagFindLink (q118L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118RB0 : treeBlock 0 64 q118RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118RB64 : treeBlock 64 64 q118RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118RB128 : treeBlock 128 64 q118RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118RB192 : treeBlock 192 64 q118RA = true := by decide +kernel
theorem q118R : dagCheckRootsBin q118M q118G (dagKnownClosesBin q118G q118C) q118E (dagRefBin q118M 128 q118St q118Mv (fun p tok => dagFindLink (q118L p) tok) 0) q118N 13 = true := (@treeBlock_merge 0 128 128 q118RA (@treeBlock_merge 0 64 64 q118RA q118RB0 q118RB64) (@treeBlock_merge 128 64 64 q118RA q118RB128 q118RB192))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B0 : treeBlock 0 16 q118Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B16 : treeBlock 16 16 q118Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B32 : treeBlock 32 16 q118Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B48 : treeBlock 48 16 q118Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B64 : treeBlock 64 16 q118Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B80 : treeBlock 80 16 q118Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B96 : treeBlock 96 16 q118Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118B112 : treeBlock 112 16 q118Ck = true := by decide +kernel
theorem q118Bf : treeBlock 0 128 q118Ck = true := (@treeBlock_merge 0 64 64 q118Ck (@treeBlock_merge 0 32 32 q118Ck (@treeBlock_merge 0 16 16 q118Ck q118B0 q118B16) (@treeBlock_merge 32 16 16 q118Ck q118B32 q118B48)) (@treeBlock_merge 64 32 32 q118Ck (@treeBlock_merge 64 16 16 q118Ck q118B64 q118B80) (@treeBlock_merge 96 16 16 q118Ck q118B96 q118B112)))
theorem q118Bk : treeBlock 0 128 (dagCheckNodeBin q118M q118G q118NB 128 q118St q118Mv q118L q118S q118T) = true := by
  rw [← dagCheckNodeFastEq]
  exact q118Bf
theorem q118K : KnownBin q118C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q117Bin) q115Bin) q104Bin) q102Bin) q110Bin) q105Bin) q103Bin) q71Bin) q80Bin) q47Bin) q116Bin) q101Bin) q72Bin) q67Bin) q109Bin) q112Bin) q96Bin) q114Bin) q107Bin) q98Bin) q113Bin) q74Bin) q106Bin) q11Bin) q99Bin) q100Bin) q51Bin) q13Bin) q70Bin) q94Bin) q45Bin) q93Bin) q111Bin) q95Bin) q12Bin) q97Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q118Bin : BinLower q118M q118W q118G 14 := by
  apply lowerDagBin _ _ _ _ q118A _ _ _ q118K _ (fun _ b hb => dagNodeBounds_mem b hb) q118R q118Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q118C.all (fun b => q118M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
theorem binLowerEq {m m2 : Word} {s s2 : List Word} {t t2 : Word} {k : Nat}
    (hm : m = m2) (hs : s = s2) (ht : t = t2) (h : BinLower m s t k) : BinLower m2 s2 t2 k := by
  subst hm; subst hs; subst ht; exact h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootLower : BinLower (fullMask 256) qBase qGoal 14 :=
  binLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) q118Bin

end PEqualNP.Outside.L_meta_34788.Cert

namespace PEqualNP.Outside.L_meta_34788

open PEqualNP.CircuitLowerBounds

def upperGates : List Gate :=
  [⟨.and, [0, 3]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [18, 12]⟩, ⟨.or, [20, 15]⟩, ⟨.and, [19, 21]⟩]

def graphList : List Nat := [0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7]

def edgeValue (s : List Bool) : Bool := decide (∃ i < graphList.length / 2,
  s.getD (graphList.getD (2*i) 0) false = true ∧ s.getD (graphList.getD (2*i+1) 0) false = true)

theorem upper_shape : ∀ g ∈ upperGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem upper_sem (x : Fin 8 → Bool) :
    Circuit.eval ⟨upperGates, 22⟩ (List.ofFn x) = edgeValue (List.ofFn x) := by
  have h : ∀ a b c d e f g h : Bool,
      Circuit.eval ⟨upperGates, 22⟩ [a,b,c,d,e,f,g,h] = edgeValue [a,b,c,d,e,f,g,h] := by decide
  simp only [List.ofFn_succ, List.ofFn_zero]
  apply h

end PEqualNP.Outside.L_meta_34788

namespace PEqualNP.Outside.L_meta_34788
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_34788.Contraction

def truthInputs : List (BitVec 256) := Cert.qBase.map (BitVec.ofNat 256)
def truthGoal : BitVec 256 := BitVec.ofNat 256 Cert.qGoal

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
theorem countBinary (lb : BinLower (fullMask 256) Cert.qBase Cert.qGoal 14)
    (gates : List Gate) (o : Nat) (hfan : FanInTwo ⟨gates, o⟩)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeValue (List.ofFn x)) :
    14 ≤ countNonNot gates := by
  let eb := gates.foldl hcsStep truthInputs
  have same : eb.getD o 0 = truthGoal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let x : Fin 8 → Bool := fun k => j.testBit k.val
    have hbank : ∀ i : Fin 256, truthInputs.map (fun v => v.getLsbD i.val) =
        List.ofFn (fun k : Fin 8 => i.val.testBit k.val) := by decide +kernel
    have hgraph : ∀ i : Fin 256, truthGoal.getLsbD i.val =
        edgeValue (List.ofFn (fun k : Fin 8 => i.val.testBit k.val)) := by decide +kernel
    have bits := hcsFoldBits truthInputs ⟨j,hj⟩ gates hfan
    calc
      (eb.getD o 0).getLsbD j = (eb.map fun v => v.getLsbD j).getD o false := hcsGetDBit eb j o
      _ = edgeValue (List.ofFn x) := by
        dsimp only [eb]
        rw [bits, hbank ⟨j,hj⟩]
        exact he x
      _ = truthGoal.getLsbD j := (hgraph ⟨j,hj⟩).symm
  have hroot : truthInputs.map BitVec.toNat = Cert.qBase := by decide +kernel
  have hr : ∀ v ∈ truthInputs, AvBin (fullMask 256) Cert.qBase v.toNat := by
    intro v hv
    apply Or.inr (Or.inr (Or.inl ?_))
    rw [← hroot]
    exact List.mem_map_of_mem hv
  obtain ⟨vs, len, built, reach⟩ := hcsBuildsBin truthInputs Cert.qBase gates hr hfan
  have av : AvBin (fullMask 256) (vs ++ Cert.qBase) Cert.qGoal := by
    rw [show Cert.qGoal = truthGoal.toNat by decide +kernel, ← same, List.getD_eq_getElem?_getD]
    cases h : eb[o]? with
    | none => exact Or.inl rfl
    | some v => exact reach v (List.mem_of_getElem? h)
  exact (lb vs built av).trans len

theorem finish (lb : BinLower (fullMask 256) Cert.qBase Cert.qGoal 14)
    (gates : List Gate) (o : Nat)
    (hg : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeValue (List.ofFn x)) :
    ∃ (out : List Gate) (p : Nat),
      (∀ g ∈ out, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ out.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨out,p⟩ (List.ofFn x) = edgeValue (List.ofFn x) := by
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hfan : FanInTwo ⟨gates,o⟩ := by
      intro g h
      obtain ⟨hop, len⟩ := hg g h
      refine ⟨?_, len⟩
      rcases hop with h | h | h <;> simp [h]
    have floor := countBinary lb gates o hfan he
    have used := countNonNot_le_sub hn
    refine ⟨upperGates,22,upper_shape,?_,upper_sem⟩
    change 15 ≤ gates.length
    omega
  · refine ⟨gates,o,?_,Nat.le_refl _,he⟩
    intro g h
    obtain ⟨hop, len⟩ := hg g h
    refine ⟨?_,len⟩
    rcases hop with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · exact (hn ⟨g,h,h₃⟩).elim

end PEqualNP.Outside.L_meta_34788

theorem PEqualNP.Outside.L_meta_34788 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ hu
  apply PEqualNP.Outside.L_meta_34788.finish _ gates o hg hu
  exact PEqualNP.Outside.L_meta_34788.Cert.rootLower
