import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1519
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

abbrev Ports (m : Nat) := Fin m ⊕ Fin m
abbrev Host (m : Nat) := Finset (Ports m × Bool)
def Cov {m} (A : Finset (Fin m × Fin m)) (C : Host m) :=
  (∀ z : Ports m, (z,false) ∈ C ∨ (z,true) ∈ C) ∧
  ∀ e ∈ A, (Sum.inl e.1,false) ∈ C ∨ (Sum.inr e.2,true) ∈ C

def rails {m} (f : Ports m → Bool) : Host m := Finset.univ.image (fun z => (z,f z))
lemma memRails {m} (f : Ports m → Bool) (z : Ports m) (b : Bool) :
    (z,b) ∈ rails f ↔ f z = b := by simp [rails]
lemma cardRails {m} (f : Ports m → Bool) : (rails f).card = Fintype.card (Ports m) := by
  rw [rails, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Finset.card_univ]
lemma chooseRail {m} {A : Finset (Fin m × Fin m)} {C : Host m} (h : Cov A C) :
    ∃ f : Ports m → Bool, rails f ⊆ C := by
  classical
  refine ⟨fun z => decide ((z,false) ∉ C), ?_⟩
  rintro ⟨z,b⟩ hb
  obtain rfl := (memRails _ z b).mp hb
  by_cases hz : (z,false) ∈ C <;> simp [hz, (h.1 z).resolve_left] at *
lemma pin {m} (A : Finset (Fin m × Fin m)) (i j : Fin m) :
    (∃ C : Host m, (Cov A C ∧ ∀ B, Cov A B → C.card ≤ B.card) ∧
      (Sum.inl i,true) ∈ C ∧ (Sum.inr j,true) ∉ C) ↔ (i,j) ∉ A := by
  classical
  have ones : Cov A (rails (fun _ => true)) := by
    constructor
    · intro z; exact Or.inr ((memRails _ _ _).mpr rfl)
    · intro e _; exact Or.inr ((memRails _ _ _).mpr rfl)
  constructor
  · rintro ⟨C,⟨hc,ho⟩,hi,hj⟩ h
    obtain ⟨f,hf⟩ := chooseRail hc
    have eq := Finset.eq_of_subset_of_card_le hf (by simpa only [cardRails] using ho _ ones)
    rw [← eq] at hi hj hc
    have hn := (hc.2 (i,j) h).resolve_right hj
    have := (memRails _ _ _).mp hn
    have := (memRails _ _ _).mp hi
    grind
  · intro hn
    let f : Ports m → Bool := Sum.elim (fun u => decide (u = i)) (fun v => decide ((i,v) ∈ A))
    refine ⟨rails f, ⟨⟨?_,?_⟩,?_⟩, ?_, ?_⟩
    · intro z; cases h : f z <;> simp [memRails,h]
    · rintro ⟨u,v⟩ h
      by_cases he : u = i <;> simp_all [memRails,f]
    · intro B hb; obtain ⟨g,hg⟩ := chooseRail hb
      simpa only [cardRails] using Finset.card_le_card hg
    · simp [memRails,f]
    · simp [memRails,f,hn]

abbrev Slot (W : Nat) := Fin 3 × Option (Fin W) × Option (Fin W)
def decode {W} (s : Slot W) : Option Gate :=
  let op := if s.1 = 0 then GateOp.and else if s.1 = 1 then GateOp.or else GateOp.not
  match s.2 with
  | (none,none) => some ⟨op,[]⟩
  | (some a,none) => some ⟨op,[a.val]⟩
  | (some a,some b) => some ⟨op,[a.val,b.val]⟩
  | (none,some _) => none
lemma pack {W} (g : Gate) (ho : g.op ∈ ({.and,.or,.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hb : ∀ i ∈ g.inputs, i < W) : ∃ c : Slot W, decode c = some g := by
  obtain ⟨op,l⟩ := g
  change op = .and ∨ op = .or ∨ op = .not at ho
  change l.length ≤ 2 at hl
  change ∀ i ∈ l, i < W at hb
  have code : ∃ k : Fin 3, (if k = 0 then GateOp.and else if k = 1 then .or else .not) = op := by
    rcases ho with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨k,hk⟩ := code
  cases l with
  | nil => exact ⟨(k,none,none), by simpa [decode] using hk⟩
  | cons a l =>
    have ha := hb a (by simp)
    cases l with
    | nil => exact ⟨(k,some ⟨a,ha⟩,none), by simp [decode,hk]⟩
    | cons b l =>
      cases l with
      | nil => exact ⟨(k,some ⟨a,ha⟩,some ⟨b,hb b (by simp)⟩), by simp [decode,hk]⟩
      | cons c l => simp at hl

abbrev Desc (W s : Nat) := Fin W × (Fin s → Slot W)
def unpack {W s} (d : Desc W s) : Circuit := ⟨(List.ofFn d.2).filterMap decode,d.1.val⟩
lemma represent {n s} (E : Circuit) (fan : FanInTwo E) (back : NestedCover.ReadsBack n E)
    (out : E.output < n + E.size) (len : E.size ≤ s) : ∃ d : Desc (n+s) s, unpack d = E := by
  classical
  let W := n+s
  have bound : E.gates.length ≤ s := len
  have enc (j : Fin E.gates.length) : ∃ c : Slot W, decode c = some E.gates[j.val] := by
    have hg := fan _ (List.getElem_mem j.isLt)
    apply pack _ hg.1 hg.2
    intro i hi
    have h := back j.val j.isLt i (by simpa [NestedCover.gateAt, List.getD, j.isLt] using hi)
    dsimp [W]; omega
  let pre := (List.finRange E.gates.length).map (fun j => (enc j).choose)
  let filler : Slot W := (0,none,some ⟨E.output,by dsimp [W]; omega⟩)
  let slots := pre ++ List.replicate (s-E.size) filler
  have sl : slots.length = s := by simp [slots,pre,Circuit.size]; omega
  let d : Desc W s := (⟨E.output,by dsimp [W]; omega⟩, fun j => slots[j.val]'(by omega))
  have he : List.ofFn d.2 = slots := by apply List.ext_getElem <;> simp [d,sl]
  have hp : pre.filterMap decode = E.gates := by
    simp only [pre,List.filterMap_map,Function.comp_def,fun j => (enc j).choose_spec,List.filterMap_eq_map']
    apply List.ext_getElem <;> simp
  have hf : decode filler = none := rfl
  refine ⟨d, ?_⟩
  simp only [unpack,he,slots,List.filterMap_append,hp,List.filterMap_replicate_of_none hf,List.append_nil]
  rfl

end PEqualNP.Outside.L_lib_1519

open PEqualNP.Outside.L_lib_1519 in

theorem PEqualNP.Outside.L_lib_1519 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ m s : Nat,
  let W := 4*m+2+s
  W*(3*(W+1)^2)^s < 2^(m*m) →
  ∃ A : Finset (Fin m × Fin m),
    let cover := fun (C : Finset ((Fin m ⊕ Fin m) × Bool)) =>
      (∀ z : Fin m ⊕ Fin m, (z,false) ∈ C ∨ (z,true) ∈ C) ∧
      ∀ e ∈ A, (Sum.inl e.1,false) ∈ C ∨ (Sum.inr e.2,true) ∈ C
    let opt := fun C => cover C ∧ ∀ B, cover B → C.card ≤ B.card
    let word := fun (i j : Fin m) =>
      List.replicate m true ++ List.ofFn (fun v : Fin m => decide (v ≠ j)) ++
      List.ofFn (fun u : Fin m => decide (u ≠ i)) ++ List.replicate m true ++ [false,true]
    ∀ E : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo E →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (4*m+2) E →
      E.output < 4*m+2+E.size → E.size ≤ s →
      ∃ i j : Fin m, ¬ (E.eval (word i j) = true ↔
        ∃ C, opt C ∧ (Sum.inl i,true) ∈ C ∧ (Sum.inr j,true) ∉ C)) := by
  classical
  intro m s W hlt
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let word := fun (i j : Fin m) => List.replicate m true ++ List.ofFn (fun v : Fin m => decide (v ≠ j)) ++ List.ofFn (fun u : Fin m => decide (u ≠ i)) ++ List.replicate m true ++ [false,true]
  let table := fun (d : Desc W s) => Finset.univ.filter (fun ij : Fin m × Fin m => (unpack d).eval (word ij.1 ij.2) ≠ true)
  have smaller : Fintype.card (Desc W s) < Fintype.card (Finset (Fin m × Fin m)) := by
    simpa [Desc,Slot,Fintype.card_prod,Fintype.card_fun,pow_two, Nat.mul_assoc] using hlt
  have miss : ¬ Function.Surjective table := fun h => (Nat.not_le_of_lt smaller) (Fintype.card_le_of_surjective _ h)
  obtain ⟨A,hA⟩ := Classical.not_forall.mp miss
  refine ⟨A, ?_⟩
  intro cover opt postedWord E hf hb ho hs
  obtain ⟨d,hd⟩ := represent E hf hb ho hs
  by_contra! h
  apply hA
  refine ⟨d, ?_⟩
  ext ⟨i,j⟩
  have eqWord : postedWord i j = word i j := rfl
  have test := (h i j).trans (pin A i j)
  rw [eqWord] at test
  simp only [table,Finset.mem_filter,Finset.mem_univ,true_and,hd,ne_eq,test,not_not]
