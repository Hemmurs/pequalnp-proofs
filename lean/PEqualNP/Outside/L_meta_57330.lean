import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_29768

namespace PEqualNP.Outside.L_meta_57330

abbrev V := Fin 4 → ZMod 2

def detects (x : V) : Prop :=
  x 0 + x 3 + x 0 * x 3 - x 1 * x 2 ≠ 0

instance (x : V) : Decidable (detects x) := inferInstanceAs (Decidable (_ ≠ _))

def visible : Finset V := Finset.univ.filter detects

theorem ten_visible : visible.card = 10 := by decide

theorem zero_blind : ¬ detects 0 := by decide

theorem sum_of_blind : ∀ x y : V, x ≠ 0 → y ≠ 0 → x ≠ y →
    ¬ detects x → ¬ detects y → detects (x + y) := by decide

theorem split_visible : ∀ z : V, detects z →
    ∃ x y : V, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧ ¬ detects x ∧ ¬ detects y ∧ x + y = z := by
  have cert : ∀ z : V, detects z →
      ∃ x ∈ (Finset.univ : Finset V), ∃ y ∈ (Finset.univ : Finset V),
        x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧ ¬ detects x ∧ ¬ detects y ∧ x + y = z := by decide
  intro z hz
  obtain ⟨x, _, y, _, h⟩ := cert z hz
  exact ⟨x, y, h⟩

theorem small_sample (S : Finset V) (hs : S ⊆ visible) (hc : S.card ≤ 9) :
    ∃ x y : V, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧ x ∉ S ∧ y ∉ S ∧ (x + y) ∉ S := by
  have hproper : ¬ visible ⊆ S := by
    intro h
    have he := Finset.card_le_card h
    rw [ten_visible] at he
    omega
  obtain ⟨z, hz, hzs⟩ := Finset.not_subset.mp hproper
  obtain ⟨x, y, hx, hy, hxy, hbx, hby, hsum⟩ :=
    split_visible z ((Finset.mem_filter.mp hz).2)
  refine ⟨x, y, hx, hy, hxy, ?_, ?_, by rwa [hsum]⟩
  · exact fun h => hbx (Finset.mem_filter.mp (hs h)).2
  · exact fun h => hby (Finset.mem_filter.mp (hs h)).2

def dot4 (a x : V) : ZMod 2 :=
  a 0 * x 0 + a 1 * x 1 + a 2 * x 2 + a 3 * x 3

theorem blind_in_hyperplane : ∀ a : V, a ≠ 0 →
    ∃ x ∈ (Finset.univ : Finset V), x ≠ 0 ∧ dot4 a x = 0 ∧ ¬ detects x := by decide

theorem plane_hits_visible (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    detects x ∨ detects y ∨ detects (x + y) := by
  by_cases h : detects x
  · exact Or.inl h
  by_cases h' : detects y
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (sum_of_blind x y hx hy hxy h h'))


def hitsAll (S : Finset V) : Prop :=
  ∀ x y : V, x ≠ 0 → y ≠ 0 → x ≠ y → x ∈ S ∨ y ∈ S ∨ x + y ∈ S

theorem least_visible_blocker :
    IsLeast {m : ℕ | ∃ S : Finset V, S ⊆ visible ∧ S.card = m ∧ hitsAll S} 10 := by
  constructor
  · refine ⟨visible, fun _ h => h, ten_visible, ?_⟩
    intro x y hx hy hxy
    simpa [visible] using plane_hits_visible x y hx hy hxy
  · intro m hm
    obtain ⟨S, hs, rfl, hh⟩ := hm
    by_contra! h
    obtain ⟨x, y, hx, hy, hxy, ha, hb, hc⟩ := small_sample S hs (by omega)
    exact (hh x y hx hy hxy).elim ha (fun h' => h'.elim hb hc)


theorem prescribed_kernel : ∀ a b c : ZMod 2,
    detects ![a, b, a+b, b+c] ↔ a ≠ 0 ∨ c ≠ 0 := by decide

theorem field_kernel {K : Type} [Field K] [Algebra (ZMod 2) K]
    (f : K →ₗ[ZMod 2] ZMod 2) (t x : K) :
    detects ![f x, f (t*x), f x + f (t*x), f (t*x) + f (t*(t*x))] ↔
      f x ≠ 0 ∨ f ((t*t)*x) ≠ 0 := by
  rw [mul_assoc t t x]
  exact prescribed_kernel _ _ _

open Module
variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

private noncomputable def actionCoords (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (b i))

private theorem actionCoords_apply (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (x : K) (i : Fin k) :
    actionCoords b bit x i = bit (b i * x) := rfl

private noncomputable def actionEquiv (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0) :
    K ≃ₗ[F] (Fin k → F) := by
  letI : FiniteDimensional F K := b.finiteDimensional_of_finite
  have dim : finrank F K = finrank F (Fin k → F) := by
    simp [Module.finrank_eq_card_basis b]
  have hinj : Function.Injective (actionCoords b bit) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hz : bit.comp (LinearMap.mulLeft F x) = 0 := by
      apply b.ext
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [actionCoords_apply, mul_comm x (b i)] using hi
    apply hbit
    ext y
    have hy := DFunLike.congr_fun hz (x⁻¹ * y)
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hy
  exact LinearEquiv.ofBijective (actionCoords b bit)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hinj⟩


theorem rotate_dual (b : Basis (Fin k) F K) (f g : K →ₗ[F] F) (hf : f ≠ 0) :
    ∃ s : K, ∀ x : K, f (s*x) = g x := by
  let e := actionEquiv b f hf
  obtain ⟨s, hs⟩ := e.surjective (fun i => g (b i))
  refine ⟨s, ?_⟩
  have h : f.comp (LinearMap.mulLeft F s) = g := by
    apply b.ext
    intro i
    have hi := congrFun hs i
    change f (b i * s) = g (b i) at hi
    simpa [mul_comm] using hi
  exact fun x => DFunLike.congr_fun h x

theorem realize_two_forms {K : Type} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] {k : ℕ} (b : Basis (Fin k) (ZMod 2) K)
    (f g : K →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) :
    ∃ (u : Fin 2 → K) (l : Fin 2 → (K →ₗ[ZMod 2] ZMod 2)), ∀ x : K,
      detects ![l 0 (x*u 0), l 0 (x*u 1), l 1 (x*u 0), l 1 (x*u 1)] ↔
        f x ≠ 0 ∨ g x ≠ 0 := by
  letI : Finite K := Module.finite_of_finite (ZMod 2)
  letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  obtain ⟨s, hs⟩ := rotate_dual b f g hf
  obtain ⟨t, ht⟩ := surjective_frobenius K 2 s
  change t^2 = s at ht
  refine ⟨![1,t], ![f, f + f.comp (LinearMap.mulLeft (ZMod 2) t)], ?_⟩
  intro x
  change detects ![f (x*1), f (x*t), f (x*1) + f (t*(x*1)), f (x*t) + f (t*(x*t))] ↔ _
  rw [mul_one, mul_comm x t, ← hs, ← ht, pow_two]
  exact field_kernel f t x


abbrev IJ := Fin 1 × Fin 2

def named (v : V) (i j : IJ) : ZMod 2 :=
  ![![v 0, v 1], ![v 2, v 3]] i.2 j.2

noncomputable def oneMinor (v : V) (J : Finset IJ) : ZMod 2 :=
  Matrix.det (Matrix.of (named v) |>.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val))

theorem all_minors : ∀ v : V,
    (∑ J ∈ ((Finset.univ : Finset IJ).powerset.filter
       (fun J => J.image Prod.fst = Finset.univ)), oneMinor v J) ≠ 0 ↔ detects v := by decide

def pack (H : Matrix IJ IJ (ZMod 2)) : V :=
  ![H (0,0) (0,0), H (0,0) (0,1), H (0,1) (0,0), H (0,1) (0,1)]

theorem named_pack (H : Matrix IJ IJ (ZMod 2)) : Matrix.of (named (pack H)) = H := by
  ext ⟨i,j⟩ ⟨a,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> rfl

theorem minor_iff (H : Matrix IJ IJ (ZMod 2)) :
    (∃ U : Finset (Fin 1), U.Nonempty ∧
      (∑ J ∈ ((Finset.univ : Finset IJ).powerset.filter (fun J => J.image Prod.fst = U)),
        Matrix.det (H.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val))) ≠ 0)
      ↔ detects (pack H) := by
  have h := all_minors (pack H)
  simp only [oneMinor, named_pack] at h
  constructor
  · rintro ⟨U, hU, hsum⟩
    have he : U = Finset.univ := by
      obtain ⟨a, ha⟩ := hU
      apply Finset.eq_univ_of_forall
      intro x
      rwa [Subsingleton.elim x a]
    exact h.mp (he ▸ hsum)
  · intro hp
    exact ⟨Finset.univ, Finset.univ_nonempty, h.mpr hp⟩



noncomputable def detector {K : Type} [Field K] [Algebra (ZMod 2) K]
    (u : Fin 2 → K) (f : Fin 2 → (K →ₗ[ZMod 2] ZMod 2)) : K →ₗ[ZMod 2] V :=
  LinearMap.pi ![(f 0).comp (LinearMap.mulRight _ (u 0)),
    (f 0).comp (LinearMap.mulRight _ (u 1)), (f 1).comp (LinearMap.mulRight _ (u 0)),
    (f 1).comp (LinearMap.mulRight _ (u 1))]

theorem detector_apply {K : Type} [Field K] [Algebra (ZMod 2) K]
    (u : Fin 2 → K) (f : Fin 2 → (K →ₗ[ZMod 2] ZMod 2)) (x : K) :
    detector u f x = ![f 0 (x*u 0), f 0 (x*u 1), f 1 (x*u 0), f 1 (x*u 1)] := by
  ext i
  fin_cases i <;> rfl

def admissible {K : Type} [Field K] [Algebra (ZMod 2) K] (Z : Finset K) : Prop :=
  (0 : K) ∉ Z ∧ ∃ (u : Fin 2 → K) (f : Fin 2 → (K →ₗ[ZMod 2] ZMod 2)),
      ∀ z ∈ Z, detects (detector u f z⁻¹)



def form4 (a : V) : V →ₗ[ZMod 2] ZMod 2 where
  toFun := dot4 a
  map_add' x y := by simp [dot4, mul_add]; ring
  map_smul' c x := by simp [dot4]; ring

theorem separate_omission : ∀ z : V, detects z →
    ∃ a ∈ (Finset.univ : Finset V), ∃ b ∈ (Finset.univ : Finset V),
      ∀ x : V, detects x → x ≠ z → dot4 a x ≠ 0 ∨ dot4 b x ≠ 0 := by decide

theorem forms_on_sample (S : Finset V) (hs : S ⊆ visible) (hn : ¬ visible ⊆ S) :
    ∃ (a b : V →ₗ[ZMod 2] ZMod 2), ∀ x ∈ S, a x ≠ 0 ∨ b x ≠ 0 := by
  obtain ⟨z, hz, hnz⟩ := Finset.not_subset.mp hn
  obtain ⟨a, _, b, _, hab⟩ := separate_omission z (Finset.mem_filter.mp hz).2
  exact ⟨form4 a, form4 b, fun x hx => hab x (Finset.mem_filter.mp (hs hx)).2
    (fun e => hnz (e ▸ hx))⟩

abbrev Two := Fin 2 → ZMod 2

theorem refine_kernel {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (k : ℕ) (h : Module.finrank (ZMod 2) E = k)
    (hk : 2 ≤ k) (p : E →ₗ[ZMod 2] Two) :
    ∃ q : E →ₗ[ZMod 2] Two, Function.Surjective q ∧ LinearMap.ker q ≤ LinearMap.ker p := by
  classical
  have hd := p.finrank_range_add_finrank_ker
  have htwo : Module.finrank (ZMod 2) Two = 2 := by simp [Two]
  have hr := (LinearMap.range p).finrank_le
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := LinearMap.ker p)
    (n := k-2) (by omega)
  let w : Fin (k-2) → E := fun i => (v i).val
  have hw : LinearIndependent (ZMod 2) w := hv.map' _ (Submodule.ker_subtype _)
  let W := Submodule.span (ZMod 2) (Set.range w)
  have hl : W ≤ LinearMap.ker p := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).property)
  have hdim : Module.finrank (ZMod 2) W = k-2 := by simpa [W] using finrank_span_eq_card hw
  have hdq := W.finrank_quotient_add_finrank
  let e : (E ⧸ W) ≃ₗ[ZMod 2] Two := LinearEquiv.ofFinrankEq _ _ (by omega)
  refine ⟨e.toLinearMap.comp W.mkQ, e.surjective.comp W.mkQ_surjective, ?_⟩
  simpa [LinearMap.ker_comp] using hl



theorem uniform_count {E D : Type} [AddCommGroup E] [AddCommGroup D]
    [Module (ZMod 2) E] [Module (ZMod 2) D] [Fintype E] [Fintype D] [DecidableEq D]
    (q : E →ₗ[ZMod 2] D) (hq : Function.Surjective q) (S : Finset D) :
    (Finset.univ.filter (fun x => q x ∈ S)).card * Fintype.card D = Fintype.card E * S.card := by
  classical
  let c := (Finset.univ.filter (fun x => q x = 0)).card
  have he (y : D) : (Finset.univ.filter (fun x => q x = y)).card = c :=
    AddMonoidHom.card_fiber_eq_of_mem_range q (hq y) (hq 0)
  have hc (T : Finset D) : (Finset.univ.filter (fun x => q x ∈ T)).card = T.card * c := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter]
    simp [he]
  have ht := hc Finset.univ
  simp at ht
  rw [hc, ht]
  ring

theorem full_detector {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    (f : K →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (hk : 4 ≤ Module.finrank (ZMod 2) K) :
    ∃ (u : Fin 2 → K) (l : Fin 2 → (K →ₗ[ZMod 2] ZMod 2)),
      Function.Surjective (detector u l) := by
  classical
  let p := Field.powerBasisOfFiniteOfSeparable (ZMod 2) K
  have hdim : 4 ≤ p.dim := by simpa [Module.finrank_eq_card_basis p.basis] using hk
  let t := p.gen
  let u : Fin 2 → K := ![1,t]
  let l : Fin 2 → (K →ₗ[ZMod 2] ZMod 2) := ![f, f.comp (LinearMap.mulLeft _ (t^2))]
  refine ⟨u, l, ?_⟩
  intro y
  let val : Fin p.dim → ZMod 2 := fun i => if h : i.val < 4 then y ⟨i.val,h⟩ else 0
  obtain ⟨x, hx⟩ := (actionEquiv p.basis f hf).surjective val
  have coord (i : Fin p.dim) : f (t^i.val * x) = val i := by
    have h := congrFun hx i
    change f (p.basis i * x) = val i at h
    rwa [p.basis_eq_pow] at h
  have h0 := coord ⟨0, by omega⟩
  have h1 := coord ⟨1, by omega⟩
  have h2 := coord ⟨2, by omega⟩
  have h3 := coord ⟨3, by omega⟩
  simp [val] at h0 h1 h2 h3
  refine ⟨x, ?_⟩
  rw [detector_apply]
  change ![f (x*1), f (x*t), f (t^2*(x*1)), f (t^2*(x*t))] = y
  rw [mul_one, mul_comm x t, ← mul_assoc, ← pow_succ]
  ext i
  fin_cases i <;> assumption



theorem extension {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    {k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) K) (hk : 2 ≤ k)
    (Z : Finset K) (p : K →ₗ[ZMod 2] Two) (hp : ∀ z ∈ Z, p z⁻¹ ≠ 0) :
    ∃ Y : Finset K, admissible Y ∧ Z ⊆ Y ∧ Y.card = 3 * 2^(k-2) := by
  classical
  letI : Finite K := Module.finite_of_finite (ZMod 2)
  letI := Fintype.ofFinite K
  have hdim : Module.finrank (ZMod 2) K = k := by simp [Module.finrank_eq_card_basis basis]
  obtain ⟨q, hq, hker⟩ := refine_kernel k hdim hk p
  let f : K →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj 0).comp q
  let g : K →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj 1).comp q
  have hf : f ≠ 0 := by
    obtain ⟨x, hx⟩ := hq ![1,0]
    intro h
    have ht := DFunLike.congr_fun h x
    change q x 0 = 0 at ht
    rw [hx] at ht
    exact one_ne_zero ht
  obtain ⟨u, l, hu⟩ := realize_two_forms basis f g hf
  let T : Finset Two := Finset.univ.erase 0
  let X := Finset.univ.filter (fun x => q x ∈ T)
  let Y := X.image Inv.inv
  have hmem (z : K) : z ∈ Y ↔ q z⁻¹ ≠ 0 := by simp [Y, X, T, Finset.mem_image, inv_eq_iff_eq_inv]
  refine ⟨Y, ⟨?_, u, l, ?_⟩, ?_, ?_⟩
  · simp [hmem]
  · intro z hz
    rw [detector_apply, hu]
    by_contra! hh
    apply (hmem z).mp hz
    ext i
    fin_cases i
    · exact hh.1
    · exact hh.2
  · intro z hz
    apply (hmem z).mpr
    exact fun e => hp z hz (hker (show z⁻¹ ∈ LinearMap.ker q from e))
  · have ht : T.card = 3 := by decide
    have htwo : Fintype.card Two = 4 := by decide
    have hc := uniform_count q hq T
    have hK : Fintype.card K = 2^k := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hdim]
    rw [ht, htwo, hK, show k = k-2+2 by omega, pow_add] at hc
    change X.card * 4 = _ at hc
    rw [show Y.card = X.card from Finset.card_image_of_injective _ inv_injective]
    omega

theorem sample_map {K : Type} [Field K] [Algebra (ZMod 2) K] (Z : Finset K)
    (d : K →ₗ[ZMod 2] V) (pos : ∀ z ∈ Z, detects (d z⁻¹))
    (miss : ¬ visible ⊆ Z.image (fun z => d z⁻¹)) :
    ∃ p : K →ₗ[ZMod 2] Two, ∀ z ∈ Z, p z⁻¹ ≠ 0 := by
  classical
  let S := Z.image (fun z => d z⁻¹)
  have hs : S ⊆ visible := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pos z hz⟩
  obtain ⟨a,b,hab⟩ := forms_on_sample S hs miss
  let p := (LinearMap.pi ![a,b]).comp d
  refine ⟨p, ?_⟩
  intro z hz he
  rcases hab (d z⁻¹) (Finset.mem_image_of_mem _ hz) with h | h
  · exact h (congrFun he 0)
  · exact h (congrFun he 1)

theorem small_extends {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    {k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) K) (hk : 2 ≤ k)
    (Z : Finset K) (hz : admissible Z) (hc : Z.card < 10) :
    ∃ Y : Finset K, admissible Y ∧ Z ⊆ Y ∧ Y.card = 3 * 2^(k-2) := by
  obtain ⟨_, u, f, h⟩ := hz
  have miss : ¬ visible ⊆ Z.image (fun z => detector u f z⁻¹) := by
    intro he
    have ha := Finset.card_le_card he
    rw [ten_visible] at ha
    have hb := Finset.card_image_le (s := Z) (f := fun z => detector u f z⁻¹)
    omega
  obtain ⟨p,hp⟩ := sample_map Z _ h miss
  exact extension basis hk Z p hp



theorem visible_sums : ∀ v : V, ∃ a ∈ visible, ∃ b ∈ visible, a+b=v := by decide

theorem hit_kernel (p : V →ₗ[ZMod 2] Two) : ∃ v ∈ visible, p v = 0 := by
  have hdim := p.finrank_range_add_finrank_ker
  have hr := (LinearMap.range p).finrank_le
  have h4 : Module.finrank (ZMod 2) V = 4 := by simp [V]
  have h2 : Module.finrank (ZMod 2) Two = 2 := by simp [Two]
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2)
    (M := LinearMap.ker p) (n := 2) (by omega)
  let w : Fin 2 → V := fun i => (v i).val
  have hw : LinearIndependent (ZMod 2) w := hv.map' _ (Submodule.ker_subtype _)
  have hxy : w 0 ≠ w 1 := fun e => (by decide : (0 : Fin 2) ≠ 1) (hw.injective e)
  have hmem (i : Fin 2) : p (w i) = 0 := (v i).property
  rcases plane_hits_visible _ _ (hw.ne_zero 0) (hw.ne_zero 1) hxy with h | h | h
  · exact ⟨w 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hmem 0⟩
  · exact ⟨w 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hmem 1⟩
  · exact ⟨w 0+w 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, by simp [hmem]⟩

theorem large_avoids_kernel {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    {k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) K) (hk : 4 ≤ k)
    (Y : Finset K) (hy : admissible Y) (hc : Y.card = 3*2^(k-2)) :
    ∃ p : K →ₗ[ZMod 2] Two, ∀ z ∈ Y, p z⁻¹ ≠ 0 := by
  classical
  letI : Finite K := Module.finite_of_finite (ZMod 2)
  letI := Fintype.ofFinite K
  obtain ⟨_, u, f, hh⟩ := hy
  let d := detector u f
  apply sample_map Y d hh
  intro hall
  have surj : Function.Surjective d := by
    intro v
    obtain ⟨a,ha,b,hb,rfl⟩ := visible_sums v
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp (hall ha)
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp (hall hb)
    exact ⟨_, d.map_add _ _⟩
  have hsub : Y.image Inv.inv ⊆ Finset.univ.filter (fun x => d x ∈ visible) := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh z hz⟩⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ inv_injective, hc] at hle
  have hcount := uniform_count d surj visible
  have hd : Fintype.card V = 16 := by decide
  have hK : Fintype.card K = 2^k := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, Module.finrank_eq_card_basis basis, Fintype.card_fin]
  rw [hd, ten_visible, hK, show k = (k-2)+2 by omega, pow_add] at hcount
  have hpos : 0 < 2^(k-2) := Nat.two_pow_pos _
  omega

theorem obstructing_sample {K : Type} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] {k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) K)
    (f : K →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (hk : 4 ≤ k) :
    ∃ Z : Finset K, admissible Z ∧ Z.card = 10 ∧
      ¬ ∃ Y : Finset K, admissible Y ∧ Z ⊆ Y ∧ Y.card = 3*2^(k-2) := by
  classical
  have hdim : Module.finrank (ZMod 2) K = k := by simp [Module.finrank_eq_card_basis basis]
  obtain ⟨u,l,hs⟩ := full_detector f hf (by omega)
  let d := detector u l
  obtain ⟨s, hsec⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  have hleft (v : V) : d (s v) = v := DFunLike.congr_fun hsec v
  let Z := visible.image (fun v => (s v)⁻¹)
  refine ⟨Z, ⟨?_,u,l,?_⟩, ?_, ?_⟩
  · intro hz
    obtain ⟨v,hv,e⟩ := Finset.mem_image.mp hz
    have h0 : s v = 0 := inv_eq_zero.mp e
    have he : v = 0 := by rw [← hleft v, h0, map_zero]
    exact zero_blind (he ▸ (Finset.mem_filter.mp hv).2)
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    change detects (d (s v)⁻¹⁻¹)
    rw [inv_inv, hleft]
    exact (Finset.mem_filter.mp hv).2
  · exact (Finset.card_image_of_injective _ (inv_injective.comp (show Function.Injective s from
      (show Function.LeftInverse d s from hleft).injective))).trans ten_visible
  · rintro ⟨Y,hy,hsub,hcard⟩
    obtain ⟨p,hp⟩ := large_avoids_kernel basis hk Y hy hcard
    obtain ⟨v,hv,hkill⟩ := hit_kernel (p.comp s)
    have hn := hp _ (hsub (Finset.mem_image_of_mem _ hv))
    apply hn
    simpa only [inv_inv, LinearMap.comp_apply] using hkill


end PEqualNP.Outside.L_meta_57330

theorem PEqualNP.Outside.L_meta_57330 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
  let n := k+1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : K) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)
  let serves := fun (s : ℕ) (Z : Finset K) =>
    ∃ (p : ℕ) (T : Fin p → Fin n → Fin n → Bool),
      fits n n p T s ∧ ∀ z ∈ Z, ∃ S : Finset (Fin p),
        fits n n 1 (fun _ => residual T S z) (k/2)

  let feasible := fun (Z : Finset K) => (0 : K) ∉ Z ∧ serves 1 Z
  5 ≤ k → k % 2 = 1 →
    IsLeast {m : ℕ | ∃ Z : Finset K, feasible Z ∧ Z.card = m ∧
      ¬ ∃ Y : Finset K, feasible Y ∧ Z ⊆ Y ∧ Y.card = 3 * 2^(k-2)} 10) := by
  intro nonlinear depths fits F K _ _ _ k basis bit hbit n point mult residual serves feasible hk odd
  have characterization (Z : Finset K) : feasible Z ↔ L_meta_57330.admissible Z := by
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro h0
    rw [show serves 1 Z ↔ _ from
      PEqualNP.Outside.L_meta_29768 K k basis bit hbit odd 1 Z h0]
    constructor
    · rintro ⟨u, f, hh⟩
      refine ⟨(fun j => u (0,j)), (fun i => f (0,i)), ?_⟩
      intro z hz
      rw [L_meta_57330.detector_apply]
      exact (L_meta_57330.minor_iff _).mp (hh z hz)
    · rintro ⟨u, f, hh⟩
      refine ⟨(fun j => u j.2), (fun i => f i.2), ?_⟩
      intro z hz
      apply (L_meta_57330.minor_iff _).mpr
      simpa only [L_meta_57330.detector_apply, L_meta_57330.pack] using hh z hz
  simp only [characterization]
  constructor
  · exact L_meta_57330.obstructing_sample basis bit hbit (by omega)
  · rintro m ⟨Z, hz, rfl, hn⟩
    by_contra! hc
    exact hn (L_meta_57330.small_extends basis (by omega) Z hz hc)
