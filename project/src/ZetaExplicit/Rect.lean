import Mathlib

/-! Boundary integrals over rectangles: basic algebra, the Cauchy–Goursat theorem and the
value `2πi` for the integral of `1/(s - a)` with `a` inside. Mathlib only. -/

open Complex Set MeasureTheory intervalIntegral Topology

noncomputable section
namespace ZetaExplicit

/-- The integral of `f` over the positively oriented boundary of `[x₁, x₂] × [y₁, y₂]`. -/
def rectInt (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : ℂ :=
  (∫ x in x₁..x₂, f (x + y₁ * I)) - (∫ x in x₁..x₂, f (x + y₂ * I)) +
    I * (∫ y in y₁..y₂, f (x₂ + y * I)) - I * ∫ y in y₁..y₂, f (x₁ + y * I)

/-- The boundary of the rectangle `[x₁, x₂] × [y₁, y₂]`. -/
def rectBdry (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  {s : ℂ | x₁ ≤ s.re ∧ s.re ≤ x₂ ∧ y₁ ≤ s.im ∧ s.im ≤ y₂ ∧
    (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂)}

/-- The closed rectangle. -/
def rectClosed (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  {s : ℂ | x₁ ≤ s.re ∧ s.re ≤ x₂ ∧ y₁ ≤ s.im ∧ s.im ≤ y₂}

variable {x₁ x₂ y₁ y₂ : ℝ}

lemma rectBdry_subset_closed : rectBdry x₁ x₂ y₁ y₂ ⊆ rectClosed x₁ x₂ y₁ y₂ :=
  fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

lemma horiz_mem_bottom (hy : y₁ ≤ y₂) {x : ℝ} (hx : x ∈ uIcc x₁ x₂) (hx12 : x₁ ≤ x₂) :
    (x : ℂ) + y₁ * I ∈ rectBdry x₁ x₂ y₁ y₂ := by
  rw [uIcc_of_le hx12] at hx
  simp only [rectBdry, mem_ofPred_eq]
  simp [hx.1, hx.2, hy]

lemma horiz_mem_top (hy : y₁ ≤ y₂) {x : ℝ} (hx : x ∈ uIcc x₁ x₂) (hx12 : x₁ ≤ x₂) :
    (x : ℂ) + y₂ * I ∈ rectBdry x₁ x₂ y₁ y₂ := by
  rw [uIcc_of_le hx12] at hx
  simp only [rectBdry, mem_ofPred_eq]
  simp [hx.1, hx.2, hy]

lemma vert_mem_right (hx12 : x₁ ≤ x₂) {y : ℝ} (hy : y ∈ uIcc y₁ y₂) (hy12 : y₁ ≤ y₂) :
    (x₂ : ℂ) + y * I ∈ rectBdry x₁ x₂ y₁ y₂ := by
  rw [uIcc_of_le hy12] at hy
  simp only [rectBdry, mem_ofPred_eq]
  simp [hy.1, hy.2, hx12]

lemma vert_mem_left (hx12 : x₁ ≤ x₂) {y : ℝ} (hy : y ∈ uIcc y₁ y₂) (hy12 : y₁ ≤ y₂) :
    (x₁ : ℂ) + y * I ∈ rectBdry x₁ x₂ y₁ y₂ := by
  rw [uIcc_of_le hy12] at hy
  simp only [rectBdry, mem_ofPred_eq]
  simp [hy.1, hy.2, hx12]

lemma rectInt_congr (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {f g : ℂ → ℂ}
    (h : EqOn f g (rectBdry x₁ x₂ y₁ y₂)) : rectInt f x₁ x₂ y₁ y₂ = rectInt g x₁ x₂ y₁ y₂ := by
  unfold rectInt
  rw [integral_congr (g := fun x : ℝ => g (x + y₁ * I)) fun x hx' => h (horiz_mem_bottom hy hx' hx),
    integral_congr (g := fun x : ℝ => g (x + y₂ * I)) fun x hx' => h (horiz_mem_top hy hx' hx),
    integral_congr (g := fun y : ℝ => g (x₂ + y * I)) fun y hy' => h (vert_mem_right hx hy' hy),
    integral_congr (g := fun y : ℝ => g (x₁ + y * I)) fun y hy' => h (vert_mem_left hx hy' hy)]

/-- Interval integrability of the four side integrands. -/
lemma sides_integrable (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {f : ℂ → ℂ}
    (hf : ContinuousOn f (rectBdry x₁ x₂ y₁ y₂)) :
    IntervalIntegrable (fun x : ℝ => f (x + y₁ * I)) volume x₁ x₂ ∧
    IntervalIntegrable (fun x : ℝ => f (x + y₂ * I)) volume x₁ x₂ ∧
    IntervalIntegrable (fun y : ℝ => f (x₂ + y * I)) volume y₁ y₂ ∧
    IntervalIntegrable (fun y : ℝ => f (x₁ + y * I)) volume y₁ y₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop) fun x hx' => horiz_mem_bottom hy hx' hx).intervalIntegrable
  · exact (hf.comp (by fun_prop) fun x hx' => horiz_mem_top hy hx' hx).intervalIntegrable
  · exact (hf.comp (by fun_prop) fun y hy' => vert_mem_right hx hy' hy).intervalIntegrable
  · exact (hf.comp (by fun_prop) fun y hy' => vert_mem_left hx hy' hy).intervalIntegrable

lemma rectInt_add (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (rectBdry x₁ x₂ y₁ y₂)) (hg : ContinuousOn g (rectBdry x₁ x₂ y₁ y₂)) :
    rectInt (fun s => f s + g s) x₁ x₂ y₁ y₂ = rectInt f x₁ x₂ y₁ y₂ + rectInt g x₁ x₂ y₁ y₂ := by
  obtain ⟨f1, f2, f3, f4⟩ := sides_integrable hx hy hf
  obtain ⟨g1, g2, g3, g4⟩ := sides_integrable hx hy hg
  unfold rectInt
  rw [integral_add f1 g1, integral_add f2 g2, integral_add f3 g3, integral_add f4 g4]
  ring

lemma rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) :
    rectInt (fun s => c * f s) x₁ x₂ y₁ y₂ = c * rectInt f x₁ x₂ y₁ y₂ := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma rectInt_zero : rectInt (fun _ => 0) x₁ x₂ y₁ y₂ = 0 := by
  unfold rectInt; simp

lemma rectInt_sum (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, ContinuousOn (f i) (rectBdry x₁ x₂ y₁ y₂)) :
    rectInt (fun s => ∑ i ∈ S, f i s) x₁ x₂ y₁ y₂ = ∑ i ∈ S, rectInt (f i) x₁ x₂ y₁ y₂ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectInt_zero]
  | insert a S ha ih =>
    have h1 : ContinuousOn (f a) (rectBdry x₁ x₂ y₁ y₂) := hf a (Finset.mem_insert_self a S)
    have h2 : ∀ i ∈ S, ContinuousOn (f i) (rectBdry x₁ x₂ y₁ y₂) := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have h3 : ContinuousOn (fun s => ∑ i ∈ S, f i s) (rectBdry x₁ x₂ y₁ y₂) :=
      continuousOn_finsetSum S h2
    simp only [Finset.sum_insert ha]
    rw [rectInt_add hx hy h1 h3, ih h2]

/-- Cauchy–Goursat for a rectangle. -/
lemma rectInt_eq_zero (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (rectClosed x₁ x₂ y₁ y₂)) : rectInt f x₁ x₂ y₁ y₂ = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    (hf.mono ?_)
  · simpa [rectInt] using h
  · intro s hs
    rw [mem_reProdIm] at hs
    simp only [uIcc_of_le hx, uIcc_of_le hy, mem_Icc] at hs
    exact ⟨hs.1.1, hs.1.2, hs.2.1, hs.2.2⟩

/-- Integral of `v / (p + t v)` along an affine path inside the slit plane. -/
lemma integral_affine_inv {p v : ℂ} {t₁ t₂ : ℝ}
    (h : ∀ t ∈ uIcc t₁ t₂, p + t * v ∈ slitPlane) :
    ∫ t in t₁..t₂, v * (p + t * v)⁻¹ = Complex.log (p + t₂ * v) - Complex.log (p + t₁ * v) := by
  refine integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => Complex.log (p + t * v)) ?_ ?_
  · intro t ht
    have h1 : HasDerivAt (fun t : ℝ => p + (t : ℂ) * v) v t := by
      have := ((hasDerivAt_id t).ofReal_comp.mul_const v).const_add p
      simpa using this
    have h2 := h1.clog_real (h t ht)
    rwa [div_eq_mul_inv] at h2
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) ?_)
    exact fun t ht => slitPlane_ne_zero (h t ht)

lemma integral_affine_inv_neg {p v : ℂ} {t₁ t₂ : ℝ}
    (h : ∀ t ∈ uIcc t₁ t₂, -(p + t * v) ∈ slitPlane) :
    ∫ t in t₁..t₂, v * (p + t * v)⁻¹ =
      Complex.log (-(p + t₂ * v)) - Complex.log (-(p + t₁ * v)) := by
  have h' : ∀ t ∈ uIcc t₁ t₂, -p + t * -v ∈ slitPlane := fun t ht => by
    have := h t ht
    rwa [show -p + (t : ℂ) * -v = -(p + t * v) by ring]
  have := integral_affine_inv h'
  rw [show -p + (t₂ : ℂ) * -v = -(p + t₂ * v) by ring,
    show -p + (t₁ : ℂ) * -v = -(p + t₁ * v) by ring] at this
  rw [← this]
  refine integral_congr fun t _ => ?_
  rw [show -p + (t : ℂ) * -v = -(p + t * v) by ring, inv_neg]
  ring

lemma log_sub_log_neg_of_im_pos {w : ℂ} (h : 0 < w.im) :
    Complex.log w - Complex.log (-w) = Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos h]

lemma log_neg_sub_log_of_im_neg {w : ℂ} (h : w.im < 0) :
    Complex.log (-w) - Complex.log w = Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg h]

/-- The boundary integral of `1/(s - a)` is `2πi` when `a` is strictly inside. -/
theorem rectInt_inv_sub {a : ℂ} (hx₁ : x₁ < a.re) (hx₂ : a.re < x₂) (hy₁ : y₁ < a.im)
    (hy₂ : a.im < y₂) :
    rectInt (fun s => (s - a)⁻¹) x₁ x₂ y₁ y₂ = 2 * Real.pi * I := by
  have hb : ∫ x in x₁..x₂, (((x : ℂ) + y₁ * I) - a)⁻¹ =
      Complex.log (x₂ + y₁ * I - a) - Complex.log (x₁ + y₁ * I - a) := by
    have := integral_affine_inv (p := y₁ * I - a) (v := 1) (t₁ := x₁) (t₂ := x₂) fun t _ => by
      rw [mem_slitPlane_iff]; right; simp; linarith
    rw [show (y₁ * I - a + (x₂ : ℂ) * 1) = x₂ + y₁ * I - a by ring,
      show (y₁ * I - a + (x₁ : ℂ) * 1) = x₁ + y₁ * I - a by ring] at this
    rw [← this]
    refine integral_congr fun t _ => ?_
    rw [one_mul]; congr 1; ring
  have ht : ∫ x in x₁..x₂, (((x : ℂ) + y₂ * I) - a)⁻¹ =
      Complex.log (x₂ + y₂ * I - a) - Complex.log (x₁ + y₂ * I - a) := by
    have := integral_affine_inv (p := y₂ * I - a) (v := 1) (t₁ := x₁) (t₂ := x₂) fun t _ => by
      rw [mem_slitPlane_iff]; right; simp; linarith
    rw [show (y₂ * I - a + (x₂ : ℂ) * 1) = x₂ + y₂ * I - a by ring,
      show (y₂ * I - a + (x₁ : ℂ) * 1) = x₁ + y₂ * I - a by ring] at this
    rw [← this]
    refine integral_congr fun t _ => ?_
    rw [one_mul]; congr 1; ring
  have hr : I * ∫ y in y₁..y₂, (((x₂ : ℂ) + y * I) - a)⁻¹ =
      Complex.log (x₂ + y₂ * I - a) - Complex.log (x₂ + y₁ * I - a) := by
    have := integral_affine_inv (p := x₂ - a) (v := I) (t₁ := y₁) (t₂ := y₂) fun t _ => by
      rw [mem_slitPlane_iff]; left; simp; linarith
    rw [show ((x₂ : ℂ) - a + (y₂ : ℂ) * I) = x₂ + y₂ * I - a by ring,
      show ((x₂ : ℂ) - a + (y₁ : ℂ) * I) = x₂ + y₁ * I - a by ring] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine integral_congr fun t _ => ?_
    congr 2; ring
  have hl : I * ∫ y in y₁..y₂, (((x₁ : ℂ) + y * I) - a)⁻¹ =
      Complex.log (-(x₁ + y₂ * I - a)) - Complex.log (-(x₁ + y₁ * I - a)) := by
    have := integral_affine_inv_neg (p := x₁ - a) (v := I) (t₁ := y₁) (t₂ := y₂) fun t _ => by
      rw [mem_slitPlane_iff]; left; simp; linarith
    rw [show ((x₁ : ℂ) - a + (y₂ : ℂ) * I) = x₁ + y₂ * I - a by ring,
      show ((x₁ : ℂ) - a + (y₁ : ℂ) * I) = x₁ + y₁ * I - a by ring] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine integral_congr fun t _ => ?_
    congr 2; ring
  have e1 := log_sub_log_neg_of_im_pos (w := x₁ + y₂ * I - a) (by simp; linarith)
  have e2 := log_neg_sub_log_of_im_neg (w := x₁ + y₁ * I - a) (by simp; linarith)
  unfold rectInt
  rw [hb, ht, hr, hl]
  linear_combination e1 + e2

/-- Boundary integral of a principal part. -/
theorem rectInt_div_sub {a : ℂ} (c : ℂ) (hx₁ : x₁ < a.re) (hx₂ : a.re < x₂) (hy₁ : y₁ < a.im)
    (hy₂ : a.im < y₂) :
    rectInt (fun s => c / (s - a)) x₁ x₂ y₁ y₂ = 2 * Real.pi * I * c := by
  simp only [div_eq_mul_inv]
  rw [rectInt_const_mul, rectInt_inv_sub hx₁ hx₂ hy₁ hy₂]
  ring

lemma continuousOn_div_sub {a : ℂ} (c : ℂ) (hx₁ : x₁ < a.re) (hx₂ : a.re < x₂) (hy₁ : y₁ < a.im)
    (hy₂ : a.im < y₂) : ContinuousOn (fun s : ℂ => c / (s - a)) (rectBdry x₁ x₂ y₁ y₂) := by
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun s hs h0 => ?_
  have hsa : s = a := sub_eq_zero.mp h0
  subst hsa
  obtain ⟨-, -, -, -, h | h | h | h⟩ := hs <;> linarith

lemma mem_interior_ne_bdry {a s : ℂ} (hx₁ : x₁ < a.re) (hx₂ : a.re < x₂) (hy₁ : y₁ < a.im)
    (hy₂ : a.im < y₂) (hs : s ∈ rectBdry x₁ x₂ y₁ y₂) : s ≠ a := by
  rintro rfl
  obtain ⟨-, -, -, -, h | h | h | h⟩ := hs <;> linarith

/-- A residue theorem for rectangles: if on the boundary `F` is a finite sum of terms
`H a s / (s - a)` with `H a` holomorphic near the closed rectangle and `a` strictly inside, then
the boundary integral of `F` is `2πi ∑ H a a`. -/
theorem rectInt_eq_sum_residues (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {U : Set ℂ} (hU : IsOpen U)
    (hsub : rectClosed x₁ x₂ y₁ y₂ ⊆ U) (P : Finset ℂ) (H : ℂ → ℂ → ℂ)
    (hH : ∀ a ∈ P, DifferentiableOn ℂ (H a) U)
    (hP : ∀ a ∈ P, x₁ < a.re ∧ a.re < x₂ ∧ y₁ < a.im ∧ a.im < y₂) {F : ℂ → ℂ}
    (hF : ∀ s ∈ rectBdry x₁ x₂ y₁ y₂, F s = ∑ a ∈ P, H a s / (s - a)) :
    rectInt F x₁ x₂ y₁ y₂ = 2 * Real.pi * I * ∑ a ∈ P, H a a := by
  have hPU : ∀ a ∈ P, a ∈ U := fun a ha => hsub
    ⟨(hP a ha).1.le, (hP a ha).2.1.le, (hP a ha).2.2.1.le, (hP a ha).2.2.2.le⟩
  have hd : ∀ a ∈ P, DifferentiableOn ℂ (dslope (H a) a) U := fun a ha =>
    (Complex.differentiableOn_dslope (hU.mem_nhds (hPU a ha))).mpr (hH a ha)
  have hG : DifferentiableOn ℂ (fun s => ∑ a ∈ P, dslope (H a) a s) U :=
    DifferentiableOn.fun_sum hd
  have hGc : ContinuousOn (fun s => ∑ a ∈ P, dslope (H a) a s) (rectBdry x₁ x₂ y₁ y₂) :=
    hG.continuousOn.mono (rectBdry_subset_closed.trans hsub)
  have hPPc : ∀ a ∈ P, ContinuousOn (fun s : ℂ => H a a / (s - a)) (rectBdry x₁ x₂ y₁ y₂) :=
    fun a ha => continuousOn_div_sub _ (hP a ha).1 (hP a ha).2.1 (hP a ha).2.2.1 (hP a ha).2.2.2
  have hPP : ContinuousOn (fun s : ℂ => ∑ a ∈ P, H a a / (s - a)) (rectBdry x₁ x₂ y₁ y₂) :=
    continuousOn_finsetSum P hPPc
  have hEq : EqOn F (fun s => (∑ a ∈ P, dslope (H a) a s) + ∑ a ∈ P, H a a / (s - a))
      (rectBdry x₁ x₂ y₁ y₂) := by
    intro s hs
    beta_reduce
    rw [hF s hs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hne : s ≠ a :=
      mem_interior_ne_bdry (hP a ha).1 (hP a ha).2.1 (hP a ha).2.2.1 (hP a ha).2.2.2 hs
    have h0 : s - a ≠ 0 := sub_ne_zero.mpr hne
    rw [dslope_of_ne _ hne, slope_def_field]
    field_simp
    ring
  rw [rectInt_congr hx hy hEq, rectInt_add hx hy hGc hPP,
    rectInt_eq_zero hx hy (hG.mono hsub), zero_add, rectInt_sum hx hy P _ hPPc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  exact rectInt_div_sub _ (hP a ha).1 (hP a ha).2.1 (hP a ha).2.2.1 (hP a ha).2.2.2

end ZetaExplicit

#print axioms ZetaExplicit.rectInt_inv_sub
#print axioms ZetaExplicit.rectInt_eq_sum_residues
