import Mathlib

/-! Local lemmas of Landau type, from the Borel–Carathéodory theorem.

* `norm_logDeriv_le_of_ne_zero`: if `f` is holomorphic and zero-free on a disc of radius `r` and
  `‖f‖ ≤ e^M ‖f c‖` there, then `‖f'/f‖ ≤ 24 M / r` on the concentric disc of radius `r/2`.
* `re_logDeriv_ge`: if `f` is holomorphic on a disc of radius `R` about `c`, `f c ≠ 0`,
  `‖f‖ ≤ e^M ‖f c‖` there and every zero in the disc of radius `R/4` lies weakly to the left of
  `c`, then `re (f'/f) c ≥ -96 M / R`.
* `re_logDeriv_ge_of_zero`: the same with the contribution `re (1/(c-u))` of a chosen zero `u`.

Zeros are divided out one at a time with `dslope`; each division halves `e^M`, so the process
stops. No products over zeros and no multiplicities are needed. -/

open Complex Metric Set Filter Topology

noncomputable section
namespace ZetaRegion

/-- A zero-free holomorphic function on a disc has a holomorphic logarithm. -/
lemma exists_log_on_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hne : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c r) ∧ h c = 0 ∧
      (∀ z ∈ ball c r, f z = f c * exp (h z)) ∧
      ∀ z ∈ ball c r, deriv h z = deriv f z / f z := by
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨h, hc, hh⟩ := hd.isExactOn_ball.with_val_at c 0
  have hcb : c ∈ ball c r := mem_ball_self hr
  refine ⟨h, fun z hz => (hh z hz).differentiableAt.differentiableWithinAt, hc, ?_,
    fun z hz => (hh z hz).deriv⟩
  have hg : ∀ z ∈ ball c r, HasDerivAt (fun z => f z * exp (-h z)) 0 z := by
    intro z hz
    have h1 : HasDerivAt f (deriv f z) z :=
      (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h2 := (hh z hz).neg.cexp
    have h3 := h1.mul h2
    have e : deriv f z * exp (-h z) + f z * (exp (-h z) * -(deriv f z / f z)) = 0 := by
      have := hne z hz
      field_simp
      ring
    rw [← e]
    exact h3
  have hconst : ∀ z ∈ ball c r, f z * exp (-h z) = f c * exp (-h c) := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hg z hz).deriv) hz hcb
  intro z hz
  have := hconst z hz
  rw [hc, neg_zero, exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]

/-- The exponent in a bound `‖f‖ ≤ e^M ‖f c‖` near `c` is nonnegative. -/
lemma exponent_nonneg {f : ℂ → ℂ} {c : ℂ} {M : ℝ} (hfc : f c ≠ 0)
    (hb : ‖f c‖ ≤ Real.exp M * ‖f c‖) : 0 ≤ M := by
  have hpos : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have h1 : 1 ≤ Real.exp M := by
    by_contra h
    push Not at h
    nlinarith
  rwa [← Real.exp_zero, Real.exp_le_exp] at h1

/-- **Zero-free local lemma.** -/
theorem norm_logDeriv_le_of_ne_zero {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hne : ∀ z ∈ ball c r, f z ≠ 0)
    (hb : ∀ z ∈ ball c r, ‖f z‖ ≤ Real.exp M * ‖f c‖) {s : ℂ} (hs : s ∈ closedBall c (r / 2)) :
    ‖deriv f s / f s‖ ≤ 24 * M / r := by
  have hcb : c ∈ ball c r := mem_ball_self hr
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hne c hcb)
  have hM : 0 ≤ M := exponent_nonneg (hne c hcb) (hb c hcb)
  obtain ⟨h, hh, hhc, hexp, hderiv⟩ := exists_log_on_ball hr hf hne
  have hre : ∀ z ∈ ball c r, (h z).re ≤ M := by
    intro z hz
    have h1 := hb z hz
    rw [hexp z hz, norm_mul, Complex.norm_exp, mul_comm] at h1
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_right h1 hfc)
  have hsb : s ∈ ball c r := by
    rw [mem_closedBall] at hs
    rw [mem_ball]
    linarith
  rw [← hderiv s hsb]
  have key : ∀ δ > 0, ‖deriv h s‖ ≤ 24 * (M + δ) / r := by
    intro δ hδ
    have hM' : 0 < M + δ := by linarith
    have hmem : ∀ w ∈ ball (0 : ℂ) r, c + w ∈ ball c r := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hw
    have hHd : DifferentiableOn ℂ (fun w => h (c + w)) (ball 0 r) := by
      intro w hw
      exact ((hh.differentiableAt (isOpen_ball.mem_nhds (hmem w hw))).comp w
        (differentiableAt_id.const_add c)).differentiableWithinAt
    have hHm : MapsTo (fun w => h (c + w)) (ball 0 r) {z | z.re ≤ M + δ} := by
      intro w hw
      have := hre _ (hmem w hw)
      simp only [mem_ofPred_eq]
      linarith
    have hbound : ∀ z ∈ closedBall c (3 * r / 4), ‖h z‖ ≤ 6 * (M + δ) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      have hw : z - c ∈ ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff]
        linarith
      have h0 : (fun w => h (c + w)) 0 = 0 := by simp [hhc]
      have := Complex.borelCaratheodory_zero hM' hHd hHm hr hw h0
      simp only [add_sub_cancel] at this
      refine this.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (z - c),
        mul_nonneg hM'.le (by linarith : (0 : ℝ) ≤ 3 * r / 4 - ‖z - c‖)]
    have hsub : closedBall s (r / 4) ⊆ closedBall c (3 * r / 4) := by
      intro z hz
      rw [mem_closedBall] at hz hs ⊢
      linarith [dist_triangle z s c]
    have hsub' : closedBall s (r / 4) ⊆ ball c r :=
      hsub.trans (closedBall_subset_ball (by linarith))
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r / 4)
      (hh.diffContOnCl_ball hsub') (fun z hz => hbound z (hsub (sphere_subset_closedBall hz)))
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := key (ε * r / 24) (by positivity)
  refine this.trans (le_of_eq ?_)
  field_simp

/-- Dividing out one zero `u` near the centre: the quotient `dslope f u` satisfies the same
hypotheses with `M` replaced by `M - log 2`. -/
lemma factor_zero {f : ℂ → ℂ} {c u : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hfc : f c ≠ 0)
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hu : u ∈ closedBall c (R / 4)) (hfu : f u = 0) :
    DifferentiableOn ℂ (dslope f u) (ball c R) ∧ dslope f u c ≠ 0 ∧
    (∀ z, f z = (z - u) * dslope f u z) ∧
    (∀ z ∈ ball c R, ‖dslope f u z‖ ≤ Real.exp (M - Real.log 2) * ‖dslope f u c‖) ∧
    deriv f c / f c = 1 / (c - u) + deriv (dslope f u) c / dslope f u c := by
  have hcb : c ∈ ball c R := mem_ball_self hR
  have hub : u ∈ ball c R := closedBall_subset_ball (by linarith) hu
  have hgd : DifferentiableOn ℂ (dslope f u) (ball c R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds hub)).mpr hf
  have hfg : ∀ z, f z = (z - u) * dslope f u z := by
    intro z
    have := sub_smul_dslope f u z
    rw [hfu, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hcu : c - u ≠ 0 := by
    intro h
    apply hfc
    rw [hfg c, h, zero_mul]
  have hgc : dslope f u c ≠ 0 := by
    intro h
    apply hfc
    rw [hfg c, h, mul_zero]
  have hcu_norm : ‖c - u‖ ≤ R / 4 := by
    rw [mem_closedBall, dist_comm, dist_eq_norm] at hu
    exact hu
  have hfc_le : ‖f c‖ ≤ R / 4 * ‖dslope f u c‖ := by
    rw [hfg c, norm_mul]
    gcongr
  have houter : ∀ z ∈ ball c R, 3 * R / 4 ≤ dist z c →
      ‖dslope f u z‖ ≤ Real.exp M * ‖f c‖ / (R / 2) := by
    intro z hz hzc
    have hzu : R / 2 ≤ ‖z - u‖ := by
      have := dist_triangle z u c
      rw [mem_closedBall] at hu
      rw [← dist_eq_norm]
      linarith
    rw [le_div_iff₀ (by positivity)]
    calc ‖dslope f u z‖ * (R / 2) ≤ ‖dslope f u z‖ * ‖z - u‖ := by gcongr
      _ = ‖f z‖ := by rw [hfg z, norm_mul, mul_comm]
      _ ≤ Real.exp M * ‖f c‖ := hb z hz
  have hall : ∀ z ∈ ball c R, ‖dslope f u z‖ ≤ Real.exp M * ‖f c‖ / (R / 2) := by
    intro z hz
    by_cases hzc : 3 * R / 4 ≤ dist z c
    · exact houter z hz hzc
    · push Not at hzc
      have hsub : closedBall c (3 * R / 4) ⊆ ball c R := closedBall_subset_ball (by linarith)
      refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball c (3 * R / 4))
        isBounded_ball (hgd.diffContOnCl_ball hsub) (fun w hw => ?_)
        (subset_closure (mem_ball.mpr hzc))
      rw [frontier_ball c (by positivity)] at hw
      refine houter w (hsub (sphere_subset_closedBall hw)) ?_
      rw [mem_sphere] at hw
      rw [hw]
  refine ⟨hgd, hgc, hfg, fun z hz => ?_, ?_⟩
  · refine (hall z hz).trans ?_
    rw [Real.exp_sub, Real.exp_log (by norm_num), div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ Real.exp M := (Real.exp_pos M).le
    nlinarith [mul_le_mul_of_nonneg_left hfc_le h0]
  · have hgdc : HasDerivAt (dslope f u) (deriv (dslope f u) c) c :=
      (hgd.differentiableAt (isOpen_ball.mem_nhds hcb)).hasDerivAt
    have hfd : HasDerivAt f (1 * dslope f u c + (c - u) * deriv (dslope f u) c) c := by
      have := ((hasDerivAt_id c).sub_const u).mul hgdc
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
      simp [hfg z]
    rw [hfd.deriv, hfg c]
    field_simp

theorem re_logDeriv_ge_aux {c : ℂ} {R : ℝ} (hR : 0 < R) : ∀ (n : ℕ) (f : ℂ → ℂ) (M : ℝ),
    M < n * Real.log 2 → DifferentiableOn ℂ f (ball c R) → f c ≠ 0 →
    (∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp M * ‖f c‖) →
    (∀ u ∈ closedBall c (R / 4), f u = 0 → u.re ≤ c.re) →
    -(96 * M / R) ≤ (deriv f c / f c).re := by
  intro n
  induction n with
  | zero =>
    intro f M hM hf hfc hb _
    have hM0 := exponent_nonneg hfc (hb c (mem_ball_self hR))
    simp at hM
    linarith
  | succ n ih =>
    intro f M hM hf hfc hb hz
    by_cases hex : ∃ u ∈ closedBall c (R / 4), f u = 0
    · obtain ⟨u, hu, hfu⟩ := hex
      obtain ⟨hgd, hgc, hfg, hgb, hld⟩ := factor_zero hR hf hfc hb hu hfu
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hM' : M - Real.log 2 < n * Real.log 2 := by
        push_cast at hM
        linarith
      have h1 := ih (dslope f u) (M - Real.log 2) hM' hgd hgc hgb
        (fun v hv hgv => hz v hv (by rw [hfg v, hgv, mul_zero]))
      rw [hld, add_re]
      have hre : 0 ≤ (1 / (c - u)).re := by
        rw [one_div, inv_re]
        have := hz u hu hfu
        exact div_nonneg (by simpa using this) (normSq_nonneg _)
      have h2 : 96 * (M - Real.log 2) / R ≤ 96 * M / R := by
        gcongr
        linarith
      linarith
    · push Not at hex
      have hr : 0 < R / 4 := by positivity
      have hsub : ball c (R / 4) ⊆ ball c R := ball_subset_ball (by linarith)
      have h1 := norm_logDeriv_le_of_ne_zero hr (hf.mono hsub)
        (fun z hz => hex z (ball_subset_closedBall hz)) (fun z hz => hb z (hsub hz))
        (mem_closedBall_self (by positivity) : c ∈ closedBall c (R / 4 / 2))
      have h2 := (abs_le.mp ((abs_re_le_norm _).trans h1)).1
      have h3 : 24 * M / (R / 4) = 96 * M / R := by
        field_simp
        ring
      linarith

/-- **Local lemma, no zero singled out.** -/
theorem re_logDeriv_ge {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hfc : f c ≠ 0)
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hz : ∀ u ∈ closedBall c (R / 4), f u = 0 → u.re ≤ c.re) :
    -(96 * M / R) ≤ (deriv f c / f c).re := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (M / Real.log 2)
  exact re_logDeriv_ge_aux hR n f M ((div_lt_iff₀ hlog2).mp hn) hf hfc hb hz

/-- **Local lemma with one zero singled out.** -/
theorem re_logDeriv_ge_of_zero {f : ℂ → ℂ} {c u : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hfc : f c ≠ 0)
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hz : ∀ u ∈ closedBall c (R / 4), f u = 0 → u.re ≤ c.re)
    (hu : u ∈ closedBall c (R / 4)) (hfu : f u = 0) :
    (1 / (c - u)).re - 96 * M / R ≤ (deriv f c / f c).re := by
  obtain ⟨hgd, hgc, hfg, hgb, hld⟩ := factor_zero hR hf hfc hb hu hfu
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := re_logDeriv_ge hR hgd hgc hgb
    (fun v hv hgv => hz v hv (by rw [hfg v, hgv, mul_zero]))
  rw [hld, add_re]
  have h2 : 96 * (M - Real.log 2) / R ≤ 96 * M / R := by
    gcongr
    linarith
  linarith

end ZetaRegion

#print axioms ZetaRegion.norm_logDeriv_le_of_ne_zero
#print axioms ZetaRegion.re_logDeriv_ge
#print axioms ZetaRegion.re_logDeriv_ge_of_zero
