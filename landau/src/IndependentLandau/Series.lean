import Mathlib

/-! Power-series bookkeeping: coefficient bounds for a function that is, near `0`,
a holomorphic function on a larger disc plus a simple polar term `c / (v - w)`. -/

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal

noncomputable section

namespace IndependentLandau

/-- A function given near `0` by a convergent scalar series has that series as its
formal power series at `0`. -/
theorem hasFPowerSeriesAt_zero_of_hasSum {F : ℂ → ℂ} {a : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ w : ℂ, ‖w‖ < r → HasSum (fun k => a k * w ^ k) (F w)) :
    HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  have hr2 : 0 < r / 2 := by positivity
  set r' : ℝ≥0 := ⟨r / 2, hr2.le⟩ with hr'
  have hr'c : (r' : ℝ) = r / 2 := rfl
  refine ⟨(r' : ℝ≥0∞), ?_, ?_, ?_⟩
  · have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ < r := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr2.le]; linarith
    have hs := (hF ((r / 2 : ℝ) : ℂ) hnorm).summable.norm.tendsto_atTop_zero
    refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
    refine hs.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr2.le, hr'c]
  · exact_mod_cast (show (0 : ℝ) < r' from hr2)
  · intro y hy
    have hy' : ‖y‖ < r := by
      rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_lt_coe] at hy
      have : ‖y‖ < r / 2 := by exact_mod_cast hy
      linarith
    have := hF y hy'
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using this

/-- Coefficient comparison. If `F w = ∑ a k * w ^ k` near `0`, and `F = H + c / (v - ·)`
near `0` with `H` holomorphic on the disc of radius `e`, then `a k - c / v ^ (k + 1)`
decays like `e' ^ (-k)` for every `e' < e`. -/
theorem coeff_bound0 {F : ℂ → ℂ} {a : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ w : ℂ, ‖w‖ < r → HasSum (fun k => a k * w ^ k) (F w))
    {H : ℂ → ℂ} {e : ℝ} (hH : DifferentiableOn ℂ H (ball 0 e)) {c v : ℂ} (hv : v ≠ 0)
    (heq : ∀ᶠ w in 𝓝 (0 : ℂ), F w = H w + c / (v - w))
    {e' : ℝ} (he' : 0 < e') (he'e : e' < e) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖a k - c / v ^ (k + 1)‖ ≤ M / e' ^ k := by
  lift e' to ℝ≥0 using he'.le
  have he'0 : 0 < e' := by exact_mod_cast he'
  have hq : HasFPowerSeriesOnBall H (cauchyPowerSeries H 0 e') 0 e' :=
    DifferentiableOn.hasFPowerSeriesOnBall (hH.mono (closedBall_subset_ball he'e)) he'0
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hP₂ : HasFPowerSeriesAt (fun w => c / (v - w))
      (FormalMultilinearSeries.ofScalars ℂ fun k => c / v ^ (k + 1)) 0 := by
    refine hasFPowerSeriesAt_zero_of_hasSum hvn fun w hw => ?_
    have hξ : ‖w / v‖ < 1 := by rw [norm_div, div_lt_one hvn]; exact hw
    have hvw : v - w ≠ 0 := by
      intro h0
      have : v = w := sub_eq_zero.1 h0
      rw [this] at hw
      exact lt_irrefl _ hw
    have h := (hasSum_geometric_of_norm_lt_one hξ).mul_left (c / v)
    have e1 : c / v * (1 - w / v)⁻¹ = c / (v - w) := by
      field_simp
    rw [e1] at h
    have hfun : (fun k : ℕ => c / v ^ (k + 1) * w ^ k) = fun k => c / v * (w / v) ^ k := by
      funext k
      rw [div_pow, pow_succ]
      field_simp
    rw [hfun]
    exact h
  have h1 := hasFPowerSeriesAt_zero_of_hasSum hr hF
  have h2 : HasFPowerSeriesAt F
      (cauchyPowerSeries H 0 e' + FormalMultilinearSeries.ofScalars ℂ fun k => c / v ^ (k + 1))
      0 :=
    (hq.hasFPowerSeriesAt.add hP₂).congr (heq.mono fun w hw => hw.symm)
  have hser := h1.eq_formalMultilinearSeries h2
  have hcoef : ∀ k, a k - c / v ^ (k + 1) = (cauchyPowerSeries H 0 e').coeff k := by
    intro k
    have h3 := congrArg (fun P : FormalMultilinearSeries ℂ ℂ ℂ => P.coeff k) hser
    simp only [FormalMultilinearSeries.coeff_ofScalars] at h3
    have h4 : (cauchyPowerSeries H 0 e' +
        FormalMultilinearSeries.ofScalars ℂ fun k => c / v ^ (k + 1)).coeff k =
        (cauchyPowerSeries H 0 e').coeff k +
        (FormalMultilinearSeries.ofScalars ℂ fun k => c / v ^ (k + 1)).coeff k := rfl
    rw [h3, h4, FormalMultilinearSeries.coeff_ofScalars]
    ring
  refine ⟨(2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, ‖H (circleMap 0 e' θ)‖, ?_, fun k => ?_⟩
  · have : 0 ≤ ∫ θ : ℝ in 0..2 * Real.pi, ‖H (circleMap 0 e' θ)‖ :=
      intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
    positivity
  · rw [hcoef k, ← FormalMultilinearSeries.norm_apply_eq_norm_coef]
    refine (norm_cauchyPowerSeries_le H 0 e' k).trans (le_of_eq ?_)
    rw [abs_of_pos he', inv_pow, div_eq_mul_inv]

end IndependentLandau
