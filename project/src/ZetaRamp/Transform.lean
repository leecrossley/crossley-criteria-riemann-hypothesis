import Mathlib
import IndependentLandau.Laplace
import IndependentLandau.Analytic
import ZetaRamp.Bounds

/-! The Laplace transform of `rampH u = rampG (exp u) - (1 + γ) exp (-u)` on `re s > 1` is `psi`,
with absolute convergence. -/

open scoped ArithmeticFunction.vonMangoldt
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace ZetaRamp

open IndependentLandau ZetaShared

/-- The centred ramp in the variable `u = log y`, with its value at `u = 0` removed. -/
def rampH (u : ℝ) : ℝ :=
  rampG (Real.exp u) - (1 + Real.eulerMascheroniConstant) * Real.exp (-u)

/-- The transform of the sum part converges absolutely on `re s > 1`. -/
lemma integrableOn_rampS_laplace' {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)) (Ioi 0) := by
  have hm : Measurable (fun u : ℝ => ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)) :=
    (Complex.measurable_ofReal.comp (measurable_rampS.comp Real.measurable_exp)).mul
      (Continuous.measurable (by fun_prop))
  have h2 : ∀ u : ℝ, ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u) = ∑' n, lapT s n u := by
    intro u
    rw [rampS_eq_tsum, Complex.ofReal_tsum, ← tsum_mul_right]; rfl
  have hF_int := integrable_lapT hs
  have hF_sum := summable_integral_norm_lapT hs
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have hfin : ∑' n, ∫⁻ u in Ioi (0 : ℝ), ‖lapT s n u‖ₑ ≠ ⊤ := by
    have (i : ℕ) : ∫⁻ a in Ioi (0 : ℝ), ‖lapT s i a‖ₑ
        = ‖∫ a in Ioi (0 : ℝ), ‖lapT s i a‖‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (lapT s i a)))]
      simp only [coe_nnnorm]
    rw [funext this]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs
  refine lt_of_le_of_lt ?_ hfin.lt_top
  calc ∫⁻ u in Ioi (0 : ℝ), ‖((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)‖ₑ
      ≤ ∫⁻ u in Ioi (0 : ℝ), ∑' n, ‖lapT s n u‖ₑ := by
        refine lintegral_mono fun u => ?_
        rw [h2 u]
        exact enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ u in Ioi (0 : ℝ), ‖lapT s n u‖ₑ :=
        lintegral_tsum fun n => (hF_int n).1.enorm

/-- `∫₀^∞ u e^{-ru} du = 1 / r²`, with integrability, for `re r > 0`. -/
lemma integral_id_mul_cexp' {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * cexp (-r * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (u : ℂ) * cexp (-r * u) = 1 / r ^ 2 := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  have hnorm : ∀ u : ℝ, ‖cexp (-r * u)‖ = Real.exp (-r.re * u) := by
    intro u; simp [Complex.norm_exp]
  have hsplit : ∀ u : ℝ, Real.exp (-r.re * u)
      = Real.exp (-(r.re / 2 * u)) * Real.exp (-(r.re / 2 * u)) := by
    intro u; rw [← Real.exp_add]; congr 1; ring
  have hle : ∀ u : ℝ, 0 ≤ u → Real.exp (-r.re * u) ≤ Real.exp (-(r.re / 2 * u)) := by
    intro u hu; apply Real.exp_le_exp.mpr; nlinarith
  have hxe : ∀ u : ℝ, r.re / 2 * u * Real.exp (-(r.re / 2 * u)) ≤ 1 := by
    intro u
    have h1 : r.re / 2 * u ≤ Real.exp (r.re / 2 * u) := by
      linarith [Real.add_one_le_exp (r.re / 2 * u)]
    have h2 : Real.exp (r.re / 2 * u) * Real.exp (-(r.re / 2 * u)) = 1 := by
      rw [← Real.exp_add]; simp
    calc r.re / 2 * u * Real.exp (-(r.re / 2 * u))
        ≤ Real.exp (r.re / 2 * u) * Real.exp (-(r.re / 2 * u)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := h2
  have hue : ∀ u : ℝ, u * Real.exp (-r.re * u) ≤ 2 / r.re * Real.exp (-(r.re / 2 * u)) := by
    intro u
    have e : u * Real.exp (-r.re * u)
        = 2 / r.re * (r.re / 2 * u * Real.exp (-(r.re / 2 * u))) * Real.exp (-(r.re / 2 * u)) := by
      rw [hsplit u]; field_simp
    rw [e]
    have h3 : 2 / r.re * (r.re / 2 * u * Real.exp (-(r.re / 2 * u))) ≤ 2 / r.re * 1 :=
      mul_le_mul_of_nonneg_left (hxe u) (by positivity)
    calc 2 / r.re * (r.re / 2 * u * Real.exp (-(r.re / 2 * u))) * Real.exp (-(r.re / 2 * u))
        ≤ 2 / r.re * 1 * Real.exp (-(r.re / 2 * u)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = 2 / r.re * Real.exp (-(r.re / 2 * u)) := by ring
  -- integrability
  have hint : IntegrableOn (fun u : ℝ => (u : ℂ) * cexp (-r * u)) (Ioi 0) := by
    have hb : IntegrableOn (fun u : ℝ => 2 / r.re * Real.exp (-(r.re / 2) * u)) (Ioi 0) :=
      Integrable.const_mul (integrableOn_exp_mul_Ioi (by linarith) 0) _
    refine Integrable.mono' hb (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_mul, hnorm, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    have := hue u
    rwa [show -(r.re / 2 * u) = -(r.re / 2) * u by ring] at this
  refine ⟨hint, ?_⟩
  -- limits at infinity
  have hE : Tendsto (fun u : ℝ => Real.exp (-(r.re / 2 * u))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < r.re / 2))
  have hg2 : Tendsto (fun u : ℝ => cexp (-r * u)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun u : ℝ => Real.exp (-(r.re / 2 * u))) ?_ hE
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [hnorm]
    exact hle u hu
  have hg1 : Tendsto (fun u : ℝ => (u : ℂ) * cexp (-r * u)) atTop (𝓝 0) := by
    have hE' : Tendsto (fun u : ℝ => 2 / r.re * Real.exp (-(r.re / 2 * u))) atTop (𝓝 0) := by
      simpa using hE.const_mul (2 / r.re)
    refine squeeze_zero_norm' (a := fun u : ℝ => 2 / r.re * Real.exp (-(r.re / 2 * u))) ?_ hE'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [norm_mul, hnorm, Complex.norm_real, Real.norm_of_nonneg hu]
    exact hue u
  have hlim : Tendsto (fun u : ℝ => -(((u : ℂ) / r + 1 / r ^ 2) * cexp (-r * u))) atTop (𝓝 0) := by
    have h := (hg1.const_mul (-(1 / r))).sub (hg2.const_mul (1 / r ^ 2))
    have h0 : -(1 / r) * 0 - 1 / r ^ 2 * 0 = (0 : ℂ) := by simp
    rw [h0] at h
    refine h.congr fun u => ?_
    ring
  -- antiderivative
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt
      (fun u : ℝ => -(((u : ℂ) / r + 1 / r ^ 2) * cexp (-r * u))) ((u : ℂ) * cexp (-r * u)) u := by
    intro u _
    have h1 : HasDerivAt (fun z : ℂ => z / r + 1 / r ^ 2) (1 / r) (u : ℂ) :=
      ((hasDerivAt_id (u : ℂ)).div_const r).add_const _
    have h2 : HasDerivAt (fun z : ℂ => cexp (-r * z)) (cexp (-r * u) * (-r * 1)) (u : ℂ) :=
      ((hasDerivAt_id (u : ℂ)).const_mul (-r)).cexp
    have h3 := (h1.mul h2).neg
    have h4 : HasDerivAt (fun z : ℂ => -((z / r + 1 / r ^ 2) * cexp (-r * z)))
        ((u : ℂ) * cexp (-r * u)) (u : ℂ) := by
      refine h3.congr_deriv ?_
      field_simp
      ring
    exact h4.comp_ofReal
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [this]
  simp

lemma integral_exp_mul_id_laplace' {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u) = 1 / (s - 1) ^ 2 := by
  have hr : 0 < (s - 1).re := by simp; linarith
  have : (fun u : ℝ => ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)) =
      fun u : ℝ => (u : ℂ) * cexp (-(s - 1) * u) := by
    funext u
    calc ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)
        = (u : ℂ) * (cexp u * cexp (-s * u)) := by push_cast; ring
      _ = (u : ℂ) * cexp (-(s - 1) * u) := by
          rw [← Complex.exp_add]; congr 2; ring
  rw [this]
  exact integral_id_mul_cexp' hr

lemma integral_exp_neg_laplace {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * cexp (-s * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ((Real.exp (-u) : ℝ) : ℂ) * cexp (-s * u) = 1 / (s + 1) := by
  have hre : (-1 - s).re < 0 := by simp; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hs1' : -1 - s ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have : (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * cexp (-s * u)) =
      fun u : ℝ => cexp ((-1 - s) * u) := by
    funext u; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]
  refine ⟨integrableOn_exp_mul_complex_Ioi hre 0, ?_⟩
  rw [integral_exp_mul_complex_Ioi hre]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- The Laplace transform of `rampH` on `re s > 1`, with absolute convergence. -/
theorem laplace_rampH {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((rampH u : ℝ) : ℂ) * cexp (-s * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ((rampH u : ℝ) : ℂ) * cexp (-s * u) = psi s := by
  have h1 : s ≠ 1 := by rintro rfl; simp at hs
  have h0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hA := integrableOn_rampS_laplace' hs
  obtain ⟨hB, hBv⟩ := integral_exp_mul_id_laplace' hs
  have hC := integrableOn_exp_laplace hs
  obtain ⟨hD, hDv⟩ := integral_exp_neg_laplace hs
  have hpt : (fun u : ℝ => ((rampH u : ℝ) : ℂ) * cexp (-s * u)) = fun u : ℝ =>
      ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)
        - ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)
        + (1 + (Real.eulerMascheroniConstant : ℂ)) *
          (((Real.exp u : ℝ) : ℂ) * cexp (-s * u))
        - (1 + (Real.eulerMascheroniConstant : ℂ)) *
          (((Real.exp (-u) : ℝ) : ℂ) * cexp (-s * u)) := by
    funext u
    rw [rampH, rampG_eq, Real.log_exp]
    push_cast
    ring
  have hAB := Integrable.sub hA hB
  have hABC := Integrable.add hAB (Integrable.const_mul hC (1 + (Real.eulerMascheroniConstant : ℂ)))
  have hD' := Integrable.const_mul hD (1 + (Real.eulerMascheroniConstant : ℂ))
  rw [hpt]
  refine ⟨Integrable.sub hABC hD', ?_⟩
  have e0 := integral_sub hABC hD'
  have e1 := integral_add hAB (Integrable.const_mul hC (1 + (Real.eulerMascheroniConstant : ℂ)))
  have e2 := integral_sub hA hB
  simp only [Pi.sub_apply, Pi.add_apply] at e0 e1 e2
  rw [e0, e1, e2, integral_const_mul, integral_const_mul, integral_rampS_laplace hs, hBv,
    integral_exp_laplace hs, hDv,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, psi, zetaPhi_eq h1 h0 hζ]
  ring

end ZetaRamp
