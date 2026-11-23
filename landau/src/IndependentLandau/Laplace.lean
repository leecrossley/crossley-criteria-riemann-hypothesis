import Mathlib
import IndependentLandau.Ramp

/-! The Laplace transform of `u ↦ rampG (exp u)` on `re s > 2`, computed term by term. -/

open scoped ArithmeticFunction.vonMangoldt
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace IndependentLandau

/-- The Laplace integrand of a single ramp term. -/
def lapT (s : ℂ) (n : ℕ) (u : ℝ) : ℂ := ((rampT n (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)

lemma lapT_zero (s : ℂ) (u : ℝ) : lapT s 0 u = 0 := by simp [lapT, rampT_zero]

/-- The smooth function whose truncation to `(log n, ∞)` is the term integrand. -/
def lapG (s : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  (Λ n : ℂ) * (cexp ((1 - s) * u) / n - cexp (-s * u))

lemma lapT_eq_indicator (s : ℂ) {n : ℕ} (hn : 0 < n) :
    lapT s n = (Ioi (Real.log n)).indicator (lapG s n) := by
  funext u
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hu : u ∈ Ioi (Real.log n)
  · rw [indicator_of_mem hu]
    have h1 : (n : ℝ) < Real.exp u := (Real.log_lt_iff_lt_exp hn').mp hu
    have h2 : 0 ≤ Real.exp u / n - 1 := by
      rw [sub_nonneg, one_le_div hn']; exact h1.le
    have h3 : cexp ((1 - s) * u) = cexp u * cexp (-s * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    simp only [lapT, lapG, rampT, max_eq_left h2, h3]
    push_cast
    ring
  · rw [indicator_of_notMem hu]
    have h1 : Real.exp u ≤ n := by
      have : u ≤ Real.log n := not_lt.mp hu
      exact (Real.le_log_iff_exp_le hn').mp this
    have h2 : Real.exp u / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn']; exact h1
    simp [lapT, rampT, max_eq_right h2]

lemma integrableOn_lapG {s : ℂ} (hs : 1 < s.re) (n : ℕ) (a : ℝ) :
    IntegrableOn (lapG s n) (Ioi a) := by
  have h1 : IntegrableOn (fun u : ℝ => cexp ((1 - s) * u)) (Ioi a) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) a
  have h2 : IntegrableOn (fun u : ℝ => cexp (-s * u)) (Ioi a) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) a
  exact Integrable.const_mul (Integrable.sub (Integrable.div_const h1 _) h2) _

lemma integral_lapG {s : ℂ} (hs : 1 < s.re) {n : ℕ} (hn : 0 < n) :
    ∫ u in Ioi (Real.log n), lapG s n u = (Λ n : ℂ) / (n : ℂ) ^ s / (s * (s - 1)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hre1 : (1 - s).re < 0 := by simp; linarith
  have hre2 : (-s).re < 0 := by simp; linarith
  have h1 := integrableOn_exp_mul_complex_Ioi hre1 (Real.log n)
  have h2 := integrableOn_exp_mul_complex_Ioi hre2 (Real.log n)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hs1' : 1 - s ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hq : cexp (-s * (Real.log n : ℝ)) = ((n : ℂ) ^ s)⁻¹ := by
    rw [← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hnc, Complex.natCast_log]
    congr 1; ring
  have hq' : cexp ((1 - s) * (Real.log n : ℝ)) = n * ((n : ℂ) ^ s)⁻¹ := by
    have : cexp ((1 - s) * (Real.log n : ℝ)) =
        cexp (Real.log n : ℝ) * cexp (-s * (Real.log n : ℝ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this, hq, ← Complex.ofReal_exp, Real.exp_log hn']; simp
  unfold lapG
  rw [integral_const_mul, integral_sub (Integrable.div_const h1 _) h2, integral_div,
    integral_exp_mul_complex_Ioi hre1, integral_exp_mul_complex_Ioi hre2, hq, hq',
    div_eq_mul_inv (Λ n : ℂ)]
  generalize ((n : ℂ) ^ s)⁻¹ = q
  field_simp
  ring

lemma integral_lapT {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ∫ u in Ioi (0 : ℝ), lapT s n u =
      LSeries.term (fun n => (Λ n : ℂ)) s n / (s * (s - 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lapT_zero]
  · rw [lapT_eq_indicator s hn, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
      sup_eq_right.mpr (Real.log_natCast_nonneg n), integral_lapG hs hn,
      LSeries.term_of_ne_zero hn.ne']

lemma integrable_lapT {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    Integrable (lapT s n) (volume.restrict (Ioi (0 : ℝ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : lapT s 0 = fun _ => 0 := funext (lapT_zero s)
    rw [this]; exact integrable_zero _ _ _
  · rw [lapT_eq_indicator s hn]
    exact ((integrableOn_lapG hs n _).integrable_indicator measurableSet_Ioi).restrict

lemma norm_lapT (s : ℂ) (n : ℕ) (u : ℝ) :
    ‖lapT s n u‖ = rampT n (Real.exp u) * Real.exp (-s.re * u) := by
  simp [lapT, Complex.norm_exp, abs_of_nonneg (rampT_nonneg n _)]

lemma summable_integral_norm_lapT {s : ℂ} (hs : 1 < s.re) :
    Summable fun n => ∫ u in Ioi (0 : ℝ), ‖lapT s n u‖ := by
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have hsum : Summable (fun n => LSeries.term (fun n => (Λ n : ℂ)) (s.re : ℂ) n /
      ((s.re : ℂ) * ((s.re : ℂ) - 1))) :=
    Summable.div_const (ArithmeticFunction.LSeriesSummable_vonMangoldt hσ) _
  have key : ∀ n, ∫ u in Ioi (0 : ℝ), ‖lapT s n u‖ =
      (LSeries.term (fun n => (Λ n : ℂ)) (s.re : ℂ) n /
        ((s.re : ℂ) * ((s.re : ℂ) - 1))).re := by
    intro n
    rw [← integral_lapT hσ n]
    have : ∀ u : ℝ, lapT (s.re : ℂ) n u = ((‖lapT s n u‖ : ℝ) : ℂ) := by
      intro u; rw [norm_lapT]; simp [lapT]
    simp_rw [this]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  simp_rw [key]
  exact (Complex.hasSum_re hsum.hasSum).summable

/-- The Laplace transform of the sum part is the von Mangoldt L-series over `s (s - 1)`. -/
lemma integral_rampS_laplace {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)
      = LSeries (fun n => (Λ n : ℂ)) s / (s * (s - 1)) := by
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := lapT s) (integrable_lapT hs) (summable_integral_norm_lapT hs)
  have h2 : ∀ u : ℝ, ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u) = ∑' n, lapT s n u := by
    intro u
    rw [rampS_eq_tsum, Complex.ofReal_tsum, ← tsum_mul_right]; rfl
  simp_rw [h2]
  rw [← h.tsum_eq]
  simp_rw [integral_lapT hs]
  rw [tsum_div_const]; rfl

lemma integral_exp_laplace {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((Real.exp u : ℝ) : ℂ) * cexp (-s * u) = 1 / (s - 1) := by
  have hre : (1 - s).re < 0 := by simp; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hs1' : 1 - s ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have : ∀ u : ℝ, ((Real.exp u : ℝ) : ℂ) * cexp (-s * u) = cexp ((1 - s) * u) := by
    intro u; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; ring
  simp_rw [this]
  rw [integral_exp_mul_complex_Ioi hre]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

lemma integrableOn_exp_laplace {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((Real.exp u : ℝ) : ℂ) * cexp (-s * u)) (Ioi 0) := by
  have hre : (1 - s).re < 0 := by simp; linarith
  have : (fun u : ℝ => ((Real.exp u : ℝ) : ℂ) * cexp (-s * u)) =
      fun u : ℝ => cexp ((1 - s) * u) := by
    funext u; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; ring
  rw [this]
  exact integrableOn_exp_mul_complex_Ioi hre 0

/-- `∫₀^∞ u e^{-ru} du = 1 / r²`, with integrability, for `re r > 1`. -/
lemma integral_id_mul_cexp {r : ℂ} (hr : 1 < r.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * cexp (-r * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (u : ℂ) * cexp (-r * u) = 1 / r ^ 2 := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; linarith
  have hnorm : ∀ u : ℝ, ‖cexp (-r * u)‖ = Real.exp (-r.re * u) := by
    intro u; simp [Complex.norm_exp]
  have hle : ∀ u : ℝ, 0 ≤ u → Real.exp (-r.re * u) ≤ Real.exp (-u) := by
    intro u hu; apply Real.exp_le_exp.mpr; nlinarith
  -- integrability
  have hint : IntegrableOn (fun u : ℝ => (u : ℂ) * cexp (-r * u)) (Ioi 0) := by
    have hb : IntegrableOn (fun u : ℝ => Real.exp ((1 - r.re) * u)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine Integrable.mono' hb (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_mul, hnorm, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h2 : Real.exp ((1 - r.re) * u) = Real.exp u * Real.exp (-r.re * u) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  refine ⟨hint, ?_⟩
  -- limits at infinity
  have hg2 : Tendsto (fun u : ℝ => cexp (-r * u)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun u : ℝ => u ^ 0 * Real.exp (-u)) ?_
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [hnorm, pow_zero, one_mul]
    exact hle u hu
  have hg1 : Tendsto (fun u : ℝ => (u : ℂ) * cexp (-r * u)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun u : ℝ => u ^ 1 * Real.exp (-u)) ?_
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [norm_mul, hnorm, Complex.norm_real, Real.norm_of_nonneg hu, pow_one]
    exact mul_le_mul_of_nonneg_left (hle u hu) hu
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

lemma integral_exp_mul_id_laplace {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u) = 1 / (s - 1) ^ 2 := by
  have hr : 1 < (s - 1).re := by simp; linarith
  have : (fun u : ℝ => ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)) =
      fun u : ℝ => (u : ℂ) * cexp (-(s - 1) * u) := by
    funext u
    calc ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)
        = (u : ℂ) * (cexp u * cexp (-s * u)) := by push_cast; ring
      _ = (u : ℂ) * cexp (-(s - 1) * u) := by
          rw [← Complex.exp_add]; congr 2; ring
  rw [this]
  exact integral_id_mul_cexp hr

lemma integrableOn_rampS_laplace {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)) (Ioi 0) := by
  have hb : IntegrableOn (fun u : ℝ => 2 * Real.exp ((2 - s.re) * u)) (Ioi 0) :=
    Integrable.const_mul (integrableOn_exp_mul_Ioi (by linarith) 0) 2
  have hm : Measurable (fun u : ℝ => ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)) :=
    (Complex.measurable_ofReal.comp (measurable_rampS.comp Real.measurable_exp)).mul
      (Continuous.measurable (by fun_prop))
  refine Integrable.mono' hb hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := hu
  have hy1 : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
  have hS0 := rampS_nonneg (Real.exp u)
  have hS := rampS_le (y := Real.exp u) (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hS0, Complex.norm_exp]
  have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
  have h2 : Real.exp ((2 - s.re) * u) = Real.exp u * Real.exp u * Real.exp (-s.re * u) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hre, h2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  nlinarith

/-- The Laplace transform of the centred ramp on `re s > 2`. -/
theorem laplace_rampG {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((rampG (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)
      = LSeries (fun n => (Λ n : ℂ)) s / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + (Real.eulerMascheroniConstant : ℂ)) / (s - 1) := by
  have hs1 : 1 < s.re := by linarith
  have hA := integrableOn_rampS_laplace hs
  obtain ⟨hB, hBv⟩ := integral_exp_mul_id_laplace hs
  have hC := integrableOn_exp_laplace hs1
  have hpt : ∀ u : ℝ, ((rampG (Real.exp u) : ℝ) : ℂ) * cexp (-s * u) =
      ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)
        - ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)
        + (1 + (Real.eulerMascheroniConstant : ℂ)) *
          (((Real.exp u : ℝ) : ℂ) * cexp (-s * u)) := by
    intro u
    rw [rampG_eq, Real.log_exp]
    push_cast
    ring
  simp_rw [hpt]
  have e1 : ∫ u in Ioi (0 : ℝ), (((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)
        - ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)
        + (1 + (Real.eulerMascheroniConstant : ℂ)) *
          (((Real.exp u : ℝ) : ℂ) * cexp (-s * u)))
      = (∫ u in Ioi (0 : ℝ), (((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)
        - ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)))
        + ∫ u in Ioi (0 : ℝ), (1 + (Real.eulerMascheroniConstant : ℂ)) *
          (((Real.exp u : ℝ) : ℂ) * cexp (-s * u)) :=
    integral_add (Integrable.sub hA hB) (Integrable.const_mul hC _)
  have e2 : (∫ u in Ioi (0 : ℝ), (((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u)
        - ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u)))
      = (∫ u in Ioi (0 : ℝ), ((rampS (Real.exp u) : ℝ) : ℂ) * cexp (-s * u))
        - ∫ u in Ioi (0 : ℝ), ((Real.exp u * u : ℝ) : ℂ) * cexp (-s * u) :=
    integral_sub hA hB
  rw [e1, e2, integral_const_mul, integral_rampS_laplace hs1, hBv,
    integral_exp_laplace hs1]
  ring

end IndependentLandau
