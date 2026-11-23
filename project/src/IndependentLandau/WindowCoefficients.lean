import IndependentLandau.Defs
import IndependentLandau.Kernel
import IndependentLandau.Series

/-! Taylor expansion of the Laplace transform in terms of the moments `Bc`, and
first consequences for `PoleData`: no pole has real part `> 2`. -/

open Complex MeasureTheory Set Filter Topology
open scoped Nat

noncomputable section

namespace IndependentLandau

/-- Step A: for `re p > 2` and `‖w‖ < re p - 2`, `Φ (p - w) = ∑ Bc g k p * w ^ k`. -/
theorem laplace_hasSum {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {p : ℂ} {w : ℂ} (hw : ‖w‖ < p.re - 2) :
    HasSum (fun k => Bc g k p * w ^ k) (Φ (p - w)) := by
  have hre : 2 < (p - w).re := by
    have := Complex.re_le_norm w
    rw [Complex.sub_re]; linarith
  rw [hP.laplace _ hre]
  obtain ⟨C, hgC⟩ := hP.growth
  set r : ℝ := ‖w‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg w
  have hb : 0 < p.re - 2 - r := by linarith
  have key := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (n : ℕ) (u : ℝ) => (g u : ℂ) * cexp (-p * u) * ((w * u) ^ n / (n ! : ℂ)))
    (f := fun u : ℝ => (g u : ℂ) * cexp (-(p - w) * u))
    (fun (n : ℕ) (u : ℝ) => C * Real.exp (-((p.re - 2) * u)) * ((r * u) ^ n / (n ! : ℝ)))
    ?_ ?_ ?_ ?_ ?_
  · have hfun : (fun k => Bc g k p * w ^ k) = fun n : ℕ =>
        ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-p * u) * ((w * u) ^ n / (n ! : ℂ)) := by
      funext n
      unfold Bc
      rw [← integral_mul_const]
      congr 1
      funext u
      rw [mul_pow]
      ring
    rw [hfun]
    exact key
  · intro n
    have hgm : Measurable fun u : ℝ => (g u : ℂ) := Complex.measurable_ofReal.comp hP.meas
    have h2 : Measurable fun u : ℝ => cexp (-p * u) := by fun_prop
    have h3 : Measurable fun u : ℝ => ((w * u) ^ n / (n ! : ℂ)) := by fun_prop
    have hm : Measurable fun u : ℝ =>
        (g u : ℂ) * cexp (-p * u) * ((w * u) ^ n / (n ! : ℂ)) := (hgm.mul h2).mul h3
    exact hm.aestronglyMeasurable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have e1 : ‖cexp (-p * u)‖ = Real.exp (-(p.re * u)) := by
      rw [Complex.norm_exp]; congr 1; simp
    have e2 : ‖((w * u) ^ n / (n ! : ℂ))‖ = (r * u) ^ n / (n ! : ℝ) := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_natCast,
        Real.norm_of_nonneg hu0.le]
    rw [norm_mul, norm_mul, Complex.norm_real, e1, e2, Real.norm_eq_abs]
    have h1 := hgC u hu0.le
    have h2 : Real.exp (2 * u) * Real.exp (-(p.re * u)) = Real.exp (-((p.re - 2) * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : 0 ≤ (r * u) ^ n / (n ! : ℝ) := by positivity
    calc |g u| * Real.exp (-(p.re * u)) * ((r * u) ^ n / (n ! : ℝ))
        ≤ (C * Real.exp (2 * u)) * Real.exp (-(p.re * u)) * ((r * u) ^ n / (n ! : ℝ)) := by
          gcongr
      _ = C * Real.exp (-((p.re - 2) * u)) * ((r * u) ^ n / (n ! : ℝ)) := by
          rw [mul_assoc C, h2]
  · exact Eventually.of_forall fun u => (Real.summable_pow_div_factorial (r * u)).mul_left _
  · have hfun : (fun u : ℝ => ∑' n : ℕ,
        C * Real.exp (-((p.re - 2) * u)) * ((r * u) ^ n / (n ! : ℝ))) =
        fun u => C * Real.exp (-(p.re - 2 - r) * u) := by
      funext u
      rw [tsum_mul_left]
      have h := (NormedSpace.expSeries_div_hasSum_exp (r * u)).tsum_eq
      rw [← Real.exp_eq_exp_ℝ] at h
      rw [h, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [hfun]
    have := (exp_neg_integrableOn_Ioi 0 hb).const_mul C
    simpa using this
  · refine Eventually.of_forall fun u => ?_
    have h := (NormedSpace.expSeries_div_hasSum_exp (w * (u : ℂ))).mul_left
      ((g u : ℂ) * cexp (-p * u))
    rw [← Complex.exp_eq_exp_ℂ] at h
    have e : (g u : ℂ) * cexp (-p * u) * cexp (w * u) = (g u : ℂ) * cexp (-(p - w) * u) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    rw [e] at h
    exact h

/-- `Φ` is complex differentiable at every point of the right half plane off `Z`. -/
theorem PoleData.differentiableAt {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {s : ℂ} (hs : 0 < s.re) (hsZ : s ∉ Z) : DifferentiableAt ℂ Φ s := by
  refine hP.diff.differentiableAt ?_
  have h1 : ∀ᶠ w in 𝓝 s, 0 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have h2 : ∀ᶠ w in 𝓝 s, w ∈ ({s}ᶜ : Set ℂ) → w ∉ Z :=
    eventually_nhdsWithin_iff.1 (hP.iso s hs)
  filter_upwards [h1, h2] with w hw1 hw2
  refine ⟨hw1, ?_⟩
  by_cases hws : w = s
  · rw [hws]; exact hsZ
  · exact hw2 hws

/-- `Φ` is continuous at every point with real part `> 2` (even at points of `Z`). -/
theorem PoleData.continuousAt_of_two_lt {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : PoleData g Φ Z) {ρ : ℂ} (hρ : 2 < ρ.re) : ContinuousAt Φ ρ := by
  have hr : 0 < ρ.re - 2 := by linarith
  have hps := hasFPowerSeriesAt_zero_of_hasSum (F := fun w => Φ (ρ - w)) hr
    fun w hw => laplace_hasSum hP hw
  have hc0 : ContinuousAt (fun w => Φ (ρ - w)) 0 := hps.continuousAt
  have hc0' : ContinuousAt (fun w => Φ (ρ - w)) (ρ - ρ) := by rw [sub_self]; exact hc0
  have hcomp : ContinuousAt (fun s : ℂ => (fun w => Φ (ρ - w)) (ρ - s)) ρ :=
    ContinuousAt.comp (f := fun s : ℂ => ρ - s) hc0' (by fun_prop)
  simpa using hcomp

/-- No pole has real part exceeding `2`. -/
theorem PoleData.re_le_two {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {ρ : ℂ} (hρ : ρ ∈ Z) : ρ.re ≤ 2 := by
  by_contra hcon
  have h2 : 2 < ρ.re := not_le.1 hcon
  have hc := hP.continuousAt_of_two_lt h2
  obtain ⟨c, hc0, -, h, hh, heq⟩ := hP.pole ρ hρ
  have T0 : Tendsto (fun s => (s - ρ) * (Φ s - h s)) (𝓝 ρ) (𝓝 ((ρ - ρ) * (Φ ρ - h ρ))) :=
    ((continuousAt_id.sub continuousAt_const).mul (hc.sub hh.continuousAt)).tendsto
  rw [sub_self, zero_mul] at T0
  have T : Tendsto (fun s => (s - ρ) * (Φ s - h s)) (𝓝[≠] ρ) (𝓝 0) :=
    T0.mono_left nhdsWithin_le_nhds
  have E : (fun s => (s - ρ) * (Φ s - h s)) =ᶠ[𝓝[≠] ρ] fun _ => c := by
    filter_upwards [heq, self_mem_nhdsWithin] with s hs hne
    have hne' : s - ρ ≠ 0 := sub_ne_zero.2 hne
    rw [hs]
    field_simp
    ring
  have := tendsto_nhds_unique (T.congr' E) tendsto_const_nhds
  exact hc0 this.symm

end IndependentLandau
