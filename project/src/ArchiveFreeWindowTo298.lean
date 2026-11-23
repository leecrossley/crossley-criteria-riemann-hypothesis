import RampWindowEquivalence
import ZeroFreeShellMoment
import Crossley.RealZeros
import IndependentLandau.Zeta
import IndependentLandau.WindowLemma

/-!
# Archive-Free Transfer from `OrdinaryWindowUnit θ` to the `2.98` Shell Moment & Stencil Persistence

1. **Archive-Free `2.98` (`149/50`) Shell Moment Transfer (`archiveFree_moment_of_ordinaryWindow`
   & `archiveFree_moment_of_window_087`):**
   Connects `OrdinaryWindowUnit θ` (for any `1 / 2 ≤ θ < 349 / 400`, and specifically `θ = 87 / 100`)
   directly to `ZeroFreeShellMoment.full_shell_moment_of_zero_free` using only Mathlib and
   first-party Mathlib-only modules (`IndependentLandau`, `ZeroFreeToMertens`,
   `ZeroFreeMertensBridge`, `ZeroFreeShellCriterion`, `ZeroFreeShellMoment`), completely eliminating
   all external archive and `GaloisForLFunctions` imports.

2. **Dirichlet-Stencil Pole-Persistence (`dirichlet_stencil_nonvanishing_large_re`,
   `stenciled_poleData_of_nonzero_multiplier`, & `stenciled_zero_re_le_of_window`):**
   Proves that for any finite real stencil `c : ℕ → ℝ` supported on `1 ≤ m ≤ M`:
   - If `c 1 ≠ 0`, `∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ)^(-s) → c 1 ≠ 0` as `s.re → ∞`.
   - The stenciled ramp `G_c(u) := ∑ m ∈ Finset.Icc 1 M, c m * rampG (exp (u - log m))` satisfies
     `IndependentLandau.PoleData` on `{ρ ∈ zetaZeros | ∑ m ∈ Icc 1 M, (c m : ℂ) * m^(-ρ) ≠ 0}`.
   - Consequently, if `WindowHypU G_c θ δ` holds (`0 < θ < 1`, `0 < δ`), every `ρ ∈ zetaZeros` at
     which the finite Dirichlet multiplier does not vanish must satisfy `ρ.re ≤ θ`.
-/

open Complex MeasureTheory Set Filter Topology Metric Finset
open RiemannReduction.ShortTail.LossFrequency

noncomputable section

namespace DirectRampEquivalence

/-! ### 1. Archive-Free Transfer to the `2.98` (`149 / 50`) Shell Benchmark -/

/-- **General Window-to-Shell-Moment Transfer:**
Any one-sided window bound `OrdinaryWindow θ δ₀` (`1 / 2 ≤ θ < 1`, `0 < δ₀`) implies the block
moment bound `weighted uniformShellScore m ≤ m^δ` for every `δ > 8 * θ - 4`. -/
theorem archiveFree_moment_of_ordinaryWindow_general {θ δ₀ δ : ℝ}
    (hθ_lo : 1 / 2 ≤ θ) (hθ_hi : θ < 1) (hδ₀ : 0 < δ₀) (hgap : 8 * θ - 4 < δ)
    (hW : OrdinaryWindow θ δ₀) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ δ :=
  full_shell_moment_of_zero_free hθ_lo hθ_hi.le
    (zeta_zeroFree_of_ordinaryWindow (by linarith) hθ_hi hδ₀ hW) hgap

/-- **Archive-Free `2.98` (`149 / 50`) Transfer (`archiveFree_moment_of_ordinaryWindow`):**
For any `θ ∈ [1/2, 349/400)` (`349/400 = 0.8725`), `OrdinaryWindowUnit θ` implies
`∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ)`. -/
theorem archiveFree_moment_of_ordinaryWindow {θ : ℝ}
    (hθ_lo : 1 / 2 ≤ θ) (hθ_hi : θ < 349 / 400) (hW : OrdinaryWindowUnit θ) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ) :=
  full_shell_moment_of_zero_free hθ_lo (by linarith)
    (zeta_zeroFree_of_ordinaryWindowUnit (by linarith) (by linarith) hW) (by linarith)

/-- **Archive-Free `2.98` Benchmark at `θ = 0.87` (`archiveFree_moment_of_window_087`):**
`OrdinaryWindowUnit (87 / 100)` directly implies the `149 / 50 = 2.98` weighted uniform shell
first-moment bound with zero external archive imports. -/
theorem archiveFree_moment_of_window_087 (hW : OrdinaryWindowUnit (87 / 100)) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ) ^ (149 / 50 : ℝ) :=
  archiveFree_moment_of_ordinaryWindow (by norm_num) (by norm_num) hW

/-! ### 2. Finite Dirichlet-Stencil Nonvanishing & Pole-Persistence -/

/-- Finite Dirichlet polynomial `P_c(s) = ∑_{1 ≤ m ≤ M} c_m m^{-s}`. -/
def dirichletStencilPoly (c : ℕ → ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-s)

/-- Stenciled ramp `G_c(u) = ∑_{1 ≤ m ≤ M} c_m rampG(exp(u - log m))`. -/
def stenciledRampU (c : ℕ → ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, c m * IndependentLandau.rampG (Real.exp (u - Real.log m))

private lemma natCast_cpow_neg_eq_cexp {m : ℕ} (hm : 1 ≤ m) (s : ℂ) :
    (m : ℂ) ^ (-s) = cexp (-s * (Real.log m : ℂ)) := by
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hmc, Complex.natCast_log]
  congr 1; ring

/-- **Dirichlet-Stencil Asymptotic Limit & Large-`Re` Nonvanishing
(`dirichlet_stencil_nonvanishing_large_re`):**
For any finite stencil `c : ℕ → ℝ` on `1 ≤ m ≤ M` (`M ≥ 1`) with `c 1 ≠ 0`,
`∑_{1 ≤ m ≤ M} c_m m^{-s} → c 1` as `s.re → ∞`, and in particular the finite Dirichlet polynomial
is nonzero on an entire right half-plane `s.re ≥ σ₀`. -/
theorem dirichlet_stencil_nonvanishing_large_re (c : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M)
    (hc1 : c 1 ≠ 0) :
    Tendsto (fun s : ℂ => ∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-s))
      (Filter.comap Complex.re atTop) (𝓝 (c 1 : ℂ)) ∧
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ ≤ s.re →
      (∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-s)) ≠ 0 := by
  have hsplit : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 M := by simp
  let S_tail : ℝ := ∑ m ∈ Finset.Icc 2 M, |c m|
  have hS_nonneg : 0 ≤ S_tail := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdiff_bd : ∀ s : ℂ, 0 ≤ s.re →
      ‖(∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-s)) - (c 1 : ℂ)‖ ≤
        S_tail * (2 : ℝ) ^ (-s.re) := by
    intro s hs0
    rw [hsplit, Finset.sum_insert hnotmem]
    have h1 : (c 1 : ℂ) * ((1 : ℕ) : ℂ) ^ (-s) = (c 1 : ℂ) := by simp
    rw [h1, add_sub_cancel_left]
    calc ‖∑ m ∈ Finset.Icc 2 M, (c m : ℂ) * (m : ℂ) ^ (-s)‖
        ≤ ∑ m ∈ Finset.Icc 2 M, ‖(c m : ℂ) * (m : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 2 M, |c m| * (2 : ℝ) ^ (-s.re) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm_pos : 0 < m := by omega
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast_cpow_of_pos hm_pos]
          simp only [neg_re]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hm2) (by linarith))
            (abs_nonneg _)
      _ = S_tail * (2 : ℝ) ^ (-s.re) := by rw [← Finset.sum_mul]
  have htend_real : Tendsto (fun σ : ℝ => S_tail * (2 : ℝ) ^ (-σ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (-σ)) atTop (𝓝 0) := by
      have heq : (fun σ : ℝ => (2 : ℝ) ^ (-σ)) = fun σ : ℝ => Real.exp (-(Real.log 2 * σ)) := by
        funext σ
        rw [Real.rpow_def_of_pos (by norm_num)]
        congr 1; ring
      rw [heq]
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (Real.log_pos (by norm_num)))
    simpa using h2.const_mul S_tail
  have htend_zero : Tendsto
      (fun s : ℂ => (∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-s)) - (c 1 : ℂ))
      (Filter.comap Complex.re atTop) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero_norm' ?_ (htend_real.comp tendsto_comap)
    refine Filter.eventually_comap.mpr ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with σ hσ s hs_eq
    subst hs_eq
    dsimp only [Function.comp_apply]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdiff_bd s hσ
  have htend_c1 : Tendsto (fun s : ℂ => ∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-s))
      (Filter.comap Complex.re atTop) (𝓝 (c 1 : ℂ)) := by
    have h := htend_zero.add (tendsto_const_nhds (x := (c 1 : ℂ)))
    simpa only [zero_add, sub_add_cancel] using h
  refine ⟨htend_c1, ?_⟩
  have hne_ev : ∀ᶠ s : ℂ in Filter.comap Complex.re atTop,
      (∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-s)) ≠ 0 :=
    htend_c1.eventually_ne (Complex.ofReal_ne_zero.mpr hc1)
  rw [Filter.Eventually, Filter.mem_comap] at hne_ev
  obtain ⟨S, hS_atTop, hS_sub⟩ := hne_ev
  obtain ⟨σ₀, hσ₀⟩ := Filter.mem_atTop_sets.mp hS_atTop
  exact ⟨σ₀, fun s hs => hS_sub (hσ₀ s.re hs)⟩

/-- `riemannZeta` has no real zeros in `(0, ∞)`, so every `ρ ∈ zetaZeros` has `ρ.im ≠ 0`. -/
private lemma zetaZeros_im_ne_zero {ρ : ℂ} (hρ : ρ ∈ IndependentLandau.zetaZeros) : ρ.im ≠ 0 := by
  intro him
  have hρ_eq : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
  have hre : 0 < ρ.re := hρ.1
  have hz : riemannZeta (ρ.re : ℂ) = 0 := by rw [← hρ_eq]; exact hρ.2
  rcases lt_or_ge ρ.re 1 with hlt | hge
  · exact Crossley.riemannZeta_ne_zero_of_mem_Ioo hre hlt hz
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hge) hz

/-- Uniform bound `|rampG (exp v)| ≤ 5` for `v ≤ 0` and `|rampG (exp (u - log m))| ≤ 5 * exp (2 * u)`
for all `u ≥ 0` and `m ≥ 1`. -/
private lemma abs_rampG_exp_le_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    |IndependentLandau.rampG (Real.exp v)| ≤ 5 := by
  rcases eq_or_lt_of_le hv with rfl | hv_neg
  · simpa using IndependentLandau.abs_rampG_exp_le le_rfl
  · set y : ℝ := Real.exp v
    have hy0 : 0 < y := Real.exp_pos v
    have hy1 : y < 1 := Real.exp_lt_one_iff.mpr hv_neg
    have hfl : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy1
    have hS0 : IndependentLandau.rampS y = 0 := by
      simp [IndependentLandau.rampS, hfl, IndependentLandau.rampT_zero]
    have hlog_neg : 0 ≤ -y * Real.log y := by
      have : Real.log y ≤ 0 := Real.log_nonpos hy0.le hy1.le
      nlinarith
    have hlog_up : -y * Real.log y ≤ 1 := by
      have hinv_pos : 0 < 1 / y := one_div_pos.mpr hy0
      have h1 := Real.log_le_sub_one_of_pos hinv_pos
      rw [one_div, Real.log_inv] at h1
      have hmul := mul_le_mul_of_nonneg_left h1 hy0.le
      have hy_inv : y * (y⁻¹ - 1) = 1 - y := by field_simp [hy0.ne']
      linarith
    have hγ0 := Real.one_half_lt_eulerMascheroniConstant
    have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
    have hlin_nonneg : 0 ≤ (1 + Real.eulerMascheroniConstant) * y := by positivity
    have hlin_up : (1 + Real.eulerMascheroniConstant) * y ≤ 2 := by nlinarith
    have hG : IndependentLandau.rampG y =
        -y * Real.log y + (1 + Real.eulerMascheroniConstant) * y := by
      rw [IndependentLandau.rampG_eq, hS0]; ring
    dsimp [y] at hG ⊢
    rw [hG, abs_le]
    constructor <;> linarith

private lemma abs_rampG_shifted_le {m : ℕ} (_hm : 1 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    |IndependentLandau.rampG (Real.exp (u - Real.log m))| ≤ 5 * Real.exp (2 * u) := by
  have hLm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  rcases le_or_gt 0 (u - Real.log m) with hv | hv
  · refine (IndependentLandau.abs_rampG_exp_le hv).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  · have h5 := abs_rampG_exp_le_of_nonpos hv.le
    have h1 : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
    linarith

/-- Finite-interval Laplace correction `E_m(s) = ∫_{u ∈ (0, log m]} rampG(exp(u - log m)) e^{-su} du`. -/
private def stencilFinError (m : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Ioc (0 : ℝ) (Real.log m),
    ((IndependentLandau.rampG (Real.exp (u - Real.log m)) : ℝ) : ℂ) * cexp (-s * u)

private lemma differentiable_stencilFinError {m : ℕ} (_hm : 1 ≤ m) :
    Differentiable ℂ (stencilFinError m) := by
  intro s₀
  set L : ℝ := Real.log m
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg m
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) L)
  let F : ℂ → ℝ → ℂ := fun s u =>
    ((IndependentLandau.rampG (Real.exp (u - L)) : ℝ) : ℂ) * cexp (-s * u)
  let F' : ℂ → ℝ → ℂ := fun s u =>
    ((IndependentLandau.rampG (Real.exp (u - L)) : ℝ) : ℂ) * (-(u : ℂ) * cexp (-s * u))
  let B_dom : ℝ := 5 * L * Real.exp ((|s₀.re| + 1) * L)
  have hmeas_F : ∀ s : ℂ, Measurable (F s) := fun s =>
    (Complex.measurable_ofReal.comp
      (IndependentLandau.measurable_rampG.comp
        (Real.measurable_exp.comp (measurable_id.sub_const L)))).mul
      (Continuous.measurable (by fun_prop))
  have hmeas_F' : ∀ s : ℂ, Measurable (F' s) := fun s =>
    (Complex.measurable_ofReal.comp
      (IndependentLandau.measurable_rampG.comp
        (Real.measurable_exp.comp (measurable_id.sub_const L)))).mul
      (Continuous.measurable (by fun_prop))
  have hint_s₀ : Integrable (F s₀) μ := by
    have hconst : Integrable (fun _ : ℝ => 5 * Real.exp ((|s₀.re| + 1) * L)) μ :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    refine hconst.mono' (hmeas_F s₀).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have huL : u - L ≤ 0 := by linarith [hu.2]
    have hG := abs_rampG_exp_le_of_nonpos huL
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-s₀ * (u : ℂ)).re = -s₀.re * u := by simp
    rw [hre]
    have hexp : Real.exp (-s₀.re * u) ≤ Real.exp ((|s₀.re| + 1) * L) := by
      apply Real.exp_le_exp.mpr
      have h1 : -s₀.re ≤ |s₀.re| + 1 := by linarith [neg_le_abs s₀.re]
      calc -s₀.re * u ≤ (|s₀.re| + 1) * u := mul_le_mul_of_nonneg_right h1 hu.1.le
        _ ≤ (|s₀.re| + 1) * L := mul_le_mul_of_nonneg_left hu.2 (by positivity)
    exact mul_le_mul hG hexp (Real.exp_pos _).le (by norm_num)
  have hbound : ∀ᵐ u ∂μ, ∀ s ∈ ball s₀ 1, ‖F' s u‖ ≤ B_dom := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu s hs
    have huL : u - L ≤ 0 := by linarith [hu.2]
    have hG := abs_rampG_exp_le_of_nonpos huL
    have hs_re : -s.re ≤ |s₀.re| + 1 := by
      have hd : ‖s - s₀‖ < 1 := mem_ball_iff_norm.mp hs
      have hrd := (abs_lt.mp ((Complex.abs_re_le_norm (s - s₀)).trans_lt hd)).1
      rw [Complex.sub_re] at hrd
      linarith [neg_le_abs s₀.re]
    dsimp [F', B_dom]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_of_nonneg hu.1.le, Complex.norm_exp]
    have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
    rw [hre]
    have hexp : Real.exp (-s.re * u) ≤ Real.exp ((|s₀.re| + 1) * L) := by
      apply Real.exp_le_exp.mpr
      calc -s.re * u ≤ (|s₀.re| + 1) * u := mul_le_mul_of_nonneg_right hs_re hu.1.le
        _ ≤ (|s₀.re| + 1) * L := mul_le_mul_of_nonneg_left hu.2 (by positivity)
    have hu_pos : 0 < u := hu.1
    have hprod : u * Real.exp (-s.re * u) ≤ L * Real.exp ((|s₀.re| + 1) * L) :=
      mul_le_mul hu.2 hexp (Real.exp_pos _).le hL0
    calc |IndependentLandau.rampG (Real.exp (u - L))| * (u * Real.exp (-s.re * u))
        ≤ 5 * (L * Real.exp ((|s₀.re| + 1) * L)) :=
          mul_le_mul hG hprod (mul_nonneg hu_pos.le (Real.exp_pos _).le) (by norm_num)
      _ = 5 * L * Real.exp ((|s₀.re| + 1) * L) := by ring
  have hdiff : ∀ᵐ u ∂μ, ∀ s ∈ ball s₀ 1, HasDerivAt (fun z => F z u) (F' s u) s := by
    filter_upwards with u s _
    dsimp [F, F']
    have h1 : HasDerivAt (fun z : ℂ => -z * (u : ℂ)) (-(u : ℂ)) s := by
      simpa using ((hasDerivAt_id s).neg).mul_const (u : ℂ)
    have h2 := h1.cexp.const_mul ((IndependentLandau.rampG (Real.exp (u - L)) : ℝ) : ℂ)
    exact h2.congr_deriv (by ring)
  have hdom_int : Integrable (fun _ : ℝ => B_dom) μ :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ zero_lt_one)
    (Eventually.of_forall fun s => (hmeas_F s).aestronglyMeasurable)
    hint_s₀ (hmeas_F' s₀).aestronglyMeasurable hbound hdom_int hdiff).2.differentiableAt

private lemma laplace_shifted_rampG {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn
      (fun u : ℝ => ((IndependentLandau.rampG (Real.exp (u - Real.log m)) : ℝ) : ℂ) * cexp (-s * u))
      (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ),
        ((IndependentLandau.rampG (Real.exp (u - Real.log m)) : ℝ) : ℂ) * cexp (-s * u)) =
      (m : ℂ) ^ (-s) * IndependentLandau.zetaPhi s + stencilFinError m s := by
  set L : ℝ := Real.log m
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg m
  let f : ℝ → ℂ := fun u =>
    ((IndependentLandau.rampG (Real.exp (u - L)) : ℝ) : ℂ) * cexp (-s * u)
  have hf_meas : Measurable f :=
    (Complex.measurable_ofReal.comp
      (IndependentLandau.measurable_rampG.comp
        (Real.measurable_exp.comp (measurable_id.sub_const L)))).mul
      (Continuous.measurable (by fun_prop))
  have hint : IntegrableOn f (Ioi 0) := by
    have hb : IntegrableOn (fun u : ℝ => 5 * Real.exp ((2 - s.re) * u)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul 5
    refine hb.mono' hf_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
    have hsplit_e : Real.exp ((2 - s.re) * u) = Real.exp (2 * u) * Real.exp (-s.re * u) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hre, hsplit_e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_rampG_shifted_le hm hu0.le) (Real.exp_pos _).le
  refine ⟨hint, ?_⟩
  have hunion : Ioc (0 : ℝ) L ∪ Ioi L = Ioi (0 : ℝ) := by
    ext u; simp only [mem_union, Set.mem_Ioc, Set.mem_Ioi]
    exact ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => hL0.trans_lt h2),
      fun hu => (le_or_gt u L).imp (fun hle => ⟨hu, hle⟩) id⟩
  have hdisj : Disjoint (Ioc (0 : ℝ) L) (Ioi L) := by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    exact not_lt.mpr hu1.2 hu2
  have hint_Ioc : IntegrableOn f (Ioc 0 L) := hint.mono_set fun u hu => hu.1
  have hint_Ioi : IntegrableOn f (Ioi L) := hint.mono_set fun u hu => hL0.trans_lt hu
  have hsplit_int : ∫ u in Ioi (0 : ℝ), f u =
      (∫ u in Ioc (0 : ℝ) L, f u) + ∫ u in Ioi L, f u := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint_Ioc hint_Ioi]
  have hshift : ∫ u in Ioi L, f u = (m : ℂ) ^ (-s) * IndependentLandau.zetaPhi s := by
    let ind_hi : ℝ → ℂ := (Ioi L).indicator f
    have htrans := MeasureTheory.integral_add_right_eq_self (μ := volume) ind_hi L
    have h1 : ∫ u : ℝ, ind_hi u = ∫ u in Ioi L, f u := integral_indicator measurableSet_Ioi
    have hpt : (fun v : ℝ => ind_hi (v + L)) =
        (Ioi (0 : ℝ)).indicator (fun v =>
          (m : ℂ) ^ (-s) * (((IndependentLandau.rampG (Real.exp v) : ℝ) : ℂ) * cexp (-s * v))) := by
      funext v
      by_cases hv : v ∈ Ioi (0 : ℝ)
      · have hvL : v + L ∈ Ioi L := by
          rw [Set.mem_Ioi] at hv ⊢; linarith
        dsimp [ind_hi, f]
        rw [indicator_of_mem hvL, indicator_of_mem hv]
        have hsub : v + L - L = v := by ring
        have hexp_sum : cexp (-s * ((v + L : ℝ) : ℂ)) =
            (m : ℂ) ^ (-s) * cexp (-s * (v : ℂ)) := by
          rw [natCast_cpow_neg_eq_cexp hm s, ← Complex.exp_add]
          congr 1; dsimp [L]; push_cast; ring
        rw [hsub, hexp_sum]
        ring
      · have hvL : v + L ∉ Ioi L := by
          rw [Set.mem_Ioi] at hv ⊢; linarith
        dsimp [ind_hi]
        rw [indicator_of_notMem hvL, indicator_of_notMem hv]
    rw [← h1, ← htrans, hpt, integral_indicator measurableSet_Ioi,
      integral_const_mul, ← IndependentLandau.zetaPhi_eq_laplace hs]
  rw [hsplit_int, hshift]
  unfold stencilFinError
  dsimp [f, L]
  ring

private def removableVal (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  open Classical in
  if h : ∃ L : ℂ, Tendsto f (𝓝[≠] z) (𝓝 L) then Classical.choose h else f z

private lemma removableVal_eq_of_tendsto {f : ℂ → ℂ} {z L : ℂ}
    (ht : Tendsto f (𝓝[≠] z) (𝓝 L)) : removableVal f z = L := by
  classical
  have hneBot : NeBot (𝓝[≠] z) := by
    let seq : ℕ → ℂ := fun n => z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hlim : Tendsto seq atTop (𝓝 z) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := tendsto_const_nhds (x := z) |>.add ((Complex.continuous_ofReal.tendsto 0).comp h1)
      rw [ofReal_zero, add_zero] at h2
      exact h2
    have hne : ∀ n : ℕ, seq n ≠ z := by
      intro n hc
      have := congrArg Complex.re hc
      simp only [seq, add_re, ofReal_re] at this
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have htend : Tendsto seq atTop (𝓝[≠] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hne⟩
    exact htend.neBot
  have hex : ∃ L' : ℂ, Tendsto f (𝓝[≠] z) (𝓝 L') := ⟨L, ht⟩
  unfold removableVal
  rw [dif_pos hex]
  exact tendsto_nhds_unique (Classical.choose_spec hex) ht

private lemma analyticAt_dirichletStencilPoly (c : ℕ → ℝ) (M : ℕ) (z : ℂ) :
    AnalyticAt ℂ (dirichletStencilPoly c M) z := by
  have heq : dirichletStencilPoly c M =
      fun s : ℂ => ∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * cexp (-s * (Real.log m : ℂ)) := by
    funext s
    unfold dirichletStencilPoly
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [natCast_cpow_neg_eq_cexp (Finset.mem_Icc.mp hm).1 s]
  rw [heq]
  have hdiff : Differentiable ℂ
      (fun s : ℂ => ∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * cexp (-s * (Real.log m : ℂ))) := by
    intro w
    exact DifferentiableAt.fun_sum fun m _ => by fun_prop
  exact hdiff.analyticAt z

/-- **Stenciled `PoleData` Lemma (`stenciled_poleData_of_nonzero_multiplier`):**
For any finite stencil `c : ℕ → ℝ` supported on `1 ≤ m ≤ M`, the stenciled ramp
`G_c(u) = ∑_{1 ≤ m ≤ M} c_m rampG(exp(u - log m))` satisfies `IndependentLandau.PoleData` with
pole set `{ρ ∈ zetaZeros | ∑_{1 ≤ m ≤ M} c_m ρ^{-m} ≠ 0}` (i.e., `P_c(ρ) ≠ 0`). -/
theorem stenciled_poleData_of_nonzero_multiplier (c : ℕ → ℝ) (M : ℕ) :
    ∃ Φ_c : ℂ → ℂ, IndependentLandau.PoleData
      (fun u => ∑ m ∈ Finset.Icc 1 M, c m * IndependentLandau.rampG (Real.exp (u - Real.log m)))
      Φ_c
      {ρ ∈ IndependentLandau.zetaZeros |
        (∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-ρ)) ≠ 0} := by
  classical
  let P_c : ℂ → ℂ := dirichletStencilPoly c M
  let E_c : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * stencilFinError m s
  let Φ_raw : ℂ → ℂ := fun s => P_c s * IndependentLandau.zetaPhi s + E_c s
  let Z_c : Set ℂ :=
    {ρ ∈ IndependentLandau.zetaZeros |
      (∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-ρ)) ≠ 0}
  let Φ_c : ℂ → ℂ := fun s =>
    if s ∈ IndependentLandau.zetaZeros ∧ P_c s = 0 then removableVal Φ_raw s else Φ_raw s
  have han_Ec : ∀ z : ℂ, AnalyticAt ℂ E_c z := by
    intro z
    have hd : Differentiable ℂ E_c := by
      intro w
      exact DifferentiableAt.fun_sum fun m hm =>
        (differentiable_stencilFinError (Finset.mem_Icc.mp hm).1 w).const_mul _
    exact hd.analyticAt z
  have han_Pc : ∀ z : ℂ, AnalyticAt ℂ P_c z := analyticAt_dirichletStencilPoly c M
  refine ⟨Φ_c, ?_⟩
  refine
    { meas := ?_
      growth := ?_
      laplace := ?_
      pos := fun ρ hρ => hρ.1.1
      diff := ?_
      iso := ?_
      pole := ?_ }
  · -- Measurability of `G_c`
    refine Finset.measurable_fun_sum _ fun m _ => ?_
    exact measurable_const.mul
      (IndependentLandau.measurable_rampG.comp
        (Real.measurable_exp.comp (measurable_id.sub_const _)))
  · -- `O(exp(2u))` growth on `u ≥ 0`
    refine ⟨∑ m ∈ Finset.Icc 1 M, |c m| * 5, fun u hu => ?_⟩
    calc |∑ m ∈ Finset.Icc 1 M, c m * IndependentLandau.rampG (Real.exp (u - Real.log m))|
        ≤ ∑ m ∈ Finset.Icc 1 M, |c m * IndependentLandau.rampG (Real.exp (u - Real.log m))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 M, |c m| * (5 * Real.exp (2 * u)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (abs_rampG_shifted_le (Finset.mem_Icc.mp hm).1 hu) (abs_nonneg _)
      _ = (∑ m ∈ Finset.Icc 1 M, |c m| * 5) * Real.exp (2 * u) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
  · -- Laplace identity on `Re s > 2`
    intro s hs
    have hs_notZ : s ∉ IndependentLandau.zetaZeros := by
      intro hmem
      exact riemannZeta_ne_zero_of_one_le_re (by linarith) hmem.2
    have hΦ_eq : Φ_c s = Φ_raw s := by
      dsimp [Φ_c]
      rw [if_neg (fun h => hs_notZ h.1)]
    rw [hΦ_eq]
    have hint_m : ∀ m ∈ Finset.Icc 1 M, IntegrableOn
        (fun u : ℝ =>
          (c m : ℂ) * (((IndependentLandau.rampG (Real.exp (u - Real.log m)) : ℝ) : ℂ) * cexp (-s * u)))
        (Ioi 0) := fun m hm =>
      (laplace_shifted_rampG (Finset.mem_Icc.mp hm).1 hs).1.const_mul _
    have hpt : (fun u : ℝ =>
          (((∑ m ∈ Finset.Icc 1 M, c m * IndependentLandau.rampG (Real.exp (u - Real.log m))) : ℝ) : ℂ) *
            cexp (-s * u)) =
        fun u : ℝ => ∑ m ∈ Finset.Icc 1 M,
          (c m : ℂ) * (((IndependentLandau.rampG (Real.exp (u - Real.log m)) : ℝ) : ℂ) * cexp (-s * u)) := by
      funext u
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hpt, integral_finsetSum _ hint_m]
    have hsum_eval : (∑ m ∈ Finset.Icc 1 M,
          ∫ u in Ioi (0 : ℝ),
            (c m : ℂ) * (((IndependentLandau.rampG (Real.exp (u - Real.log m)) : ℝ) : ℂ) * cexp (-s * u))) =
        ∑ m ∈ Finset.Icc 1 M,
          ((c m : ℂ) * (m : ℂ) ^ (-s) * IndependentLandau.zetaPhi s +
            (c m : ℂ) * stencilFinError m s) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [integral_const_mul, (laplace_shifted_rampG (Finset.mem_Icc.mp hm).1 hs).2]
      ring
    rw [hsum_eval, Finset.sum_add_distrib, ← Finset.sum_mul]
    rfl
  · -- Holomorphy of `Φ_c` on `{s | 0 < s.re} \ Z_c`
    rintro z₀ ⟨hz₀_re, hz₀_notZc⟩
    have hz₀_re' : 0 < z₀.re := hz₀_re
    have hz₀_ne0 : z₀ ≠ 0 := by rintro rfl; simp at hz₀_re'
    by_cases hz₀_Z : z₀ ∈ IndependentLandau.zetaZeros
    · -- Removable common zero: `z₀ ∈ zetaZeros` with `P_c z₀ = 0`
      have hPc0 : P_c z₀ = 0 := by
        by_contra hne
        exact hz₀_notZc ⟨hz₀_Z, hne⟩
      obtain ⟨res₀, _, _, h₀, hh₀_an, hev_pole⟩ := IndependentLandau.zetaPhi_pole hz₀_Z
      let H₀ : ℂ → ℂ := fun w => dslope P_c z₀ w * res₀ + P_c w * h₀ w + E_c w
      have hH₀_an : AnalyticAt ℂ H₀ z₀ := by
        have hdslope_an : AnalyticAt ℂ (dslope P_c z₀) z₀ := by
          have hd : DifferentiableOn ℂ P_c univ := fun x _ =>
            (han_Pc x).differentiableAt.differentiableWithinAt
          exact ((Complex.differentiableOn_dslope univ_mem).mpr hd).analyticAt univ_mem
        exact (((hdslope_an.mul analyticAt_const).add ((han_Pc z₀).mul hh₀_an)).add (han_Ec z₀))
      have hev_raw : Φ_raw =ᶠ[𝓝[≠] z₀] H₀ := by
        filter_upwards [hev_pole, eventually_mem_nhdsWithin] with w hw_pole hw_ne
        have hsub_ne : w - z₀ ≠ 0 := sub_ne_zero.mpr hw_ne
        have hPc_fac : P_c w = (w - z₀) * dslope P_c z₀ w := by
          have := sub_smul_dslope P_c z₀ w
          rw [hPc0, sub_zero, smul_eq_mul] at this
          exact this.symm
        dsimp [Φ_raw, H₀]
        rw [hw_pole, hPc_fac]
        field_simp [hsub_ne]
      have htend_raw : Tendsto Φ_raw (𝓝[≠] z₀) (𝓝 (H₀ z₀)) :=
        (hH₀_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hev_raw.symm
      have hval_z₀ : Φ_c z₀ = H₀ z₀ := by
        dsimp [Φ_c]
        rw [if_pos ⟨hz₀_Z, hPc0⟩, removableVal_eq_of_tendsto htend_raw]
      have hiso := IndependentLandau.zetaZeros_iso z₀
      have hev_nhds : Φ_c =ᶠ[𝓝 z₀] H₀ := by
        have hev_raw' : ∀ᶠ w in 𝓝[≠] z₀, Φ_raw w = H₀ w := hev_raw
        rw [eventually_nhdsWithin_iff] at hev_raw' hiso
        filter_upwards [hev_raw', hiso] with w hw1 hw2
        by_cases hw_eq : w = z₀
        · rw [hw_eq, hval_z₀]
        · have hw_notZ : w ∉ IndependentLandau.zetaZeros := hw2 hw_eq
          dsimp [Φ_c]
          rw [if_neg (fun h => hw_notZ h.1), hw1 hw_eq]
      exact (hH₀_an.differentiableAt.congr_of_eventuallyEq hev_nhds).differentiableWithinAt
    · -- Ordinary non-pole: `z₀ ∉ zetaZeros`
      have hZ1_ne : riemannZeta₁ z₀ ≠ 0 := fun h0 =>
        hz₀_Z (IndependentLandau.mem_zetaZeros.mpr ⟨hz₀_re', h0⟩)
      have han_raw : AnalyticAt ℂ Φ_raw z₀ :=
        ((han_Pc z₀).mul (IndependentLandau.analyticAt_zetaPhi hZ1_ne hz₀_ne0)).add (han_Ec z₀)
      have hiso := IndependentLandau.zetaZeros_iso z₀
      rw [eventually_nhdsWithin_iff] at hiso
      have hev_nhds : Φ_c =ᶠ[𝓝 z₀] Φ_raw := by
        filter_upwards [hiso] with w hw
        by_cases hw_eq : w = z₀
        · subst hw_eq
          dsimp [Φ_c]
          rw [if_neg (fun h => hz₀_Z h.1)]
        · have hw_notZ : w ∉ IndependentLandau.zetaZeros := hw hw_eq
          dsimp [Φ_c]
          rw [if_neg (fun h => hw_notZ h.1)]
      exact (han_raw.differentiableAt.congr_of_eventuallyEq hev_nhds).differentiableWithinAt
  · -- Isolation of `Z_c`
    intro z _
    filter_upwards [IndependentLandau.zetaZeros_iso z] with w hw hmem
    exact hw hmem.1
  · -- Simple pole with residue `P_c ρ * res_ρ ≠ 0` at each `ρ ∈ Z_c`
    rintro ρ ⟨hρ_Z, hPc_ne⟩
    obtain ⟨res_ρ, hres_ne, _, h_ρ, hh_an, hev_pole⟩ := IndependentLandau.zetaPhi_pole hρ_Z
    have hdslope_an : AnalyticAt ℂ (dslope P_c ρ) ρ := by
      have hd : DifferentiableOn ℂ P_c univ := fun x _ =>
        (han_Pc x).differentiableAt.differentiableWithinAt
      exact ((Complex.differentiableOn_dslope univ_mem).mpr hd).analyticAt univ_mem
    let H_ρ : ℂ → ℂ := fun w => dslope P_c ρ w * res_ρ + P_c w * h_ρ w + E_c w
    have hH_an : AnalyticAt ℂ H_ρ ρ :=
      (((hdslope_an.mul analyticAt_const).add ((han_Pc ρ).mul hh_an)).add (han_Ec ρ))
    refine ⟨P_c ρ * res_ρ, mul_ne_zero hPc_ne hres_ne,
      fun him => absurd him (zetaZeros_im_ne_zero hρ_Z), H_ρ, hH_an, ?_⟩
    filter_upwards [hev_pole, IndependentLandau.zetaZeros_iso ρ, eventually_mem_nhdsWithin]
      with w hw_pole hw_notZ hw_ne
    have hsub_ne : w - ρ ≠ 0 := sub_ne_zero.mpr hw_ne
    have hPc_decomp : P_c w = P_c ρ + (w - ρ) * dslope P_c ρ w := by
      have := sub_smul_dslope P_c ρ w
      rw [smul_eq_mul] at this
      linear_combination -this
    dsimp [Φ_c]
    rw [if_neg (fun h => hw_notZ h.1)]
    dsimp [Φ_raw, H_ρ]
    rw [hw_pole, hPc_decomp]
    field_simp [hsub_ne]
    ring

/-- **Dirichlet-Stencil Pole-Persistence Under Window Bounds (`stenciled_zero_re_le_of_window`):**
If `G_c(u) := ∑ m ∈ Finset.Icc 1 M, c m * rampG (exp (u - log m))` satisfies `WindowHypU G_c θ δ`
(`0 < θ < 1`, `0 < δ`), then every `ρ ∈ zetaZeros` with `∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * m^(-ρ) ≠ 0`
must still satisfy `ρ.re ≤ θ`. -/
theorem stenciled_zero_re_le_of_window (c : ℕ → ℝ) (M : ℕ) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hW : IndependentLandau.WindowHypU
      (fun u => ∑ m ∈ Finset.Icc 1 M, c m * IndependentLandau.rampG (Real.exp (u - Real.log m)))
      θ δ)
    {ρ : ℂ} (hρ : ρ ∈ IndependentLandau.zetaZeros)
    (hmult : (∑ m ∈ Finset.Icc 1 M, (c m : ℂ) * (m : ℂ) ^ (-ρ)) ≠ 0) :
    ρ.re ≤ θ := by
  obtain ⟨Φ_c, hP⟩ := stenciled_poleData_of_nonzero_multiplier c M
  exact IndependentLandau.landau_window hP hθ hθ1 hδ hW ρ ⟨hρ, hmult⟩

end DirectRampEquivalence

export DirectRampEquivalence (
  archiveFree_moment_of_ordinaryWindow_general
  archiveFree_moment_of_ordinaryWindow
  archiveFree_moment_of_window_087
  dirichletStencilPoly
  stenciledRampU
  dirichlet_stencil_nonvanishing_large_re
  stenciled_poleData_of_nonzero_multiplier
  stenciled_zero_re_le_of_window
)

#print axioms archiveFree_moment_of_ordinaryWindow
#print axioms archiveFree_moment_of_window_087
#print axioms dirichlet_stencil_nonvanishing_large_re
#print axioms stenciled_poleData_of_nonzero_multiplier
#print axioms stenciled_zero_re_le_of_window
