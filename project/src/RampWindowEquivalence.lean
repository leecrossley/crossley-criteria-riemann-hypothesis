import Mathlib
import IndependentLandau.ZetaWindow
import Reflection
import ZetaRegion.Local
import ZetaRegion.ZetaBounds
import ZetaRamp.Bounds
import ZetaRamp.Transform
import ZetaRamp.Inversion
import ZetaRamp.Contour

/-!
# Complete Two-Way Analytic Characterization of `rampG x ≤ x^θ` on `[Y, Y^(3/2)]`

This module proves, 100% from Mathlib and first-party Mathlib-only modules (`IndependentLandau`,
`Crossley`, `ZetaRegion`, `ZetaRamp`), the two-way analytic equivalence between:

1. One-sided window bounds `rampG x ≤ x^θ` on cofinally many multiplicative windows `[Y, Y^(3/2)]`
   (`OrdinaryWindowUnit θ`, and more generally `OrdinaryWindow θ δ`),
2. Zero-free half-planes `∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0`,
3. Global two-sided pointwise bounds `|rampG x| ≤ C * x^θ` at **every** `x ≥ 1`,

together with the specialization `RiemannHypothesis ↔ ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1, OrdinaryWindowUnit θ`.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped FourierTransform Interval

noncomputable section

namespace DirectRampEquivalence

local notation "γ" => (Real.eulerMascheroniConstant : ℂ)

/-! ### 1. Window Definitions and Direct Landau Converse -/

/-- General one-sided multiplicative window bound on `[Y, Y^(1 + δ)]` with constant `C > 0`. -/
def OrdinaryWindow (θ δ : ℝ) : Prop :=
  ∃ C > 0, ∀ Y₀ : ℝ, ∃ Y ≥ max Y₀ 1,
    ∀ x ∈ Set.Icc Y (Y ^ (1 + δ)), IndependentLandau.rampG x ≤ C * x ^ θ

/-- Unit-constant one-sided multiplicative window bound on `[Y, Y^(3/2)]`. -/
def OrdinaryWindowUnit (θ : ℝ) : Prop :=
  ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
    ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)), IndependentLandau.rampG x ≤ x ^ θ

/-- `OrdinaryWindowUnit θ` specializes `OrdinaryWindow θ (1 / 2)` with `C = 1`. -/
theorem ordinaryWindow_of_unit {θ : ℝ} (h : OrdinaryWindowUnit θ) :
    OrdinaryWindow θ (1 / 2) := by
  refine ⟨1, zero_lt_one, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hwin⟩ := h (max Y₀ 1)
  refine ⟨Y, hY, fun x hx => ?_⟩
  have h32 : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [h32] at hx
  simpa only [one_mul] using hwin x hx

/-- Direct logarithmic change of variables converting `OrdinaryWindow θ δ` into
`IndependentLandau.WindowHypU (fun u => rampG (Real.exp u)) θ δ`. -/
theorem windowHypU_of_ordinaryWindow {θ δ : ℝ} (hδ : 0 < δ) (hW : OrdinaryWindow θ δ) :
    IndependentLandau.WindowHypU (fun u => IndependentLandau.rampG (Real.exp u)) θ δ := by
  obtain ⟨C, hC, hY⟩ := hW
  intro η hη U₀
  let B : ℝ := max (max U₀ 1) (4 * C * δ / η ^ 2)
  have hB_U₀ : U₀ ≤ B := (le_max_left U₀ 1).trans (le_max_left _ _)
  have hB_one : 1 ≤ B := (le_max_right U₀ 1).trans (le_max_left _ _)
  have hB_pos : 0 < B := zero_lt_one.trans_le hB_one
  have hB_rate : 4 * C * δ / η ^ 2 ≤ B := le_max_right _ _
  obtain ⟨Y, hY_ge, hwin⟩ := hY (Real.exp B)
  have hY_expB : Real.exp B ≤ Y := (le_max_left _ _).trans hY_ge
  have hY_pos : 0 < Y := (Real.exp_pos B).trans_le hY_expB
  let U : ℝ := Real.log Y
  have hBU : B ≤ U := (Real.le_log_iff_exp_le hY_pos).mpr hY_expB
  have hU_pos : 0 < U := hB_pos.trans_le hBU
  have hU_le : U ≤ (1 + δ) * U := by nlinarith
  refine ⟨U, hB_U₀.trans hBU, fun u => C * Real.exp (θ * u), ?_, ?_, ?_⟩
  · have hconst : (fun u : ℝ => C * Real.exp (θ * u) * Real.exp (-θ * u)) = fun _ => C := by
      funext u
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [hconst]
    exact integrableOn_const (hs := measure_Icc_lt_top.ne)
  · intro u hu
    refine ⟨by positivity, ?_⟩
    have hx_lo : Y ≤ Real.exp u := by
      have : Real.exp U ≤ Real.exp u := Real.exp_le_exp.mpr hu.1
      rwa [Real.exp_log hY_pos] at this
    have hx_hi : Real.exp u ≤ Y ^ (1 + δ) := by
      rw [Real.rpow_def_of_pos hY_pos]
      have : Real.log Y * (1 + δ) = (1 + δ) * U := by dsimp [U]; ring
      rw [this]
      exact Real.exp_le_exp.mpr hu.2
    have hbd := hwin (Real.exp u) ⟨hx_lo, hx_hi⟩
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_comm u θ] at hbd
    exact hbd
  · have hconst : (fun u : ℝ => C * Real.exp (θ * u) * Real.exp (-θ * u)) = fun _ => C := by
      funext u
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [hconst, MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hU_le]
    have hlen : (1 + δ) * U - U = δ * U := by ring
    rw [hlen]
    have hexp_sq : (η * U / 2) ^ 2 ≤ Real.exp (η * U) := by
      have h1 : η * U / 2 ≤ Real.exp (η * U / 2) := by
        linarith [Real.add_one_le_exp (η * U / 2)]
      have h2 : Real.exp (η * U) = Real.exp (η * U / 2) * Real.exp (η * U / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h2, sq]
      exact mul_le_mul h1 h1 (by positivity) (Real.exp_pos _).le
    have hquad : δ * U * C ≤ (η * U / 2) ^ 2 := by
      have hmul : 4 * C * δ ≤ η ^ 2 * U := by
        have := (div_le_iff₀ (pow_pos hη 2)).mp (hB_rate.trans hBU)
        linarith
      have hmulU := mul_le_mul_of_nonneg_right hmul hU_pos.le
      nlinarith
    exact hquad.trans hexp_sq

/-- **Converse Theorem (General Window):**
A one-sided bound `rampG x ≤ C * x^θ` on cofinally many `[Y, Y^(1+δ)]` windows excludes all zeros
of `riemannZeta` in the half-plane `Re s > θ`. -/
theorem zeta_zeroFree_of_ordinaryWindow {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : OrdinaryWindow θ δ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  IndependentLandau.zeta_zeroFree_of_window hθ hθ1 hδ (windowHypU_of_ordinaryWindow hδ hW)

/-- **Converse Theorem (Unit `[Y, Y^(3/2)]` Window):**
`OrdinaryWindowUnit θ` directly implies `riemannZeta s ≠ 0` for all `s` with `θ < s.re`. -/
theorem zeta_zeroFree_of_ordinaryWindowUnit {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hW : OrdinaryWindowUnit θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  zeta_zeroFree_of_ordinaryWindow hθ hθ1 (by norm_num : (0 : ℝ) < 1 / 2) (ordinaryWindow_of_unit hW)

/-! ### 2. Forward Direction: Zero-Free Half-Plane Implies Global `|rampG x| ≤ C * x^θ` -/

/-- Borel–Carathéodory transfer from a real-part upper bound on `ball c R` to a norm bound on
`closedBall c r`. -/
private lemma norm_le_of_re_le_on_ball {h : ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr0 : 0 ≤ r) (hrR : r < R) (hM : 0 < M)
    (hh : DifferentiableOn ℂ h (ball c R)) (hhc : h c = 0)
    (hre : ∀ z ∈ ball c R, (h z).re ≤ M) :
    ∀ z ∈ closedBall c r, ‖h z‖ ≤ 2 * M * r / (R - r) := by
  have hR0 : 0 < R := hr0.trans_lt hrR
  have hmem : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hw
  have hHd : DifferentiableOn ℂ (fun w => h (c + w)) (ball 0 R) := fun w hw =>
    ((hh.differentiableAt (isOpen_ball.mem_nhds (hmem w hw))).comp w
      (differentiableAt_id.const_add c)).differentiableWithinAt
  have hHm : MapsTo (fun w => h (c + w)) (ball 0 R) {z | z.re ≤ M} :=
    fun w hw => hre _ (hmem w hw)
  have h0 : (fun w => h (c + w)) 0 = 0 := by simp [hhc]
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have hw : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hbc := Complex.borelCaratheodory_zero hM hHd hHm hR0 hw h0
  simp only [add_sub_cancel] at hbc
  refine hbc.trans ?_
  have hden1 : 0 < R - ‖z - c‖ := by linarith
  have hden2 : 0 < R - r := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  have hdiff_pos : 0 ≤ 2 * M * R * (r - ‖z - c‖) :=
    mul_nonneg (by positivity) (by linarith)
  linarith [show 2 * M * r * (R - ‖z - c‖) - 2 * M * ‖z - c‖ * (R - r) =
    2 * M * R * (r - ‖z - c‖) by ring]

/-- Logarithmic-derivative bound on a closed vertical strip `[θ, 2]` (`|Im s| ≥ 1`) inside a
zero-free half-plane `Re s > θ₀`, proved via Borel–Carathéodory on `log riemannZeta₁` around
`2 + t * I` plus Cauchy's derivative estimate on discs of radius `(θ - θ₀)/4`. -/
private lemma exists_strip_logDeriv_bound {θ₀ θ : ℝ}
    (hθ₀ : 1 / 2 ≤ θ₀) (hθ₀θ : θ₀ < θ) (hθ1 : θ < 1)
    (hz : ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) :
    ∃ C_ld > 0, ∀ s : ℂ, θ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C_ld * Real.log (|s.im| + 2) ^ 2 := by
  let δ : ℝ := (θ - θ₀) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let R_out : ℝ := 2 - θ₀ - δ
  let R_mid : ℝ := 2 - θ₀ - 2 * δ
  have hR_mid_pos : 0 < R_mid := by dsimp [R_mid, δ]; linarith
  have hR_mid_lt : R_mid < R_out := by dsimp [R_mid, R_out]; linarith
  have hR_out_pos : 0 < R_out := hR_mid_pos.trans hR_mid_lt
  have hR_out_lt : R_out < 3 / 2 := by dsimp [R_out]; linarith
  have hR_mid_le2 : R_mid ≤ 2 := by dsimp [R_mid]; linarith
  let C_ld : ℝ := 2 * (56 / δ ^ 2 + 2)
  have hC_ld_pos : 0 < C_ld := by dsimp [C_ld]; positivity
  refine ⟨C_ld, hC_ld_pos, fun s hs_lo hs_hi ht1 => ?_⟩
  set t : ℝ := s.im
  set c : ℂ := (2 : ℂ) + (t : ℂ) * I with hc_def
  have hcre : c.re = 2 := by simp [hc_def]
  have hcim : c.im = t := by simp [hc_def]
  have hc_lo : (2 - 1 : ℝ) / 3 ≤ ‖riemannZeta₁ c‖ := by
    have := ZetaRegion.le_norm_zeta₁ (s := c) (by rw [hcre]; norm_num) (by rw [hcre]) (by rw [hcim]; exact ht1)
    rwa [hcre] at this
  have hc_pos : 0 < ‖riemannZeta₁ c‖ := by linarith
  have hball_ne : ∀ z ∈ ball c R_out, riemannZeta₁ z ≠ 0 := by
    intro z hz_mem
    rcases eq_or_ne z 1 with rfl | hne1
    · simp
    · have hdist : ‖z - c‖ < R_out := mem_ball_iff_norm.mp hz_mem
      have hre_d := (abs_lt.mp ((Complex.abs_re_le_norm (z - c)).trans_lt hdist)).1
      rw [Complex.sub_re, hcre] at hre_d
      have hz_re : θ₀ < z.re := by dsimp [R_out] at hre_d; linarith
      exact fun h0 => hz z hz_re (IndependentLandau.zeta₁_eq_zero_iff.mp h0)
  have hball_up : ∀ z ∈ ball c R_out, ‖riemannZeta₁ z‖ ≤ 21 * (|t| + 2) ^ 2 := by
    intro z hz_mem
    have hdist : ‖z - c‖ < R_out := mem_ball_iff_norm.mp hz_mem
    have hre_d := abs_lt.mp ((Complex.abs_re_le_norm (z - c)).trans_lt hdist)
    have him_d := abs_lt.mp ((Complex.abs_im_le_norm (z - c)).trans_lt hdist)
    rw [Complex.sub_re, hcre] at hre_d
    rw [Complex.sub_im, hcim] at him_d
    have hz_re_lo : 1 / 2 ≤ z.re := by dsimp [R_out] at hre_d; linarith
    have hz_re_hi : z.re ≤ 7 / 2 := by linarith [hre_d.2, hR_out_lt]
    have hz_im_abs : |z.im| ≤ |t| + 3 / 2 := by
      have htri := abs_add_le (z.im - t) t
      rw [sub_add_cancel] at htri
      have hzim_t : |z.im - t| < 3 / 2 := (abs_lt.mpr him_d).trans hR_out_lt
      linarith
    have hz_norm : ‖z‖ ≤ 3 * (|t| + 2) := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 7 / 2 + (|t| + 3 / 2) := by
            rw [abs_of_pos (by linarith : 0 < z.re)]
            linarith
        _ = |t| + 5 := by ring
        _ ≤ 3 * (|t| + 2) := by linarith [abs_nonneg t]
    have hz1_norm : ‖z - 1‖ ≤ 3 * (|t| + 2) := by
      have hr : |(z - 1).re| ≤ 5 / 2 := by
        rw [abs_le]
        constructor <;> simp <;> linarith
      have hi : (z - 1).im = z.im := by simp
      calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 5 / 2 + (|t| + 3 / 2) := by rw [hi]; linarith
        _ = |t| + 4 := by ring
        _ ≤ 3 * (|t| + 2) := by linarith [abs_nonneg t]
    have hbase := ZetaRegion.norm_zeta₁_le (s := z) (by linarith)
    have hdiv : ‖z‖ * ‖z - 1‖ / z.re ≤ 2 * (‖z‖ * ‖z - 1‖) := by
      rw [div_le_iff₀ (by linarith : 0 < z.re)]
      nlinarith [mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))]
    have hprod : ‖z‖ * ‖z - 1‖ ≤ 9 * (|t| + 2) ^ 2 := by
      calc ‖z‖ * ‖z - 1‖ ≤ (3 * (|t| + 2)) * (3 * (|t| + 2)) :=
            mul_le_mul hz_norm hz1_norm (norm_nonneg _) (by positivity)
        _ = 9 * (|t| + 2) ^ 2 := by ring
    have ht2_ge1 : 1 ≤ |t| + 2 := by linarith [abs_nonneg t]
    have ht2_le_sq : |t| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith
    nlinarith
  obtain ⟨h, hh_diff, hhc, h_exp, h_deriv⟩ :=
    ZetaRegion.exists_log_on_ball hR_out_pos differentiable_riemannZeta₁.differentiableOn hball_ne
  set L : ℝ := Real.log (|t| + 2)
  have hL_half : 1 / 2 < L := ZetaRamp.half_lt_log_abs_add_two t
  have hL_pos : 0 < L := by linarith
  have hre_bd : ∀ z ∈ ball c R_out, (h z).re ≤ 14 * L := by
    intro z hz_mem
    have heq := congrArg norm (h_exp z hz_mem)
    rw [norm_mul, Complex.norm_exp] at heq
    have hexp_le : Real.exp (h z).re ≤ 63 * (|t| + 2) ^ 2 := by
      have h1 : ‖riemannZeta₁ c‖ * Real.exp (h z).re ≤ 21 * (|t| + 2) ^ 2 := by
        linarith [hball_up z hz_mem]
      have h3 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
      have h13 : 1 ≤ 3 * ‖riemannZeta₁ c‖ := by linarith
      nlinarith [Real.exp_pos (h z).re]
    have hlog_le := Real.log_le_log (Real.exp_pos _) hexp_le
    rw [Real.log_exp, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog_le
    push_cast at hlog_le
    have hlog63 : Real.log 63 ≤ 6 := by
      have h63 : (63 : ℝ) ≤ 2 ^ 6 := by norm_num
      have h1 := Real.log_le_log (by norm_num) h63
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith [Real.log_two_lt_d9]
    have h6_le : (6 : ℝ) ≤ 12 * L := by linarith
    dsimp [L] at h6_le ⊢
    linarith
  have hmid_bd : ∀ z ∈ closedBall c R_mid, ‖h z‖ ≤ (56 / δ) * L := by
    intro z hz_mid
    have hbc := norm_le_of_re_le_on_ball hR_mid_pos.le hR_mid_lt
      (by positivity : 0 < 14 * L) hh_diff hhc hre_bd z hz_mid
    have hsub_R : R_out - R_mid = δ := by dsimp [R_out, R_mid]; ring
    rw [hsub_R] at hbc
    refine hbc.trans ?_
    have : 2 * (14 * L) * R_mid / δ ≤ 2 * (14 * L) * 2 / δ := by
      gcongr
    refine this.trans_eq ?_
    ring
  have hs_dist : dist s c ≤ R_mid - 2 * δ := by
    rw [dist_eq_norm]
    have hs_sub : s - c = (((s.re - 2) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc_def, t]
    rw [hs_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    dsimp [R_mid, δ]; linarith
  have hsub_mid : closedBall s δ ⊆ closedBall c R_mid := by
    intro z hz_s
    rw [mem_closedBall] at hz_s ⊢
    linarith [dist_triangle z s c]
  have hsub_out : closedBall s δ ⊆ ball c R_out :=
    hsub_mid.trans (closedBall_subset_ball hR_mid_lt)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
    (hh_diff.diffContOnCl_ball hsub_out)
    (fun z hz_sph => hmid_bd z (hsub_mid (sphere_subset_closedBall hz_sph)))
  have hs_in_out : s ∈ ball c R_out := hsub_out (mem_closedBall_self hδ.le)
  have hld1 : ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤ (56 / δ ^ 2) * L := by
    rw [← h_deriv s hs_in_out]
    exact hcauchy.trans_eq (by field_simp)
  have hs_ne1 : s ≠ 1 := by
    intro hs1
    have : t = 0 := by dsimp [t]; rw [hs1]; simp
    rw [this] at ht1
    norm_num at ht1
  have hs_zeta_ne : riemannZeta s ≠ 0 := hz s (by linarith)
  rw [ZetaRegion.logDeriv_zeta_eq hs_ne1 hs_zeta_ne]
  have hs1_inv : ‖1 / (s - 1)‖ ≤ 2 * L := by
    have him1 : 1 ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      simp only [sub_im, one_im, sub_zero] at h
      linarith
    rw [norm_div, norm_one, one_div]
    exact (inv_le_one_of_one_le₀ him1).trans (by linarith : (1 : ℝ) ≤ 2 * L)
  have htri : ‖deriv riemannZeta₁ s / riemannZeta₁ s - 1 / (s - 1)‖ ≤
      (56 / δ ^ 2 + 2) * L := by
    calc ‖deriv riemannZeta₁ s / riemannZeta₁ s - 1 / (s - 1)‖
        ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
      _ ≤ (56 / δ ^ 2) * L + 2 * L := add_le_add hld1 hs1_inv
      _ = (56 / δ ^ 2 + 2) * L := by ring
  refine htri.trans ?_
  have hL_sq : L ≤ 2 * L ^ 2 := by nlinarith
  calc (56 / δ ^ 2 + 2) * L ≤ (56 / δ ^ 2 + 2) * (2 * L ^ 2) :=
        mul_le_mul_of_nonneg_left hL_sq (by positivity)
    _ = C_ld * L ^ 2 := by dsimp [C_ld]; ring

/-- Uniform `(1 + |Im s|)^(-3/2)` decay and holomorphy of `ZetaRamp.psi` across the entire closed
strip `θ ≤ Re s ≤ 2` inside a zero-free half-plane `Re s > θ₀`. -/
private lemma exists_strip_psi_bound {θ₀ θ : ℝ}
    (hθ₀ : 1 / 2 ≤ θ₀) (hθ₀θ : θ₀ < θ) (hθ1 : θ < 1)
    (hz : ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) :
    (∀ s : ℂ, θ ≤ s.re → AnalyticAt ℂ ZetaRamp.psi s) ∧
    ∃ B > 0, ∀ s : ℂ, θ ≤ s.re → s.re ≤ 2 →
      ‖ZetaRamp.psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
  have han : ∀ s : ℂ, θ ≤ s.re → AnalyticAt ℂ ZetaRamp.psi s := by
    intro s hs_re
    have hre_half : 1 / 2 ≤ s.re := by linarith
    have hZ1 : riemannZeta₁ s ≠ 0 := by
      rcases eq_or_ne s 1 with rfl | h1
      · simp
      · exact fun h0 => hz s (by linarith) (IndependentLandau.zeta₁_eq_zero_iff.mp h0)
    exact (IndependentLandau.analyticAt_zetaPhi hZ1 (ZetaRamp.ne_zero_of_half_le_re hre_half)).sub
      (analyticAt_const.div (analyticAt_id.add analyticAt_const)
        (ZetaRamp.add_one_ne_zero_of_half_le_re hre_half))
  obtain ⟨C_ld, hC_ld, hLD_strip⟩ := exists_strip_logDeriv_bound hθ₀ hθ₀θ hθ1 hz
  have hhigh : ∀ s : ℂ, θ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖ZetaRamp.psi s‖ ≤ 4 * (32 * C_ld + 5) * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
    intro s hs_lo hs_hi ht
    have hre_half : 1 / 2 ≤ s.re := by linarith
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at ht
    have hζ : riemannZeta s ≠ 0 := hz s (by linarith)
    have hLD := hLD_strip s hs_lo hs_hi ht
    rw [ZetaRamp.psi_eq hs1 (ZetaRamp.ne_zero_of_half_le_re hre_half)
      (ZetaRamp.add_one_ne_zero_of_half_le_re hre_half) hζ]
    have n0 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have n1 : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
    have n2 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
    generalize |s.im| = τ at *
    have hτ0 : 0 < τ := by linarith
    have hτ2 : 0 < τ ^ 2 := by positivity
    have t1 : ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1))‖
        ≤ C_ld * Real.log (τ + 2) ^ 2 / τ ^ 2 := by
      rw [norm_div, norm_neg, norm_mul]
      refine div_le_div₀ (by positivity) hLD hτ2 ?_
      rw [pow_two]
      exact mul_le_mul n0 n1 hτ0.le (norm_nonneg _)
    have t2 : ‖1 / (s - 1) ^ 2‖ ≤ 1 / τ ^ 2 := by
      rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le hτ2 (pow_le_pow_left₀ hτ0.le n1 2)
    have t3 : ‖2 * (1 + γ) / ((s - 1) * (s + 1))‖ ≤ 4 / τ ^ 2 := by
      rw [norm_div, norm_mul, norm_mul]
      refine div_le_div₀ (by norm_num) ?_ hτ2 ?_
      · have : ‖(2 : ℂ)‖ = 2 := by simp
        rw [this]
        linarith [ZetaRamp.norm_one_add_gamma_le]
      · rw [pow_two]
        exact mul_le_mul n1 n2 hτ0.le (norm_nonneg _)
    have hsum : ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + 2 * (1 + γ) / ((s - 1) * (s + 1))‖ ≤ (C_ld * Real.log (τ + 2) ^ 2 + 5) / τ ^ 2 := by
      calc _ ≤ ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2‖
            + ‖2 * (1 + γ) / ((s - 1) * (s + 1))‖ := norm_add_le _ _
        _ ≤ ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1))‖ + ‖1 / (s - 1) ^ 2‖
            + ‖2 * (1 + γ) / ((s - 1) * (s + 1))‖ := by
            gcongr
            exact norm_sub_le _ _
        _ ≤ C_ld * Real.log (τ + 2) ^ 2 / τ ^ 2 + 1 / τ ^ 2 + 4 / τ ^ 2 := by gcongr
        _ = (C_ld * Real.log (τ + 2) ^ 2 + 5) / τ ^ 2 := by ring
    refine hsum.trans ?_
    set w := Real.sqrt (1 + τ) with hwdef
    have hw2 : w ^ 2 = 1 + τ := Real.sq_sqrt (by linarith)
    have hp : Real.sqrt (τ + 2) ≤ 2 * w := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, hw2]; linarith
    have hL : Real.log (τ + 2) ^ 2 ≤ 32 * w := by
      have := ZetaRamp.log_sq_le (x := τ + 2) (by linarith)
      linarith
    have hnum : C_ld * Real.log (τ + 2) ^ 2 + 5 ≤ (32 * C_ld + 5) * w := by
      have : C_ld * Real.log (τ + 2) ^ 2 ≤ C_ld * (32 * w) :=
        mul_le_mul_of_nonneg_left hL hC_ld.le
      nlinarith [Real.sqrt_pos.mpr (by linarith : 0 < 1 + τ)]
    rw [ZetaRamp.rpow_neg_three_half (by linarith), ← hwdef]
    have e : ((1 + τ) * w)⁻¹ = w / (1 + τ) ^ 2 := by rw [← hw2]; field_simp
    rw [e]
    have key : (1 + τ) ^ 2 ≤ 4 * τ ^ 2 := by nlinarith
    have h1τ : 0 < (1 + τ) ^ 2 := by positivity
    calc (C_ld * Real.log (τ + 2) ^ 2 + 5) / τ ^ 2 ≤ (32 * C_ld + 5) * w / τ ^ 2 := by gcongr
      _ ≤ 4 * (32 * C_ld + 5) * (w / (1 + τ) ^ 2) := by
          rw [div_le_iff₀ hτ2]
          have h3 : 1 ≤ 4 * τ ^ 2 / (1 + τ) ^ 2 := by rw [le_div_iff₀ h1τ]; linarith
          have h4 : 4 * (32 * C_ld + 5) * (w / (1 + τ) ^ 2) * τ ^ 2
              = (32 * C_ld + 5) * w * (4 * τ ^ 2 / (1 + τ) ^ 2) := by field_simp
          rw [h4]
          exact le_mul_of_one_le_right (by positivity) h3
  -- Compact low-height box `[θ, 2] ×ℂ [-1, 1]`
  let boxLow : Set ℂ := Icc θ 2 ×ℂ Icc (-1 : ℝ) 1
  have hcomp : IsCompact boxLow := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn ZetaRamp.psi boxLow := fun s hs =>
    (han s hs.1.1).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  let B : ℝ := 4 * |M| + 4 * (32 * C_ld + 5) + 1
  refine ⟨han, B, by positivity, fun s hs_lo hs_hi => ?_⟩
  rcases le_total |s.im| 1 with ht | ht
  · have hmem : s ∈ boxLow := ⟨⟨hs_lo, hs_hi⟩, abs_le.mp ht⟩
    have h1 : ‖ZetaRamp.psi s‖ ≤ |M| := (hM s hmem).trans (le_abs_self M)
    have h2 : (1 : ℝ) / 4 ≤ (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
      rw [ZetaRamp.rpow_neg_three_half (by positivity)]
      set w := Real.sqrt (1 + |s.im|) with hwdef
      have hw2 : w ^ 2 = 1 + |s.im| := Real.sq_sqrt (by positivity)
      have hw0 : 0 < w := Real.sqrt_pos.mpr (by positivity)
      have hw_le2 : w ≤ 2 := by nlinarith
      rw [one_div, inv_le_inv₀ (by norm_num) (by positivity)]
      nlinarith [abs_nonneg s.im]
    calc ‖ZetaRamp.psi s‖ ≤ |M| := h1
      _ ≤ 4 * |M| * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by nlinarith [abs_nonneg M]
      _ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          dsimp [B]; linarith
  · refine (hhigh s hs_lo hs_hi ht).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
    dsimp [B]; linarith [abs_nonneg M]

/-- **Forward Direction (`abs_rampG_le_of_zeroFree`):**
If `1 / 2 ≤ θ₀ < θ < 1` and `riemannZeta` has no zeros in `Re s > θ₀`, then the centred ramp
satisfies the global two-sided bound `|rampG x| ≤ C * x ^ θ` for **every** `x ≥ 1`. -/
theorem abs_rampG_le_of_zeroFree {θ₀ θ : ℝ}
    (hθ₀ : 1 / 2 ≤ θ₀) (hθ₀θ : θ₀ < θ) (hθ1 : θ < 1)
    (hz : ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |IndependentLandau.rampG x| ≤ C * x ^ θ := by
  have hθ_pos : 0 < θ := by linarith
  obtain ⟨han, B, hB_pos, hB⟩ := exists_strip_psi_bound hθ₀ hθ₀θ hθ1 hz
  set b : ℝ := 3 / 2
  have hb1 : 1 < b := by dsimp [b]; norm_num
  have hb2 : b ≤ 2 := by dsimp [b]; norm_num
  have hθb : θ ≤ b := by dsimp [b]; linarith
  have hcont_line : Continuous fun t : ℝ => ZetaRamp.psi ((b : ℂ) + (t : ℂ) * I) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : ((b : ℂ) + (t : ℂ) * I).re = b := by simp
    exact (han _ (by rw [hre]; exact hθb)).continuousAt.comp (by fun_prop)
  -- Integrability of `𝓕 (invF b)` on `ℝ`
  have hint_fourier : Integrable (𝓕 (ZetaRamp.invF b)) := by
    have e : 𝓕 (ZetaRamp.invF b) =
        fun w : ℝ => ZetaRamp.psi ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) :=
      funext (ZetaRamp.fourier_invF hb1)
    rw [e]
    have hcont : Continuous fun w : ℝ =>
        ZetaRamp.psi ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) :=
      hcont_line.comp (continuous_const.mul continuous_id)
    have hJ : Integrable (fun w : ℝ => B * (1 + ‖w‖) ^ (-(3 / 2) : ℝ)) :=
      (integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)).const_mul B
    refine hJ.mono' hcont.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    have hre : ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I).re = b := by simp
    have him : ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I).im = 2 * Real.pi * w := by simp
    have hbd := hB _ (by rw [hre]; exact hθb) (by rw [hre]; exact hb2)
    rw [him] at hbd
    refine hbd.trans (mul_le_mul_of_nonneg_left ?_ hB_pos.le)
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
    have h2pi : (1 : ℝ) ≤ |2 * Real.pi| := by
      rw [abs_of_pos (by positivity)]; linarith [Real.pi_gt_three]
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg w]
  -- Fourier inversion + rectangle shift to `Re s = θ` at height `T = exp (8 * u)` for all `u > 0`
  let K_H : ℝ := B * (ZetaRamp.J (3 / 2) + ZetaRamp.J (5 / 4) + 2)
  have hKH_pos : 0 < K_H := by
    dsimp [K_H]
    have := ZetaRamp.J_nonneg (3 / 2)
    have := ZetaRamp.J_nonneg (5 / 4)
    positivity
  have hrampH_pos : ∀ u : ℝ, 0 < u → |ZetaRamp.rampH u| ≤ K_H * Real.exp (θ * u) := by
    intro u hu
    -- Fourier inversion on `Re s = b`
    have hinv_eq : ((ZetaRamp.rampH u : ℝ) : ℂ) = ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ t : ℝ, ZetaRamp.psi ((b : ℂ) + (t : ℂ) * I) * cexp (((b : ℂ) + (t : ℂ) * I) * u) := by
      have hinv := (ZetaRamp.integrable_invF hb1).fourierInv_fourier_eq
        hint_fourier (ZetaRamp.continuousAt_invF b hu)
      rw [Real.fourierInv_eq'] at hinv
      have hval : ZetaRamp.invF b u = ((ZetaRamp.rampH u : ℝ) : ℂ) * cexp (-(b : ℂ) * u) :=
        indicator_of_mem (mem_Ioi.mpr hu) _
      rw [hval] at hinv
      let G : ℝ → ℂ := fun t => cexp (((t * u : ℝ) : ℂ) * I) * ZetaRamp.psi ((b : ℂ) + (t : ℂ) * I)
      have hG : ∀ v : ℝ, cexp (((2 * Real.pi * inner ℝ v u : ℝ) : ℂ) * I) • 𝓕 (ZetaRamp.invF b) v
          = G (2 * Real.pi * v) := by
        intro v
        rw [ZetaRamp.fourier_invF hb1, smul_eq_mul]
        have hin : inner ℝ v u = v * u := by simp [mul_comm]
        simp only [G, hin]
        rw [show 2 * Real.pi * (v * u) = 2 * Real.pi * v * u by ring]
      simp_rw [hG] at hinv
      have hcomp := Measure.integral_comp_mul_left G (2 * Real.pi)
      have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
      rw [habs, hinv] at hcomp
      have hpt : ∀ t : ℝ, ZetaRamp.psi ((b : ℂ) + (t : ℂ) * I) * cexp (((b : ℂ) + (t : ℂ) * I) * u)
          = cexp ((b : ℂ) * u) * G t := by
        intro t
        simp only [G]
        rw [show ((b : ℂ) + (t : ℂ) * I) * (u : ℂ) = (b : ℂ) * u + ((t * u : ℝ) : ℂ) * I by
          push_cast; ring, Complex.exp_add]
        ring
      simp_rw [hpt]
      rw [integral_const_mul, ← mul_smul_comm, ← hcomp]
      have hone : cexp ((b : ℂ) * u) * cexp (-(b : ℂ) * u) = 1 := by
        rw [← Complex.exp_add]; simp
      rw [mul_comm ((ZetaRamp.rampH u : ℝ) : ℂ), ← mul_assoc, hone, one_mul]
    set T : ℝ := Real.exp (8 * u) with hT_def
    have hT_pos : 0 < T := Real.exp_pos _
    have hTT : -T ≤ T := by linarith
    set f : ℂ → ℂ := fun s => ZetaRamp.psi s * cexp (s * u)
    have hbd_strip : ∀ x y : ℝ, θ ≤ x → x ≤ b →
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * (1 + |y|) ^ (-(3 / 2) : ℝ) * Real.exp (x * u) := by
      intro x y hx1 hx2
      have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
      have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
      have hre_mul : (((x : ℂ) + (y : ℂ) * I) * u).re = x * u := by simp
      dsimp [f]
      rw [norm_mul, Complex.norm_exp, hre_mul]
      have hp := hB _ (by rw [hre]; exact hx1) (by rw [hre]; exact hx2.trans hb2)
      rw [him] at hp
      exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    have hI32 := ZetaRamp.integrable_J (r := 3 / 2) (by norm_num)
    have hI54 := ZetaRamp.integrable_J (r := 5 / 4) (by norm_num)
    have hfcont : Continuous fun t : ℝ => f ((b : ℂ) + (t : ℂ) * I) :=
      hcont_line.mul (by fun_prop)
    have hfi : Integrable fun t : ℝ => f ((b : ℂ) + (t : ℂ) * I) :=
      Integrable.mono' ((hI32.const_mul B).mul_const (Real.exp (b * u)))
        hfcont.aestronglyMeasurable (ae_of_all _ fun t => hbd_strip b t hθb le_rfl)
    have hsplit : (∫ t in Ioc (-T) T, f ((b : ℂ) + (t : ℂ) * I))
        + ∫ t in (Ioc (-T) T)ᶜ, f ((b : ℂ) + (t : ℂ) * I)
        = ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I) := integral_add_compl measurableSet_Ioc hfi
    have htail : ‖∫ t in (Ioc (-T) T)ᶜ, f ((b : ℂ) + (t : ℂ) * I)‖
        ≤ B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * ZetaRamp.J (5 / 4) := by
      have hbd : Integrable fun t : ℝ =>
          B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) :=
        hI54.const_mul _
      refine (ZetaRamp.norm_setIntegral_le_of_bound measurableSet_Ioc.compl hbd
        (fun _ => by positivity) fun t ht => ?_).trans (le_of_eq ?_)
      · have htT : T ≤ |t| := by
          rw [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
          rcases ht with ht | ht
          · exact (by linarith : T ≤ -t).trans (neg_le_abs t)
          · exact ht.le.trans (le_abs_self t)
        have hpow : (1 + |t|) ^ (-(3 / 2) : ℝ)
            ≤ (1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
          have h1 : (1 + |t|) ^ (-(3 / 2) : ℝ)
              = (1 + |t|) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
            rw [← Real.rpow_add (by positivity)]
            congr 1; norm_num
          rw [h1]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num))
            (Real.rpow_nonneg (by positivity) _)
        calc ‖f ((b : ℂ) + (t : ℂ) * I)‖
            ≤ B * (1 + |t|) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) := hbd_strip b t hθb le_rfl
          _ ≤ B * ((1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ)) * Real.exp (b * u) := by
              gcongr
          _ = B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
              ring
      · rw [integral_const_mul]; rfl
    have Hdiff : DifferentiableOn ℂ f ([[θ, b]] ×ℂ [[-T, T]]) := by
      intro s hs
      rw [mem_reProdIm, uIcc_of_le hθb, uIcc_of_le hTT] at hs
      exact ((han s hs.1.1).differentiableAt.mul (by fun_prop)).differentiableWithinAt
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ⟨θ, -T⟩ ⟨b, T⟩ Hdiff
    dsimp only at hrect
    have hbot : ‖∫ x in θ..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        ≤ B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - θ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [uIoc_of_le hθb] at hx
      have h1 := hbd_strip x (-T) hx.1.le hx.2
      rw [abs_neg, abs_of_pos hT_pos] at h1
      refine h1.trans ?_
      gcongr
      exact hx.2
    have htop : ‖∫ x in θ..b, f ((x : ℂ) + (T : ℂ) * I)‖
        ≤ B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - θ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [uIoc_of_le hθb] at hx
      have h1 := hbd_strip x T hx.1.le hx.2
      rw [abs_of_pos hT_pos] at h1
      refine h1.trans ?_
      gcongr
      exact hx.2
    have hleft : ‖∫ y in (-T)..T, f ((θ : ℂ) + (y : ℂ) * I)‖
        ≤ B * Real.exp (θ * u) * ZetaRamp.J (3 / 2) := by
      rw [intervalIntegral.integral_of_le hTT]
      have hbd : Integrable fun t : ℝ =>
          B * Real.exp (θ * u) * (1 + |t|) ^ (-(3 / 2) : ℝ) := hI32.const_mul _
      refine (ZetaRamp.norm_setIntegral_le_of_bound measurableSet_Ioc hbd
        (fun _ => by positivity) fun t _ => ?_).trans (le_of_eq ?_)
      · exact (hbd_strip θ t le_rfl hθb).trans_eq (by ring)
      · rw [integral_const_mul]; rfl
    have hmid : ‖∫ t in Ioc (-T) T, f ((b : ℂ) + (t : ℂ) * I)‖
        ≤ ‖∫ y in (-T)..T, f ((θ : ℂ) + (y : ℂ) * I)‖
          + ‖∫ x in θ..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
          + ‖∫ x in θ..b, f ((x : ℂ) + (T : ℂ) * I)‖ := by
      rw [← intervalIntegral.integral_of_le hTT]
      simp only [smul_eq_mul] at hrect
      have e : I * (∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * I))
          = I * (∫ y in (-T)..T, f ((θ : ℂ) + (y : ℂ) * I))
            - (∫ x in θ..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
            + ∫ x in θ..b, f ((x : ℂ) + (T : ℂ) * I) := by
        linear_combination hrect
      calc ‖∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * I)‖
          = ‖I * (∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * I))‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
        _ ≤ ‖I * (∫ y in (-T)..T, f ((θ : ℂ) + (y : ℂ) * I))‖
            + ‖∫ x in θ..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
            + ‖∫ x in θ..b, f ((x : ℂ) + (T : ℂ) * I)‖ := by
            rw [e]
            exact (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
        _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
    have hT_decay : Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) ≤ Real.exp (θ * u) := by
      have h1 : (1 + T) ^ (-(1 / 4) : ℝ) ≤ T ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hT_pos (by linarith) (by norm_num)
      have h2 : T ^ (-(1 / 4) : ℝ) = Real.exp (-2 * u) := by
        rw [hT_def, ← Real.exp_mul]; congr 1; ring
      calc Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ)
          ≤ Real.exp (b * u) * Real.exp (-2 * u) :=
            mul_le_mul_of_nonneg_left (h1.trans_eq h2) (Real.exp_pos _).le
        _ = Real.exp (-(u / 2)) := by rw [← Real.exp_add]; congr 1; dsimp [b]; ring
        _ ≤ Real.exp (θ * u) := Real.exp_le_exp.mpr (by nlinarith)
    have hT32_le : (1 + T) ^ (-(3 / 2) : ℝ) ≤ (1 + T) ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hbθ_le1 : |b - θ| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]; dsimp [b]; linarith
    have hpi : (2 * Real.pi)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; linarith [Real.pi_gt_three]
    have habs : |ZetaRamp.rampH u| ≤ ‖∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I)‖ := by
      have h0 : |ZetaRamp.rampH u| = ‖((ZetaRamp.rampH u : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [h0, hinv_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (norm_nonneg _) hpi
    have hJ54 := ZetaRamp.J_nonneg (5 / 4)
    have hside_le : B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - θ| ≤
        B * Real.exp (θ * u) := by
      calc B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - θ|
          ≤ B * (1 + T) ^ (-(1 / 4) : ℝ) * Real.exp (b * u) * 1 := by gcongr
        _ = B * (Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ)) := by ring
        _ ≤ B * Real.exp (θ * u) := mul_le_mul_of_nonneg_left hT_decay hB_pos.le
    have htail_le : B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * ZetaRamp.J (5 / 4) ≤
        B * Real.exp (θ * u) * ZetaRamp.J (5 / 4) := by
      calc B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * ZetaRamp.J (5 / 4)
          = B * ZetaRamp.J (5 / 4) * (Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ)) := by ring
        _ ≤ B * ZetaRamp.J (5 / 4) * Real.exp (θ * u) :=
            mul_le_mul_of_nonneg_left hT_decay (by positivity)
        _ = B * Real.exp (θ * u) * ZetaRamp.J (5 / 4) := by ring
    have hsum_all : ‖∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I)‖ ≤ K_H * Real.exp (θ * u) := by
      rw [← hsplit]
      refine (norm_add_le _ _).trans ?_
      dsimp [K_H]
      linarith [hmid, hleft, hbot, htop, hside_le, htail, htail_le]
    exact habs.trans hsum_all
  -- Extend from `u > 0` to `u ≥ 0` by continuity of `rampH` at `0`
  have hrampH_nonneg : ∀ u : ℝ, 0 ≤ u → |ZetaRamp.rampH u| ≤ K_H * Real.exp (θ * u) := by
    intro u hu
    rcases eq_or_lt_of_le hu with rfl | hu_pos
    · let seq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
      have hlim : Tendsto seq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hlhs : Tendsto (fun n => |ZetaRamp.rampH (seq n)|) atTop (𝓝 |ZetaRamp.rampH 0|) :=
        (ZetaRamp.continuous_rampH.abs.tendsto 0).comp hlim
      have hrhs : Tendsto (fun n => K_H * Real.exp (θ * seq n)) atTop
          (𝓝 (K_H * Real.exp (θ * 0))) :=
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul K_H |>.tendsto 0).comp hlim
      refine le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall fun n => ?_)
      exact hrampH_pos (seq n) (by dsimp [seq]; positivity)
    · exact hrampH_pos u hu_pos
  refine ⟨K_H + 2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  set u : ℝ := Real.log x
  have hu0 : 0 ≤ u := Real.log_nonneg hx
  have hexp_u : Real.exp u = x := Real.exp_log hx0
  have hexp_θu : Real.exp (θ * u) = x ^ θ := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  have hG_eq : IndependentLandau.rampG x =
      ZetaRamp.rampH u + (1 + Real.eulerMascheroniConstant) * Real.exp (-u) := by
    rw [← hexp_u]; unfold ZetaRamp.rampH; ring
  have hsec : |(1 + Real.eulerMascheroniConstant) * Real.exp (-u)| ≤ 2 * Real.exp (θ * u) := by
    have hγ0 := Real.one_half_lt_eulerMascheroniConstant
    have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
    rw [abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le)]
    calc (1 + Real.eulerMascheroniConstant) * Real.exp (-u)
        ≤ 2 * Real.exp (-u) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ 2 * Real.exp (θ * u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)
  rw [hG_eq, ← hexp_θu]
  calc |ZetaRamp.rampH u + (1 + Real.eulerMascheroniConstant) * Real.exp (-u)|
      ≤ |ZetaRamp.rampH u| + |(1 + Real.eulerMascheroniConstant) * Real.exp (-u)| := abs_add_le _ _
    _ ≤ K_H * Real.exp (θ * u) + 2 * Real.exp (θ * u) := add_le_add (hrampH_nonneg u hu0) hsec
    _ = (K_H + 2) * Real.exp (θ * u) := by ring

/-! ### 3. Three-Way Collapse Theorem & Riemann Hypothesis Equivalence -/

/-- **Single-Window to Global Two-Sided Collapse:**
A one-sided unit upper bound `rampG x ≤ x^θ` on cofinally many `[Y, Y^(3/2)]` windows at a single
exponent `θ ∈ [1/2, 1)` forces a global **two-sided** bound `|rampG x| ≤ C * x^{θ'}` at **every**
`x ≥ 1` for every `θ' ∈ (θ, 1)`. -/
theorem abs_rampG_of_single_ordinaryWindowUnit {θ θ' : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθθ' : θ < θ') (hθ'1 : θ' < 1) (hW : OrdinaryWindowUnit θ) :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |IndependentLandau.rampG x| ≤ C * x ^ θ' :=
  abs_rampG_le_of_zeroFree hθ hθθ' hθ'1
    (zeta_zeroFree_of_ordinaryWindowUnit (by linarith) (hθθ'.trans hθ'1) hW)

/-- **Three-Way Collapse Theorem (`ordinaryWindow_three_way_iff`):**
For any `θ₀ ∈ [1/2, 1)`, the following three conditions are logically equivalent:
1. `∀ θ ∈ Set.Ioo θ₀ 1, OrdinaryWindowUnit θ` (one-sided `rampG x ≤ x^θ` on cofinal `[Y, Y^(3/2)]`),
2. `∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0` (zero-free half-plane `Re s > θ₀`),
3. `∀ θ ∈ Set.Ioo θ₀ 1, ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |rampG x| ≤ C * x ^ θ` (global two-sided bound). -/
theorem ordinaryWindow_three_way_iff {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ((∀ θ ∈ Set.Ioo θ₀ 1, OrdinaryWindowUnit θ) ↔
      (∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0)) ∧
    ((∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) ↔
      (∀ θ ∈ Set.Ioo θ₀ 1, ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |IndependentLandau.rampG x| ≤ C * x ^ θ)) := by
  obtain ⟨hθ₀_lo, hθ₀_hi⟩ := hθ₀
  have h12 : (∀ θ ∈ Set.Ioo θ₀ 1, OrdinaryWindowUnit θ) →
      (∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) := by
    intro hW s hs
    rcases le_or_gt 1 s.re with hs1 | hs1
    · exact riemannZeta_ne_zero_of_one_le_re hs1
    · let θ : ℝ := (θ₀ + s.re) / 2
      have hθ_mem : θ ∈ Set.Ioo θ₀ 1 := ⟨by dsimp [θ]; linarith, by dsimp [θ]; linarith⟩
      exact zeta_zeroFree_of_ordinaryWindowUnit (by linarith [hθ_mem.1]) hθ_mem.2
        (hW θ hθ_mem) s (by dsimp [θ]; linarith)
  have h23 : (∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0) →
      (∀ θ ∈ Set.Ioo θ₀ 1, ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |IndependentLandau.rampG x| ≤ C * x ^ θ) :=
    fun hz θ hθ => abs_rampG_le_of_zeroFree hθ₀_lo hθ.1 hθ.2 hz
  have h31 : (∀ θ ∈ Set.Ioo θ₀ 1, ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |IndependentLandau.rampG x| ≤ C * x ^ θ) →
      (∀ θ ∈ Set.Ioo θ₀ 1, OrdinaryWindowUnit θ) := by
    intro hG θ hθ Y₀
    let θ₁ : ℝ := (θ₀ + θ) / 2
    have hθ₁_mem : θ₁ ∈ Set.Ioo θ₀ 1 := ⟨by dsimp [θ₁]; linarith [hθ.1], by dsimp [θ₁]; linarith [hθ.2]⟩
    have hgap : 0 < θ - θ₁ := by dsimp [θ₁]; linarith [hθ.1]
    obtain ⟨C, hC, hbd⟩ := hG θ₁ hθ₁_mem
    let Y : ℝ := max (max Y₀ 1) (C ^ (1 / (θ - θ₁)))
    have hY_Y₀ : Y₀ ≤ Y := (le_max_left Y₀ 1).trans (le_max_left _ _)
    have hY_one : 1 ≤ Y := (le_max_right Y₀ 1).trans (le_max_left _ _)
    have hY_C : C ^ (1 / (θ - θ₁)) ≤ Y := le_max_right _ _
    refine ⟨Y, hY_Y₀, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := hY_one.trans hx.1
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hC_le : C ≤ x ^ (θ - θ₁) := by
      have hpow := Real.rpow_le_rpow (by positivity) (hY_C.trans hx.1) hgap.le
      rwa [← Real.rpow_mul hC.le, one_div_mul_cancel hgap.ne', Real.rpow_one] at hpow
    calc IndependentLandau.rampG x
        ≤ |IndependentLandau.rampG x| := le_abs_self _
      _ ≤ C * x ^ θ₁ := hbd x hx1
      _ ≤ x ^ (θ - θ₁) * x ^ θ₁ := mul_le_mul_of_nonneg_right hC_le (Real.rpow_nonneg hx0.le _)
      _ = x ^ θ := by rw [← Real.rpow_add hx0, sub_add_cancel]
  exact ⟨⟨h12, fun hz => h31 (h23 hz)⟩, ⟨h23, fun hG => h12 (h31 hG)⟩⟩

/-- `List.TFAE` formulation of `ordinaryWindow_three_way_iff`. -/
theorem ordinaryWindow_three_way_tfae {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    List.TFAE
      [ ∀ θ ∈ Set.Ioo θ₀ 1, OrdinaryWindowUnit θ
      , ∀ s : ℂ, θ₀ < s.re → riemannZeta s ≠ 0
      , ∀ θ ∈ Set.Ioo θ₀ 1, ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |IndependentLandau.rampG x| ≤ C * x ^ θ ] := by
  obtain ⟨h12, h23⟩ := ordinaryWindow_three_way_iff hθ₀
  tfae_have 1 ↔ 2 := h12
  tfae_have 2 ↔ 3 := h23
  tfae_finish

/-- **Riemann Hypothesis Window Equivalence (`rh_iff_ordinaryWindowUnit_above_half`):**
`RiemannHypothesis` holds if and only if `OrdinaryWindowUnit θ` holds for every `θ ∈ (1/2, 1)`. -/
theorem rh_iff_ordinaryWindowUnit_above_half :
    RiemannHypothesis ↔ ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1, OrdinaryWindowUnit θ := by
  have h12 := (ordinaryWindow_three_way_iff (θ₀ := 1 / 2) ⟨le_rfl, by norm_num⟩).1
  rw [h12]
  refine ⟨?_, fun h => RiemannReduction.rh_of_right fun s hs _ => h s hs⟩
  intro rh s hs hz
  have hnt : ¬∃ k : ℕ, s = -2 * (k + 1) := by
    rintro ⟨k, rfl⟩
    simp at hs
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpole : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  exact (ne_of_gt hs) (rh s hz hnt hpole)

end DirectRampEquivalence

export DirectRampEquivalence (
  OrdinaryWindow
  OrdinaryWindowUnit
  ordinaryWindow_of_unit
  windowHypU_of_ordinaryWindow
  zeta_zeroFree_of_ordinaryWindow
  zeta_zeroFree_of_ordinaryWindowUnit
  abs_rampG_le_of_zeroFree
  abs_rampG_of_single_ordinaryWindowUnit
  ordinaryWindow_three_way_iff
  ordinaryWindow_three_way_tfae
  rh_iff_ordinaryWindowUnit_above_half
)

#print axioms zeta_zeroFree_of_ordinaryWindow
#print axioms zeta_zeroFree_of_ordinaryWindowUnit
#print axioms abs_rampG_le_of_zeroFree
#print axioms ordinaryWindow_three_way_iff
#print axioms rh_iff_ordinaryWindowUnit_above_half
