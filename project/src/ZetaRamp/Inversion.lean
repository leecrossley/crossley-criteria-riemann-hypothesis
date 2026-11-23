import Mathlib
import ZetaRamp.Transform

/-! Fourier inversion on a vertical line `re s = b`, `1 < b ≤ 2`:
`rampH u = (1 / 2π) ∫ psi (b + it) exp ((b + it) u) dt` for `u > 0`. -/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace ZetaRamp

open IndependentLandau ZetaShared

/-! ### Continuity of the ramp -/

lemma continuous_rampT (n : ℕ) : Continuous (rampT n) := by
  unfold rampT
  exact continuous_const.mul
    (((continuous_id.div_const _).sub continuous_const).max continuous_const)

lemma continuous_rampS : Continuous rampS := by
  rw [continuous_iff_continuousAt]
  intro y₀
  have hev : (fun y => ∑ n ∈ Finset.range (⌊y₀⌋₊ + 1), rampT n y) =ᶠ[𝓝 y₀] rampS := by
    have hlt : y₀ < (⌊y₀⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y₀
    filter_upwards [Iio_mem_nhds hlt] with y hy
    rw [rampS_eq_tsum]
    symm
    refine tsum_eq_sum fun n hn => ?_
    apply rampT_eq_zero_of_floor_lt
    have h1 : ⌊y⌋₊ < ⌊y₀⌋₊ + 1 :=
      (Nat.floor_lt' (Nat.succ_ne_zero _)).mpr (by push_cast; exact hy)
    have h2 : ⌊y₀⌋₊ + 1 ≤ n := by simpa using hn
    omega
  exact ContinuousAt.congr
    (continuous_finsetSum _ fun n _ => continuous_rampT n).continuousAt hev

lemma continuous_rampG : Continuous rampG := by
  have : rampG = fun y => rampS y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y :=
    funext rampG_eq
  rw [this]
  exact (continuous_rampS.sub Real.continuous_mul_log).add (continuous_const.mul continuous_id)

lemma continuous_rampH : Continuous rampH := by
  unfold rampH
  exact (continuous_rampG.comp Real.continuous_exp).sub
    (continuous_const.mul (Real.continuous_exp.comp continuous_neg))

/-! ### Points of the region -/

lemma mem_region_of_le {c : ℝ} (hc : 0 < c) {x y T : ℝ} (hy : |y| ≤ T)
    (hx : 1 - c / Real.log (T + 2) ≤ x) : (x : ℂ) + (y : ℂ) * I ∈ region c := by
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  show 1 - c / Real.log (|((x : ℂ) + (y : ℂ) * I).im| + 2) ≤ ((x : ℂ) + (y : ℂ) * I).re
  rw [him, hre]
  have hL := half_lt_log_abs_add_two y
  have hLT : Real.log (|y| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have : c / Real.log (T + 2) ≤ c / Real.log (|y| + 2) :=
    div_le_div_of_nonneg_left hc.le (by linarith) hLT
  linarith

lemma line_mem_region {c : ℝ} (hc : 0 < c) {b : ℝ} (hb : 1 ≤ b) (t : ℝ) :
    (b : ℂ) + (t : ℂ) * I ∈ region c := by
  refine mem_region_of_le hc le_rfl ?_
  have hL := half_lt_log_abs_add_two t
  have : 0 ≤ c / Real.log (|t| + 2) := div_nonneg hc.le (by linarith)
  linarith

lemma norm_psi_line_le {c B : ℝ}
    (hB : ∀ s ∈ region c, s.re ≤ 2 → ‖psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ))
    {x y : ℝ} (hmem : (x : ℂ) + (y : ℂ) * I ∈ region c) (hx : x ≤ 2) :
    ‖psi ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * (1 + |y|) ^ (-(3 / 2) : ℝ) := by
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have := hB _ hmem (by rw [hre]; exact hx)
  rwa [him] at this

lemma continuous_psi_line {c C : ℝ} (h : RegionData c C) (hc : c ≤ 1 / 4) {b : ℝ}
    (hb : 1 ≤ b) : Continuous fun t : ℝ => psi ((b : ℂ) + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h1 : ContinuousAt psi ((b : ℂ) + (t : ℂ) * I) :=
    (analyticAt_psi h hc (line_mem_region h.c_pos hb t)).continuousAt
  have h2 : ContinuousAt (fun t : ℝ => (b : ℂ) + (t : ℂ) * I) t := by fun_prop
  exact ContinuousAt.comp (g := psi) h1 h2

/-! ### The function to invert -/

/-- `rampH u exp (-b u)` on `u > 0`, extended by zero. -/
def invF (b : ℝ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (fun u => ((rampH u : ℝ) : ℂ) * cexp (-(b : ℂ) * u))

lemma integrable_invF {b : ℝ} (hb : 1 < b) : Integrable (invF b) :=
  (laplace_rampH (s := (b : ℂ)) (by simpa using hb)).1.integrable_indicator measurableSet_Ioi

lemma continuousAt_invF (b : ℝ) {u : ℝ} (hu : 0 < u) : ContinuousAt (invF b) u := by
  have hc : Continuous (fun u : ℝ => ((rampH u : ℝ) : ℂ) * cexp (-(b : ℂ) * u)) :=
    (Complex.continuous_ofReal.comp continuous_rampH).mul (by fun_prop)
  refine hc.continuousAt.congr ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  have e : invF b v = ((rampH v : ℝ) : ℂ) * cexp (-(b : ℂ) * v) := indicator_of_mem hv _
  exact e.symm

lemma fourier_invF {b : ℝ} (hb : 1 < b) (w : ℝ) :
    𝓕 (invF b) w = psi ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have key : ∀ v : ℝ, cexp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) • invF b v =
      (Ioi (0 : ℝ)).indicator (fun u : ℝ => ((rampH u : ℝ) : ℂ) *
        cexp (-((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) * u)) v := by
    intro v
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · have e1 : invF b v = ((rampH v : ℝ) : ℂ) * cexp (-(b : ℂ) * v) := indicator_of_mem hv _
      have e2 : cexp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) * cexp (-(b : ℂ) * v)
          = cexp (-((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) * v) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [e1, indicator_of_mem hv, smul_eq_mul, ← e2]
      ring
    · have e1 : invF b v = 0 := indicator_of_notMem hv _
      rw [e1, indicator_of_notMem hv, smul_zero]
  simp_rw [key]
  rw [integral_indicator measurableSet_Ioi]
  have hre : ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I).re = b := by simp
  exact (laplace_rampH (by rw [hre]; exact hb)).2

section

variable {c C B : ℝ}

lemma integrable_fourier_invF (h : RegionData c C) (hc : c ≤ 1 / 4) (hB0 : 0 ≤ B)
    (hB : ∀ s ∈ region c, s.re ≤ 2 → ‖psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ))
    {b : ℝ} (hb : 1 < b) (hb2 : b ≤ 2) : Integrable (𝓕 (invF b)) := by
  have e : 𝓕 (invF b) = fun w : ℝ => psi ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) :=
    funext (fourier_invF hb)
  rw [e]
  have hcont : Continuous fun w : ℝ => psi ((b : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) :=
    (continuous_psi_line h hc hb.le).comp (continuous_const.mul continuous_id)
  have hJ : Integrable (fun w : ℝ => B * (1 + ‖w‖) ^ (-(3 / 2) : ℝ)) :=
    (integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)).const_mul B
  refine hJ.mono' hcont.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  refine (norm_psi_line_le hB (line_mem_region h.c_pos hb.le _) hb2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hB0
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
  have h2 : (1 : ℝ) ≤ |2 * Real.pi| := by
    rw [abs_of_pos (by positivity)]; linarith [Real.pi_gt_three]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [abs_nonneg w]

/-- Fourier inversion on the line `re s = b`. -/
theorem inversion (h : RegionData c C) (hc : c ≤ 1 / 4) (hB0 : 0 ≤ B)
    (hB : ∀ s ∈ region c, s.re ≤ 2 → ‖psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ))
    {b u : ℝ} (hb : 1 < b) (hb2 : b ≤ 2) (hu : 0 < u) :
    ((rampH u : ℝ) : ℂ) = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t : ℝ, psi ((b : ℂ) + (t : ℂ) * I) * cexp (((b : ℂ) + (t : ℂ) * I) * u) := by
  have hinv := (integrable_invF hb).fourierInv_fourier_eq
    (integrable_fourier_invF h hc hB0 hB hb hb2) (continuousAt_invF b hu)
  rw [Real.fourierInv_eq'] at hinv
  have hval : invF b u = ((rampH u : ℝ) : ℂ) * cexp (-(b : ℂ) * u) :=
    indicator_of_mem (mem_Ioi.mpr hu) _
  rw [hval] at hinv
  let G : ℝ → ℂ := fun t => cexp (((t * u : ℝ) : ℂ) * I) * psi ((b : ℂ) + (t : ℂ) * I)
  have hG : ∀ v : ℝ, cexp (((2 * Real.pi * inner ℝ v u : ℝ) : ℂ) * I) • 𝓕 (invF b) v
      = G (2 * Real.pi * v) := by
    intro v
    rw [fourier_invF hb, smul_eq_mul]
    have hin : inner ℝ v u = v * u := by simp [mul_comm]
    simp only [G, hin]
    rw [show 2 * Real.pi * (v * u) = 2 * Real.pi * v * u by ring]
  simp_rw [hG] at hinv
  have hcomp := Measure.integral_comp_mul_left G (2 * Real.pi)
  have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
  rw [habs, hinv] at hcomp
  have hpt : ∀ t : ℝ, psi ((b : ℂ) + (t : ℂ) * I) * cexp (((b : ℂ) + (t : ℂ) * I) * u)
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
  rw [mul_comm ((rampH u : ℝ) : ℂ), ← mul_assoc, hone, one_mul]

end

end ZetaRamp
