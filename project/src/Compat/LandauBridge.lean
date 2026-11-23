import Mathlib
import IndependentLandau.ZetaWindow
import Crossley.RealZeros

/-! First-party Landau window bridge for the Riemann zeta function.

Provides the ordinary-zeta ramp, pole data, real-interval nonvanishing, divided-difference
analyticity, Laplace derivative domination, logarithmic power comparison, and functional-equation
reflection directly on top of `IndependentLandau` and `Crossley.RealZeros`, with zero external
archive namespaces or character-family wrappers. -/

open scoped ArithmeticFunction.vonMangoldt
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace ZetaShared

abbrev PoleData := IndependentLandau.PoleData
abbrev WindowHypU := IndependentLandau.WindowHypU
abbrev rampS := IndependentLandau.rampS
abbrev rampG := IndependentLandau.rampG
abbrev zetaZeros := IndependentLandau.zetaZeros

/-- Centred von Mangoldt ramp of `riemannZeta` in the logarithmic variable `u = log y`. -/
def zetaLogRamp (u : ℝ) : ℝ := IndependentLandau.rampG (Real.exp u)

/-- Pole data for `zetaLogRamp` on `zetaZeros = {ρ | 0 < ρ.re ∧ riemannZeta ρ = 0}`. -/
theorem zeta_poleData : ∃ Φ : ℂ → ℂ, PoleData zetaLogRamp Φ zetaZeros :=
  IndependentLandau.zeta_poleData

/-- Window form of Landau's oscillation theorem. -/
theorem landau_window {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : PoleData g Φ Z) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hW : WindowHypU g θ δ) : ∀ ρ ∈ Z, ρ.re ≤ θ :=
  IndependentLandau.landau_window hP hθ hθ1 hδ hW

/-- Zeros of `riemannZeta` in `{Re s > 0}` satisfy `Re s < 1`. -/
theorem zetaZeros_strip : ∀ ρ ∈ zetaZeros, ρ.re < 1 := by
  rintro ρ ⟨_, hz⟩
  by_contra! h
  exact riemannZeta_ne_zero_of_one_le_re h hz

/-- `riemannZeta` has no zeros on the open real unit interval `(0, 1)`. -/
theorem zeta_ne_zero_of_mem_Ioo (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 :=
  Crossley.riemannZeta_ne_zero_of_mem_Ioo h0 h1

/-- Nontrivial zeros of `riemannZeta` in `{Re s > 0}` have nonzero imaginary part. -/
theorem zetaZeros_not_real : ∀ z ∈ zetaZeros, z.im ≠ 0 := by
  intro z hz hi
  have hlt := zetaZeros_strip z hz
  obtain ⟨hp, he⟩ := hz
  have hne := zeta_ne_zero_of_mem_Ioo z.re hp hlt
  have ee : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hi])
  rw [ee] at hne
  exact hne he

/-- Divided difference `dslope f a` at `a` preserves analyticity at `a`. -/
theorem poleData_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

theorem iteratedDeriv_laplace_int (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ))
    (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) one_pos hb
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

theorem iteratedDeriv_laplace_bound (g : ℝ → ℝ) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (b : ℝ) (z : ℂ)
    (hz : 2 + b ≤ z.re) (u : ℝ) (hu : 0 < u) :
    ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u)‖ ≤ C * (u ^ k * Real.exp (-b * u)) := by
  have hre : (-z * (u : ℂ)).re = -z.re * u := by simp
  have hC : 0 ≤ C := by
    have h := hgC 0 le_rfl
    simpa using (abs_nonneg (g 0)).trans h
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_neg, abs_of_pos hu, Complex.norm_exp, hre]
  have h1 : |g u| * u ^ k * Real.exp (-z.re * u) ≤
      C * Real.exp (2 * u) * u ^ k * Real.exp (-z.re * u) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hgC u hu.le) (pow_nonneg hu.le k))
      (Real.exp_pos _).le
  have h2 : Real.exp (2 * u) * Real.exp (-z.re * u) ≤ Real.exp (-b * u) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc |g u| * u ^ k * Real.exp (-z.re * u)
      ≤ C * Real.exp (2 * u) * u ^ k * Real.exp (-z.re * u) := h1
    _ = C * u ^ k * (Real.exp (2 * u) * Real.exp (-z.re * u)) := by ring
    _ ≤ C * u ^ k * Real.exp (-b * u) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC (pow_nonneg hu.le k))
    _ = C * (u ^ k * Real.exp (-b * u)) := by ring

/-- Eventually `K * log Y ≤ Y ^ η` for any `K ≥ 0` and `η > 0`. -/
theorem windowHyp_of_rpow_eventually (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → 1 ≤ Y ∧ K * Real.log Y ≤ Y ^ η := by
  have hb := (isLittleO_log_rpow_atTop hη).bound (show (0 : ℝ) < 1 / (K + 1) by positivity)
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.mp (hb.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨Y₁, fun Y hY => ?_⟩
  obtain ⟨h, h1⟩ := hY₁ Y hY
  refine ⟨h1, ?_⟩
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg h1
  have hpow : 0 ≤ Y ^ η := Real.rpow_nonneg (by linarith) η
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] at h
  have hK1 : 0 < K + 1 := by linarith
  have h' : (K + 1) * Real.log Y ≤ Y ^ η := by
    have := mul_le_mul_of_nonneg_left h hK1.le
    rwa [← mul_assoc, mul_one_div_cancel hK1.ne', one_mul] at this
  nlinarith

namespace Reflection

private theorem completed_zero {s : ℂ} (hz : riemannZeta s = 0)
    (ht : ¬ ∃ n : ℕ, s = -2 * (n + 1)) : completedRiemannZeta s = 0 := by
  have hs : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  have hg : Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
    cases n with
    | zero => exact hs (by simpa using hn)
    | succ k => exact ht ⟨k, by simpa [Nat.cast_succ, neg_mul] using hn⟩
  exact (div_eq_zero_iff.mp ((riemannZeta_def_of_ne_zero hs).symm.trans hz)).resolve_right hg

/-- Functional-equation reflection from `{Re s > 1 / 2}` to `RiemannHypothesis`. -/
theorem rh_of_right (right : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz ht h1
  refine le_antisymm (not_lt.mp fun h => right s h h1 hz) ?_
  by_contra! h
  have h0 : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  apply right (1 - s) (by simp [Complex.sub_re]; linarith) (by intro e; apply h0; linear_combination -e)
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr h1.symm), completedRiemannZeta_one_sub,
    completed_zero hz ht, zero_div]

end Reflection

end ZetaShared
