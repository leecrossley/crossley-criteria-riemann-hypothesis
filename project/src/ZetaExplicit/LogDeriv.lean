import Mathlib
import ZetaShared.Perron
import IndependentLandau.Analytic
import ZetaCount.Order

/-! Facts about `ζ'/ζ` and the Perron integrand used in the contour shift. -/

open Complex Set Filter Topology ComplexConjugate
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

noncomputable section
namespace ZetaExplicit

open ZetaShared

lemma zeta₁_order_ne_top (z : ℂ) : analyticOrderAt riemannZeta₁ z ≠ ⊤ := by
  rw [Ne, analyticOrderAt_eq_top]
  exact IndependentLandau.zeta₁_not_eventually_zero z

/-- `ζ'/ζ = Z'/Z - 1/(s - 1)` with `Z s = (s - 1) ζ(s)`. -/
lemma logDeriv_zeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannZeta₁ s / riemannZeta₁ s - 1 / (s - 1) := by
  have hZ : riemannZeta₁ s ≠ 0 := fun h => hz (IndependentLandau.zeta₁_eq_zero_iff.mp h)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hev : riemannZeta =ᶠ[𝓝 s] fun w => riemannZeta₁ w / (w - 1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    rw [IndependentLandau.zeta₁_eq hw]
    field_simp
  have h1 : logDeriv riemannZeta s = logDeriv (fun w => riemannZeta₁ w / (w - 1)) s :=
    (logDeriv_congr_nhds hev).eq_of_nhds
  have h2 := logDeriv_div s (f := riemannZeta₁) (g := fun w => w - 1) hZ hs1
    (differentiable_riemannZeta₁ s) (by fun_prop)
  have h3 : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    simp [logDeriv_apply]
  rw [← logDeriv_apply, ← logDeriv_apply, h1, h2, h3]

/-- On `re s > 1` the logarithmic derivative is dominated by its value at the real part. -/
lemma norm_logDeriv_le_real {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ := by
  have hs' : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'
  have e1 : ‖deriv riemannZeta s / riemannZeta s‖ = ‖L ↗Λ s‖ := by
    rw [h1, neg_div, norm_neg]
  have e2 : ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ = ‖L ↗Λ (s.re : ℂ)‖ := by
    rw [h2, neg_div, norm_neg]
  rw [e1, e2]
  have hsum : Summable (fun n => ‖LSeries.term ↗Λ s n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  have hterm : ∀ n, LSeries.term ↗Λ (s.re : ℂ) n = ((‖LSeries.term ↗Λ s n‖ : ℝ) : ℂ) := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.term_def]
    split_ifs with h
    · simp
    · rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      push_cast
      rw [ofReal_cpow (Nat.cast_nonneg n)]
      simp
  calc ‖L ↗Λ s‖ ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ = ‖L ↗Λ (s.re : ℂ)‖ := by
      unfold LSeries
      simp_rw [hterm]
      rw [← Complex.ofReal_tsum, Complex.norm_real,
        Real.norm_of_nonneg (tsum_nonneg fun n => norm_nonneg _)]

/-- `|ζ'/ζ(σ)| ≤ 1/(σ - 1) + M` for real `1 < σ ≤ 3`. -/
lemma exists_bound_real : ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 3 →
    ‖deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ ≤ 1 / (σ - 1) + M := by
  have hc : ContinuousOn (fun σ : ℝ => deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ))
      (Icc 1 3) := by
    intro σ hσ
    have hne : riemannZeta₁ (σ : ℂ) ≠ 0 := by
      rw [Ne, IndependentLandau.zeta₁_eq_zero_iff]
      exact riemannZeta_ne_zero_of_one_le_re (by simpa using hσ.1)
    have h1 : ContinuousAt (deriv riemannZeta₁) (σ : ℂ) :=
      (IndependentLandau.analyticAt_zeta₁ _).deriv.continuousAt
    have h2 : ContinuousAt riemannZeta₁ (σ : ℂ) := (differentiable_riemannZeta₁ _).continuousAt
    have h3 : ContinuousAt (fun z : ℂ => deriv riemannZeta₁ z / riemannZeta₁ z) (σ : ℂ) :=
      h1.div h2 hne
    exact (h3.comp continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 ⟨le_rfl, by norm_num⟩)
  refine ⟨M, hM0, fun σ h1 h3 => ?_⟩
  have hne1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hz : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simpa using h1.le)
  rw [logDeriv_zeta_eq hne1 hz]
  have hn : ‖(1 : ℂ) / ((σ : ℂ) - 1)‖ = 1 / (σ - 1) := by
    rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, norm_div, norm_one,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  calc _ ≤ ‖deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)‖ + ‖(1 : ℂ) / ((σ : ℂ) - 1)‖ :=
        norm_sub_le _ _
    _ ≤ M + 1 / (σ - 1) := by rw [hn]; linarith [hM σ ⟨h1.le, h3⟩]
    _ = 1 / (σ - 1) + M := by ring

/-- `|ζ'/ζ(s)| ≤ 1/(re s - 1) + M` for `1 < re s ≤ 3`. -/
lemma exists_bound_right : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 3 →
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + M := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_real
  exact ⟨M, hM0, fun s h1 h3 => (norm_logDeriv_le_real h1).trans (hM s.re h1 h3)⟩

lemma deriv_zeta_conj (s : ℂ) : deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have hf : conj ∘ riemannZeta ∘ conj = riemannZeta := by
    funext z; simp [riemannZeta_conj]
  have h := deriv_conj_conj (f := riemannZeta)
  rw [hf] at h
  have := congrFun h (conj s)
  simpa using this

/-- The size of `ζ'/ζ` is symmetric under conjugation. -/
lemma norm_logDeriv_conj (s : ℂ) :
    ‖deriv riemannZeta (conj s) / riemannZeta (conj s)‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ := by
  rw [deriv_zeta_conj, riemannZeta_conj, ← map_div₀, Complex.norm_conj]

lemma norm_perronIntegrand {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ‖perronIntegrand u s‖ = ‖deriv riemannZeta s / riemannZeta s‖ * u ^ s.re / ‖s‖ := by
  unfold perronIntegrand
  rw [norm_div, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu]

lemma continuousAt_perronIntegrand {u : ℝ} (hu : 0 < u) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) : ContinuousAt (perronIntegrand u) s := by
  have hd : ContinuousAt (deriv riemannZeta) s := (ZetaCount.analyticAt_zeta h1).deriv.continuousAt
  have hζ : ContinuousAt riemannZeta s := (ZetaCount.analyticAt_zeta h1).continuousAt
  have hc : ContinuousAt (fun z : ℂ => (u : ℂ) ^ z) s :=
    continuousAt_const_cpow (by exact_mod_cast hu.ne')
  unfold perronIntegrand
  exact ((hd.div hζ hz).neg.mul hc).div continuousAt_id h0

lemma zeta_conj_ne_zero {s : ℂ} (h : riemannZeta s ≠ 0) : riemannZeta (conj s) ≠ 0 := by
  rw [riemannZeta_conj]; simpa using h

lemma zerosBelow_finite (T : ℝ) : (zerosBelow T).Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite).subset
    fun ρ hρ => ⟨?_, hρ.2.2.2⟩
  obtain ⟨h0, h1, h2, -⟩ := hρ
  rw [Metric.mem_closedBall, dist_zero_right]
  have h3 : |ρ.re| ≤ 1 := by rw [abs_of_pos h0]; exact h1.le
  have h4 : |ρ.im| ≤ |T| := h2.le.trans (le_abs_self T)
  linarith [Complex.norm_le_abs_re_add_abs_im ρ]

end ZetaExplicit

#print axioms ZetaExplicit.exists_bound_right
#print axioms ZetaExplicit.norm_logDeriv_conj
#print axioms ZetaExplicit.logDeriv_zeta_eq
