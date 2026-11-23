import Mathlib
import ZetaShared.Statements
import ZetaCount.Growth
import ZetaCount.Order

/-! Zeros with `1/2 ≤ re ρ < 1` in a unit window, counted with multiplicity, by Jensen's
inequality (`AnalyticOnNhd.sum_divisor_le`) applied to `riemannZeta₁` on discs centred at
`2 + it` of radii `1.81 < 1.95`. -/

open Complex Set Filter Topology Metric

noncomputable section
namespace ZetaCount

/-- Zeros in the right half of the window at height `t`. -/
def rightZeros (t : ℝ) : Set ℂ :=
  {ρ : ℂ | 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0}

lemma enat_map_untop₀ (n : ℕ∞) : ((n.map (Nat.cast : ℕ → ℤ)).untop₀ : ℤ) = (n.toNat : ℤ) := by
  induction n using ENat.recTopCoe <;> simp

lemma divisor_zeta₁ {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor riemannZeta₁ U z = (analyticOrderNatAt riemannZeta₁ z : ℤ) := by
  have hA : AnalyticOnNhd ℂ riemannZeta₁ U := fun w _ => IndependentLandau.analyticAt_zeta₁ w
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hA hz, enat_map_untop₀]; rfl

lemma rightZeros_subset_ball (t : ℝ) :
    rightZeros t ⊆ closedBall (2 + t * I : ℂ) |(1.81 : ℝ)| := by
  intro ρ hρ
  obtain ⟨h1, h2, h3, -⟩ := hρ
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 1.81)]
  have hsq : ‖ρ - (2 + t * I)‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h3' := abs_le.mp h3
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg (ρ - (2 + t * I))]

lemma rightZeros_finite (t : ℝ) : (rightZeros t).Finite := by
  refine ((isCompact_closedBall (2 + t * I : ℂ) |(1.81 : ℝ)|).inter_riemannZetaZeros_finite).subset
    fun ρ hρ => ⟨rightZeros_subset_ball t hρ, hρ.2.2.2⟩

/-- Jensen's inequality for the right half of the window. -/
theorem rightCount_le_log (t : ℝ) :
    ∑ᶠ ρ ∈ rightZeros t, (ZetaShared.mult ρ : ℝ) ≤
      Real.log (244 * (|t| + 2) ^ 2) / Real.log (1.95 / 1.81) := by
  set c : ℂ := 2 + t * I with hc
  have ha : 0 ≤ |t| := abs_nonneg t
  have e1 : |(1.81 : ℝ)| = 1.81 := abs_of_pos (by norm_num)
  have e2 : |(1.95 : ℝ)| = 1.95 := abs_of_pos (by norm_num)
  have hA : AnalyticOnNhd ℂ riemannZeta₁ (closedBall c |(1.95 : ℝ)|) :=
    fun w _ => IndependentLandau.analyticAt_zeta₁ w
  have hcge : 1 / 4 ≤ ‖riemannZeta₁ c‖ := norm_zeta₁_two_add_ge t
  have hc0 : riemannZeta₁ c ≠ 0 := by
    intro h; rw [h, norm_zero] at hcge; norm_num at hcge
  have hM : (1 : ℝ) ≤ 61 * (|t| + 2) ^ 2 := by nlinarith
  have hcn : ‖c‖ ≤ 2 + |t| := by
    calc ‖c‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
  have hcn1 : ‖c - 1‖ ≤ 1 + |t| := by
    have e : c - 1 = 1 + (t : ℂ) * I := by rw [hc]; ring
    rw [e]
    calc ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |t| := by simp
  have hbound : ∀ z ∈ sphere c |(1.95 : ℝ)|, ‖riemannZeta₁ z‖ ≤ 61 * (|t| + 2) ^ 2 := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, e2] at hz
    have hre : 1 / 20 ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - c)
      rw [hz] at h
      have h' := (abs_le.mp h).1
      have e : (z - c).re = z.re - 2 := by simp [hc]
      rw [e] at h'
      norm_num at h' ⊢
      linarith
    have hz1 : ‖z‖ ≤ |t| + 4 := by
      have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        have := norm_add_le (z - c) c
        rwa [sub_add_cancel] at this
      rw [hz] at this
      norm_num at this ⊢
      linarith
    have hz2 : ‖z - 1‖ ≤ |t| + 3 := by
      have : ‖z - 1‖ ≤ ‖z - c‖ + ‖c - 1‖ := by
        have := norm_add_le (z - c) (c - 1)
        rwa [sub_add_sub_cancel] at this
      rw [hz] at this
      norm_num at this ⊢
      linarith
    refine (norm_zeta₁_le hre).trans ?_
    have hn0 := norm_nonneg z
    have hn1 := norm_nonneg (z - 1)
    calc ‖z‖ + 20 * ‖z‖ * ‖z - 1‖ ≤ (|t| + 4) + 20 * (|t| + 4) * (|t| + 3) := by gcongr
      _ ≤ 61 * (|t| + 2) ^ 2 := by nlinarith
  have jensen := AnalyticOnNhd.sum_divisor_le (c := c) (r := 1.81) (R := 1.95)
    (M := 61 * (|t| + 2) ^ 2) (f := riemannZeta₁) (by rw [e1]; norm_num)
    (by rw [e1, e2]; norm_num) hM hA hc0 hbound
  -- the divisor dominates the multiplicities of the zeros in the right half
  set D := MeromorphicOn.divisor riemannZeta₁ (closedBall c |(1.81 : ℝ)|) with hD
  have hDfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hcast : ((∑ᶠ u, D u : ℤ) : ℝ) = ∑ᶠ u, (D u : ℝ) :=
    map_finsum (Int.castRingHom ℝ) hDfin
  have hDnn : ∀ u, 0 ≤ D u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := riemannZeta₁) (U := closedBall c |(1.81 : ℝ)|)
      (fun w _ => IndependentLandau.analyticAt_zeta₁ w)) u
  have hle : ∑ᶠ ρ ∈ rightZeros t, (ZetaShared.mult ρ : ℝ) ≤ ∑ᶠ u, (D u : ℝ) := by
    rw [finsum_mem_def]
    refine finsum_le_finsum' ?_ ?_ fun u => ?_
    · exact (rightZeros_finite t).subset fun u hu => by
        by_contra h
        exact hu (indicator_of_notMem h _)
    · exact hDfin.subset fun u hu => by
        simp only [Function.mem_support, ne_eq] at hu ⊢
        exact fun h => hu (by rw [h]; simp)
    · by_cases hu : u ∈ rightZeros t
      · rw [indicator_of_mem hu]
        have hu1 : u ≠ 1 := by rintro rfl; have := hu.2.1; simp at this
        rw [hD, divisor_zeta₁ (rightZeros_subset_ball t hu), mult_eq_orderNat_zeta₁ hu1]
        simp
      · rw [indicator_of_notMem hu]
        exact Int.cast_nonneg (hDnn u)
  have hlogpos : 0 < Real.log ((1.95 : ℝ) / 1.81) := Real.log_pos (by norm_num)
  have hcpos : 0 < ‖riemannZeta₁ c‖ := by linarith
  have hlog : Real.log (61 * (|t| + 2) ^ 2 / ‖riemannZeta₁ c‖) ≤
      Real.log (244 * (|t| + 2) ^ 2) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hcpos]
    nlinarith [sq_nonneg (|t| + 2)]
  calc ∑ᶠ ρ ∈ rightZeros t, (ZetaShared.mult ρ : ℝ) ≤ ∑ᶠ u, (D u : ℝ) := hle
    _ = ((∑ᶠ u, D u : ℤ) : ℝ) := hcast.symm
    _ ≤ Real.log (61 * (|t| + 2) ^ 2 / ‖riemannZeta₁ c‖) / Real.log (1.95 / 1.81) := jensen
    _ ≤ Real.log (244 * (|t| + 2) ^ 2) / Real.log (1.95 / 1.81) := by gcongr

/-- The constant for the right half. -/
def rightConst : ℝ := (Real.log 244 / Real.log 2 + 2) / Real.log (1.95 / 1.81)

lemma rightConst_pos : 0 < rightConst := by
  have h1 : 0 < Real.log ((1.95 : ℝ) / 1.81) := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 244 := Real.log_pos (by norm_num)
  unfold rightConst
  positivity

/-- Zeros in the right half of a unit window number `O(log (|t| + 2))`. -/
theorem rightCount_le (t : ℝ) :
    ∑ᶠ ρ ∈ rightZeros t, (ZetaShared.mult ρ : ℝ) ≤ rightConst * Real.log (|t| + 2) := by
  have ha : 0 ≤ |t| := abs_nonneg t
  have h1 : 0 < Real.log ((1.95 : ℝ) / 1.81) := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 244 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hsplit : Real.log (244 * (|t| + 2) ^ 2) = Real.log 244 + 2 * Real.log (|t| + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hmain : Real.log (244 * (|t| + 2) ^ 2) ≤
      (Real.log 244 / Real.log 2 + 2) * Real.log (|t| + 2) := by
    rw [hsplit, add_mul]
    have : Real.log 244 ≤ Real.log 244 / Real.log 2 * Real.log (|t| + 2) := by
      calc Real.log 244 = Real.log 244 / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ Real.log 244 / Real.log 2 * Real.log (|t| + 2) := by gcongr
    linarith
  refine (rightCount_le_log t).trans ?_
  unfold rightConst
  rw [div_mul_eq_mul_div]
  gcongr

end ZetaCount
