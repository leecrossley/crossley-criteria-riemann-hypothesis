import PrimeBand
import Compat.LandauBridge

open scoped ArithmeticFunction.vonMangoldt
open ZetaShared

noncomputable section
namespace ThetaTransfer

private theorem ramp_extend {x z : ℝ} (hxz : x ≤ z) :
    rampS x = ∑ n ∈ Finset.range (⌊z⌋₊ + 1), Λ n * max (x / n - 1) 0 := by
  unfold ZetaShared.rampS IndependentLandau.rampS
  refine Finset.sum_subset
    (Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.floor_le_floor hxz))) ?_
  intro n _ hn
  exact IndependentLandau.rampT_eq_zero_of_floor_lt
    (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn)

theorem primePowerSum_eq_ramps {y : ℝ} (hy : 0 < y) :
    primePowerSum y = rampS (4*y) - 3 * rampS (2*y) + 2 * rampS y := by
  rw [ramp_extend (z := 4*y) le_rfl, ramp_extend (x := 2*y) (z := 4*y) (by linarith),
    ramp_extend (x := y) (z := 4*y) (by linarith)]
  simp only [primePowerSum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [tent, mul_div_assoc]
  ring

theorem deficit_eq_centered_ramps {y : ℝ} (hy : 0 < y) :
    2 * Real.log 2 * y - primePowerSum y =
      -rampG (4*y) + 3 * rampG (2*y) - 2 * rampG y := by
  rw [primePowerSum_eq_ramps hy]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  simp only [ZetaShared.rampG, IndependentLandau.rampG_eq, ZetaShared.rampS]
  rw [Real.log_mul (by norm_num) hy.ne', Real.log_mul (by norm_num) hy.ne', h4]
  ring

end ThetaTransfer
