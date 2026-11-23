import AnchorWeight
import IndependentLandau.Ramp

noncomputable section
open Finset IndependentLandau
open scoped ArithmeticFunction.vonMangoldt

namespace SparseAnchor

/-- The elementary remainder in the integral comparison for log(X!). -/
def logError (X : ℕ) : ℝ := (∑ n ∈ Ioc 0 X, Real.log n) - X*Real.log X + X

theorem logError_bounds {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ logError X ∧ logError X ≤ 1 + Real.log X := by
  induction X, hX using Nat.le_induction with
  | base => norm_num [logError, ←one_Icc]
  | succ n h1 ih =>
    have ns : (0:ℝ) < n := by exact_mod_cast h1
    have s : (0:ℝ) < (n:ℝ)+1 := by linarith
    have increment : logError (n+1) = logError n + 1 - (n:ℝ)*(Real.log (n+1)-Real.log n) := by
      unfold logError
      rw [←one_Icc, sum_Icc_succ_top (show 1 ≤ n+1 by omega), one_Icc, Nat.cast_add_one]
      ring
    have hi := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (div_pos s ns)) ns.le
    have lo := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (div_pos ns s)) s.le
    simp only [Real.log_div s.ne' ns.ne', sub_mul, div_mul_cancel₀ _ ns.ne', one_mul] at hi
    simp only [Real.log_div ns.ne' s.ne', sub_mul, div_mul_cancel₀ _ s.ne', one_mul] at lo
    rw [increment, Nat.cast_add_one]
    constructor <;> nlinarith only [ih.1, ih.2, hi, lo]

/-- Signed deficit against unit density with the right-endpoint convention. -/
def deficit (X cutoff : ℕ) : ℝ :=
  ∑ n ∈ Ioc cutoff X, (1 - Λ n)*weight X n

/-- Exact integer version of the prime-power ramp. Convolution with the
constant arithmetic function gives the log-factorial term. -/
theorem ramp_identity (X : ℕ) :
    rampG X - deficit X 0 =
      logError X + (Real.eulerMascheroniConstant*X - ∑ n ∈ Ioc 0 X, weight X n) := by
  have logsum : (∑ n ∈ Ioc 0 X, Λ n*((X/n:ℕ):ℝ)) = ∑ n ∈ Ioc 0 X, Real.log n := by
    simpa only [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply] using
      (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt X).symm
  have set_eq : range (X+1) = insert 0 (Ioc 0 X) := by
    ext n
    simp only [mem_range,mem_insert,mem_Ioc]
    omega
  have sum_eq : (∑ n ∈ range (X+1), Λ n * max ((X:ℝ)/n-1) 0) =
      ∑ n ∈ Ioc 0 X, Λ n * ((X:ℝ)/n-1) := by
    rw [set_eq, sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero, zero_mul, zero_add]
    apply sum_congr rfl
    intro n hn
    have nr : 0 < (n:ℝ) := by exact_mod_cast (mem_Ioc.mp hn).1
    have nx : (n:ℝ) ≤ X := by exact_mod_cast (mem_Ioc.mp hn).2
    rw [max_eq_left (sub_nonneg.mpr ((one_le_div nr).mpr nx))]
  have algebra : (∑ n ∈ Ioc 0 X, Λ n*((X:ℝ)/n-1)) - deficit X 0 =
      (∑ n ∈ Ioc 0 X, Real.log n) - ∑ n ∈ Ioc 0 X, weight X n := by
    rw [←logsum, deficit, ←sum_sub_distrib, ←sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    unfold weight
    ring
  rw [rampG, Nat.floor_natCast, sum_eq, logError]
  linarith only [algebra]

end SparseAnchor
