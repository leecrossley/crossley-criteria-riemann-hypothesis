import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open Finset MeasureTheory
open scoped Interval
namespace RiemannReduction.DivisorBand.FourthMass

/-- A block starting at m ends at m². The bound holds also where the summand
    decreases, and retains the exponent of the integral. -/
theorem block_power_sum {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Icc m (m^2), (n:ℝ)^(t-1) ≤
      (2*(2:ℝ)^t/t)*(m:ℝ)^(2*t) := by
  let b : ℕ := m^2+1
  have ml : (1:ℝ) ≤ m := by exact_mod_cast hm
  have mp : 0 < (m:ℝ) := by linarith
  have mb : m ≤ b := by dsimp [b]; nlinarith
  have integral : IntegrableOn (fun x : ℝ => 2*x^(t-1)) (Set.Ico (m:ℝ) (b:ℝ)) := by
    have cont : ContinuousOn (fun x : ℝ => 2*x^(t-1)) (Set.Icc (m:ℝ) (b:ℝ)) := by
      intro x hx
      exact (continuousAt_const.mul (Real.continuousAt_rpow_const x (t-1) (Or.inl (mp.trans_le hx.1).ne'))).continuousWithinAt
    exact cont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have compare := sum_Ico_le_integral_of_le (f:=fun x : ℝ => x^(t-1))
    (g:=fun x : ℝ => 2*x^(t-1)) mb (fun i hi x hx => by
      have il : (1:ℝ) ≤ i := by exact_mod_cast hm.trans hi.1
      have ip : 0 < (i:ℝ) := by linarith
      have xp := ip.trans_le hx.1
      have upper : x ≤ 2*(i:ℝ) := by
        have u := hx.2
        push_cast at u
        linarith
      rw [Real.rpow_sub ip,Real.rpow_one,Real.rpow_sub xp,Real.rpow_one,←mul_div_assoc,
        div_le_div_iff₀ ip xp]
      calc (i:ℝ)^t*x ≤ x^t*x := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ip.le hx.1 ht.le) xp.le
           _ ≤ x^t*(2*(i:ℝ)) := mul_le_mul_of_nonneg_left upper (Real.rpow_nonneg xp.le _)
           _ = _ := by ring) integral
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (show -1 < t-1 by linarith)),
    sub_add_cancel] at compare
  have ico : Ico m b = Icc m (m^2) := by ext i; simp [b]
  rw [ico] at compare
  have cap : (b:ℝ) ≤ 2*(m:ℝ)^2 := by dsimp [b]; push_cast; nlinarith
  have grow := Real.rpow_le_rpow (Nat.cast_nonneg b) cap ht.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (sq_nonneg (m:ℝ)),← Real.rpow_natCast_mul mp.le] at grow
  calc _ ≤ 2*(((b:ℝ)^t-(m:ℝ)^t)/t) := compare
       _ ≤ 2*((b:ℝ)^t/t) := by
           gcongr
           exact sub_le_self _ (Real.rpow_nonneg mp.le _)
       _ ≤ 2*(((2:ℝ)^t*(m:ℝ)^((2:ℕ)*t))/t) := by gcongr
       _ = _ := by push_cast; ring

end RiemannReduction.DivisorBand.FourthMass
