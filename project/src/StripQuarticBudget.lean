import StripDeficit
import QuarticPowerSum

open Finset
namespace RiemannReduction.DivisorBand.FourthMass
noncomputable section

/-- A zero-free strip gives the power 8σ−4 for the signed mass. The same
    positive constant works for all blocks and both signs. -/
theorem quartic_bound_of_strip {σ : ℝ} (lower : 1/2 < σ) (upper : σ ≤ 7/8)
    (free : ZetaWindow.Strip.ZeroFreeTo σ) :
    ∃ C > (0:ℝ), ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ m : ℕ, 10^8 ≤ m →
      mass (signedRemainder s) m ≤ C*(m:ℝ)^(8*σ-4) := by
  obtain ⟨A,ap,bound⟩ := deficit_of_strip lower.le upper free
  let t := 4*σ-2
  have tp : 0 < t := by dsimp [t]; linarith
  refine ⟨(A+2)*(2*(2:ℝ)^t/t),by positivity,fun s sign m late => ?_⟩
  have each (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      max (signedRemainder s n) 0/(n:ℝ)^3 ≤ (A+2)*(n:ℝ)^(t-1) := by
    have nl := late.trans (mem_Icc.mp hn).1
    have nr : (10^8:ℝ) ≤ n := by exact_mod_cast nl
    have np : 0 < (n:ℝ) := by linarith
    have n1 : (1:ℝ) ≤ n := by linarith
    have nr4 : (8:ℝ) ≤ (n:ℝ)^4 :=
      (by norm_num : (8:ℝ) ≤ (10^8:ℝ)^4).trans (pow_le_pow_left₀ (by norm_num) nr 4)
    have d := bound ((n:ℝ)^4) nr4
    rw [← Real.rpow_natCast_mul np.le] at d
    have late2 : 10^16 ≤ n^2 := (by norm_num : 10^16 = (10^8)^2) ▸ Nat.pow_le_pow_left nl 2
    have e := deficit_pair_error_two late2
    change |D (((n^2:ℕ):ℝ)^2)-remainder n| ≤ 2*((n^2:ℕ):ℝ) at e
    rw [Nat.cast_pow,show ((n:ℝ)^2)^2 = (n:ℝ)^4 by ring] at e
    have tri := abs_sub_le (remainder n) (D ((n:ℝ)^4)) 0
    rw [sub_zero,sub_zero,abs_sub_comm (remainder n)] at tri
    have clipped : max (signedRemainder s n) 0 ≤ |remainder n| := by
      apply max_le _ (abs_nonneg _)
      rcases sign with rfl|rfl
      · simpa [signedRemainder] using le_abs_self (remainder n)
      · simpa [signedRemainder] using neg_le_abs (remainder n)
    have two := Real.rpow_le_rpow_of_exponent_le n1 (show (2:ℝ)≤4*σ by linarith)
    rw [Real.rpow_two] at two
    have powers : (n:ℝ)^(t-1)*(n:ℝ)^3 = (n:ℝ)^(4*σ) := by
      rw [show (n:ℝ)^3=(n:ℝ)^(3:ℝ) by norm_num,←Real.rpow_add np]
      congr 1
      dsimp [t]
      ring
    apply (div_le_iff₀ (pow_pos np 3)).mpr
    rw [mul_assoc,powers]
    norm_num only [Nat.cast_ofNat] at d
    nlinarith only [clipped,tri,e,d,two]
  have summed := sum_le_sum each
  unfold mass
  rw [←mul_sum] at summed
  have ms := block_power_sum tp (show 1 ≤ m by omega)
  apply summed.trans
  calc _ ≤ (A+2)*((2*(2:ℝ)^t/t)*(m:ℝ)^(2*t)) :=
             mul_le_mul_of_nonneg_left ms (by linarith)
       _ = _ := by rw [show 2*t=8*σ-4 by dsimp [t]; ring]; ring

/-- The zeta specialization of Xu and Sang, Theorem 1.1, is the argument. -/
theorem quartic_bound_of_xu_sang
    (free : ZetaWindow.Strip.ZeroFreeTo (8748867/10000000)) :
    ∃ C > (0:ℝ), ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ m : ℕ, 10^8 ≤ m →
      mass (signedRemainder s) m ≤ C*(m:ℝ)^(29990936/10000000:ℝ) := by
  simpa only [show 8*(8748867/10000000:ℝ)-4 = 29990936/10000000 by norm_num] using
    quartic_bound_of_strip (by norm_num : (1/2:ℝ) < 8748867/10000000)
      (by norm_num : (8748867/10000000:ℝ) ≤ 7/8) free

#print axioms quartic_bound_of_strip
#print axioms quartic_bound_of_xu_sang
end
end RiemannReduction.DivisorBand.FourthMass
