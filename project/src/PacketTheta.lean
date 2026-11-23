import PacketProfile
import Compat.PsiBound

open Finset
namespace RiemannReduction.DivisorBand
noncomputable section

/-- The classical prime number theorem gives all fixed inverse logarithmic powers
for the ordinary Chebyshev theta function. -/
theorem packetTheta_decay (m : ℕ) : ∃ H ≥ (1:ℝ), ∀ t : ℝ, 1 ≤ t →
    |Chebyshev.theta t-t| * (packetLog t)^m ≤ H*t := by
  obtain ⟨cg,Kg,cgp,gz⟩ := Compat.gzPNT
  let c₀ := cg
  have cp : 0 < c₀ := cgp
  obtain ⟨F,Fp,f⟩ := exp_sqrt_log_power m (show 0<c₀/4 by linarith)
  obtain ⟨J,Jp,j⟩ := log_power_sqrt m
  obtain ⟨V,v⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let B := 1/2+7*|Kg|+6*Real.exp (c₀/2)
  have bp : 0 ≤ B := by dsimp [B]; positivity
  let H := 1+B*F+|V| *J+(packetLog 2)^m
  have smallN : 0 ≤ (packetLog 2)^m := pow_nonneg (by linarith [packetLog_ge (by norm_num : (1:ℝ)≤2)]) _
  have h1 : 1 ≤ H := by dsimp [H]; linarith [mul_nonneg bp Fp.le,mul_nonneg (abs_nonneg V) Jp.le]
  refine ⟨H,h1,fun t ht => ?_⟩
  have tp : 0 < t := by linarith
  have ln : 0 ≤ (packetLog t)^m := pow_nonneg (by linarith [packetLog_ge ht]) _
  by_cases ht2 : 2 ≤ t
  · have ep : |Chebyshev.psi t-t| ≤ B*t*Real.exp (-(c₀/4)*Real.sqrt (Real.log t)) :=
      Compat.psi_sub_id_of_ramp cgp gz t ht2
    have p1 := mul_le_mul_of_nonneg_right ep ln
    have p2 := mul_le_mul_of_nonneg_left (f t ht) (mul_nonneg bp tp.le)
    have gap := (v t).trans (mul_le_mul_of_nonneg_right (le_abs_self V) (Real.sqrt_nonneg t))
    have g1 := mul_le_mul_of_nonneg_right gap ln
    have g2 := mul_le_mul_of_nonneg_left (j t ht) (mul_nonneg (abs_nonneg V) (Real.sqrt_nonneg t))
    have ss := Real.mul_self_sqrt tp.le
    have triangle := abs_sub_le (Chebyshev.theta t) (Chebyshev.psi t) t
    rw [abs_of_nonpos (sub_nonpos.mpr (Chebyshev.theta_le_psi t))] at triangle
    have total := mul_le_mul_of_nonneg_right triangle ln
    dsimp [H]
    nlinarith only [p1,p2,g1,g2,total,show |V| *Real.sqrt t*(J*Real.sqrt t) = |V| *J*t by
      calc _ = |V| *J*(Real.sqrt t*Real.sqrt t) := by ring
           _ = _ := by rw [ss],tp.le,mul_nonneg smallN tp.le]
  · have z := Chebyshev.theta_eq_zero_of_lt_two (lt_of_not_ge ht2)
    rw [z,zero_sub,abs_neg,abs_of_pos tp]
    have pow := pow_le_pow_left₀ (by linarith [packetLog_ge ht]) (packetLog_mono tp (le_of_not_ge ht2)) m
    have le : (packetLog 2)^m ≤ H := by dsimp [H]; linarith [mul_nonneg bp Fp.le,mul_nonneg (abs_nonneg V) Jp.le]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right (pow.trans le) tp.le

end
end RiemannReduction.DivisorBand
