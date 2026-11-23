import OddBandDilation
import OddKernelVariation

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real RiemannReduction.ThirdBridge
open scoped ArithmeticFunction.Moebius

/-- The pointwise decay can be evaluated at the lower quotient Q even if an
interval after halving has been shortened at its left endpoint. -/
theorem kernel_at_larger_quotient {Q y : ℝ} (q1 : 1 ≤ Q) (hy : 2 ≤ y) (qy : Q ≤ y) :
    |surviving y| * Q ≤ kernelConstant*(1+log Q) := by
  have qp : 0<Q := by linarith
  have yp : 0<y := by linarith
  have lg := log_le_sub_one_of_pos (div_pos yp qp)
  rw [log_div yp.ne' qp.ne'] at lg
  have lmul := mul_le_mul_of_nonneg_right lg qp.le
  have cancel : y/Q*Q=y := div_mul_cancel₀ _ qp.ne'
  have inc := mul_le_mul_of_nonneg_right qy (log_nonneg q1)
  have comp : (1+log y)*Q ≤ (1+log Q)*y := by linarith only [lmul,cancel,inc]
  have dec : |surviving y| ≤ kernelConstant*(1+log y)/y := signedQuotientKernel_decay hy
  have step := mul_le_mul_of_nonneg_right ((le_div_iff₀ yp).mp dec) qp.le
  have rhs := mul_le_mul_of_nonneg_left comp kernelConstant_nonneg
  apply le_of_mul_le_mul_right _ yp
  linarith only [step,rhs]

/-- The cardinality of a halved interval contributes 2⁻ⁱ/2ʲ and the
actual kernel contributes another 2⁻ʲ times its logarithm. The arbitrary
left endpoint includes every additional large-divisor cutoff. -/
theorem halved_net_size (n j i a : ℕ) :
    |halvedNet ((n:ℝ)^4) a (bandHi n j) i| * (2:ℝ)^(i+2*j) ≤
      kernelConstant*(1+log ((2:ℝ)^j))*(n:ℝ)^4 := by
  let S := Ioc (a/2^i) (bandHi n j/2^i)
  let Q : ℝ := 2^j
  let w (d : ℕ) := (μ d:ℝ)*surviving ((n:ℝ)^4/(2:ℝ)^i/d)
  have qp : 0<Q := by dsimp [Q]; positivity
  have sp : 0<(2:ℝ)^i := by positivity
  have rowBounds (d : ℕ) (h : d ≤ bandHi n j/2^i) :
      d*2^i*2^j ≤ n^4 ∧ d*2^i*2 ≤ n^4 := by
    have top := (Nat.le_div_iff_mul_le (by positivity : 0<(2:ℕ)^i)).mp h
    exact ⟨(Nat.le_div_iff_mul_le (by positivity)).mp (top.trans (min_le_right ..)),
      (Nat.le_div_iff_mul_le (by decide)).mp (top.trans (min_le_left ..))⟩
  have each (d : ℕ) (hd : d∈S) : |w d| * Q ≤ kernelConstant*(1+log Q) := by
    obtain ⟨left,upper⟩ := mem_Ioc.mp hd
    have dr : 0<(d:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt left)
    obtain ⟨band,half⟩ := rowBounds d upper
    have bR : (d:ℝ)*(2:ℝ)^i*Q ≤ (n:ℝ)^4 := by dsimp [Q]; exact_mod_cast band
    have hR : (d:ℝ)*(2:ℝ)^i*2 ≤ (n:ℝ)^4 := by exact_mod_cast half
    have toY (q : ℝ) (hq : (d:ℝ)*(2:ℝ)^i*q ≤ (n:ℝ)^4) :
        q ≤ (n:ℝ)^4/(2:ℝ)^i/d := by
      apply (le_div_iff₀ dr).mpr
      apply (le_div_iff₀ sp).mpr
      linarith only [hq]
    have k := kernel_at_larger_quotient (show 1≤Q from one_le_pow₀ (by norm_num))
      (toY _ hR) (toY _ bR)
    have mu : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
    dsimp [w]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) mu) qp.le).trans k
  have total : |∑ d ∈ S, w d| * Q ≤ (S.card:ℝ)*(kernelConstant*(1+log Q)) := by
    apply (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs ..) qp.le).trans
    simpa only [sum_mul, sum_const, nsmul_eq_mul] using
      (show (∑ d ∈ S, |w d|)*Q ≤ ∑ _d ∈ S, kernelConstant*(1+log Q) by
        rw [sum_mul]; exact sum_le_sum each)
  have card : S.card ≤ bandHi n j/2^i := by
    simp [S]
  have bound : (S.card:ℝ)*(2:ℝ)^i*Q ≤ (n:ℝ)^4 := by
    dsimp [Q]; exact_mod_cast (rowBounds S.card card).1
  have nonneg : 0≤kernelConstant*(1+log Q) := by
    have lg : 0≤log Q := log_nonneg (one_le_pow₀ (by norm_num))
    positivity [kernelConstant_nonneg]
  have mul := mul_le_mul_of_nonneg_right total (mul_nonneg sp.le qp.le)
  have rhs := mul_le_mul_of_nonneg_left bound nonneg
  change |∑ d ∈ S, w d| * (2:ℝ)^(i+2*j) ≤ kernelConstant*(1+log Q)*(n:ℝ)^4
  rw [two_mul j,pow_add,pow_add]
  change |∑ d ∈ S, w d| * ((2:ℝ)^i*(Q*Q)) ≤ _
  linarith only [mul,rhs]

end RiemannReduction.ShortTail.LossFrequency
