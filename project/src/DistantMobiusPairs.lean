import DyadicLoss

/-! Large losses require a positive net contribution from well-separated
divisor pairs in the square of the original signed Möbius sum. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

theorem row_uniform {n d : ℕ} (hn : 2 ≤ n) (hd : d ∈ late n) : |term n d| ≤ kernelConstant := by
  have h := mem_Ioc.mp (mem_filter.mp hd).1
  have dp : 0 < (d:ℝ) := Nat.cast_pos.mpr (by omega)
  have np : 0 < ((n^4:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos (by omega) _)
  let y := ((n^4:ℕ):ℝ)/d
  have yp : 0 < y := div_pos np dp
  have y2 : 2 ≤ y := (le_div_iff₀ dp).mpr (by exact_mod_cast (show 2*d ≤ n^4 by omega))
  have u : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  let c := 72+60*|fixedBandLogConstant|
  have c0 : 0 ≤ c := by dsimp [c]; positivity
  have bounded : c*(1+log y)/y ≤ c := (div_le_iff₀ yp).mpr
    (mul_le_mul_of_nonneg_left (by linarith only [log_le_sub_one_of_pos yp]) c0)
  have inv : 1500/y ≤ (1500:ℝ) := (div_le_iff₀ yp).mpr (by linarith only [y2])
  change |(μ d:ℝ)*(fixedBandCenteredKernel y-fixedBandFirstCorrection y)| ≤ _
  rw [abs_mul]
  apply (mul_le_of_le_one_left (abs_nonneg _) u).trans ((abs_sub _ _).trans _)
  have sum := add_le_add (fixedBandCenteredKernel_bound y2) (fixedBandFirstCorrection_decay yp)
  unfold kernelConstant
  dsimp [c] at bounded
  linarith only [sum,bounded,inv]

def nearIndices (n d h : ℕ) := (late n).filter (· ∈ Icc (d-h) (d+h))
def farIndices (n d h : ℕ) := (late n).filter (fun e => e ∉ Icc (d-h) (d+h))
def nearProducts (n h : ℕ) := ∑ d ∈ late n, ∑ e ∈ nearIndices n d h, term n d*term n e
def farProducts (n h : ℕ) := ∑ d ∈ late n, ∑ e ∈ farIndices n d h, term n d*term n e

theorem pair_square (n h : ℕ) : nearProducts n h+farProducts n h=(core n)^2 := by
  unfold nearProducts farProducts core
  rw [←sum_add_distrib,pow_two,sum_mul]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]
  exact sum_filter_add_sum_filter_not (late n) (· ∈ Icc (d-h) (d+h)) (fun e => term n d*term n e)

private theorem size_late (n : ℕ) : ((late n).card:ℝ) ≤ (n:ℝ)^4 := by
  have sub : late n ⊆ Ioc 0 (n^4) := by
    intro d hd
    have h := mem_Ioc.mp (mem_filter.mp hd).1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  exact_mod_cast (show (late n).card ≤ n^4 by simpa using card_le_card sub)

/-- Absolute control includes all ordered pairs at distance at most h,
including the diagonal. No independence of signs is used. -/
theorem near_absolute {n : ℕ} (hn : 2 ≤ n) (h : ℕ) :
    |nearProducts n h| ≤ (2*(h:ℝ)+1)*kernelConstant^2*(n:ℝ)^4 := by
  let K := kernelConstant
  have row (d : ℕ) (hd : d ∈ late n) :
      |∑ e ∈ nearIndices n d h, term n d*term n e| ≤ (2*(h:ℝ)+1)*K^2 := by
    have each (e : ℕ) (he : e ∈ nearIndices n d h) : |term n d*term n e| ≤ K^2 := by
      rw [abs_mul,pow_two]
      exact mul_le_mul (row_uniform hn hd) (row_uniform hn (mem_filter.mp he).1) (abs_nonneg _) kernelConstant_nonneg
    have sub : nearIndices n d h ⊆ Icc (d-h) (d+h) := fun _ he => (mem_filter.mp he).2
    have count : ((nearIndices n d h).card:ℝ) ≤ 2*(h:ℝ)+1 := by
      have ub := card_le_card sub
      rw [Nat.card_Icc] at ub
      exact_mod_cast (show (nearIndices n d h).card ≤ 2*h+1 by omega)
    apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum each).trans _)
    simp only [sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right count (sq_nonneg _)
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum row).trans _)
  simp only [sum_const,nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (size_late n) (by positivity : 0 ≤ (2*(h:ℝ)+1)*K^2)).trans_eq (by ring)

/-- The Möbius signs occur in farProducts through the original term n d
times term n e. This is a signed lower bound on that sum at every hit. -/
theorem far_positive_at_hit {n h : ℕ} {t : ℝ} (hn : 2 ≤ n) (hp : 0 < t)
    (hit : t < score n) :
    (t^2-(2*(h:ℝ)+1)*kernelConstant^2)*(n:ℝ)^4 < farProducts n h := by
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have bad := (lt_div_iff₀ (pow_pos np 2)).mp hit
  change t*(n:ℝ)^2 < max (-core n) 0 at bad
  have neg := (lt_max_iff.mp bad).resolve_right (not_lt.mpr (by positivity))
  have sq := pow_lt_pow_left₀ neg (by positivity) (by decide : 2 ≠ 0)
  have near := (le_abs_self _).trans (near_absolute hn h)
  nlinarith only [sq,pair_square n h,near]

/-- Simultaneous in t and h on a complete block. Only samples exceeding the
threshold enter the right-hand side, with their signed far-pair totals. -/
theorem frequency_from_far {m h : ℕ} {t : ℝ} (hm : 2 ≤ m) (hp : 0 < t)
    (width : (2*(h:ℝ)+1)*kernelConstant^2 ≤ t^2/2) :
    t^2/2*frequency score m t ≤
      ∑ n ∈ Icc m (m^2), if t < score n then farProducts n h/(n:ℝ)^5 else 0 := by
  unfold frequency
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have late := hm.trans (mem_Icc.mp hn).1
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  split_ifs with hit
  · apply (le_div_iff₀ (pow_pos np 5)).mpr
    have low := far_positive_at_hit (h:=h) late hp hit
    have save := mul_le_mul_of_nonneg_right width (by positivity : 0 ≤ (n:ℝ)^4)
    rw [show t^2/2*(n:ℝ)⁻¹*(n:ℝ)^5 = t^2/2*(n:ℝ)^4 by field_simp]
    linarith only [low,save]
  · simp

end RiemannReduction.ShortTail.LossFrequency
