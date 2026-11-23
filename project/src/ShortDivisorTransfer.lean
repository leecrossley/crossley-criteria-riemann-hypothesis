import DivisorAttribution
import FrequencyCriterion
import BalancedSquareKernel

/-! The signed Möbius correction relocates every sufficiently large threshold
hit to rows with both arithmetic tables ending at n². The weights change. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real RiemannGaussian.AlpogeMined
open RiemannReduction.BalancedSquare RiemannReduction.DivisorBand RiemannReduction.DyadicBands

def shortScore (n : ℕ) := max (-normalizedRows (n^2)) 0/(n:ℝ)^2

private theorem exact_half {n : ℕ} (hn : 4 ≤ n) :
    normalizedRows (n^2) = ∑ d ∈ Ioc 0 (n^4/2), term n d := by
  have p : 0 < ((n^4:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos (by omega) _)
  have big : 16 ≤ n^4 := (by decide : 16 ≤ 2^4).trans (Nat.pow_le_pow_left (by omega : 2 ≤ n) 4)
  have eqn : D ((n^4:ℕ):ℝ) = ∑ d ∈ Ioc 0 (n^4/2), term n d := by
    rw [deficit_contrast p, fixedBand_centered_identity (by omega)]
    have delta := fixedBandHalfTail_error (K:=0) big (Nat.zero_le _)
    simp only [Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_div,abs_nonpos_iff,sub_eq_zero] at delta
    exact delta
  have large : 16 ≤ n^2 := (by decide : 16 ≤ 4^2).trans (Nat.pow_le_pow_left hn 2)
  rw [←balanced_square large,Nat.cast_pow,show ((n:ℝ)^2)^2=(n:ℝ)^4 by ring,←Nat.cast_pow,eqn]

private theorem cutoff_dominates (n : ℕ) : fixedBandMultipleCutoff n ≤ cutoff n := by
  apply (Nat.div_le_self ..).trans
  apply Nat.le_floor
  rw [Nat.cast_pow]
  exact le_mul_of_one_le_right (by positivity) (one_le_exp (sqrt_nonneg _))

def discarded (n : ℕ) := (Ioc 0 (n^4/2)).filter (· ≤ cutoff n)
def discardedSum (n : ℕ) := ∑ d ∈ discarded n, term n d

/-- All signed rows below the cutoff and above it recover the original
prime deficit, also given by the corrected sum with both tables ending at n². -/
theorem discarded_identity {n : ℕ} (hn : 4 ≤ n) :
    discardedSum n + core n = normalizedRows (n^2) := by
  let S := Ioc 0 (n^4/2)
  have high : S.filter (fun d => ¬d ≤ cutoff n) = late n := by
    ext d
    have dom := cutoff_dominates n
    simp only [S,late,indices,mem_filter,mem_Ioc]
    omega
  have split := sum_filter_add_sum_filter_not S (· ≤ cutoff n) (term n)
  rw [high] at split
  exact split.trans (exact_half hn).symm

/-- Absolute error from dropping d <= cutoff n in the original half-tail. -/
theorem short_distance_explicit {n : ℕ} (hn : 4 ≤ n) :
    |core n - normalizedRows (n^2)| ≤ envelope n*(cutoff n:ℝ)^2 := by
  have diff : core n-normalizedRows (n^2) = -discardedSum n := by linarith only [discarded_identity hn]
  rw [diff,abs_neg]
  apply (abs_sum_le_sum_abs _ _).trans
  apply cut_absolute (by omega) _ (filter_subset ..)
  intro d hd
  exact mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hd).1).1,(mem_filter.mp hd).2⟩

/-- Pointwise subpower error on the normalized scores with no strip input. -/
theorem score_distance_subpower {η : ℝ} (hp : 0 < η) :
    ∀ᶠ n : ℕ in atTop, |score n-shortScore n| ≤ (n:ℝ)^η := by
  filter_upwards [eventual_exp_sqrt (2*kernelConstant) 4 η hp,eventually_ge_atTop (4:ℕ)]
    with n small hn
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have floor := Nat.floor_le (show 0 ≤ (n:ℝ)^3*exp (sqrt (log n)) by positivity)
  change (cutoff n:ℝ) ≤ _ at floor
  have env : 0 ≤ envelope n := by
    unfold envelope
    exact div_nonneg (mul_nonneg kernelConstant_nonneg (by linarith [log_natCast_nonneg (n^4)])) (by positivity)
  have close := (short_distance_explicit hn).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) floor 2) env)
  let u := sqrt (2*log n)
  have u0 : 0 ≤ u := sqrt_nonneg _
  have l0 := log_natCast_nonneg n
  have root : sqrt (log n) ≤ u := sqrt_le_sqrt (by linarith)
  have sq : u^2 = 2*log n := sq_sqrt (by linarith)
  have grow := pow_le_pow_left₀ (by linarith : 0 ≤ u+1) (add_one_le_exp u) 2
  have logCap : 1+4*log n ≤ 2*(exp u)^2 := by nlinarith only [sq,u0,grow]
  have expCap := pow_le_pow_left₀ (exp_pos _).le (exp_le_exp.mpr root) 2
  have factors := mul_le_mul logCap expCap (sq_nonneg _) (by positivity : 0 ≤ 2*(exp u)^2)
  have id : (exp u)^4 = exp (4*u) := by rw [←exp_nat_mul]; norm_num
  have combined : kernelConstant*(1+4*log n)*(exp (sqrt (log n)))^2 ≤ (n:ℝ)^η := by
    have scaled := mul_le_mul_of_nonneg_left factors kernelConstant_nonneg
    change 2*kernelConstant*exp (4*u) ≤ _ at small
    rw [←id] at small
    linarith only [scaled,small]
  unfold envelope at close
  rw [Nat.cast_pow,log_pow] at close
  norm_num only [Nat.cast_ofNat] at close
  have rearrange : kernelConstant*(1+4*log n)/(n:ℝ)^4*((n:ℝ)^3*exp (sqrt (log n)))^2 =
      (kernelConstant*(1+4*log n)*(exp (sqrt (log n)))^2)*(n:ℝ)^2 := by field_simp
  rw [rearrange] at close
  unfold score excess shortScore
  rw [←sub_div,abs_div,abs_of_nonneg (sq_nonneg (n:ℝ))]
  apply (div_le_iff₀ (pow_pos np 2)).mpr
  have clip := abs_max_sub_max_le_abs (-core n) (-normalizedRows (n^2)) 0
  rw [neg_sub_neg,abs_sub_comm (normalizedRows _)] at clip
  exact clip.trans (close.trans (mul_le_mul_of_nonneg_right combined (sq_nonneg _)))

/-- On each late block the same comparison holds for all t >= 2m^η and all
samples. An exceptional large hit forces a hit of half the size on the
corrected rows, and conversely. -/
theorem identical_large_hits_up_to_factor_two {η : ℝ} (hp : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 2*(m:ℝ)^η ≤ t → ∀ n ∈ Icc m (m^2),
      (t < score n → t/2 < shortScore n) ∧ (t < shortScore n → t/2 < score n) := by
  obtain ⟨A,uniform⟩ := eventually_atTop.mp (score_distance_subpower (half_pos hp))
  filter_upwards [eventually_ge_atTop A] with m hm t large n hn
  have diff := uniform n (hm.trans (mem_Icc.mp hn).1)
  have ncap : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast (mem_Icc.mp hn).2
  have mono := rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) n) ncap (half_pos hp).le
  have e : ((m:ℝ)^2)^(η/2)=(m:ℝ)^η := by
    rw [←rpow_natCast_mul (Nat.cast_nonneg (α:=ℝ) m)]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [e] at mono
  obtain ⟨a,b⟩ := abs_le.mp (diff.trans mono)
  constructor <;> intro hit <;> linarith only [a,b,large,hit]

end RiemannReduction.ShortTail.LossFrequency
