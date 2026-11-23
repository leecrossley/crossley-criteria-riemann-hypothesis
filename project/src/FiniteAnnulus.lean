import ShortDivisorTransfer
import FiniteFifthBlocks

/-! On the published finite prime-deficit range, a large negative retained
sum forces a positive signed contribution in an explicit discarded annulus. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real RiemannReduction.DivisorBand RiemannReduction.BalancedSquare
open RiemannGaussian.AlpogeMined

def annulus (n b : ℕ) :=
  ∑ d ∈ (discarded n).filter (fun d => ¬d ≤ b), term n d

private theorem low_cost {n : ℕ} (hn : 2 ≤ n) (hi : n ≤ 26*10^9) :
    envelope n*((n^3/1000:ℕ):ℝ)^2 ≤ (n:ℝ)^2/4 := by
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have p2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have v2 := log_nonneg (by norm_num : (1:ℝ)≤2)
  have c : |fixedBandLogConstant| ≤ 1 := by
    unfold fixedBandLogConstant
    apply abs_le.mpr
    constructor <;> linarith [one_half_lt_eulerMascheroniConstant,eulerMascheroniConstant_lt_two_thirds]
  have k : kernelConstant ≤ 1632 := by unfold kernelConstant; linarith only [c]
  have num : (n:ℝ) ≤ (2:ℝ)^35 := by
    exact_mod_cast hi.trans (by decide : 26*10^9 ≤ 2^35)
  have lg := log_le_log np num
  rw [log_pow] at lg
  norm_num only [Nat.cast_ofNat] at lg
  have s : 1+4*log n ≤ 141 := by linarith only [lg,p2]
  have cap : kernelConstant*(1+4*log n) ≤ 1632*141 :=
    mul_le_mul k s (by linarith [log_natCast_nonneg n]) (by norm_num)
  let b := n^3/1000
  have br : (b:ℝ)*1000 ≤ (n:ℝ)^3 := by exact_mod_cast Nat.div_mul_le_self (n^3) 1000
  have bs := pow_le_pow_left₀ (by positivity : 0 ≤ (b:ℝ)*1000) br 2
  change envelope n*(b:ℝ)^2 ≤ _
  unfold envelope
  rw [Nat.cast_pow,log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [div_mul_eq_mul_div,(div_le_iff₀ (pow_pos np 4))]
  nlinarith only [mul_le_mul_of_nonneg_right cap (sq_nonneg (b:ℝ)),bs,
    show 0 ≤ (b:ℝ)^2 by positivity]

/-- This local implication uses the actual normalized prime deficit at n⁴.
It holds for any pre-cut divisor bound for which the indicated cost fits. -/
theorem positive_annulus_at_hit {n b : ℕ} {t : ℝ} (hn : 4 ≤ n) (ht : 1 ≤ t)
    (hit : t < score n) (prime : -(n:ℝ)^2/5 ≤ normalizedRows (n^2))
    (small : envelope n*(b:ℝ)^2 ≤ (n:ℝ)^2/4) :
    t*(n:ℝ)^2/2 < annulus n b := by
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have tp : 0 < t := zero_lt_one.trans_le ht
  have bad := (lt_div_iff₀ (pow_pos np 2)).mp hit
  change t*(n:ℝ)^2 < max (-core n) 0 at bad
  have neg := (lt_max_iff.mp bad).resolve_right (not_lt.mpr (by positivity))
  let S := (discarded n).filter (· ≤ b)
  have split : (∑ d ∈ S, term n d)+annulus n b=discardedSum n :=
    sum_filter_add_sum_filter_not (discarded n) (· ≤ b) (term n)
  have lo : ∑ d ∈ S, term n d ≤ (n:ℝ)^2/4 := by
    apply (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (le_trans _ small))
    apply cut_absolute (by omega)
    · exact (filter_subset ..).trans (filter_subset ..)
    · intro d hd
      obtain ⟨hd,db⟩ := mem_filter.mp hd
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hd).1).1,db⟩
  have size := mul_le_mul_of_nonneg_right ht (sq_nonneg (n:ℝ))
  nlinarith only [neg,prime,discarded_identity hn,split,lo,size,sq_nonneg (n:ℝ)]

/-- The analytic finite-height inequality is explicit, as in FiniteFifthBlocks.
Every index and every threshold in this finite range shares the same input. -/
theorem finite_annulus
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (FiniteFifth.cap:ℝ)^2 → |D x| < sqrt x/5)
    {n : ℕ} (hn : 100000 ≤ n) (hi : n ≤ 26*10^9) {t : ℝ} (ht : 1 ≤ t) (hit : t < score n) :
    t*(n:ℝ)^2/2 < annulus n (n^3/1000) := by
  have k : 16 ≤ n^2 := (by decide : 16 ≤ 100000^2).trans (Nat.pow_le_pow_left hn 2)
  have k' : n^2 ≤ FiniteFifth.cap := (Nat.pow_le_pow_left hi 2).trans (by decide)
  have r : (n:ℝ)^2 ≤ (FiniteFifth.cap:ℝ) := by exact_mod_cast k'
  have l : (1024:ℝ) ≤ ((n:ℝ)^2)^2 := by
    exact_mod_cast ((by decide : 1024 ≤ (100000^2)^2).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left hn 2) 2))
  have est := published (((n:ℝ)^2)^2) l (pow_le_pow_left₀ (sq_nonneg _) r 2)
  rw [sqrt_sq (sq_nonneg (n:ℝ))] at est
  apply positive_annulus_at_hit (by omega) ht hit _ (low_cost (by omega) hi)
  rw [←balanced_square k,Nat.cast_pow]
  linarith only [(abs_lt.mp est).1]

theorem finite_annulus_blocks
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (FiniteFifth.cap:ℝ)^2 → |D x| < sqrt x/5)
    {m : ℕ} (hm : 100000 ≤ m) (cap : m ≤ 161245) :
    ∀ j : ℕ, ∀ n ∈ Icc m (m^2), (2:ℝ)^j < score n →
      (2:ℝ)^j*(n:ℝ)^2/2 < annulus n (n^3/1000) := by
  intro j n hn hit
  apply finite_annulus published (hm.trans (mem_Icc.mp hn).1) _ (one_le_pow₀ (by norm_num)) hit
  exact (mem_Icc.mp hn).2.trans ((Nat.pow_le_pow_left cap 2).trans (by decide))

end RiemannReduction.ShortTail.LossFrequency
