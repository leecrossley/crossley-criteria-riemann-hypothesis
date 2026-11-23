import GcdFrequency
import GcdGapShells

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

private theorem log_endpoint_slack {κ : ℝ} (kp : 0 < κ) (n j : ℕ) (hn : 1 ≤ n) :
    1+log ((n^4/2^j:ℕ):ℝ) ≤ (1+4/κ)*(n:ℝ)^κ := by
  let U := n^4/2^j
  have np := Nat.cast_pos (α:=ℝ).mpr hn
  have up : (U:ℝ) ≤ (n:ℝ)^4 := by exact_mod_cast Nat.div_le_self (n^4) (2^j)
  have lg : log (U:ℝ) ≤ 4*log n := by
    by_cases z : U=0
    · rw [z,Nat.cast_zero,log_zero]; positivity
    · simpa only [log_pow,Nat.cast_ofNat] using
        log_le_log (Nat.cast_pos (α:=ℝ).mpr (Nat.pos_of_ne_zero z)) up
  have one := one_le_rpow (show (1:ℝ) ≤ n by exact_mod_cast hn) kp.le
  have exp := log_le_sub_one_of_pos (rpow_pos_of_pos np κ)
  rw [log_rpow np] at exp
  have scaled := mul_le_mul_of_nonneg_left exp (show 0 ≤ 4/κ by positivity)
  have cancel : (4/κ)*(κ*log n) = 4*log n := by field_simp
  rw [cancel] at scaled
  change 1+log (U:ℝ) ≤ _
  linarith only [lg,scaled,one,show 0 ≤ 4/κ by positivity]

private theorem diagonal_cost (n j : ℕ) :
    ((n^4/2^j:ℕ):ℝ)*(kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j)^2 ≤ kernelConstant^2*(n:ℝ)^4 := by
  let Q : ℝ := 2^j
  have qp : 0 < Q := by dsimp [Q]; positivity
  have lg := log_nonneg (show 1 ≤ Q from one_le_pow₀ (by norm_num))
  have cap : kernelConstant*(1+log Q)/Q ≤ kernelConstant := by
    apply (div_le_iff₀ qp).mpr
    exact mul_le_mul_of_nonneg_left (by linarith only [log_le_sub_one_of_pos qp]) kernelConstant_nonneg
  have up : ((n^4/2^j:ℕ):ℝ) ≤ (n:ℝ)^4 := by exact_mod_cast Nat.div_le_self (n^4) (2^j)
  simpa only [mul_comm (kernelConstant^2)] using
    mul_le_mul up (pow_le_pow_left₀ (by positivity [kernelConstant_nonneg]) cap 2)
      (sq_nonneg _) (by positivity)

theorem near_gap_cost {η κ : ℝ} (hp : 0 ≤ η) (kp : 0 < κ)
    {t : ℝ} (ht : 1 ≤ t) (n j : ℕ) (hn : 1 ≤ n) :
    ((n^4/2^j:ℕ):ℝ)*(1+2*(rayCut η t n j:ℝ)*(1+log (n^4/2^j:ℕ)))*
      (kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j)^2 ≤
      ((kernelConstant^2*(1+2*(1+4/κ)))*t)*(n:ℝ)^4*(n:ℝ)^(η+κ) := by
  let R := rayCut η t n j
  let U : ℝ := (n^4/2^j:ℕ)
  let F : ℝ := kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j
  have np := Nat.cast_pos (α:=ℝ).mpr hn
  have tp : 0 ≤ t := zero_le_one.trans ht
  have extra := log_endpoint_slack kp n j hn
  have ln : 0 ≤ 1+log U := by dsimp [U]; positivity
  have raw := ray_kernel_budget η t tp n j
  change 2*(R:ℝ)*U*F^2 ≤ _ at raw
  have combined := mul_le_mul raw extra ln (by positivity)
  have one : 1 ≤ t*(n:ℝ)^(η+κ) :=
    one_le_mul_of_one_le_of_one_le ht (one_le_rpow (by exact_mod_cast hn) (by linarith))
  have base : U*F^2 ≤ (kernelConstant^2*(n:ℝ)^4)*(t*(n:ℝ)^(η+κ)) :=
    (diagonal_cost n j).trans (le_mul_of_one_le_right (by positivity) one)
  have factor : (n:ℝ)^(η+κ) = (n:ℝ)^η*(n:ℝ)^κ := rpow_add np _ _
  rw [factor] at base ⊢
  change U*(1+2*(R:ℝ)*(1+log U))*F^2 ≤ _
  change _*(1+log U) ≤ _ at combined
  linarith only [combined,base]

/-- Every pair whose reduced coordinates differ by at most rayCut contributes
at most m^δ in total absolute block mass, on every late block simultaneously for all t ≥ 1. -/
theorem near_gap_frequency {η δ : ℝ} (hp : 0 ≤ η) (gap : 2*η < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      |crossingPairMass (fun n j => nearGapShellContribution n j (rayCut η t n j)) m t| ≤ (m:ℝ)^δ := by
  let κ := (δ-2*η)/4
  have kp : 0 < κ := by dsimp [κ]; linarith
  apply crossing_pair_part_subpower (C:=kernelConstant^2*(1+2*(1+4/κ))) (η:=η+κ)
    (by positivity) (by linarith only [hp,kp]) (by dsimp [κ]; linarith)
  exact fun t ht n j hn jp => (near_gap_shell_bound n j (rayCut η t n j) jp).trans
    (near_gap_cost hp kp ht n j hn)

/-- Signed contribution of the pairs with large reduced coordinate difference. -/
def farGapMass (δ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  crossingPairMass (fun n j => farGapShellContribution n j (rayCut (δ/4) t n j)) m t

theorem frequency_minus_far_gap {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      |t*frequency uniformShellScore m t-farGapMass δ m t| ≤ (m:ℝ)^δ := by
  filter_upwards [near_gap_frequency (η:=δ/4) (by positivity) (by linarith : 2*(δ/4)<δ),
    eventually_ge_atTop (1:ℕ)] with m paid hm t ht
  rw [crossing_pair_mass_split
    (fun n j => nearGapShellContribution n j (rayCut (δ/4) t n j))
    (fun n j => farGapShellContribution n j (rayCut (δ/4) t n j))
    (fun n j => full_shell_gap_square n j _) hm (zero_lt_one.trans_le ht)]
  simpa only [farGapMass,add_sub_cancel_right] using paid t ht

theorem uniform_frequency_iff_far_gap :
    sameBlockWeak uniformShellScore ↔ ∀ δ > (0:ℝ), sameBlockUpper (farGapMass δ) δ :=
  uniform_frequency_iff_approximation farGapMass (fun _ ep => frequency_minus_far_gap ep)

theorem rh_of_far_gap (h : ∀ δ > (0:ℝ), sameBlockUpper (farGapMass δ) δ) : RiemannHypothesis :=
  rh_of_uniform_shell_score (uniform_frequency_iff_far_gap.mpr h)

end RiemannReduction.ShortTail.LossFrequency
