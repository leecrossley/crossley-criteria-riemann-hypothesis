import SurplusObstruction
import SurplusStrip

/-! Quantitative coverage of every unused negative term at its own sample. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter Real RiemannReduction.DivisorBand RiemannReduction.DivisorBand.FourthMass
open RiemannReduction.DivisorBand.FourthMass.Contact

private theorem term_coverage_of_shortfall {n : ℕ} {η : ℝ} (gp : 0 < unusedDebt n)
    (cap : unpaid n (allocation n (funds n)) ≤ unusedDebt n * η) :
    ∀ d ∈ unused n, debt n d - allocation n (funds n) d ≤ η*debt n d := by
  have fracBalance : unusedDebt n * (1-fraction n (funds n)) = unpaid n (allocation n (funds n)) := by
    unfold unpaid allocation unusedDebt
    rw [sum_sub_distrib,←sum_mul]
    ring
  rw [←fracBalance] at cap
  have rate := le_of_mul_le_mul_left cap gp
  intro d _
  calc
    debt n d - allocation n (funds n) d = (1-fraction n (funds n))*debt n d := by unfold allocation; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right rate (le_max_right _ _)

/-- The prime number theorem suffices to pay an arbitrarily high fixed
fraction of every debt from both sources of funds, at every late sample. -/
theorem unpaid_fraction_tends_to_zero {η : ℝ} (hp : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ d ∈ unused n, debt n d - allocation n (funds n) d ≤ η*debt n d := by
  filter_upwards [payment_at_each_sample η hp,surplus_alone_at_sample,
    eventually_ge_atTop (100000:ℕ)] with n near gross hn
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hc := (show 0 ≤ (n:ℝ)^4 / 1600000000 by positivity).trans (covered_weight hn).2
  have diff : 0 < unusedDebt n - credit n :=
    (show 0 < (n:ℝ)^4/10000 by positivity).trans_le gross
  apply term_coverage_of_shortfall (by linarith only [diff,hc])
  rw [full_payment hn, decompose hn]
  have h := (abs_le.mp near).2
  apply max_le
  · have amt := mul_le_mul_of_nonneg_left (sub_pos.mp diff).le hp.le
    linarith only [h,amt]
  · exact mul_nonneg (by linarith only [diff,hc]) hp.le

private theorem sample_at_contact (given : AllDirichletAbove boundary) (upper : boundary ≤ rankedUpper) :
    ∃ K > (0:ℝ), ∀ᶠ n : ℕ in atTop, |core n| ≤ K*(n:ℝ)^(4*rankedUpper) := by
  have free : RiemannReduction.ZetaWindow.Strip.ZeroFreeTo rankedUpper := by
    intro s hs
    exact ordinaryAbove given (upper.trans_lt hs)
  obtain ⟨C,cp,est⟩ := deficit_of_strip (σ:=rankedUpper) (by norm_num [rankedUpper]) (by norm_num [rankedUpper]) free
  refine ⟨C+3,by positivity,?_⟩
  filter_upwards [core_distance_subpower (1/4) (by norm_num),eventually_ge_atTop (10^8:ℕ)] with n near hn
  have nr : (10^8:ℝ) ≤ n := by exact_mod_cast hn
  have np : 0 < (n:ℝ) := by linarith
  have n1 : (1:ℝ) ≤ n := by linarith
  have d := est ((n:ℝ)^4)
    ((by norm_num : (8:ℝ) ≤ (10^8:ℝ)^4).trans (pow_le_pow_left₀ (by norm_num) nr 4))
  rw [←rpow_natCast_mul np.le] at d
  norm_num only [Nat.cast_ofNat] at d
  have late : 10^16 ≤ n^2 := (by norm_num : 10^16 = (10^8)^2) ▸ Nat.pow_le_pow_left hn 2
  have e := deficit_pair_error_two late
  change |D (((n^2:ℕ):ℝ)^2)-remainder n| ≤ 2*((n^2:ℕ):ℝ) at e
  rw [Nat.cast_pow,show ((n:ℝ)^2)^2 = (n:ℝ)^4 by ring] at e
  have nearOne : |remainder n - core n|/(n:ℝ)^3 ≤ window (fun k => |remainder k-core k|) n :=
    single_le_sum (f:=fun k : ℕ => |remainder k-core k|/(k:ℝ)^3)
      (fun _ _ => div_nonneg (abs_nonneg _) (by positivity))
      (mem_Icc.mpr ⟨le_rfl,Nat.le_self_pow (by decide) _⟩)
  have err := (div_le_iff₀ (pow_pos np 3)).mp (nearOne.trans near)
  have exponent : (n:ℝ)^(1/4:ℝ)*(n:ℝ)^3 = (n:ℝ)^(13/4:ℝ) := by
    rw [show (n:ℝ)^3=(n:ℝ)^(3:ℝ) by norm_num,←rpow_add np]
    norm_num
  rw [exponent] at err
  have low := rpow_le_rpow_of_exponent_le n1 (show (13/4:ℝ) ≤ 4*rankedUpper by norm_num [rankedUpper])
  have two := rpow_le_rpow_of_exponent_le n1 (show (2:ℝ) ≤ 4*rankedUpper by norm_num [rankedUpper])
  rw [rpow_two] at two
  have ab := abs_sub_le (core n) (remainder n) 0
  have bc := abs_sub_le (remainder n) (D ((n:ℝ)^4)) 0
  rw [sub_zero,sub_zero,abs_sub_comm (core n) (remainder n)] at ab
  rw [sub_zero,sub_zero,abs_sub_comm (remainder n)] at bc
  linarith only [d,e,ab,bc,err,low,two]

/-- When both sources of funds are allowed, every actual debt can be paid
to within the same shrinking fraction. The constant is one for the stated
strict range of exponents. -/
theorem unpaid_fraction_of_contact (given : AllDirichletAbove boundary) (upper : boundary ≤ rankedUpper)
    {κ : ℝ} (hk' : κ < 4-4*rankedUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ d ∈ unused n, debt n d - allocation n (funds n) d ≤
      (n:ℝ)^(-κ)*debt n d := by
  obtain ⟨K,_,cap⟩ := sample_at_contact given upper
  have gap : 0 < 4-κ-4*rankedUpper := by linarith only [hk']
  have grow := ((tendsto_rpow_atTop gap).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (10000*K)
  filter_upwards [grow,cap,surplus_alone_at_sample,eventually_ge_atTop (100000:ℕ)] with n big close raw hn
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hc := (show 0 ≤ (n:ℝ)^4 / 1600000000 by positivity).trans (covered_weight hn).2
  have gross : (n:ℝ)^4/10000 ≤ unusedDebt n := by linarith only [raw,hc]
  have gp := (show 0 < (n:ℝ)^4/10000 by positivity).trans_le gross
  have budget : unpaid n (allocation n (funds n)) ≤ K*(n:ℝ)^(4*rankedUpper) := by
    rw [full_payment hn]
    exact (max_le (neg_le_abs _) (abs_nonneg _)).trans close
  change 10000*K ≤ (n:ℝ)^(4-κ-4*rankedUpper) at big
  have powEq : (n:ℝ)^(4-κ-4*rankedUpper)*(n:ℝ)^(4*rankedUpper) = (n:ℝ)^4*(n:ℝ)^(-κ) := by
    rw [←rpow_add np,sub_add_cancel,show (n:ℝ)^4=(n:ℝ)^(4:ℝ) by norm_num,←rpow_add np]
    rfl
  have base := mul_le_mul_of_nonneg_right big (rpow_nonneg np.le (4*rankedUpper))
  rw [powEq] at base
  apply term_coverage_of_shortfall gp
  linarith only [budget,base,mul_le_mul_of_nonneg_right gross (rpow_nonneg np.le (-κ))]

theorem unpaid_fraction_half (given : AllDirichletAbove boundary) (upper : boundary ≤ rankedUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ d ∈ unused n, debt n d - allocation n (funds n) d ≤
      (n:ℝ)^(-(1/2:ℝ))*debt n d :=
  unpaid_fraction_of_contact given upper (by norm_num [rankedUpper])

end RiemannReduction.ShortTail.SignPairs
