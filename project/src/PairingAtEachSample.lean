import PairingWindows

/-! The surplus also approximates the negative of the unused sum at every
sufficiently large individual fourth-power sample. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter Real RiemannReduction.DivisorBand RiemannReduction.DivisorBand.FourthMass

private theorem small_sample (η : ℝ) (hp : 0 < η) :
    ∀ᶠ n : ℕ in atTop, |core n| ≤ η*(n:ℝ)^4 := by
  obtain ⟨b,bp,M,Mp,est⟩ := whole_tail_pnt
  have grow := tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2)
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))
  have vanish := tendsto_exp_atBot.comp (grow.const_mul_atTop_of_neg (neg_lt_zero.mpr bp))
  have sqrtGrow := tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [vanish.eventually_lt_const (div_pos (half_pos hp) Mp),sqrtGrow.eventually_ge_atTop (2/η),
    core_distance_subpower (1/2) (by norm_num),eventually_ge_atTop (108:ℕ)] with n tiny big err hn
  change exp (-b*sqrt (2*log n)) < (η/2)/M at tiny
  change 2/η ≤ sqrt (n:ℝ) at big
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have bound := (est (n^2) (Nat.pow_le_pow_left hn 2)).2.2
  change |remainder n| ≤ M*((n^2:ℕ):ℝ)^2*exp (-b*sqrt (log ((n^2:ℕ):ℝ))) at bound
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at bound
  have coeff : M*exp (-b*sqrt (2*log n)) ≤ η/2 := by linarith only [(lt_div_iff₀ Mp).mp tiny]
  have low : |remainder n| ≤ η/2*(n:ℝ)^4 := bound.trans (by
    calc _ = (M*exp (-b*sqrt (2*log n)))*(n:ℝ)^4 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right coeff (by positivity))
  have member : n ∈ Icc n (n^2) := mem_Icc.mpr ⟨le_rfl,Nat.le_self_pow (by decide) _⟩
  have one : |remainder n-core n|/(n:ℝ)^3 ≤ window (fun k => |remainder k-core k|) n :=
    single_le_sum (f:=fun k : ℕ => |remainder k-core k|/(k:ℝ)^3)
      (fun k _ => div_nonneg (abs_nonneg _) (by positivity)) member
  have point := one.trans err
  rw [←sqrt_eq_rpow] at point
  have scaled := mul_le_mul_of_nonneg_right ((div_le_iff₀ hp).mp big) (sqrt_nonneg (n:ℝ))
  have ident := congrArg (fun t : ℝ => η*t) (sq_sqrt np.le)
  have rt : sqrt (n:ℝ) ≤ η/2*(n:ℝ) := by nlinarith only [scaled,ident]
  have high : |remainder n-core n| ≤ η/2*(n:ℝ)^4 :=
    ((div_le_iff₀ (pow_pos np 3)).mp point).trans
      ((mul_le_mul_of_nonneg_right rt (by positivity : 0 ≤ (n:ℝ)^3)).trans_eq (by ring))
  have tri := abs_sub_le (core n) (remainder n) 0
  rw [sub_zero,sub_zero,abs_sub_comm (core n) (remainder n)] at tri
  linarith only [low,high,tri]

theorem payment_at_each_sample (η : ℝ) (hp : 0 < η) :
    ∀ᶠ n : ℕ in atTop, |(-rest n)-credit n| ≤ η*credit n := by
  filter_upwards [small_sample (η/1600000000) (by positivity),eventually_ge_atTop (100000:ℕ)]
    with n small hn
  have eqn : (-rest n)-credit n= -(core n) := by rw [decompose hn]; ring
  rw [eqn,abs_neg]
  exact small.trans ((show η/1600000000*(n:ℝ)^4 = η*((n:ℝ)^4/1600000000) by ring).le.trans
    (mul_le_mul_of_nonneg_left (covered_weight hn).2 hp.le))

theorem unused_negative_at_each_sample :
    ∀ᶠ n : ℕ in atTop, rest n ≤ -(n:ℝ)^4/3200000000 := by
  filter_upwards [payment_at_each_sample (1/2) (by norm_num),eventually_ge_atTop (100000:ℕ)]
    with n close hn
  linarith only [(abs_le.mp close).1,(covered_weight hn).2]

end RiemannReduction.ShortTail.SignPairs
