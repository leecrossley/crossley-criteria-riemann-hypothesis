import DyadicLoss

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real SignPairs RiemannReduction.DivisorBand.FourthMass.Contact

private theorem log_factor {C η : ℝ} (hc : 0 ≤ C) (hp : 0 < η) :
    ∀ᶠ m : ℕ in atTop, C*(1+8*log m) ≤ (m:ℝ)^η := by
  filter_upwards [eventual_exp_sqrt (4*C) 2 η hp] with m cap
  let u := sqrt (2*log m)
  have hu : 0 ≤ u := sqrt_nonneg _
  have sq : u^2=2*log m := sq_sqrt (by linarith [log_natCast_nonneg m])
  have expBound := pow_le_pow_left₀ (by linarith : 0 ≤ u+1) (add_one_le_exp u) 2
  have h : 1+8*log m ≤ 4*(exp u)^2 := by nlinarith only [sq,expBound,hu]
  exact (mul_le_mul_of_nonneg_left h hc).trans (by
    change _ ≤ (m:ℝ)^η
    change 4*C*exp (2*u) ≤ _ at cap
    rw [two_mul,exp_add,←pow_two] at cap
    linarith only [cap])

private theorem level_count {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.log 2 (m^4)+1:ℕ):ℝ) ≤ 1+8*log m := by
  let J := Nat.log 2 (m^4)
  have np : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  have p : (2:ℝ)^J ≤ (m:ℝ)^4 := by
    exact_mod_cast Nat.pow_log_le_self 2 (show m^4 ≠ 0 by positivity)
  have l := log_le_log (by positivity : 0 < (2:ℝ)^J) p
  rw [log_pow,log_pow] at l
  norm_num only [Nat.cast_ofNat] at l
  have c := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at c
  push_cast
  change (J:ℝ)+1 ≤ _
  linarith only [l,mul_le_mul_of_nonneg_left c (Nat.cast_nonneg (α:=ℝ) J)]

/-- The quantifier over thresholds is inside the choice of a block. Even
allowing one constant per exponent, this is equivalent to the strong bound. -/
theorem weak_iff_outstanding : sameBlockWeak score ↔ cofinalSubpower outstanding := by
  constructor
  · intro weak ε ep A
    let η := ε/2
    have hp : 0 < η := half_pos ep
    obtain ⟨C,cp,w⟩ := weak η hp
    obtain ⟨u,poly⟩ := eventually_atTop.mp score_polynomial
    obtain ⟨v,absorb⟩ := eventually_atTop.mp (log_factor (C:=1+C) (by positivity) hp)
    obtain ⟨m,hm,levels⟩ := w (max (max A 100000) (max u v))
    have lo := (le_max_left _ _).trans hm
    have hi := (le_max_right _ _).trans hm
    have ml := (le_max_right A 100000).trans lo
    have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
    have m1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    let J := Nat.log 2 (m^4)+1
    have cap (n : ℕ) (hn : n ∈ Icc m (m^2)) : score n ≤ (2:ℝ)^J := by
      have lower := (le_max_left u v).trans (hi.trans (mem_Icc.mp hn).1)
      have n2 : (n:ℝ)^2 ≤ (m:ℝ)^4 := by
        have nm : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast (mem_Icc.mp hn).2
        exact (pow_le_pow_left₀ (by positivity) nm 2).trans_eq (by ring)
      exact (poly n lower).trans (n2.trans (by
        exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m^4)).le))
    have sums := sum_le_sum (s:=range J) (fun j _ => levels j)
    simp only [sum_const,card_range,nsmul_eq_mul] at sums
    have base := weighted_le_levels score m J cap
    have hJ : (J:ℝ) ≤ 1+8*log m := level_count (by omega)
    let p := (m:ℝ)^η
    have pp : 1 ≤ p := one_le_rpow m1 hp.le
    have lnon := log_natCast_nonneg m
    have harmonic := harmonic_window (show 1 ≤ m by omega)
    have fac := absorb m ((le_max_right u v).trans hi)
    have power : p*p = (m:ℝ)^ε := by
      rw [show ε=η+η by dsimp [η]; ring, rpow_add mp]
    have bound : weighted score m ≤ (1+C)*(1+8*log m)*p := by
      have s : (J:ℝ)*(C*p) ≤ (1+8*log m)*(C*p) :=
        mul_le_mul_of_nonneg_right hJ (by dsimp [p]; positivity)
      have dom := mul_le_mul_of_nonneg_left pp (by linarith : 0 ≤ 1+8*log m)
      change ∑ j ∈ range J, _ ≤ (J:ℝ)*(C*p) at sums
      linarith only [base,sums,s,dom,harmonic,lnon]
    refine ⟨m,(le_max_left A 100000).trans lo,?_⟩
    rw [←weighted_score_eq_outstanding ml,←power]
    exact bound.trans (mul_le_mul_of_nonneg_right fac (by dsimp [p]; positivity))
  · intro strong δ hp
    refine ⟨1,zero_lt_one,fun A => ?_⟩
    obtain ⟨m,large,cap⟩ := strong δ hp (max A 100000)
    refine ⟨m,(le_max_left _ _).trans large,fun j => ?_⟩
    simpa only [one_mul] using (weak_le_weighted score_nonneg m ((2:ℝ)^j)).trans
      ((weighted_score_eq_outstanding ((le_max_right _ _).trans large)).le.trans cap)

/-- Published strip input yields all thresholds simultaneously on every late
block for exponents above its threshold, including 2.986767. -/
theorem all_thresholds_of_contact (given : AllDirichletAbove boundary) (upper : boundary ≤ rankedUpper)
    {δ : ℝ} (hδ : 8*rankedUpper-4 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, t*frequency score m t ≤ (m:ℝ)^δ := by
  filter_upwards [payment_window_of_contact given upper hδ,eventually_ge_atTop (100000:ℕ)] with m pass late t
  rw [allocation_window late,←weighted_score_eq_outstanding late] at pass
  exact (weak_le_weighted score_nonneg m t).trans pass

/-- For every exponent the low thresholds pass on every sufficiently late
block using the harmonic length alone. -/
theorem low_thresholds (z : ℕ → ℝ) {δ : ℝ} (hp : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ (m:ℝ)^(δ/2) →
      t*frequency z m t ≤ (m:ℝ)^δ := by
  filter_upwards [log_factor (C:=1) zero_le_one (half_pos hp),eventually_ge_atTop (1:ℕ)]
    with m small hm t tp limit
  have size : frequency z m t ≤ ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ := by
    apply sum_le_sum
    intro n _
    split <;> simp_all only [le_refl,inv_nonneg,Nat.cast_nonneg]
  have l := log_natCast_nonneg m
  have h : frequency z m t ≤ (m:ℝ)^(δ/2) := by
    linarith only [size,harmonic_window hm,l,small]
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  calc
    _ ≤ t*(m:ℝ)^(δ/2) := mul_le_mul_of_nonneg_left h tp
    _ ≤ (m:ℝ)^(δ/2)*(m:ℝ)^(δ/2) := mul_le_mul_of_nonneg_right limit (rpow_nonneg mp.le _)
    _ = _ := by rw [←rpow_add mp]; congr 1; ring

theorem rh_iff_frequency : RiemannHypothesis ↔ sameBlockWeak score := by
  have h : RiemannHypothesis ↔ cofinalSubpower outstanding :=
    (RiemannReduction.DivisorBand.FourthMass.rh_iff_subpower_quartic_budget (-1) (Or.inr rfl)).trans original_iff_outstanding
  exact h.trans weak_iff_outstanding.symm

end RiemannReduction.ShortTail.LossFrequency
