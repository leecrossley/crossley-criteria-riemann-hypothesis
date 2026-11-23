import UniformShellCriterion

/-! Harmonic first moments on square blocks, including the high-quotient contribution. -/
noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- A crossing on a square block carries at least the reciprocal of its index. -/
private theorem atom_le_frequency {z : ℕ → ℝ} {m n : ℕ} {t : ℝ}
    (hn : n ∈ Icc m (m^2)) (hit : t < z n) : (n:ℝ)⁻¹ ≤ frequency z m t := by
  classical
  have nonneg (i : ℕ) (_ : i ∈ Icc m (m^2)) :
      0 ≤ (if t < z i then (i:ℝ)⁻¹ else 0) := by split <;> positivity
  simpa only [frequency,if_pos hit] using single_le_sum nonneg hn

/-- The weak bound itself truncates the layer cake. A sample above the cutoff
would give frequency at least 1/m², contradicting the highest-level bound. -/
private theorem cap_from_weak {z : ℕ → ℝ} {m : ℕ} {η C : ℝ} (hm : 1 ≤ m)
    (small : C ≤ (m:ℝ)) (exp_le : η ≤ 1)
    (levels : ∀ j : ℕ, (2:ℝ)^j * frequency z m ((2:ℝ)^j) ≤ C*(m:ℝ)^η) :
    ∀ n ∈ Icc m (m^2), z n ≤ (2:ℝ)^(bandCount m 0) := by
  intro n hn
  by_contra! hit
  let t := (2:ℝ)^(bandCount m 0)
  have mp : (1:ℝ) ≤ m := by exact_mod_cast hm
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (hm.trans (mem_Icc.mp hn).1)
  have nm : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast (mem_Icc.mp hn).2
  have cap : C*(m:ℝ)^η ≤ (m:ℝ)^2 := by
    rw [sq]
    exact mul_le_mul small ((rpow_le_rpow_of_exponent_le mp exp_le).trans_eq (rpow_one _))
      (rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  have paid : t*(n:ℝ)⁻¹ ≤ (m:ℝ)^2 :=
    (mul_le_mul_of_nonneg_left (atom_le_frequency hn hit) (by dsimp [t]; positivity)).trans
      ((levels _).trans cap)
  rw [←div_eq_mul_inv] at paid
  have tooLarge : (m:ℝ)^4 < t := by
    dsimp [t,bandCount]
    simp only [Nat.div_one]
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m^4)
  have bound := ((div_le_iff₀ np).mp paid).trans
    (mul_le_mul_of_nonneg_left nm (sq_nonneg _))
  linarith only [bound,tooLarge]

/-- Weak and strong subpower bounds on arbitrarily late square blocks are
equivalent for every nonnegative statistic. No separate growth bound is needed. -/
theorem same_block_weak_iff_weighted {z : ℕ → ℝ} (hz : ∀ n, 0 ≤ z n) :
    sameBlockWeak z ↔ cofinalSubpower (weighted z) := by
  constructor
  · intro weak ε ep A
    let η := min (ε/2) 1
    have hp : 0 < η := lt_min (half_pos ep) zero_lt_one
    obtain ⟨C,cp,w⟩ := weak η hp
    obtain ⟨u,hu⟩ := exists_nat_ge C
    obtain ⟨v,absorb⟩ := eventually_atTop.mp (absorb_log_square (1+C) (by positivity) hp)
    obtain ⟨m,hm,levels⟩ := w (max (max A 1) (max u v))
    have lo := (le_max_left _ _).trans hm
    have hi := (le_max_right _ _).trans hm
    have m1 := (le_max_right A 1).trans lo
    have mr : (1:ℝ) ≤ m := by exact_mod_cast m1
    have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr m1
    have cap := cap_from_weak m1 (hu.trans (by exact_mod_cast (le_max_left u v).trans hi))
      (min_le_right (ε/2) 1) levels
    let J := bandCount m 0
    have sums := sum_le_sum (s:=range J) (fun j _ => levels j)
    simp only [sum_const,card_range,nsmul_eq_mul] at sums
    have base := weighted_le_levels z m J cap
    have hJ : (J:ℝ) ≤ 1+8*log m := band_count_log m1
    let p := (m:ℝ)^η
    have pp : 1 ≤ p := one_le_rpow mr hp.le
    have lm := log_natCast_nonneg m
    have harmonic := harmonic_window m1
    have fac := absorb m ((le_max_right u v).trans hi)
    have p0 : 0 ≤ p := zero_le_one.trans pp
    have L1 : 1 ≤ 1+8*log (m:ℝ) := by linarith only [lm]
    have fac1 : (1+C)*(1+8*log m) ≤ p := by
      have square := mul_le_mul_of_nonneg_left L1 (zero_le_one.trans L1)
      nlinarith only [fac,mul_le_mul_of_nonneg_left square (show 0 ≤ 1+C by positivity)]
    have bound : weighted z m ≤ (1+C)*(1+8*log m)*p := by
      have s := mul_le_mul_of_nonneg_right hJ (mul_nonneg cp.le p0)
      have dom := mul_le_mul_of_nonneg_left pp (zero_le_one.trans L1)
      change ∑ j ∈ range J, _ ≤ (J:ℝ)*(C*p) at sums
      linarith only [base,sums,s,dom,harmonic,lm]
    refine ⟨m,(le_max_left A 1).trans lo,bound.trans ?_⟩
    apply (mul_le_mul_of_nonneg_right fac1 p0).trans
    dsimp [p]
    rw [←rpow_add mp]
    exact rpow_le_rpow_of_exponent_le mr (by linarith only [min_le_left (ε/2) (1:ℝ)])
  · intro strong δ hp
    refine ⟨1,zero_lt_one,fun A => ?_⟩
    obtain ⟨m,large,cap⟩ := strong δ hp A
    exact ⟨m,large,fun j => by simpa only [one_mul] using
      (weak_le_weighted hz m ((2:ℝ)^j)).trans cap⟩

theorem uniform_weak_iff_first_moment :
    sameBlockWeak uniformShellScore ↔ cofinalSubpower (weighted uniformShellScore) :=
  same_block_weak_iff_weighted uniform_shell_score_nonnegative


/-- The positive part of the worst normalized negative net within a set of bins. -/
def maskedShellScore (keep : ℕ → ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact (range (bandCount n 0)).sup' (nonempty_range_iff.mpr (by unfold bandCount; omega))
    (fun j => if keep n j then -fullFirstShell n j/share n 0 1 else 0)

def lowQuotientScore (δ : ℝ) := maskedShellScore (fun n j => (2:ℝ)^j < (n:ℝ)^(1-3*δ/16))

def highQuotientScore (δ : ℝ) := maskedShellScore (fun n j => (n:ℝ)^(1-3*δ/16) ≤ (2:ℝ)^j)

theorem masked_shell_score_nonnegative (keep : ℕ → ℕ → Prop) (n : ℕ) : 0 ≤ maskedShellScore keep n := by
  classical
  have zero : 0 ∈ range (bandCount n 0) := mem_range.mpr (by unfold bandCount; omega)
  have h := le_sup' (fun j => if keep n j then -fullFirstShell n j/share n 0 1 else 0) zero
  simpa only [full_first_zero_bin,neg_zero,zero_div,ite_self,maskedShellScore] using h

theorem masked_shell_score_le_uniform (keep : ℕ → ℕ → Prop) (n : ℕ) :
    maskedShellScore keep n ≤ uniformShellScore n := by
  classical
  apply sup'_le
  intro j hj
  split
  · exact le_sup' (fun i => -fullFirstShell n i/share n 0 1) hj
  · exact uniform_shell_score_nonnegative n

/-- Equality keeps the low and high bins on the same sample. -/
theorem uniform_score_eq_max_low_high (δ : ℝ) (n : ℕ) :
    uniformShellScore n = max (lowQuotientScore δ n) (highQuotientScore δ n) := by
  classical
  apply le_antisymm _ (max_le (masked_shell_score_le_uniform ..) (masked_shell_score_le_uniform ..))
  apply sup'_le
  intro j hj
  by_cases low : (2:ℝ)^j < (n:ℝ)^(1-3*δ/16)
  · apply le_trans _ (le_max_left ..)
    have sel := le_sup' (fun i => if (2:ℝ)^i < (n:ℝ)^(1-3*δ/16)
      then -fullFirstShell n i/share n 0 1 else 0) hj
    simpa only [lowQuotientScore,maskedShellScore,if_pos low] using sel
  · apply le_trans _ (le_max_right ..)
    have sel := le_sup' (fun i => if (n:ℝ)^(1-3*δ/16) ≤ (2:ℝ)^i
      then -fullFirstShell n i/share n 0 1 else 0) hj
    simpa only [highQuotientScore,maskedShellScore,if_pos (le_of_not_gt low)] using sel

/-- Two powers of the bin's lower quotient come from the interval length and
the corrected kernel. The two logarithms account for the share and the kernel. -/
theorem normalized_shell_quotient_ceiling {n j : ℕ} (hn : 1 ≤ n) (hj : j < bandCount n 0) :
    (-fullFirstShell n j/share n 0 1)*(2:ℝ)^(2*j) ≤
      4*kernelConstant*(1+8*log n)^2*(n:ℝ)^2 := by
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  by_cases zero : j = 0
  · rw [zero,full_first_zero_bin,neg_zero,zero_div,zero_mul]
    positivity [kernelConstant_nonneg]
  have jp : 1 ≤ j := by omega
  have two : 2 ≤ (2:ℕ)^j := by
    calc (2:ℕ) = 2^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by decide) jp
  have cap : bandHi n j=n^4/2^j := min_eq_right (Nat.div_le_div_left two (by decide))
  have size := halved_net_size n j 0 (n^4/2^(j+1))
  simp only [zero_add,halvedNet,intervalNet,cap,pow_zero,Nat.div_one,div_one] at size
  change |fullFirstShell n j| * (2:ℝ)^(2*j) ≤ _ at size
  have bp : 0 < (bandCount n 0:ℝ) := by unfold bandCount; positivity
  have share_eq : share n 0 1 * (4*(bandCount n 0:ℝ)) = (n:ℝ)^2 := by
    unfold share
    field_simp
    ring
  have sp : 0 < share n 0 1 := by unfold share; positivity
  have denom : -fullFirstShell n j/share n 0 1*(n:ℝ)^2 =
      -fullFirstShell n j*(4*(bandCount n 0:ℝ)) := by
    rw [←share_eq,←mul_assoc,div_mul_cancel₀ _ sp.ne']
  have rank : j ≤ Nat.log 2 (n^4) := by simpa [bandCount] using hj
  have limit : (2:ℕ)^j ≤ n^4 := (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) rank).trans
    (Nat.pow_log_le_self 2 (by positivity))
  have lq := log_le_log (by positivity : 0<(2:ℝ)^j) (show (2:ℝ)^j ≤ (n:ℝ)^4 by exact_mod_cast limit)
  rw [log_pow (n:ℝ) 4,Nat.cast_ofNat] at lq
  have ln := log_natCast_nonneg n
  have qbound : 1+log ((2:ℝ)^j) ≤ 1+8*log n := by linarith only [lq,ln]
  have pair := mul_le_mul qbound (band_count_log hn) bp.le (by positivity : 0 ≤ 1+8*log n)
  have factor := mul_le_mul_of_nonneg_left pair
    (show 0 ≤ 4*kernelConstant*(n:ℝ)^4 by positivity [kernelConstant_nonneg])
  have sized := (mul_le_mul_of_nonneg_right (neg_le_abs _) (by positivity : 0 ≤ (2:ℝ)^(2*j))).trans size
  have withBand := mul_le_mul_of_nonneg_right sized (show 0 ≤ 4*(bandCount n 0:ℝ) by positivity)
  apply le_of_mul_le_mul_right _ (pow_pos np 2)
  rw [show (-fullFirstShell n j/share n 0 1*(2:ℝ)^(2*j))*(n:ℝ)^2 =
    (-fullFirstShell n j/share n 0 1*(n:ℝ)^2)*(2:ℝ)^(2*j) by ring,denom]
  linarith only [withBand,factor]

theorem high_quotient_score_height (δ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    highQuotientScore δ n ≤ 4*kernelConstant*(1+8*log n)^2*(n:ℝ)^(3*δ/8) := by
  classical
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have pos : 0 ≤ 4*kernelConstant*(1+8*log n)^2*(n:ℝ)^(3*δ/8) := by
    positivity [kernelConstant_nonneg]
  simp only [highQuotientScore,maskedShellScore,sup'_le_iff]
  intro j hj
  split
  · rename_i high
    by_cases neg : -fullFirstShell n j/share n 0 1 ≤ 0
    · exact neg.trans pos
    have square : (n:ℝ)^(2-3*δ/8) ≤ (2:ℝ)^(2*j) :=
      le_of_not_gt fun shallow => (not_lt_of_ge high) ((first_shell_quotient_iff n j δ).mp shallow)
    have paid := (mul_le_mul_of_nonneg_left square (le_of_not_ge neg)).trans
      (normalized_shell_quotient_ceiling hn (mem_range.mp hj))
    have scaled := mul_le_mul_of_nonneg_right paid (rpow_nonneg np.le (3*δ/8))
    rw [mul_assoc,←rpow_add np,sub_add_cancel,rpow_two] at scaled
    apply le_of_mul_le_mul_right _ (pow_pos np 2)
    linarith only [scaled]
  · exact pos

/-- The cutoff parameter and target exponent may be chosen independently.
The factor two from the square block is the only loss in the power. -/
theorem high_quotient_first_moment_below {κ δ : ℝ} (hk : 0 ≤ κ) (gap : 3*κ/4 < δ) :
    ∀ᶠ m : ℕ in atTop, weighted (highQuotientScore κ) m ≤ (m:ℝ)^δ := by
  let η := (δ-3*κ/4)/4
  have ep : 0 < η := by dsimp [η]; linarith
  obtain ⟨N,absorb⟩ := eventually_atTop.mp
    (absorb_log_square (4*kernelConstant) (by positivity [kernelConstant_nonneg]) ep)
  filter_upwards [eventually_ge_atTop (max N 1),absorb_log_square 1 zero_le_one
    (show 0 < 2*η by positivity)] with m hm small
  have m1 := (le_max_right N 1).trans hm
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr m1
  have expNonneg : 0 ≤ η+3*κ/8 := by positivity
  have single (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      highQuotientScore κ n ≤ (m:ℝ)^(2*(η+3*κ/8)) := by
    obtain ⟨mn,nm⟩ := mem_Icc.mp hn
    have nn := m1.trans mn
    have np := Nat.cast_pos (α:=ℝ).mpr nn
    have paid := mul_le_mul_of_nonneg_right (absorb n ((le_max_left N 1).trans (hm.trans mn)))
      (rpow_nonneg np.le (3*κ/8))
    rw [←rpow_add np] at paid
    have nr : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast nm
    have power := rpow_le_rpow np.le nr expNonneg
    rw [←rpow_natCast_mul mp.le] at power
    norm_num only [Nat.cast_ofNat] at power
    exact ((high_quotient_score_height κ nn).trans paid).trans power
  have total := sum_le_sum (s:=Icc m (m^2)) (fun n hn =>
    mul_le_mul_of_nonneg_right (single n hn) (show 0 ≤ (n:ℝ)⁻¹ by positivity))
  rw [←mul_sum] at total
  have lg := log_natCast_nonneg m
  have sq : 1+2*log m ≤ (1+8*log m)^2 := by nlinarith only [lg,sq_nonneg (log (m:ℝ))]
  have harm := (harmonic_window m1).trans (sq.trans (by simpa only [one_mul] using small))
  have paid := mul_le_mul_of_nonneg_left harm (rpow_nonneg mp.le (2*(η+3*κ/8)))
  rw [←rpow_add mp,show 2*(η+3*κ/8)+2*η=δ by dsimp [η]; ring] at paid
  exact total.trans paid

/-- The original high-quotient contribution is paid on every sufficiently
late block with constant one. -/
theorem high_quotient_first_moment {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, weighted (highQuotientScore δ) m ≤ (m:ℝ)^δ :=
  high_quotient_first_moment_below ep.le (by linarith)

/-- For 3δ/16 < b < δ/4 this also pays the intervening part of the previously
remaining low ranges, together with every larger quotient bin. -/
theorem outer_low_range_first_moment {b δ : ℝ} (hb : 0 ≤ b) (gap : 4*b < δ) :
    ∀ᶠ m : ℕ in atTop,
      weighted (maskedShellScore (fun n j => (n:ℝ)^(1-b) ≤ (2:ℝ)^j)) m ≤ (m:ℝ)^δ := by
  have bound := high_quotient_first_moment_below (κ:=16*b/3) (by positivity)
    (show 3*(16*b/3)/4 < δ by linarith only [gap])
  simpa only [highQuotientScore,show 3*(16*b/3)/16=b by ring] using bound

/-- The two parts may attain their maxima at different bins of the same sample. -/
theorem weighted_uniform_le_low_add_high (δ : ℝ) (m : ℕ) :
    weighted uniformShellScore m ≤
      weighted (lowQuotientScore δ) m + weighted (highQuotientScore δ) m := by
  unfold weighted
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro n _
  rw [uniform_score_eq_max_low_high δ n,←add_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact max_le (le_add_of_nonneg_right (masked_shell_score_nonnegative ..))
    (le_add_of_nonneg_left (masked_shell_score_nonnegative ..))

/-- A first-moment bound with a constant allowed to depend on the exponent. -/
def cofinalMomentBound (z : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∃ C > (0:ℝ), ∀ A : ℕ, ∃ m ≥ A, weighted z m ≤ C*(m:ℝ)^δ

/-- At each fixed exponent, the low-quotient condition is exactly what remains
for the first moment. The high contribution is bounded on the chosen block. -/
theorem low_quotient_first_moment_iff_below {κ δ : ℝ} (hk : 0 ≤ κ) (gap : 3*κ/4 < δ) :
    cofinalMomentBound (lowQuotientScore κ) δ ↔ cofinalMomentBound uniformShellScore δ := by
  constructor
  · rintro ⟨C,cp,blocks⟩
    obtain ⟨N,high⟩ := eventually_atTop.mp (high_quotient_first_moment_below hk gap)
    refine ⟨C+1,by linarith,fun A => ?_⟩
    obtain ⟨m,hm,low⟩ := blocks (max A N)
    refine ⟨m,(le_max_left ..).trans hm,?_⟩
    linarith only [weighted_uniform_le_low_add_high κ m,low,high m ((le_max_right ..).trans hm)]
  · rintro ⟨C,cp,blocks⟩
    refine ⟨C,cp,fun A => ?_⟩
    obtain ⟨m,hm,bound⟩ := blocks A
    exact ⟨m,hm,(sum_le_sum (s:=Icc m (m^2)) (fun n _ =>
      mul_le_mul_of_nonneg_right (masked_shell_score_le_uniform _ n) (inv_nonneg.mpr (Nat.cast_nonneg n)))).trans bound⟩

theorem low_quotient_first_moment_iff {δ : ℝ} (ep : 0 < δ) :
    cofinalMomentBound (lowQuotientScore δ) δ ↔ cofinalMomentBound uniformShellScore δ :=
  low_quotient_first_moment_iff_below ep.le (by linarith)

theorem all_cofinal_moments_iff {z : ℕ → ℝ} :
    (∀ δ > (0:ℝ), cofinalMomentBound z δ) ↔ cofinalSubpower (weighted z) := by
  constructor
  · intro h δ ep A
    obtain ⟨C,_,blocks⟩ := h (δ/2) (half_pos ep)
    have growth := ((tendsto_rpow_atTop (half_pos ep)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop C
    obtain ⟨N,absorb⟩ := eventually_atTop.mp growth
    obtain ⟨m,hm,pay⟩ := blocks (max (max A N) 1)
    have lo := (le_max_left ..).trans hm
    have mp := Nat.cast_pos (α:=ℝ).mpr ((le_max_right ..).trans hm)
    have factor : C ≤ (m:ℝ)^(δ/2) := absorb m ((le_max_right ..).trans lo)
    refine ⟨m,(le_max_left ..).trans lo,pay.trans ?_⟩
    apply (mul_le_mul_of_nonneg_right factor (rpow_nonneg mp.le _)).trans_eq
    rw [←rpow_add mp]
    congr 1
    ring
  · intro h δ ep
    exact ⟨1,zero_lt_one,fun A => by simpa only [one_mul] using h δ ep A⟩

end RiemannReduction.ShortTail.LossFrequency
