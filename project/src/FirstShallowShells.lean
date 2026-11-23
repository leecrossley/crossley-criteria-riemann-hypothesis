import FirstShallowCriterion

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real RiemannReduction.ThirdBridge RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

/-- The complete dyadic divisor interval with its original Möbius signs and
Sanftenberg's corrected kernel. -/
def fullFirstShell (n j : ℕ) : ℝ :=
  ∑ d ∈ Ioc (n^4/2^(j+1)) (n^4/2^j), (μ d:ℝ)*surviving ((n:ℝ)^4/d)

/-- The share is t n²/(4B_n). Both the quotient condition and the full
signed shell refer to this same positive j. -/
def fullFirstShellEvent (δ : ℝ) (n : ℕ) (t : ℝ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ (2:ℝ)^j < (n:ℝ)^(1-3*δ/16) ∧
    fullFirstShell n j < -share n 0 t

private theorem quotient_root {n j : ℕ} {δ : ℝ}
    (shallow : (2:ℝ)^(2*j) < (n:ℝ)^(2-3*δ/8)) :
    (2:ℝ)^j < (n:ℝ)^(1-3*δ/16) := by
  have two : ((n:ℝ)^(1-3*δ/16))^2 = (n:ℝ)^(2-3*δ/8) := by
    rw [←rpow_two,←rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  have square : ((2:ℝ)^j)^2 < ((n:ℝ)^(1-3*δ/16))^2 := by
    rw [two,←pow_mul,Nat.mul_comm]
    exact shallow
  by_contra! wrong
  exact (not_lt_of_ge (pow_le_pow_left₀ (rpow_nonneg (Nat.cast_nonneg _) _) wrong 2)) square

theorem first_shell_quotient_iff (n j : ℕ) (δ : ℝ) :
    (2:ℝ)^(2*j) < (n:ℝ)^(2-3*δ/8) ↔ (2:ℝ)^j < (n:ℝ)^(1-3*δ/16) := by
  refine ⟨quotient_root,fun h => ?_⟩
  calc (2:ℝ)^(2*j) = ((2:ℝ)^j)^2 := by rw [←pow_mul,Nat.mul_comm]
       _ < ((n:ℝ)^(1-3*δ/16))^2 := by gcongr
       _ = (n:ℝ)^(2-3*δ/8) := by
         rw [←rpow_two,←rpow_mul (Nat.cast_nonneg _)]
         congr 1
         ring

theorem first_shell_share (n : ℕ) (t : ℝ) :
    share n 0 t=t*(n:ℝ)^2/(4*((Nat.log 2 (n^4)+1:ℕ):ℝ)) := by
  unfold share bandCount
  simp only [zero_add,Nat.div_one,div_div]
  congr 1
  ring

/-- The extra divisor cutoff lies below the bottom of the complete bin,
including the integer floors, once n^(δ/16) reaches two. -/
theorem power_cut_below_first_shell {n j : ℕ} {δ : ℝ} (hn : 1 ≤ n)
    (gap : (2:ℝ) ≤ (n:ℝ)^(δ/16)) (shallow : (2:ℝ)^(2*j) < (n:ℝ)^(2-3*δ/8)) :
    powerCut (δ/8) n ≤ n^4/2^(j+1) := by
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have lo := Nat.floor_le (show 0≤(n:ℝ)^3*(n:ℝ)^(δ/8) by positivity)
  change (powerCut (δ/8) n:ℝ) ≤ _ at lo
  have scaled := mul_le_mul (quotient_root shallow).le gap (by norm_num : (0:ℝ)≤2)
    (rpow_nonneg np.le (1-3*δ/16))
  have cap : ((n:ℝ)^3*(n:ℝ)^(δ/8))*((2:ℝ)^j*2) ≤ (n:ℝ)^4 := by
    calc _ ≤ ((n:ℝ)^3*(n:ℝ)^(δ/8))*((n:ℝ)^(1-3*δ/16)*(n:ℝ)^(δ/16)) :=
            mul_le_mul_of_nonneg_left scaled (by positivity)
         _ = _ := by
            rw [show (n:ℝ)^3=(n:ℝ)^(3:ℝ) by norm_num,
                show (n:ℝ)^4=(n:ℝ)^(4:ℝ) by norm_num,
                ←rpow_add np,←rpow_add np,←rpow_add np]
            congr 1
            ring
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < (2:ℕ)^(j+1))).mpr
  have cutoff : (powerCut (δ/8) n:ℝ)*(2:ℝ)^(j+1) ≤ (n:ℝ)^4 := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right lo (by positivity)).trans cap
  exact_mod_cast cutoff

private theorem inherited_cutoffs {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ (2:ℝ) ≤ (n:ℝ)^(δ/16) ∧
      cutoff n ≤ powerCut (δ/8) n ∧ fixedBandMultipleCutoff n ≤ powerCut (δ/8) n := by
  have grow := ((tendsto_rpow_atTop (show 0<δ/16 by positivity)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1:ℕ),grow,eventual_exp_sqrt 1 1 (δ/8) (by positivity)]
    with n hn gap small
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have log0 := log_natCast_nonneg n
  simp only [one_mul] at small
  have ex := (exp_le_exp.mpr (sqrt_le_sqrt (show log (n:ℝ) ≤ 2*log n by linarith))).trans small
  have low := Nat.floor_mono (mul_le_mul_of_nonneg_left ex (show 0 ≤ (n:ℝ)^3 by positivity))
  have cube : n^3 ≤ powerCut (δ/8) n := by
    apply Nat.le_floor
    push_cast
    have power : (1:ℝ) ≤ (n:ℝ)^(δ/8) := one_le_rpow n1 (by positivity)
    exact le_mul_of_one_le_right (by positivity) power
  exact ⟨hn,gap,low,(Nat.div_le_self ..).trans cube⟩

/-- All three lower cuts lie below the original quotient endpoint. For
positive bins the old upper cap n⁴/2 also disappears. -/
theorem first_shell_rows_eventually {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j →
      (2:ℝ)^(2*j) < (n:ℝ)^(2-3*δ/8) →
      laterRows n j (powerCut (δ/8) n) = Ioc (n^4/2^(j+1)) (n^4/2^j) := by
  filter_upwards [inherited_cutoffs ep] with n gates j jp shallow
  obtain ⟨hn,gap,cut,multi⟩ := gates
  have edge := power_cut_below_first_shell hn gap shallow
  have original : max (fixedBandMultipleCutoff n) (cutoff n) ≤ n^4/2^(j+1) :=
    max_le (multi.trans edge) (cut.trans edge)
  have two : 2 ≤ (2:ℕ)^j := by
    calc (2:ℕ) = 2^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by decide) jp
  have hi : n^4/2^j ≤ n^4/2 := Nat.div_le_div_left two (by decide)
  rw [later_rows_interval,bandLo,bandHi,max_eq_right original,max_eq_right edge,min_eq_right hi]

theorem clipped_first_zero_bin (b n : ℕ) : clippedBandNet b n 0 0=0 := by
  have lo : n^4/2 ≤ bandLo n 0 := by simp [bandLo]
  have hi : bandHi n 0 ≤ n^4/2 := min_le_left ..
  have off := Ioc_eq_empty_of_le ((hi.trans lo).trans (le_max_right b (bandLo n 0)))
  simp only [clippedBandNet,halvedNet,intervalNet,pow_zero,div_one,Nat.div_one,off,sum_empty]

/-- The full j=0 interval has divisors, but its kernel vanishes throughout
the quotient interval [1,2]. The retained j=0 interval itself is empty. -/
theorem full_first_zero_bin (n : ℕ) : fullFirstShell n 0=0 := by
  unfold fullFirstShell
  apply sum_eq_zero
  intro d hd
  simp only [zero_add,pow_one,pow_zero,Nat.div_one,mem_Ioc] at hd
  have dp : 0<d := (Nat.zero_le _).trans_lt hd.1
  have dr : 0<(d:ℝ) := Nat.cast_pos.mpr dp
  have lo : (1:ℝ)≤(n:ℝ)^4/d := (one_le_div dr).mpr (by exact_mod_cast hd.2)
  have hi : (n:ℝ)^4/d≤2 := (div_le_iff₀ dr).mpr (by exact_mod_cast (show n^4≤2*d by omega))
  rw [surviving,fixedBandFirstCorrection_first lo hi,sub_self,mul_zero]

private theorem shell_band_count {n j : ℕ} {δ : ℝ} (hn : 1 ≤ n) (ep : 0 < δ)
    (q : (2:ℝ)^j < (n:ℝ)^(1-3*δ/16)) : j < bandCount n 0 := by
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have upper : (n:ℝ)^(1-3*δ/16) ≤ (n:ℝ) :=
    (rpow_le_rpow_of_exponent_le n1 (show 1-3*δ/16 ≤ 1 by linarith)).trans_eq (rpow_one _)
  have native : (2:ℕ)^j ≤ n := by exact_mod_cast q.le.trans upper
  have n4 : n ≤ n^4 :=
    calc n = n^1 := by simp
         _ ≤ n^4 := Nat.pow_le_pow_right hn (by decide)
  have index := Nat.le_log_of_pow_le (by decide : 1<2) (native.trans n4)
  simpa [bandCount] using Nat.lt_succ_of_le index

/-- At every sufficiently large sample the events are identical for all
nonnegative thresholds. The untrimmed criterion quantifies only over
positive dyadic exponents, and requires no auxiliary bound on their number. -/
theorem first_shell_event_eventually {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 ≤ t →
      (residualFirstEvent δ n t ↔ fullFirstShellEvent δ n t) := by
  filter_upwards [first_shell_rows_eventually ep,eventually_ge_atTop (1:ℕ)] with n rows hn t tp
  have align (j : ℕ) (jp : 1 ≤ j) (cond : (2:ℝ)^(2*j) < (n:ℝ)^(2-3*δ/8)) :
      clippedBandNet (powerCut (δ/8) n) n j 0 = fullFirstShell n j := by
    have same := (later_rows_interval n j (powerCut (δ/8) n)).symm.trans (rows j jp cond)
    simp only [clippedBandNet,halvedNet,intervalNet,pow_zero,div_one,Nat.div_one,fullFirstShell,same]
  constructor
  · rintro ⟨j,_,cond,bad⟩
    have jp : 1 ≤ j := by
      by_contra! invalid
      have zero : j=0 := by omega
      rw [zero,clipped_first_zero_bin] at bad
      have nonnegative : 0 ≤ share n 0 t := by unfold share; positivity
      linarith only [bad,nonnegative]
    rw [align j jp cond] at bad
    exact ⟨j,jp,quotient_root cond,bad⟩
  · rintro ⟨j,jp,q,bad⟩
    have cond := (first_shell_quotient_iff n j δ).mpr q
    rw [←align j jp cond] at bad
    exact ⟨j,shell_band_count hn ep q,cond,bad⟩

theorem first_shell_frequency_eventually {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0 ≤ t →
      eventMass (residualFirstEvent δ) m t = eventMass (fullFirstShellEvent δ) m t := by
  classical
  obtain ⟨N,equal⟩ := eventually_atTop.mp (first_shell_event_eventually ep)
  filter_upwards [eventually_ge_atTop N] with m hm t tp
  unfold eventMass
  apply sum_congr rfl
  intro n hn
  rw [equal n (hm.trans (mem_Icc.mp hn).1) t tp]

/-- The constants and all the dyadic thresholds of a common square block
carry in either direction after imposing one lower bound on its starting point. -/
theorem first_shell_shared_iff {δ : ℝ} (ep : 0 < δ) :
    sharedEventBound (residualFirstEvent δ) δ ↔ sharedEventBound (fullFirstShellEvent δ) δ := by
  obtain ⟨N,equal⟩ := eventually_atTop.mp (first_shell_frequency_eventually ep)
  constructor <;> rintro ⟨C,cp,blocks⟩ <;> refine ⟨C,cp,fun A => ?_⟩
  · obtain ⟨m,hm,all⟩ := blocks (max A N)
    exact ⟨m,(le_max_left ..).trans hm,fun j => by
      rw [←equal m ((le_max_right ..).trans hm) _ (by positivity)]
      exact all j⟩
  · obtain ⟨m,hm,all⟩ := blocks (max A N)
    exact ⟨m,(le_max_left ..).trans hm,fun j => by
      rw [equal m ((le_max_right ..).trans hm) _ (by positivity)]
      exact all j⟩

/-- A shared-block frequency bound for negative complete dyadic Möbius
shells, for every positive exponent, suffices for the Riemann Hypothesis. -/
theorem rh_of_full_first_shells
    (h : ∀ δ > (0:ℝ), sharedEventBound (fullFirstShellEvent δ) δ) : RiemannHypothesis :=
  rh_of_residual_first fun δ ep => (first_shell_shared_iff ep).mpr (h δ ep)

end RiemannReduction.ShortTail.LossFrequency
