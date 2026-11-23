import ZeroFreeShellCriterion

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- An atom on the square block has mass at least 1/m². This gives a polynomial
cutoff for its layer cake from a fixed weak bound of exponent at most five. -/
private theorem fixed_level_cap (z : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) {η : ℝ} (e5 : η ≤ 5)
    (wk : ∀ j : ℕ, (2:ℝ)^j * frequency z m ((2:ℝ)^j) ≤ 2*(m:ℝ)^η) :
    ∀ n ∈ Icc m (m^2), z n ≤ (2:ℝ)^(bandCount (m^2) 0) := by
  classical
  intro n row
  let J := bandCount (m^2) 0
  let t := (2:ℝ)^J
  by_contra! hit
  have mp : (2:ℝ) ≤ m := by exact_mod_cast hm
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by have h := (mem_Icc.mp row).1; omega)
  have nm : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast (mem_Icc.mp row).2
  have atom : (n:ℝ)⁻¹ ≤ frequency z m t := by
    have nn (i : ℕ) (_ : i ∈ Icc m (m^2)) :
        0 ≤ (if t < z i then (i:ℝ)⁻¹ else 0) := by split <;> positivity
    simpa only [frequency, if_pos (show t < z n from hit)] using single_le_sum nn row
  have expCap : (m:ℝ)^η ≤ (m:ℝ)^5 := calc
    _ ≤ (m:ℝ)^(5:ℝ) := rpow_le_rpow_of_exponent_le (by linarith) e5
    _ = _ := by norm_num
  have scale : 2*(m:ℝ)^η ≤ (m:ℝ)^6 := calc
    _ ≤ (m:ℝ)*(m:ℝ)^5 := mul_le_mul mp expCap (rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    _ = _ := by ring
  have pay := ((mul_le_mul_of_nonneg_left atom (show 0 ≤ t by dsimp [t]; positivity)).trans (wk J)).trans scale
  rw [←div_eq_mul_inv] at pay
  have small := ((div_le_iff₀ np).mp pay).trans (mul_le_mul_of_nonneg_left nm (by positivity))
  have big : (m:ℝ)^8 < t := by
    have q := Nat.lt_pow_succ_log_self (by decide : 1 < 2) ((m^2)^4)
    dsimp [t,J,bandCount]
    simp only [Nat.div_one,←pow_mul] at *
    exact_mod_cast q
  linarith only [small,big]

/-- A logarithmic layer-cake loss can be absorbed in any strict exponent gap.
All sufficiently late blocks work, with coefficient one in the resulting moment. -/
theorem eventual_moment_of_fixed_frequency (z : ℕ → ℝ) {η δ : ℝ}
    (ep : 0 ≤ η) (e5 : η ≤ 5) (spare : η < δ)
    (bound : ∀ᶠ m : ℕ in atTop, ∀ j : ℕ,
      (2:ℝ)^j * frequency z m ((2:ℝ)^j) ≤ 2*(m:ℝ)^η) :
    ∀ᶠ m : ℕ in atTop, weighted z m ≤ (m:ℝ)^δ := by
  filter_upwards [bound, eventually_ge_atTop (2:ℕ),
    absorb_log_square 5 (by norm_num) (sub_pos.mpr spare)] with m wk hm absorb
  have m1 : 1 ≤ m := by omega
  have mr : (1:ℝ) ≤ m := by exact_mod_cast m1
  have mp := Nat.cast_pos (α:=ℝ).mpr m1
  let J := bandCount (m^2) 0
  let L := 1+8*log (m:ℝ)
  let p := (m:ℝ)^η
  have pp : 1 ≤ p := one_le_rpow mr ep
  have ll : 1 ≤ L := by dsimp [L]; linarith only [log_natCast_nonneg m]
  have jcap : (J:ℝ) ≤ 2*L := by
    have lj := band_count_log (Nat.one_le_pow 2 m m1)
    rw [Nat.cast_pow,log_pow] at lj
    norm_num only [Nat.cast_ofNat] at lj
    dsimp [L,J]
    linarith only [lj]
  have harm : (∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹) ≤ L :=
    (harmonic_window m1).trans (by dsimp [L]; linarith only [log_natCast_nonneg m])
  have sums := sum_le_sum (s:=range J) (fun j _ => wk j)
  simp only [sum_const,card_range,nsmul_eq_mul] at sums
  have cost := weighted_le_levels z m J (fixed_level_cap z hm e5 wk)
  have raw : weighted z m ≤ 5*L*p := by
    have a := mul_le_mul_of_nonneg_right jcap (show 0 ≤ 2*p by positivity)
    have b := mul_le_mul_of_nonneg_left pp (zero_le_one.trans ll)
    change (∑ j ∈ range J, _) ≤ (J:ℝ)*(2*p) at sums
    linarith only [cost,sums,harm,a,b]
  have logs : 5*L ≤ (m:ℝ)^(δ-η) := calc
    _ ≤ 5*L^2 := by nlinarith only [mul_nonneg (zero_le_one.trans ll) (sub_nonneg.mpr ll)]
    _ ≤ _ := absorb
  refine raw.trans ((mul_le_mul_of_nonneg_right logs (zero_le_one.trans pp)).trans_eq ?_)
  dsimp [p]
  rw [←rpow_add mp,sub_add_cancel]

/-- The same open range δ > 8θ−4 applies to the harmonic first moment of the
true worst shell. The proof runs the frequency theorem at a smaller exponent. -/
theorem full_shell_moment_of_zero_free {θ δ : ℝ} (half : 1/2 ≤ θ) (one : θ ≤ 1)
    (nz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) (gap : 8*θ-4 < δ) :
    ∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m:ℝ)^δ := by
  let η := min ((δ+(8*θ-4))/2) (9/2)
  have middle : 8*θ-4 < η := lt_min (by linarith only [gap]) (by linarith only [one])
  have cutoff : η ≤ 5 := (min_le_right ..).trans (by norm_num)
  have spare : η < δ := (min_le_left ..).trans_lt (by linarith only [gap])
  apply eventual_moment_of_fixed_frequency uniformShellScore (η:=η) (by linarith only [half,middle]) cutoff spare
  filter_upwards [full_shell_frequency_of_zero_free half one nz middle] with m all j
  exact all _ (by positivity)

end RiemannReduction.ShortTail.LossFrequency
