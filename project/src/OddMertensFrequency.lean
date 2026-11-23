import OddTailCriterion
import OddKernelCells
import SecondOddQuotient

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real RiemannGaussian.AlpogeMined

/-- A finite ordinary Mertens bound up to ⌊m⁸/2⌋ controls the frequency of the
two original odd sums on a single complete block, at all real thresholds. -/
theorem odd_frequency_of_finite_prefix {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (cp : 0 ≤ C)
    (mertens : ∀ k ≤ m^8/2, |fixedBandPrefix k| ≤ C*sqrt k) (t : ℝ) :
    t*eventMass oddAlarm m t ≤ 640*kernelConstant*C*(1+8*log m)^2 := by
  classical
  let W := 640*kernelConstant*C*(1+8*log m)
  have lm := log_natCast_nonneg m
  have W0 : 0≤W := by dsimp [W]; positivity [kernelConstant_nonneg]
  have height (n : ℕ) (hn : n ∈ Icc m (m^2)) (hit : oddAlarm n t) : t ≤ W := by
    obtain ⟨j,_,bad⟩ := hit
    obtain ⟨mn,nm⟩ := mem_Icc.mp hn
    have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have scope : bandHi n j ≤ m^8/2 := by
      calc bandHi n j ≤ n^4/2 := min_le_left ..
           _ ≤ (m^2)^4/2 := Nat.div_le_div_right (Nat.pow_le_pow_left nm 4)
           _ = _ := by rw [←pow_mul]
    obtain ⟨oc,cc⟩ := both_signed_dyadic_of_mertens cp scope mertens
    have cost : share n 0 t < 80*kernelConstant*C*(n:ℝ)^2 := by
      rcases bad with odd|half
      · linarith only [odd,(neg_le_abs _).trans oc]
      · exact half.trans_le ((le_abs_self _).trans cc)
    have bp : 0<(bandCount n 0:ℝ) := by unfold bandCount; positivity
    have den := mul_lt_mul_of_pos_right cost (show 0<4*(bandCount n 0:ℝ) by positivity)
    have eq : share n 0 t*(4*(bandCount n 0:ℝ))=t*(n:ℝ)^2 := by unfold share; field_simp; ring
    have h : t*(n:ℝ)^2 ≤ (320*kernelConstant*C*(bandCount n 0:ℝ))*(n:ℝ)^2 := by
      linarith only [den,eq]
    have factor := le_of_mul_le_mul_right h (pow_pos np 2)
    have lg := log_le_log np (show (n:ℝ)≤(m:ℝ)^2 by exact_mod_cast nm)
    rw [log_pow,Nat.cast_ofNat] at lg
    have B := band_count_log (by omega : 1 ≤ n)
    have cap : (bandCount n 0:ℝ) ≤ 2*(1+8*log m) := by linarith only [B,lg]
    have mul := mul_le_mul_of_nonneg_left cap (show 0≤320*kernelConstant*C by positivity [kernelConstant_nonneg])
    dsimp [W]
    linarith only [factor,mul]
  unfold eventMass
  rw [mul_sum]
  have termBound (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      t*(if oddAlarm n t then (n:ℝ)⁻¹ else 0) ≤ W*(n:ℝ)⁻¹ := by
    split_ifs with hit
    · exact mul_le_mul_of_nonneg_right (height n hn hit) (by positivity)
    · rw [mul_zero]; positivity
  apply (sum_le_sum termBound).trans
  rw [←mul_sum]
  have harmonic := (harmonic_window (by omega : 1 ≤ m)).trans (show 1+2*log m ≤ 1+8*log m by linarith only [lm])
  exact (mul_le_mul_of_nonneg_left harmonic W0).trans_eq (by dsimp [W]; ring)

/-- A common ordinary-Mertens envelope of size A m^β on arbitrarily late
blocks gives the desired separate frequencies for any strictly larger exponent. -/
theorem odd_frequency_of_cofinal_mertens {β δ : ℝ} (gap : β<δ)
    (mertens : ∃ A > (0:ℝ), ∀ L : ℕ, ∃ m ≥ L, ∀ k ≤ m^8/2,
      |fixedBandPrefix k| ≤ (A*(m:ℝ)^β)*sqrt k) : sharedEventBound oddAlarm δ := by
  obtain ⟨A,ap,blocks⟩ := mertens
  have ηp : 0 < δ-β := sub_pos.mpr gap
  have absorb := absorb_log_square (640*kernelConstant*A) (by positivity [kernelConstant_nonneg]) ηp
  obtain ⟨B,after⟩ := eventually_atTop.mp absorb
  refine ⟨1,zero_lt_one,fun L => ?_⟩
  obtain ⟨m,large,all⟩ := blocks (max L (max B 2))
  have both := (le_max_right L (max B 2)).trans large
  have mp : 0<(m:ℝ) := Nat.cast_pos.mpr (by omega)
  have gain := after m ((le_max_left B 2).trans both)
  refine ⟨m,(le_max_left ..).trans large,fun j => ?_⟩
  have s := odd_frequency_of_finite_prefix ((le_max_right B 2).trans both) (by positivity : 0 ≤ A*(m:ℝ)^β) all ((2:ℝ)^j)
  have stretch := mul_le_mul_of_nonneg_right gain (rpow_nonneg mp.le β)
  rw [←rpow_add mp,sub_add_cancel] at stretch
  linarith only [s,stretch]

theorem odd_frequency_of_mertens_power {η δ : ℝ} (hp : 0 ≤ η) (gap : 8*η<δ)
    (ordinary : ∃ A > (0:ℝ), ∀ k : ℕ, |fixedBandPrefix k| ≤ A*(k:ℝ)^η*sqrt k) : sharedEventBound oddAlarm δ := by
  apply odd_frequency_of_cofinal_mertens gap
  obtain ⟨A,ap,all⟩ := ordinary
  refine ⟨A,ap,fun L => ⟨max L 2,le_max_left ..,?_⟩⟩
  intro k cap
  let m := max L 2
  have cast : (k:ℝ) ≤ (m:ℝ)^8 := by exact_mod_cast cap.trans (Nat.div_le_self ..)
  have grow := rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) k) cast hp
  rw [←rpow_natCast_mul (Nat.cast_nonneg (α:=ℝ) m)] at grow
  have scale : (k:ℝ)^η ≤ (m:ℝ)^(8*η) := by simpa only [Nat.cast_ofNat] using grow
  exact (all k).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left scale ap.le) (sqrt_nonneg _))

theorem odd_subpower_of_mertens_subpower
    (ordinary : ∀ η > (0:ℝ), ∃ A > (0:ℝ), ∀ k : ℕ, |fixedBandPrefix k| ≤ A*(k:ℝ)^η*sqrt k) :
    ∀ δ > (0:ℝ), sharedEventBound oddAlarm δ := by
  intro δ ep
  have small : 0<δ/16 := by positivity
  exact odd_frequency_of_mertens_power small.le (by linarith) (ordinary _ small)

/-- All original dyadic bins and all positive thresholds on each full block
starting at 2 through 109. Hurst's numerical result is an explicit input. -/
theorem odd_frequency_hurst_blocks
    (hurst : ∀ k : ℕ, 33 ≤ k → k ≤ 10^16 → |fixedBandPrefix k| ≤ 571/1000*sqrt k)
    {m : ℕ} (lo : 2 ≤ m) (hi : m ≤ 109) (t : ℝ) :
    t*eventMass oddAlarm m t ≤ 640*kernelConstant*(1+8*log m)^2 := by
  have scope : m^8/2 ≤ 10^16 :=
    (Nat.div_le_div_right (Nat.pow_le_pow_left hi 8)).trans (by decide)
  simpa only [mul_one] using odd_frequency_of_finite_prefix lo (C:=1) zero_le_one
    (fun k hk => finite_mertens_sqrt hurst k (hk.trans scope)) t

end RiemannReduction.ShortTail.LossFrequency
