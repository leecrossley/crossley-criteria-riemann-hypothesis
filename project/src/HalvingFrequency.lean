import HalvingSize
import HalvingIntervals

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- Indices for which the interval shrinkage and kernel decay already pay
for all crossings, uniformly over the left cutoff. -/
def deepLayer (α : ℝ) (n j i : ℕ) : Prop :=
  (n:ℝ)^(2-α) ≤ (2:ℝ)^(i+2*j)

theorem halving_count_le_bands (n j : ℕ) : halvingCount n j ≤ bandCount n 0 := by
  have h : bandHi n j ≤ n^4 := (min_le_left ..).trans (Nat.div_le_self ..)
  simpa [halvingCount,bandCount] using Nat.succ_le_succ (Nat.log_mono_right (b:=2) h)

/-- Any crossing of the signed thresholds must lie below this curve in
quotient and depth. Here the clipped upper bound applies to both signs. -/
theorem signed_layer_ceiling {b n j i : ℕ} {t : ℝ} (hn : 1≤n) (hj : j<bandCount n 0)
    (hit : adverseLayer b n j i t) :
    t*(2:ℝ)^(i+2*j) ≤ 4*kernelConstant*(1+8*log n)^3*(n:ℝ)^2 := by
  have base := halved_net_size n j i (max b (bandLo n j))
  change |clippedBandNet b n j i| * (2:ℝ)^(i+2*j) ≤ _ at base
  have adverse : layerShare n j t < |clippedBandNet b n j i| := by
    rcases hit with neg|⟨_,pos⟩
    · linarith only [neg,neg_le_abs (clippedBandNet b n j i)]
    · exact pos.trans_le (le_abs_self _)
  let den : ℝ := 4*(bandCount n 0:ℝ)*(halvingCount n j:ℝ)
  have bp : 0<(bandCount n 0:ℝ) := by unfold bandCount; positivity
  have hp : 0<(halvingCount n j:ℝ) := by unfold halvingCount; positivity
  have dp : 0<den := by dsimp [den]; positivity
  have cancel : layerShare n j t*den=t*(n:ℝ)^2 := by
    unfold layerShare share den
    field_simp
    ring
  have scaled := mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right adverse.le (by positivity : 0≤(2:ℝ)^(i+2*j))).trans base) dp.le
  have left : (t*(2:ℝ)^(i+2*j))*(n:ℝ)^2 =
      (layerShare n j t*(2:ℝ)^(i+2*j))*den := by rw [show (layerShare n j t*(2:ℝ)^(i+2*j))*den =
      (layerShare n j t*den)*(2:ℝ)^(i+2*j) by ring,cancel]; ring
  have rank : j ≤ Nat.log 2 (n^4) := by simpa [bandCount] using hj
  have qn : (2:ℕ)^j ≤ n^4 := (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) rank).trans
    (Nat.pow_log_le_self _ (by positivity))
  have lg := log_le_log (by positivity : 0<(2:ℝ)^j) (show (2:ℝ)^j ≤ (n:ℝ)^4 by exact_mod_cast qn)
  rw [log_pow (n:ℝ) 4,Nat.cast_ofNat] at lg
  have ln := log_natCast_nonneg n
  have capB := band_count_log hn
  have capH : (halvingCount n j:ℝ) ≤ 1+8*log n :=
    (show (halvingCount n j:ℝ) ≤ (bandCount n 0:ℝ) by exact_mod_cast halving_count_le_bands n j).trans capB
  have capQ : 1+log ((2:ℝ)^j) ≤ 1+8*log n := by
    calc _ ≤ 1+4*log n := by linarith only [lg]
         _ ≤ _ := by linarith only [ln]
  have pair := mul_le_mul capB capH hp.le (by linarith only [ln])
  have triple := mul_le_mul capQ pair (mul_nonneg bp.le hp.le) (by linarith only [ln])
  have coeff := mul_le_mul_of_nonneg_left triple (show 0≤4*kernelConstant by positivity [kernelConstant_nonneg])
  have scale := mul_le_mul_of_nonneg_right coeff (pow_nonneg (Nat.cast_nonneg (α:=ℝ) n) 4)
  rw [←left] at scaled
  apply le_of_mul_le_mul_right _ (pow_pos (show 0<(n:ℝ) by exact_mod_cast (show 0<n by omega)) 2)
  dsimp [den] at scaled
  linarith only [scaled,scale]

private theorem deep_height {α t : ℝ} (tp : 0<t) {b n j i : ℕ} (hn : 1≤n)
    (hj : j<bandCount n 0) (deep : deepLayer α n j i) (hit : adverseLayer b n j i t) :
    t ≤ 4*kernelConstant*(1+8*log n)^3*(n:ℝ)^α := by
  have np : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have core := (mul_le_mul_of_nonneg_left deep tp.le).trans (signed_layer_ceiling hn hj hit)
  have scale := mul_le_mul_of_nonneg_right core (rpow_nonneg np.le α)
  have eqn : (n:ℝ)^(2-α)*(n:ℝ)^α=(n:ℝ)^2 := by rw [←rpow_add np,sub_add_cancel,rpow_two]
  rw [mul_assoc t,eqn] at scale
  apply le_of_mul_le_mul_right _ (pow_pos np 2)
  linarith only [scale]

/-- A pointwise power bound at a crossing gives a harmonic frequency
bound across the whole block, uniform in its threshold. -/
theorem event_frequency_from_height {test : ℕ → ℝ → Prop} {α C : ℝ}
    (ha : 0≤α) (cp : 0≤C)
    (height : ∀ n : ℕ, 1≤n → ∀ t : ℝ, 0<t → test n t →
      t ≤ C*(1+8*log n)^3*(n:ℝ)^α) {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (tp : 0<t) :
    t*eventMass test m t ≤ 8*C*(1+8*log m)^4*(m:ℝ)^(2*α) := by
  classical
  let U := 8*C*(1+8*log m)^3*(m:ℝ)^(2*α)
  have mp : 0<(m:ℝ) := Nat.cast_pos.mpr (by omega)
  have lm := log_natCast_nonneg m
  have up : 0≤U := by dsimp [U]; positivity
  have ceiling (n : ℕ) (hn : n∈Icc m (m^2)) (alarm : test n t) : t≤U := by
    obtain ⟨mn,nm⟩ := mem_Icc.mp hn
    have np : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
    have nr : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast nm
    have first := height n (by omega) t tp alarm
    have l := log_le_log np nr
    rw [log_pow,Nat.cast_ofNat] at l
    have c := pow_le_pow_left₀ (show 0≤1+8*log n by linarith only [log_natCast_nonneg n])
      (show 1+8*log n ≤ 2*(1+8*log m) by linarith only [l]) 3
    have power := rpow_le_rpow np.le nr ha
    rw [←rpow_natCast_mul mp.le] at power
    norm_num only [Nat.cast_ofNat] at power
    have scale := mul_le_mul c power (rpow_nonneg np.le _) (by positivity)
    have endp := mul_le_mul_of_nonneg_left scale cp
    dsimp [U]
    linarith only [first,endp]
  unfold eventMass
  rw [mul_sum]
  have single (n : ℕ) (hn : n∈Icc m (m^2)) :
      t*(if test n t then (n:ℝ)⁻¹ else 0) ≤ U*(n:ℝ)⁻¹ := by
    split_ifs with hit
    · exact mul_le_mul_of_nonneg_right (ceiling n hn hit) (by positivity)
    · rw [mul_zero]; positivity
  apply (sum_le_sum single).trans
  rw [←mul_sum]
  have harmonic := (harmonic_window (by omega : 1≤ m)).trans (show 1+2*log m ≤ 1+8*log m by linarith only [lm])
  exact (mul_le_mul_of_nonneg_left harmonic up).trans_eq (by dsimp [U]; ring)

theorem event_subpower_from_height {test : ℕ → ℝ → Prop} {α C δ : ℝ}
    (ha : 0≤α) (cp : 0≤C) (gap : 2*α<δ)
    (height : ∀ n : ℕ, 1≤n → ∀ t : ℝ, 0<t → test n t →
      t ≤ C*(1+8*log n)^3*(n:ℝ)^α) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0<t → t*eventMass test m t ≤ (m:ℝ)^δ := by
  let η := (δ-2*α)/2
  have ep : 0<η := by dsimp [η]; linarith
  have c0 : 0≤8*C := by positivity
  filter_upwards [absorb_log_square (8*C) c0 ep,absorb_log_square 1 zero_le_one ep,
    eventually_ge_atTop 2] with m one two hm t tp
  have mp : 0<(m:ℝ) := Nat.cast_pos.mpr (by omega)
  have lm := log_natCast_nonneg m
  rw [one_mul] at two
  have both := mul_le_mul one two (by positivity) (rpow_nonneg mp.le η)
  have whole := mul_le_mul_of_nonneg_right both (rpow_nonneg mp.le (2*α))
  rw [←rpow_add mp,←rpow_add mp,show η+η+2*α=δ by dsimp [η]; ring] at whole
  exact (event_frequency_from_height ha cp height hm tp).trans (by linarith only [whole])

private theorem selected_deep_height {α : ℝ} (b : ℕ→ℕ) (n : ℕ) (hn : 1≤n)
    (t : ℝ) (tp : 0<t) (alarm : selectedLayerEvent b (deepLayer α) n t) :
    t ≤ (4*kernelConstant)*(1+8*log n)^3*(n:ℝ)^α := by
  obtain ⟨j,hj,i,_,deep,hit⟩ := alarm
  exact deep_height tp hn hj deep hit

/-- All deep layers satisfy one explicit estimate throughout a square block. -/
theorem deep_layer_frequency {α : ℝ} (ha : 0≤α) (b : ℕ → ℕ) {m : ℕ} (hm : 2 ≤ m)
    {t : ℝ} (tp : 0<t) :
    t*eventMass (selectedLayerEvent b (deepLayer α)) m t ≤
      32*kernelConstant*(1+8*log m)^4*(m:ℝ)^(2*α) := by
  have h := event_frequency_from_height ha
    (show 0≤4*kernelConstant by positivity [kernelConstant_nonneg]) (selected_deep_height b) hm tp
  convert h using 1
  ring

/-- Every positive threshold passes on every sufficiently late block. -/
theorem deep_layer_subpower {α δ : ℝ} (ha : 0≤α) (gap : 2*α<δ) (b : ℕ → ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0<t →
      t*eventMass (selectedLayerEvent b (deepLayer α)) m t ≤ (m:ℝ)^δ :=
  event_subpower_from_height ha (by positivity [kernelConstant_nonneg]) gap (selected_deep_height b)

end RiemannReduction.ShortTail.LossFrequency
