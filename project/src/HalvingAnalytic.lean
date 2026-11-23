import HalvingIntervals
import OddLocalOscillation

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real RiemannGaussian.AlpogeMined RiemannReduction.ThirdBridge
open scoped ArithmeticFunction.Moebius

private theorem ordinary_abel {a b : ℕ} (w : ℕ → ℝ) {H : ℝ} (hp : 0≤H)
    (bound : ∀ k ≤ b, |fixedBandPrefix k|≤H) :
    |∑ d ∈ Ioc a b, (μ d:ℝ)*w d| ≤ H*endpointVariation a b w := by
  by_cases ab : a<b
  · have base := sum_Ioc_by_parts w (fun k : ℕ => (μ k:ℝ)) ab
    simp only [smul_eq_mul] at base
    have eq : (∑ d ∈ Ioc a b, (μ d:ℝ)*w d)= w b*fixedBandPrefix b-w (a+1)*fixedBandPrefix a -
        ∑ k ∈ Ioc a (b-1), (w (k+1)-w k)*fixedBandPrefix k := by
      unfold fixedBandPrefix
      rw [←base]
      exact sum_congr rfl fun _ _ => mul_comm ..
    have edges (x k : ℕ) (hk : k≤b) : |w x*fixedBandPrefix k| ≤ |w x| * H := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (bound k hk) (abs_nonneg _)
    have mid := (abs_sum_le_sum_abs (fun k => (w (k+1)-w k)*fixedBandPrefix k) (Ioc a (b-1))).trans
      (sum_le_sum (g:=fun k => |w (k+1)-w k| * H) (fun k hk => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (bound k ((mem_Ioc.mp hk).2.trans (Nat.sub_le ..))) (abs_nonneg _)))
    rw [←sum_mul] at mid
    rw [eq]
    have left := (abs_sub (w b*fixedBandPrefix b) (w (a+1)*fixedBandPrefix a)).trans
      (add_le_add (edges b b le_rfl) (edges (a+1) a ab.le))
    apply (abs_sub ..).trans
    unfold endpointVariation
    linarith only [left,mid]
  · rw [Ioc_eq_empty_of_le (le_of_not_gt ab),sum_empty,abs_zero]
    exact mul_nonneg hp (endpointVariation_nonneg ..)

private theorem layer_cost_pos (j : ℕ) : 0<oscillationCost j := by
  have q : (1:ℝ) ≤ ((2^j:ℕ):ℝ) := by exact_mod_cast Nat.one_le_pow j 2 (by decide)
  have lg : 0≤log (2*((2^j:ℕ):ℝ)) := log_nonneg (by linarith)
  unfold oscillationCost kernelConstant
  positivity

private theorem K_positive : 0<kernelConstant := by unfold kernelConstant; positivity

/-- Ordinary Möbius prefixes control each clipped, halved net at its actual
upper divisor endpoint. This applies uniformly to the empty interval. -/
theorem clipped_net_of_ordinary_prefix (b n j i : ℕ) {H : ℝ} (hp : 0≤H)
    (control : ∀ k ≤ bandHi n j/2^i, |fixedBandPrefix k|≤H) :
    |clippedBandNet b n j i| ≤ H*oscillationCost j := by
  let r := (2:ℕ)^i
  let a := max b (bandLo n j)/r
  let u := bandHi n j/r
  let p (d : ℕ) := r*d
  let w (d : ℕ) := rowWeight n (p d)
  have eq : clippedBandNet b n j i = ∑ d ∈ Ioc a u, (μ d:ℝ)*w d := by
    simp [clippedBandNet,halvedNet,intervalNet,w,p,r,a,u,rowWeight,surviving,div_div]
  rw [eq]
  by_cases au : a<u
  · have rp : 0<r := by dsimp [r]; positivity
    have source : Set.MapsTo p (Set.Icc (a+1) u) (Set.Icc (bandLo n j+1) (bandHi n j)) := by
      intro d hd
      have lo : max b (bandLo n j) < d*r := (Nat.div_lt_iff_lt_mul rp).mp hd.1
      have hi : d*r ≤ bandHi n j := (Nat.le_div_iff_mul_le rp).mp hd.2
      exact ⟨by simpa [p,Nat.mul_comm] using (le_max_right b (bandLo n j)).trans_lt lo,
        by simpa [p,Nat.mul_comm] using hi⟩
    have shape := variation_on_original_samples au (show Monotone p from fun _ _ h => Nat.mul_le_mul_left r h)
      source signed_kernel_quotient_cells
    exact (ordinary_abel w hp control).trans (mul_le_mul_of_nonneg_left shape hp)
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty,abs_zero]
    exact mul_nonneg hp (layer_cost_pos j).le

private theorem halving_count_log {n j : ℕ} (hn : 1≤n) : (halvingCount n j:ℝ) ≤ 1+8*log n := by
  have mono : halvingCount n j ≤ bandCount n 0 := by
    simp only [halvingCount,bandCount,zero_add,Nat.div_one]
    apply Nat.succ_le_succ
    exact Nat.log_mono_right ((min_le_left ..).trans (Nat.div_le_self ..) : bandHi n j≤n^4)
  exact (show (halvingCount n j:ℝ)≤bandCount n 0 by exact_mod_cast mono).trans (band_count_log hn)

/-- The two counting factors and the kernel variation cost at most three
logarithms. The estimate uses the true net, including its cutoff and halving. -/
theorem adverse_layer_height {b n j i : ℕ} (hn : 1≤n) (hj : j<bandCount n 0) {t H : ℝ}
    (tp : 0≤t) (hp : 0≤H) (hit : adverseLayer b n j i t)
    (control : ∀ k ≤ bandHi n j/2^i, |fixedBandPrefix k|≤H) :
    t*(n:ℝ)^2 ≤ 80*kernelConstant*H*(1+8*log n)^3 := by
  have net := clipped_net_of_ordinary_prefix b n j i hp control
  have kpos : 0<(halvingCount n j:ℝ) := by unfold halvingCount; positivity
  have logn := log_natCast_nonneg n
  have lpos : 0<1+8*log n := by positivity
  have raw : layerShare n j t < H*oscillationCost j := by
    rcases hit with neg|⟨_,pos⟩
    · linarith only [neg,(neg_le_abs _).trans net]
    · exact pos.trans_le ((le_abs_self _).trans net)
  have scaled := (div_lt_iff₀ kpos).mp raw
  have shareBound : share n 0 t/oscillationCost j ≤ H*(halvingCount n j:ℝ) := by
    apply (div_le_iff₀ (layer_cost_pos j)).mpr
    linarith only [scaled]
  have thresh := (normalized_threshold_le hn hj tp).trans shareBound
  have pay := (div_le_iff₀ (show 0<80*kernelConstant*(1+8*log n)^2 by positivity [K_positive])).mp thresh
  have count := mul_le_mul_of_nonneg_left (halving_count_log (j:=j) hn)
    (show 0≤H*(80*kernelConstant*(1+8*log n)^2) by positivity [kernelConstant_nonneg])
  linarith only [pay,count]

open Filter

/-- Sanftenberg's quantitative Gaussian contour estimate in the ordinary
integer-prefix normalization used by the clipped nets. -/
def CubicContourRemainder : Prop :=
  ∃ C : ℝ, 0≤C ∧ ∃ B : ℝ, 0≤B ∧ ∃ H : ℝ, ∀ h ≥ H, ∀ k : ℕ,
    |fixedBandPrefix k| ≤ C*exp (-h/2)*(k:ℝ)+exp (B*h^3)

private theorem absorb_log_power (p : ℕ) (A : ℝ) (ap : 0≤A) :
    ∀ᶠ x : ℝ in atTop, A*(log x)^p ≤ x := by
  have little := (isLittleO_log_rpow_rpow_atTop (p:ℝ) (by norm_num : 0<(1:ℝ))).const_mul_left A
  filter_upwards [little.bound (c:=1) zero_lt_one,eventually_ge_atTop (1:ℝ)] with x h hx
  change ‖A*(log x)^(p:ℝ)‖ ≤ 1*‖x^(1:ℝ)‖ at h
  simpa only [rpow_natCast,rpow_one,Real.norm_of_nonneg (mul_nonneg ap (pow_nonneg (log_nonneg hx) _)),
    Real.norm_of_nonneg (zero_le_one.trans hx),one_mul] using h

/-- All ordinary prefixes through n⁴ save every fixed logarithmic power
against n⁴. The contour heat and height are chosen afresh for each n. -/
theorem log_power_prefix_budget (source : CubicContourRemainder) (r : ℕ) :
    ∃ C > (0:ℝ), ∀ᶠ n : ℕ in atTop, ∀ k ≤ n^4,
      |fixedBandPrefix k| * (1+8*log n)^(r+3) ≤ C*(n:ℝ)^4 := by
  obtain ⟨C,cp,B,bp,H,control⟩ := source
  refine ⟨C+1,by positivity,?_⟩
  let p := r+3
  let L (n : ℕ) := 1+8*log n
  have pp : 0<(p:ℝ) := by dsimp [p]; positivity
  have dp : 0<2*(p:ℝ) := by positivity
  have nt := tendsto_natCast_atTop_atTop (R:=ℝ)
  have logn := tendsto_log_atTop.comp nt
  have ltend : Tendsto L atTop atTop := by
    apply tendsto_atTop.mpr
    intro z
    filter_upwards [logn.eventually_ge_atTop z,logn.eventually_ge_atTop 1] with n h1 h2
    change z ≤ 1+8*log n
    change z ≤ log n at h1
    change 1 ≤ log n at h2
    linarith
  have large := (tendsto_log_atTop.comp ltend).eventually_ge_atTop (H/(2*(p:ℝ)))
  have outer := ltend.eventually (absorb_log_power 3 (16*B*(2*(p:ℝ))^3) (by positivity))
  have inner := nt.eventually (absorb_log_power p ((9:ℝ)^p) (by positivity))
  filter_upwards [large,outer,inner,logn.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)]
    with n boundHeight cubic logpower loglarge nn k cap
  change 1≤log n at loglarge
  change H/(2*(p:ℝ))≤log (L n) at boundHeight
  change 16*B*(2*(p:ℝ))^3*(log (L n))^3≤L n at cubic
  change (9:ℝ)^p*(log n)^p≤(n:ℝ) at logpower
  let h := (2*(p:ℝ))*log (L n)
  have hH : H≤h := by dsimp [h]; linarith only [(div_le_iff₀ dp).mp boundHeight]
  have Y : 0<L n := by dsimp [L]; positivity [log_natCast_nonneg n]
  have center : B*h^3 ≤ log n := by
    dsimp [h,L] at *
    linarith only [cubic,loglarge]
  have width : exp (B*h^3) ≤ n := (exp_le_exp.mpr center).trans_eq
    (exp_log (Nat.cast_pos.mpr (by omega : 0<n)))
  have saved : exp (-h/2)*(L n)^p=1 := by
    rw [show -h/2 = -log ((L n)^p) by rw [log_pow]; dsimp [h]; ring,
      exp_neg,exp_log (pow_pos Y p),inv_mul_cancel₀ (pow_pos Y p).ne']
  have paid : (L n)^p≤n := by
    apply le_trans _ logpower
    rw [←mul_pow]
    apply pow_le_pow_left₀ Y.le
    dsimp [L]
    linarith only [loglarge]
  have small := mul_le_mul width paid (pow_nonneg Y.le _) (Nat.cast_nonneg (α:=ℝ) n)
  have np : (1:ℝ)≤n := by exact_mod_cast nn
  have sqbound : (n:ℝ)*(n:ℝ)≤(n:ℝ)^4 := by
    rw [←sq]
    exact pow_le_pow_right₀ np (by decide)
  have first := mul_le_mul_of_nonneg_right (control h hH k) (pow_nonneg Y.le p)
  change |fixedBandPrefix k| * (L n)^p ≤ _
  calc
    _ ≤ C*(k:ℝ)+exp (B*h^3)*(L n)^p := first.trans_eq (by
      rw [add_mul,show C*exp (-h/2)*(k:ℝ)*(L n)^p = C*(k:ℝ)*(exp (-h/2)*(L n)^p) by ring,saved,mul_one])
    _ ≤ C*(n:ℝ)^4+(n:ℝ)^4 := add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast cap) cp) (small.trans sqbound)
    _ = _ := by ring

/-- On every sufficiently late block, at all nonnegative real thresholds
and for any clipping and layer mask, the weighted mass saves every fixed
logarithmic power at exponent four. -/
theorem selected_log_frequency_of_cubic_contour (source : CubicContourRemainder) (r : ℕ) :
    ∃ D > (0:ℝ), ∀ᶠ m : ℕ in atTop, ∀ (b : ℕ → ℕ) (keep : ℕ → ℕ → ℕ → Prop) (t : ℝ),
      0≤t → (1+8*log m)^r*t*eventMass (selectedLayerEvent b keep) m t ≤ D*(m:ℝ)^4 := by
  obtain ⟨C,cp,B,budget⟩ := (show ∃ C > (0:ℝ), ∃ B : ℕ, ∀ n ≥ B, ∀ k ≤ n^4,
      |fixedBandPrefix k| * (1+8*log n)^(r+3) ≤ C*(n:ℝ)^4 by
    obtain ⟨C,cp,h⟩ := log_power_prefix_budget source r
    exact ⟨C,cp,eventually_atTop.mp h⟩)
  let D := 80*kernelConstant*C
  have dp : 0<D := by dsimp [D]; positivity [K_positive]
  refine ⟨D,dp,?_⟩
  filter_upwards [eventually_ge_atTop (max B 1)] with m hm b keep t tp
  classical
  let L (n : ℕ) := 1+8*log n
  have lpos (n : ℕ) : 0<L n := by dsimp [L]; positivity [log_natCast_nonneg n]
  have single (n : ℕ) (hn : n ∈ Icc m (m^2)) (yes : selectedLayerEvent b keep n t) :
      (L m)^r*t ≤ D*(n:ℝ)^2 := by
    obtain ⟨mn,_⟩ := mem_Icc.mp hn
    obtain ⟨j,hj,i,_,_,bad⟩ := yes
    have nn : 1≤n := by omega
    have npos : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
    let H := C*(n:ℝ)^4/(L n)^(r+3)
    have Hpos : 0≤H := by dsimp [H]; positivity [lpos]
    have ctl (k : ℕ) (hk : k≤bandHi n j/2^i) : |fixedBandPrefix k| ≤ H := by
      apply (le_div_iff₀ (pow_pos (lpos n) _)).mpr
      have hK : k≤n^4 := hk.trans ((Nat.div_le_self ..).trans ((min_le_left ..).trans (Nat.div_le_self ..)))
      exact budget n (by omega) k hK
    have trig := adverse_layer_height nn hj tp Hpos bad ctl
    change t*(n:ℝ)^2 ≤ 80*kernelConstant*H*(L n)^3 at trig
    have height := mul_le_mul_of_nonneg_right trig (pow_nonneg (lpos n).le r)
    have paid : 80*kernelConstant*H*(L n)^3*(L n)^r=D*(n:ℝ)^4 := by
      dsimp [H,D]
      rw [pow_add]
      field_simp [(lpos n).ne']
    rw [paid] at height
    have reduced : (L n)^r*t ≤ D*(n:ℝ)^2 := by
      apply le_of_mul_le_mul_right _ (pow_pos npos 2)
      linarith only [height]
    have lm : L m≤L n := by
      dsimp [L]
      have mb : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
      linarith only [log_le_log mb (show (m:ℝ)≤(n:ℝ) by exact_mod_cast mn)]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (lpos m).le lm r) tp).trans reduced
  unfold eventMass
  rw [mul_sum]
  have each (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      (L m)^r*t*(if selectedLayerEvent b keep n t then (n:ℝ)⁻¹ else 0) ≤ D*(m:ℝ)^2 := by
    split_ifs with hit
    · obtain ⟨mn,up⟩ := mem_Icc.mp hn
      have npos : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
      have cap : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast up
      rw [←div_eq_mul_inv]
      apply (div_le_iff₀ npos).mpr
      have bound := mul_le_mul_of_nonneg_right cap (mul_nonneg dp.le npos.le)
      linarith only [single n hn hit,bound]
    · rw [mul_zero]
      positivity
  have count : ((Icc m (m^2)).card:ℝ) ≤ (m:ℝ)^2 := by
    exact_mod_cast (show (Icc m (m^2)).card ≤ m^2 by rw [Nat.card_Icc]; omega)
  have total := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at total
  apply total.trans
  linarith only [mul_le_mul_of_nonneg_right count (show 0≤D*(m:ℝ)^2 by positivity)]

theorem selected_four_of_cubic_contour (source : CubicContourRemainder) (b : ℕ → ℕ)
    (keep : ℕ → ℕ → ℕ → Prop) : sharedEventBound (selectedLayerEvent b keep) 4 := by
  obtain ⟨D,dp,freq⟩ := selected_log_frequency_of_cubic_contour source 0
  obtain ⟨B,all⟩ := eventually_atTop.mp freq
  refine ⟨D,dp,fun A => ⟨max A B,le_max_left ..,fun j => ?_⟩⟩
  simpa using all (max A B) (le_max_right ..) b keep ((2:ℝ)^j) (by positivity)

end RiemannReduction.ShortTail.LossFrequency
