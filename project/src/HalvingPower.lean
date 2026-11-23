import HalvingAnalytic
import HalvingFrequency
import HalvingPowerInput

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real RiemannGaussian.AlpogeMined

/-- A Mertens prefix exponent gives a height estimate for every individual
signed halving, including depth zero, uniformly over the cutoff. -/
private theorem height_from_prefix_power {σ A : ℝ} (sp : 0≤σ) (ap : 0≤A)
    (control : ∀ k : ℕ, |fixedBandPrefix k| ≤ A*((k:ℝ)+1)^σ)
    (b : ℕ→ℕ) (keep : ℕ→ℕ→ℕ→Prop) (n : ℕ) (hn : 1≤n) (t : ℝ) (tp : 0<t)
    (hit : selectedLayerEvent b keep n t) :
    t ≤ (80*kernelConstant*(A*(2:ℝ)^σ))*(1+8*log n)^3*(n:ℝ)^(4*σ-2) := by
  obtain ⟨j,hj,i,_,_,bad⟩ := hit
  have one : (1:ℝ)≤n := by exact_mod_cast hn
  have np : 0<(n:ℝ) := zero_lt_one.trans_le one
  have four : 1≤(n:ℝ)^4 := one_le_pow₀ one
  let H := (A*(2:ℝ)^σ)*(n:ℝ)^(4*σ)
  have hp : 0≤H := by dsimp [H]; positivity
  have ctl (k : ℕ) (hk : k≤bandHi n j/2^i) : |fixedBandPrefix k|≤H := by
    have kn : k≤n^4 := hk.trans ((Nat.div_le_self ..).trans ((min_le_left ..).trans (Nat.div_le_self ..)))
    have hkr : (k:ℝ)≤(n:ℝ)^4 := by exact_mod_cast kn
    have base : (k:ℝ)+1≤2*(n:ℝ)^4 := by linarith only [hkr,four]
    have bound := mul_le_mul_of_nonneg_left (rpow_le_rpow (by positivity) base sp) ap
    rw [mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),←rpow_natCast_mul np.le] at bound
    norm_num only [Nat.cast_ofNat] at bound
    exact (control k).trans (bound.trans_eq (by dsimp [H]; ring))
  have alarm := adverse_layer_height hn hj tp.le hp bad ctl
  have factor : (n:ℝ)^(4*σ) = (n:ℝ)^(4*σ-2)*(n:ℝ)^2 := by
    rw [←rpow_two,←rpow_add np,sub_add_cancel]
  dsimp [H] at alarm
  rw [factor] at alarm
  apply le_of_mul_le_mul_right _ (pow_pos np 2)
  linarith only [alarm]

/-- If |M(k)| has exponent θ with arbitrary positive slack, every clipped
halving passes at all thresholds on every late block for δ > 8θ−4. -/
theorem selected_layer_frequency_of_prefix_exponent {θ δ : ℝ}
    (half : (1:ℝ)/2 ≤ θ) (gap : 8*θ-4 < δ) (power : HalvingMertens.PrefixExponent θ)
    (b : ℕ→ℕ) (keep : ℕ→ℕ→ℕ→Prop) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0<t →
      t*eventMass (selectedLayerEvent b keep) m t ≤ (m:ℝ)^δ := by
  let ε := (δ-(8*θ-4))/16
  have ep : 0<ε := by dsimp [ε]; linarith only [gap]
  obtain ⟨A,ap,ctl⟩ := power ε ep
  have σp : 0≤θ+ε := by linarith only [half,ep]
  apply event_subpower_from_height (α:=4*(θ+ε)-2)
    (by linarith only [half,ep]) (by positivity [kernelConstant_nonneg])
    (by dsimp [ε]; linarith only [gap])
    (height_from_prefix_power σp ap ctl b keep)

theorem shared_layers_of_prefix_exponent {θ δ : ℝ}
    (half : (1:ℝ)/2 ≤ θ) (gap : 8*θ-4 < δ) (power : HalvingMertens.PrefixExponent θ)
    (b : ℕ→ℕ) (keep : ℕ→ℕ→ℕ→Prop) : sharedEventBound (selectedLayerEvent b keep) δ := by
  obtain ⟨B,bound⟩ := eventually_atTop.mp
    (selected_layer_frequency_of_prefix_exponent half gap power b keep)
  exact ⟨1,zero_lt_one,fun A => ⟨max A B,le_max_left ..,fun j => by
    simpa using bound (max A B) (le_max_right ..) ((2:ℝ)^j) (by positivity)⟩⟩

end RiemannReduction.ShortTail.LossFrequency
