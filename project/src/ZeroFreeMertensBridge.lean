import HalvingPower
import ZeroFreeToMertens

noncomputable section

namespace RiemannReduction.ShortTail.LossFrequency
open Filter

/-- A zero-free half-plane supplies the shared all-threshold signed frequency exponent. -/
theorem selected_layer_frequency_of_zeroFree {θ δ : ℝ} (half : 1/2 ≤ θ) (one : θ ≤ 1)
    (hz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) (gap : 8*θ-4 < δ)
    (b : ℕ → ℕ) (keep : ℕ → ℕ → ℕ → Prop) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0 < t →
      t * eventMass (selectedLayerEvent b keep) m t ≤ (m:ℝ)^δ :=
  selected_layer_frequency_of_prefix_exponent half gap (HalvingMertens.prefixExponent_of_zeroFree half one hz) b keep

/-- Exact exponent obtained from the ordinary 7/8 zero-free theorem. -/
theorem selected_layer_frequency_of_seven_eighths
    (hz : ∀ {s : ℂ}, (7/8:ℝ) < s.re → riemannZeta s ≠ 0)
    {δ : ℝ} (gap : 3 < δ) (b : ℕ → ℕ) (keep : ℕ → ℕ → ℕ → Prop) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0 < t →
      t * eventMass (selectedLayerEvent b keep) m t ≤ (m:ℝ)^δ :=
  selected_layer_frequency_of_zeroFree (θ:=7/8) (by norm_num) (by norm_num)
    (fun _ hs => hz hs) (by linarith only [gap]) b keep

end RiemannReduction.ShortTail.LossFrequency
