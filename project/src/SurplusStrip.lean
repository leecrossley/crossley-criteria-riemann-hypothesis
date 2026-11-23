import SurplusAllocation
import ContactQuartic

/-! Transport an independently supplied zero-free strip to the actual payments.
The tracker inputs have their original hypotheses at the Lean version boundary. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Filter Real RiemannReduction.DivisorBand.FourthMass
open RiemannReduction.DivisorBand.FourthMass.Contact

/-- The reconstructed payments inherit the signed remainder's strip exponent.
The coefficient is one once the exponent is taken strictly above 8σ−4. -/
theorem payment_window_of_strip {σ ε : ℝ} (lo : 1/2 < σ) (hi : σ ≤ 7/8)
    (free : RiemannReduction.ZetaWindow.Strip.ZeroFreeTo σ) (he : 8*σ-4 < ε) :
    ∀ᶠ m : ℕ in atTop, window (fun n => unpaid n (allocation n (funds n))) m ≤ (m:ℝ)^ε := by
  obtain ⟨C,_,bound⟩ := quartic_bound_of_strip lo hi free
  let a := 8*σ-4
  have ap : 0 < a := by dsimp [a]; linarith
  have gap : 0 < ε-a := sub_pos.mpr he
  have grow := ((tendsto_rpow_atTop gap).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (C+1)
  filter_upwards [negative_loss_distance a ap,loss_with_credit,grow,eventually_ge_atTop (10^8:ℕ)]
    with m distance eqn big hm
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  change C+1 ≤ (m:ℝ)^(ε-a) at big
  have neg : loss remainder m ≤ C*(m:ℝ)^a := by
    simpa [loss,window,mass,signedRemainder,a] using (bound (-1) (Or.inr rfl) m hm)
  have scale := mul_le_mul_of_nonneg_right big (rpow_nonneg mp.le a)
  rw [←rpow_add mp,sub_add_cancel] at scale
  rw [allocation_window (by omega),←eqn]
  linarith only [neg,(abs_le.mp distance).1,scale]

/-- Exact rational threshold using Joseph Bebel's published zero-free input. -/
theorem payment_window_of_contact (given : AllDirichletAbove boundary) (upper : boundary ≤ rankedUpper)
    {ε : ℝ} (he : 8*rankedUpper-4 < ε) :
    ∀ᶠ m : ℕ in atTop, window (fun n => unpaid n (allocation n (funds n))) m ≤ (m:ℝ)^ε := by
  apply payment_window_of_strip (σ:=rankedUpper) (by norm_num [rankedUpper]) (by norm_num [rankedUpper]) _ he
  intro s hs
  exact ordinaryAbove given (upper.trans_lt hs)

theorem payment_window_2986767 (given : AllDirichletAbove boundary) (upper : boundary ≤ rankedUpper) :
    ∀ᶠ m : ℕ in atTop, window (fun n => unpaid n (allocation n (funds n))) m ≤
      (m:ℝ)^(2986767/1000000:ℝ) :=
  payment_window_of_contact given upper (by norm_num [rankedUpper])

end RiemannReduction.ShortTail.SignPairs
