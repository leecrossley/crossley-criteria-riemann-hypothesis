import PrimeCentreBudget
import RampWindowEquivalence

namespace PrimeCentreMean

/-- The same finite ordinary-prime condition recovers actual, coefficient-one ramp
windows at every strictly larger exponent below one. -/
theorem rampWindows_of_primeCentreBudget {θ δ σ : ℝ} (half : 1/2 ≤ θ)
    (below : θ < σ) (one : σ < 1) (width : 0 < δ) (small : SmallPrimeCentreBudget θ δ) :
    DirectRampEquivalence.OrdinaryWindowUnit σ := by
  have zeroFree := zeroFree_of_excessMean half (below.trans one) width
    (excessMean_of_primeCentreBudget (by linarith) width small)
  exact (DirectRampEquivalence.ordinaryWindow_three_way_iff ⟨half,below.trans one⟩).1.mpr
    zeroFree σ ⟨below,one⟩

end PrimeCentreMean
