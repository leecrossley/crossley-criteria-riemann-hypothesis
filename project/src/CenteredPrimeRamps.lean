import MobiusRamps
import Compat.Ramp

namespace RiemannReduction.DivisorBand
noncomputable section

private lemma ramp_agrees (x : ℝ) : ZetaShared.rampG x = Compat.rampGz x :=
  (Compat.rampGz_eq_rampG x).symm

theorem deficit_eq_gz {x : ℝ} (xp : 0 < x) :
    D x = -Compat.rampGz x + 3*Compat.rampGz (x/2) - 2*Compat.rampGz (x/4) := by
  have h := ThetaTransfer.deficit_eq_centered_ramps (y := x/4) (by linarith)
  rw [show 4*(x/4)=x by ring,show 2*(x/4)=x/2 by ring,ramp_agrees x,
      ramp_agrees (x/2),ramp_agrees (x/4)] at h
  unfold D c
  linarith

end
end RiemannReduction.DivisorBand
