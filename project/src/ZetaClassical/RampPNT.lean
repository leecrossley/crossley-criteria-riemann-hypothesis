import ZetaRegion.Main
import ZetaRamp.Final

/-! The prime number theorem for the centred ramp with the classical error term,
with no hypothesis. Mathlib only. -/

namespace ZetaClassical

theorem rampPNTStatement : ZetaShared.RampPNTStatement :=
  ZetaRamp.rampPNT_of_region ZetaRegion.regionStatement

#print axioms rampPNTStatement

end ZetaClassical
