import ZetaPerron.Final
import ZetaStrip.Final
import ZetaExplicit.Final

/-! The truncated explicit formula for the Chebyshev function, with no hypothesis.
Mathlib only. -/

namespace ZetaClassical

theorem explicitFormulaStatement : ZetaShared.ExplicitFormulaStatement :=
  ZetaExplicit.explicitFormula_of ZetaPerron.perronStatement
    ZetaStrip.stripLogDerivStatement ZetaCount.zeroCountStatement

#print axioms explicitFormulaStatement

end ZetaClassical
