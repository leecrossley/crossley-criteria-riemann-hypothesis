import Mathlib
import ZetaClassical.Explicit

/-! Truncated explicit formula for `Chebyshev.psi u - u`, directly re-exporting
`ZetaClassical.explicitFormulaStatement` (`ZetaShared.ExplicitFormulaStatement`). -/

namespace Compat

/-- Truncated explicit formula for `Chebyshev.psi u - u` over nontrivial zeros of `riemannZeta`. -/
theorem truncated_explicit_formula_zeta : ZetaShared.ExplicitFormulaStatement :=
  ZetaClassical.explicitFormulaStatement

end Compat
