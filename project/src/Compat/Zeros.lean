import Mathlib
import ZetaCount.Final

/-! Unit-window zero count for `riemannZeta`, directly re-exporting
`ZetaCount.zeroCountStatement` (`ZetaShared.ZeroCountStatement`). -/

namespace Compat

/-- Zeros of `riemannZeta` in unit windows `[t - 1, t + 1]`, counted with multiplicity,
number at most `C * log (|t| + 2)`. -/
theorem count_zeros_window_zeta : ZetaShared.ZeroCountStatement :=
  ZetaCount.zeroCountStatement

end Compat
