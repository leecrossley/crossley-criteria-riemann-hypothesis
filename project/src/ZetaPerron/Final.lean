import Mathlib
import ZetaShared.Perron
import ZetaPerron.Error

/-! The truncated Perron formula for the Chebyshev function `ψ`. Mathlib only. -/

open Complex ArithmeticFunction
open scoped Real

noncomputable section

namespace ZetaPerron

/-- `ψ(u)` as a sum over all `n` with a cutoff. -/
lemma hasSum_psi (u : ℝ) :
    HasSum (fun n : ℕ => (Λ n : ℂ) * (if n ≤ ⌊u⌋₊ then (1 : ℂ) else 0))
      ((Chebyshev.psi u : ℝ) : ℂ) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => (Λ n : ℂ) * (if n ≤ ⌊u⌋₊ then (1 : ℂ) else 0))
    (s := Finset.Ioc 0 ⌊u⌋₊)
    (fun n hn => by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp
      · have hnot : ¬ n ≤ ⌊u⌋₊ := fun h => hn (Finset.mem_Ioc.mpr ⟨hpos, h⟩)
        show (Λ n : ℂ) * (if n ≤ ⌊u⌋₊ then (1 : ℂ) else 0) = 0
        rw [if_neg hnot, mul_zero])
  have e : ∑ n ∈ Finset.Ioc 0 ⌊u⌋₊, (Λ n : ℂ) * (if n ≤ ⌊u⌋₊ then (1 : ℂ) else 0)
      = ((Chebyshev.psi u : ℝ) : ℂ) := by
    unfold Chebyshev.psi
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [if_pos (Finset.mem_Ioc.mp hn).2, mul_one]
  rw [e] at h
  exact h

/-- **Truncated Perron formula** for the Chebyshev function, with constant `100`. -/
theorem perron_bound (u T : ℝ) (hT : 2 ≤ T) (hTu : T ≤ u) :
    ‖((Chebyshev.psi u : ℝ) : ℂ) - ZetaShared.perronIntegral u T‖
      ≤ 100 * (u * Real.log u ^ 2 / T + Real.log u) := by
  have hu0 : 0 ≤ u := by linarith
  exact perron_bound_aux u T (ZetaShared.perronAbscissa u) ⌊u⌋₊ hT hTu rfl
    (Nat.floor_le hu0) (Nat.lt_floor_add_one u) (Chebyshev.psi u) (hasSum_psi u)

theorem perronStatement : ZetaShared.PerronStatement :=
  ⟨100, by norm_num, fun u T hT hTu => perron_bound u T hT hTu⟩

end ZetaPerron

#print axioms ZetaPerron.perron_bound
#print axioms ZetaPerron.perronStatement
