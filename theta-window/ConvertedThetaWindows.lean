import ThetaDirectResult
import FixedLossShellBridge
import ReverseSizeWindow
import Reflection

noncomputable section

open FixedLossConversion Crossley.PureArithmetic

namespace ConvertedThetaWindows

/-- The ordinary window of the archived theta construction in the variable
used by the converted arithmetic modules. -/
theorem ordinary_window {θ : ℝ} (hθ : 1/2 < θ) (A : ℝ) :
    ∃ Y ≥ max A 2, ∀ x ∈ Set.Icc Y (Y^(3/2:ℝ)), IndependentLandau.rampG x ≤ x^θ := by
  obtain ⟨Y, hY, hw⟩ := ThetaExplicit.ordinary_common θ hθ A
  refine ⟨Y, hY, fun x hx => ?_⟩
  have same : Deduction.G x = IndependentLandau.rampG x := by
    unfold Deduction.G Deduction.ramp IndependentLandau.rampG
    rw [Complex.re_sum]
    simp only [mul_one, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact same ▸ hw x hx

/-- The geometric witness inhabits the converted host for each allowed accuracy. -/
def principal_window {θ : ℝ} (half : 1/2 < θ) (top : θ < 1) :
    SingleHostPrincipalWindow θ 1 where
  theta_pos := lt_trans (by norm_num : (0:ℝ) < 1/2) half
  theta_lt_one := top
  C_pos := zero_lt_one
  host := canonicalSingleHost
  cofinal_window := by
    intro A
    obtain ⟨Y, hY, hw⟩ := ordinary_window half A
    exact ⟨Y, hY, fun x hx => by simpa [canonicalSingleHost] using hw x hx⟩

/-- The exact fixed input of the converted shell theorem. -/
def principal_window_87 : SingleHostPrincipalWindow (87/100) 1 :=
  principal_window (by norm_num) (by norm_num)

/-- A second, finer fixed accuracy supplies all the integer witnesses in the
numerical theta design via the arithmetic reverse construction. -/
theorem numerical_design : SchemeFreeSelectedThetaDesign37_900 := by
  apply ReverseSizeWindow.sufficient
  intro A
  obtain ⟨Y, hY, hw⟩ := ordinary_window
    (by norm_num [ReverseSizeWindow.exponent] : (1/2:ℝ) < ReverseSizeWindow.exponent) (max A 3)
  exact ⟨Y, (le_max_left _ _).trans hY, fun x hx => by simpa only [one_mul] using hw x hx⟩

/-- Numerical design, independently implemented Landau conversion, and the
explicit ordinary half-plane including its requested boundary. -/
theorem zero_free_349_400 (s : ℂ) (hs : (349/400:ℝ) ≤ s.re) : riemannZeta s ≠ 0 :=
  zeta_zeroFree_087_of_schemeFreeThetaDesign numerical_design s
    (lt_of_lt_of_le (by norm_num : (87/100:ℝ) < 349/400) hs)

open Filter RiemannReduction.ShortTail.LossFrequency in
/-- Apply the existing converted theorem to the inhabited host. It gives the
full-shell moment and the simultaneous bound for every frequency threshold. -/
theorem full_shell_298 :
    (∀ᶠ m : ℕ in atTop, weighted uniformShellScore m ≤ (m : ℝ)^(149/50:ℝ)) ∧
    (∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0 < t →
      t * frequency uniformShellScore m t ≤ 2*(m : ℝ)^(149/50:ℝ)) :=
  full_shell_298_of_fixedLoss_conversion principal_window_87

/-- Full ordinary RH through the converted single-host Landau theorem.
Choose the geometric accuracy separately for each hypothetical right-hand zero. -/
theorem ordinary_rh : RiemannHypothesis := by
  apply RiemannReduction.rh_of_right
  intro s hs _
  obtain ⟨θ, half, upper⟩ := exists_between (lt_min hs (by norm_num : (1/2:ℝ) < 1))
  exact zero_free_of_singleHost_window
    (principal_window half (upper.trans_le (min_le_right _ _))) s
    (upper.trans_le (min_le_left _ _))

#print axioms principal_window
#print axioms principal_window_87
#print axioms numerical_design
#print axioms zero_free_349_400
#print axioms full_shell_298
#print axioms ordinary_rh

end ConvertedThetaWindows
