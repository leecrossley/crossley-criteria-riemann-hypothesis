import Mathlib
import ZetaShared.Perron
import ZetaCount.Final
import ZetaExplicit.Rect
import ZetaExplicit.LogDeriv
import ZetaExplicit.Residue
import ZetaExplicit.Sides
import ZetaExplicit.Height

/-! The truncated explicit formula for `ψ`, assembled from the truncated Perron formula, bounds
for `ζ'/ζ` in the strip, and the zero count in unit windows. -/

open Complex Set Filter Topology ComplexConjugate MeasureTheory

noncomputable section
namespace ZetaExplicit

open ZetaShared

theorem explicitFormula_of
    (hP : ZetaShared.PerronStatement) (hS : ZetaShared.StripLogDerivStatement)
    (hN : ZetaShared.ZeroCountStatement) : ZetaShared.ExplicitFormulaStatement := by
  obtain ⟨CP, hCP, hPer⟩ := hP
  obtain ⟨CS, hCS, hleft, hline, hhor⟩ := hS
  obtain ⟨CH, hCH, hheight⟩ := height_change hN
  obtain ⟨M, hM0, hM⟩ := exists_bound_right
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := (log_facts (le_refl 2) (le_refl 2)).2.2.2.2
  have hl2pos : 0 < Real.log 2 := by linarith
  set B : ℝ := max CS (1 + M) with hBdef
  have hBCS : CS ≤ B := le_max_left _ _
  have hBM : 1 + M ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := hCS.le.trans hBCS
  set K0 : ℝ := ‖zeroConst‖ / Real.log 2 with hK0def
  have hK00 : 0 ≤ K0 := div_nonneg (norm_nonneg _) hl2pos.le
  have hR0 : 0 ≤ 1 + M / Real.log 2 := by positivity
  refine ⟨CP + CH + 20 * B + 24 * CS + 6 * (1 + M / Real.log 2) + K0, by positivity,
    fun u T hT hTu => ⟨zerosBelow_finite T, ?_⟩⟩
  obtain ⟨T', hTT', hT'1, hT'⟩ := hhor T hT
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  obtain ⟨hL1, hLle, hule, h2u, -⟩ := log_facts hT hTu
  have hc1 := abscissa_gt_one hu
  have hc3 := abscissa_le_three hu
  set c : ℝ := perronAbscissa u with hc
  set X : ℝ := u * Real.log (u * T) ^ 2 / T with hX
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Real.log u := by linarith
  have hW0 : 0 ≤ ∑ᶠ ρ ∈ zerosBelow 1, (mult ρ : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  -- the pieces of the contour
  set F : ℂ → ℂ := perronIntegrand u with hF
  set Bot : ℂ := ∫ x in (-1 / 2 : ℝ)..c, F ((x : ℂ) + ((-T' : ℝ) : ℂ) * I) with hBot
  set Top : ℂ := ∫ x in (-1 / 2 : ℝ)..c, F ((x : ℂ) + (T' : ℂ) * I) with hTop
  set Rt : ℂ := ∫ y in (-T')..T', F ((c : ℂ) + (y : ℂ) * I) with hRt
  set Lf : ℂ := ∫ y in (-T')..T', F (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) with hLf
  set D₁ : ℂ := ∫ y in (-T')..(-T), F ((c : ℂ) + (y : ℂ) * I) with hD₁
  set RT : ℂ := ∫ y in (-T)..T, F ((c : ℂ) + (y : ℂ) * I) with hRT
  set D₂ : ℂ := ∫ y in T..T', F ((c : ℂ) + (y : ℂ) * I) with hD₂
  set ST : ℂ := ∑ᶠ ρ ∈ zerosBelow T, (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) with hST
  set ST' : ℂ := ∑ᶠ ρ ∈ zerosBelow T', (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) with hST'
  -- residue theorem
  have hres := residue_formula hu0 (x₂ := c) (T' := T') hc1 hT'0 hleft
    (fun σ h1 h2 => (hT' σ h1 h2).1)
  have h1 : Bot - Top + I * Rt - I * Lf =
      2 * Real.pi * I * ((u : ℂ) - ST' + zeroConst) := hres
  have h1' : Rt = 2 * Real.pi * ((u : ℂ) - ST' + zeroConst) + I * Bot - I * Top + Lf := by
    linear_combination (-I) * h1 +
      (Rt - Lf - 2 * Real.pi * ((u : ℂ) - ST' + zeroConst)) * Complex.I_mul_I
  -- splitting the right side
  have hcontR : Continuous (fun y : ℝ => F ((c : ℂ) + (y : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
    have hs0 : (c : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
    have hs1 : (c : ℂ) + (y : ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
    have hz : riemannZeta ((c : ℂ) + (y : ℂ) * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact hc1.le)
    have hca := continuousAt_perronIntegrand hu0 hs0 hs1 hz
    exact ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I) hca (by fun_prop)
  have h2 : Rt = D₁ + RT + D₂ := by
    rw [hD₁, hRT, hD₂,
      intervalIntegral.integral_add_adjacent_intervals (hcontR.intervalIntegrable _ _)
        (hcontR.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hcontR.intervalIntegrable _ _)
        (hcontR.intervalIntegrable _ _)]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have h3 : 2 * Real.pi * perronIntegral u T = RT := by
    have h : perronIntegral u T = (1 / (2 * (Real.pi : ℂ))) * RT := rfl
    rw [h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  -- the main identity
  set q : ℂ := I * Bot - I * Top + Lf - D₁ - D₂ with hq
  have key : (2 * Real.pi : ℂ) * (((Chebyshev.psi u - u : ℝ) : ℂ) + ST) =
      2 * Real.pi * ((((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T) + (ST - ST') + zeroConst)
        + q := by
    rw [hq]; push_cast
    linear_combination h1' - h2 + h3
  have hid : ((Chebyshev.psi u - u : ℝ) : ℂ) + ST =
      (((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T) + (ST - ST') + zeroConst
        + q / (2 * Real.pi) := by
    rw [← mul_right_inj' hpi, key]
    field_simp
  -- estimates
  have hPer' := hPer u T hT hTu
  have hHt : ‖ST - ST'‖ ≤ CH * X := by
    rw [norm_sub_rev]; exact hheight u T T' hT hTu hTT' hT'1
  have hbTop : ∀ x : ℝ, -1 / 2 ≤ x → x ≤ perronAbscissa u →
      ‖deriv riemannZeta ((x : ℂ) + (T' : ℂ) * I) / riemannZeta ((x : ℂ) + (T' : ℂ) * I)‖ ≤
        B * Real.log (T + 2) ^ 2 := by
    intro x hx1 hx2
    have hsq1 : 1 ≤ Real.log (T + 2) ^ 2 := by nlinarith
    rcases le_or_gt x 2 with hx | hx
    · exact ((hT' x hx1 hx).2).trans (mul_le_mul_of_nonneg_right hBCS (by positivity))
    · have hre : ((x : ℂ) + (T' : ℂ) * I).re = x := by simp
      have hb := hM ((x : ℂ) + (T' : ℂ) * I) (by rw [hre]; linarith) (by rw [hre]; linarith)
      rw [hre] at hb
      have h1x : 1 / (x - 1) ≤ 1 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      calc _ ≤ 1 / (x - 1) + M := hb
        _ ≤ B * 1 := by linarith
        _ ≤ B * Real.log (T + 2) ^ 2 := mul_le_mul_of_nonneg_left hsq1 hB0
  have hbBot : ∀ x : ℝ, -1 / 2 ≤ x → x ≤ perronAbscissa u →
      ‖deriv riemannZeta ((x : ℂ) + ((-T' : ℝ) : ℂ) * I) /
        riemannZeta ((x : ℂ) + ((-T' : ℝ) : ℂ) * I)‖ ≤ B * Real.log (T + 2) ^ 2 := by
    intro x hx1 hx2
    have hconj : (x : ℂ) + ((-T' : ℝ) : ℂ) * I = conj ((x : ℂ) + (T' : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hconj, norm_logDeriv_conj]
    exact hbTop x hx1 hx2
  have hTop' : ‖Top‖ ≤ 10 * B * X :=
    horiz_bound hT hTu hTT' (abs_of_pos hT'0) hB0 hbTop
  have hBot' : ‖Bot‖ ≤ 10 * B * X :=
    horiz_bound hT hTu hTT' (by rw [abs_neg, abs_of_pos hT'0]) hB0 hbBot
  have hLf' : ‖Lf‖ ≤ 24 * CS * X := left_bound hT hTu hTT' hT'1 hCS.le hline
  have hD₁' : ‖D₁‖ ≤ 3 * (1 + M / Real.log 2) * X :=
    right_piece hT hTu hM0 hM (by linarith) (by linarith) fun y hy => by
      rw [abs_of_neg (by linarith [hy.2])]; linarith [hy.2]
  have hD₂' : ‖D₂‖ ≤ 3 * (1 + M / Real.log 2) * X :=
    right_piece hT hTu hM0 hM hTT' hT'1 fun y hy => by
      rw [abs_of_pos (by linarith [hy.1])]; linarith [hy.1]
  have hq' : ‖q / (2 * Real.pi)‖ ≤ 20 * B * X + 24 * CS * X + 6 * (1 + M / Real.log 2) * X := by
    have hn : ‖q‖ ≤ ‖Bot‖ + ‖Top‖ + ‖Lf‖ + ‖D₁‖ + ‖D₂‖ := by
      rw [hq]
      calc ‖I * Bot - I * Top + Lf - D₁ - D₂‖
          ≤ ‖I * Bot - I * Top + Lf - D₁‖ + ‖D₂‖ := norm_sub_le _ _
        _ ≤ ‖I * Bot - I * Top + Lf‖ + ‖D₁‖ + ‖D₂‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ‖I * Bot - I * Top‖ + ‖Lf‖ + ‖D₁‖ + ‖D₂‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ‖I * Bot‖ + ‖I * Top‖ + ‖Lf‖ + ‖D₁‖ + ‖D₂‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖Bot‖ + ‖Top‖ + ‖Lf‖ + ‖D₁‖ + ‖D₂‖ := by simp
    have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [norm_div, hnorm]
    calc ‖q‖ / (2 * Real.pi) ≤ ‖q‖ := div_le_self (norm_nonneg _) h2pi
      _ ≤ _ := by linarith
  have hzc : ‖zeroConst‖ ≤ K0 * Real.log u := by
    rw [hK0def]
    calc ‖zeroConst‖ = ‖zeroConst‖ / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ ‖zeroConst‖ / Real.log 2 * Real.log u :=
          mul_le_mul_of_nonneg_left h2u (div_nonneg (norm_nonneg _) hl2pos.le)
  have hlogsq : u * Real.log u ^ 2 / T ≤ X := by
    rw [hX]
    have : Real.log u ^ 2 ≤ Real.log (u * T) ^ 2 := pow_le_pow_left₀ hY0 hule 2
    have h' : u * Real.log u ^ 2 ≤ u * Real.log (u * T) ^ 2 :=
      mul_le_mul_of_nonneg_left this hu0.le
    exact div_le_div_of_nonneg_right h' hT0.le
  have hPer'' : ‖((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T‖ ≤ CP * (X + Real.log u) :=
    hPer'.trans (mul_le_mul_of_nonneg_left (by linarith) hCP.le)
  rw [hid]
  have htri : ‖(((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T) + (ST - ST') + zeroConst
      + q / (2 * Real.pi)‖ ≤
      ‖((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T‖ + ‖ST - ST'‖ + ‖zeroConst‖
        + ‖q / (2 * Real.pi)‖ := by
    calc _ ≤ ‖(((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T) + (ST - ST') + zeroConst‖
          + ‖q / (2 * Real.pi)‖ := norm_add_le _ _
      _ ≤ ‖(((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T) + (ST - ST')‖ + ‖zeroConst‖
          + ‖q / (2 * Real.pi)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_add_le _ _
  refine htri.trans ?_
  set Ctot : ℝ := CP + CH + 20 * B + 24 * CS + 6 * (1 + M / Real.log 2) + K0 with hCtot
  have hbig : ‖((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T‖ + ‖ST - ST'‖ + ‖zeroConst‖
      + ‖q / (2 * Real.pi)‖ ≤ Ctot * (X + Real.log u) := by
    have e1 : 0 ≤ CH * Real.log u := by positivity
    have e2 : 0 ≤ B * Real.log u := by positivity
    have e3 : 0 ≤ CS * Real.log u := mul_nonneg hCS.le hY0
    have e4 : 0 ≤ (1 + M / Real.log 2) * Real.log u := mul_nonneg hR0 hY0
    have e5 : 0 ≤ K0 * X := mul_nonneg hK00 hX0
    rw [hCtot]
    nlinarith
  refine hbig.trans ?_
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hCtot0

/-- The same with the zero count supplied by `ZetaCount.zeroCountStatement`. -/
theorem explicitFormula_of_perron_strip
    (hP : ZetaShared.PerronStatement) (hS : ZetaShared.StripLogDerivStatement) :
    ZetaShared.ExplicitFormulaStatement :=
  explicitFormula_of hP hS ZetaCount.zeroCountStatement

end ZetaExplicit

#check @ZetaExplicit.explicitFormula_of
#print axioms ZetaExplicit.explicitFormula_of
#print axioms ZetaExplicit.explicitFormula_of_perron_strip
