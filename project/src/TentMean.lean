import PrimeWindow

open Set MeasureTheory
noncomputable section

namespace TentWindow

/-- A subpower bound for the unrestricted integral of a nonnegative majorant of the
normalized surplus suffices. The majorant may have arbitrarily large pointwise spikes. -/
theorem rh_of_subpower_integral {δ U₁ : ℝ} (hδ : 0 < δ) (mass : ℝ → ℝ → ℝ)
    (comparison : ∀ U ≥ U₁, ∀ u ∈ Icc U ((1 + δ) * U),
      -ThetaTransfer.primePowerDeficit u ≤ Real.exp (u / 2) * mass U u)
    (windows : ∀ ε : ℝ, 0 < ε → ∀ U₀ : ℝ, ∃ U ≥ U₀,
      IntegrableOn (mass U) (Icc U ((1 + δ) * U)) ∧
      (∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ mass U u) ∧
      (∫ u in Icc U ((1 + δ) * U), mass U u) ≤ Real.exp (ε * U)) :
    RiemannHypothesis := by
  apply ZetaShared.Reflection.rh_of_right
  intro s hs _
  let θ := (1 / 2 + min 1 s.re) / 2
  have ht : 1 / 2 < θ := by dsimp [θ]; linarith [lt_min (by norm_num : (1 : ℝ) / 2 < 1) hs]
  have ht1 : θ < 1 := by dsimp [θ]; linarith [min_le_left (1 : ℝ) s.re]
  have hts : θ < s.re := by dsimp [θ]; linarith [min_le_right (1 : ℝ) s.re]
  apply ThetaTransfer.zeta_zeroFree_of_surplus (by linarith : 0 < θ) ht1 hδ _ s hts
  intro η hη U₀
  have gap : 0 < θ - 1 / 2 := by linarith
  obtain ⟨U, hU, integrable, pos, small⟩ := windows (θ - 1 / 2) gap (max U₀ (max 0 U₁))
  have large := (le_max_right U₀ (max 0 U₁)).trans hU
  have hzero := (le_max_left 0 U₁).trans large
  have after := (le_max_right 0 U₁).trans large
  let c := Real.exp (-((θ - 1 / 2) * U))
  have hc : 0 ≤ c := (Real.exp_pos _).le
  let major (u : ℝ) := (c * Real.exp (θ * u)) * mass U u
  have weighted : (fun u => major u * Real.exp (-θ * u)) = fun u => c * mass U u := by
    funext u
    calc major u * Real.exp (-θ * u) =
         (c * mass U u) * (Real.exp (θ * u) * Real.exp (-θ * u)) := by dsimp [major]; ring
         _ = c * mass U u := by rw [← Real.exp_add]; ring_nf; simp
  refine ⟨U, (le_max_left _ _).trans hU, major, ?_, ?_, ?_⟩
  · rw [weighted]
    exact integrable.const_mul c
  · intro u hu
    have grow : Real.exp (u / 2) ≤ c * Real.exp (θ * u) := by
      dsimp [c]
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith only [mul_nonneg gap.le (sub_nonneg.mpr hu.1)]
    exact ⟨mul_nonneg (mul_nonneg hc (Real.exp_pos _).le) (pos u hu),
      (comparison U after u hu).trans (mul_le_mul_of_nonneg_right grow (pos u hu))⟩
  · rw [weighted, integral_const_mul]
    calc c * (∫ u in Icc U ((1 + δ) * U), mass U u) ≤ c * Real.exp ((θ - 1 / 2) * U) :=
           mul_le_mul_of_nonneg_left small hc
         _ = 1 := by dsimp [c]; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
         _ ≤ Real.exp (η * U) := Real.one_le_exp (mul_nonneg hη.le hzero)

#print axioms rh_of_subpower_integral

/-- A bound on the logarithmic mean of the negative part alone is enough.
The comparison is with the original centered prime-power observable. -/
theorem rh_of_signed_negative_part_mean {δ L U₁ : ℝ} (hδ : 0 < δ) (R : ℝ → ℝ → ℝ)
    (comparison : ∀ U ≥ U₁, ∀ u ∈ Icc U ((1 + δ) * U),
      (R U u - L) * Real.exp (u / 2) ≤ ThetaTransfer.primePowerDeficit u)
    (windows : ∀ ε : ℝ, 0 < ε → ∀ U₀ : ℝ, ∃ U ≥ U₀,
      IntegrableOn (fun u => max 0 (-R U u)) (Icc U ((1 + δ) * U)) ∧
      (∫ u in Icc U ((1 + δ) * U), max 0 (-R U u)) ≤ Real.exp (ε * U)) :
    RiemannHypothesis := by
  let K := max L 0
  apply rh_of_subpower_integral (U₁ := U₁) hδ (fun U u => K + max 0 (-R U u))
  · intro U hU u hu
    have cmp := comparison U hU u hu
    have rhs : L - R U u ≤ K + max 0 (-R U u) := by
      dsimp [K]
      linarith [le_max_left L 0, le_max_right 0 (-R U u)]
    have h := mul_le_mul_of_nonneg_right rhs (Real.exp_pos (u / 2)).le
    linarith
  · intro ε hε U₀
    let a := ε / 2
    have ha : 0 < a := by dsimp [a]; linarith
    have eventually_large : ∀ᶠ U : ℝ in Filter.atTop,
        0 < U ∧ K * δ * U ≤ Real.exp (a * U) ∧ 2 ≤ Real.exp (a * U) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
        (tendsto_exp_mul_div_rpow_atTop 1 a ha).eventually_ge_atTop (K * δ),
        (Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop ha)).eventually_ge_atTop 2]
        with U hpos hlin hexp
      exact ⟨hpos, (le_div_iff₀ hpos).mp (by simpa using hlin), hexp⟩
    obtain ⟨U₂, h₂⟩ := Filter.eventually_atTop.mp eventually_large
    obtain ⟨U, hU, hint, hsize⟩ := windows a ha (max U₀ U₂)
    obtain ⟨hpos, hlin, hexp⟩ := h₂ U ((le_max_right _ _).trans hU)
    have hconst : IntegrableOn (fun _ : ℝ => K) (Icc U ((1 + δ) * U)) :=
      continuousOn_const.integrableOn_Icc
    refine ⟨U, (le_max_left _ _).trans hU, hconst.add hint, fun _ _ =>
      add_nonneg (le_max_right _ _) (le_max_left _ _), ?_⟩
    rw [integral_add hconst hint, setIntegral_const, Real.volume_real_Icc_of_le
      (by nlinarith only [mul_pos hδ hpos] : U ≤ (1 + δ) * U), smul_eq_mul]
    calc ((1 + δ) * U - U) * K + (∫ u in Icc U ((1 + δ) * U), max 0 (-R U u))
          ≤ 2 * Real.exp (a * U) := by linarith only [hlin, hsize]
         _ ≤ Real.exp (a * U) * Real.exp (a * U) :=
           mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
         _ = Real.exp (ε * U) := by rw [← Real.exp_add]; congr 1; dsimp [a]; ring

#print axioms rh_of_signed_negative_part_mean
end TentWindow
