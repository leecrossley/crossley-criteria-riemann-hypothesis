import ShortDivisorTransfer

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

private theorem freq_mono {z v : ℕ → ℝ} {m : ℕ} {t s : ℝ}
    (cover : ∀ n ∈ Icc m (m^2), t < z n → s < v n) :
    frequency z m t ≤ frequency v m s := by
  apply sum_le_sum
  intro n hn
  by_cases h : t < z n
  · simp only [if_pos h,if_pos (cover n hn h),le_refl]
  · simp only [if_neg h]
    split <;> positivity

private theorem transport {z v : ℕ → ℝ}
    (cover : ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 2*(m:ℝ)^η ≤ t →
      frequency z m t ≤ frequency v m (t/2)) (good : sameBlockWeak v) : sameBlockWeak z := by
  intro δ hp
  obtain ⟨C,cp,pass⟩ := good δ hp
  let η := δ/4
  have ep : 0 < η := by dsimp [η]; linarith
  have grow := ((tendsto_rpow_atTop ep).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  obtain ⟨u,after⟩ := eventually_atTop.mp ((cover η ep).and ((low_thresholds z hp).and grow))
  refine ⟨2*(1+C),by positivity,fun A => ?_⟩
  obtain ⟨m,large,levels⟩ := pass (max (max A 1) u)
  have hA := (le_max_left A 1).trans ((le_max_left _ _).trans large)
  have m1 := (le_max_right A 1).trans ((le_max_left _ _).trans large)
  obtain ⟨transfer,weakLow,big⟩ := after m ((le_max_right _ _).trans large)
  change 2 ≤ (m:ℝ)^η at big
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  have root : (m:ℝ)^η*(m:ℝ)^η = (m:ℝ)^(δ/2) := by
    rw [←rpow_add mp]
    congr 1
    dsimp [η]
    ring
  have cut := mul_le_mul_of_nonneg_right big (rpow_nonneg mp.le η)
  rw [root] at cut
  refine ⟨m,hA,fun j => ?_⟩
  by_cases small : (2:ℝ)^j ≤ (m:ℝ)^(δ/2)
  · exact (weakLow _ (by positivity) small).trans
      (by nlinarith only [rpow_nonneg mp.le δ,mul_nonneg cp.le (rpow_nonneg mp.le δ)])
  · have largeT := cut.trans (le_of_not_ge small)
    cases j with
    | zero =>
      rw [pow_zero] at largeT
      linarith only [big,largeT]
    | succ j =>
      have f := transfer _ largeT
      rw [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2:ℝ) ≠ 0)] at f
      rw [pow_succ]
      have h := mul_le_mul_of_nonneg_left f (by positivity : 0 ≤ (2:ℝ)^j)
      linarith only [h,levels j,rpow_nonneg mp.le δ]

/-- One can use only the corrected n² tables in the frequency conjecture,
including its same-block and all-threshold quantifiers. -/
theorem short_frequency_iff : sameBlockWeak score ↔ sameBlockWeak shortScore := by
  constructor
  · apply transport
    intro η hp
    filter_upwards [identical_large_hits_up_to_factor_two hp] with m both t ht
    exact freq_mono fun n hn => (both t ht n hn).2
  · apply transport
    intro η hp
    filter_upwards [identical_large_hits_up_to_factor_two hp] with m both t ht
    exact freq_mono fun n hn => (both t ht n hn).1

end RiemannReduction.ShortTail.LossFrequency
