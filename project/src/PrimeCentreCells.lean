import PrimeExcessMean

open Set MeasureTheory
noncomputable section
namespace PrimeCentreMean

private def primeSumTo (N : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime,
    Real.log p * ThetaTransfer.tent (x/4/p)

private theorem extend_sum {x b : ℝ} (xb : x ≤ b) :
    ThetaTransfer.primeSum (x/4) = primeSumTo ⌊b⌋₊ x := by
  unfold ThetaTransfer.primeSum primeSumTo
  rw [show 4*(x/4) = x by ring]
  apply Finset.sum_subset_zero_on_sdiff
  · exact Finset.filter_subset_filter _ (Finset.range_mono (by
      have := Nat.floor_mono xb; omega))
  · intro p hp
    obtain ⟨upper, outside⟩ := Finset.mem_sdiff.mp hp
    have prim := (Finset.mem_filter.mp upper).2
    have lower : ⌊x⌋₊ < p := by
      by_contra! h
      exact outside (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), prim⟩)
    have px : x < p := (Nat.floor_lt' (by omega : p ≠ 0)).mp lower
    have hp0 : (0:ℝ) < p := by exact_mod_cast prim.pos
    have v : x/4/p < 1/4 := (div_lt_iff₀ hp0).mpr (by linarith)
    rw [ThetaTransfer.tent_pieces, if_neg (by linarith), if_neg (by linarith),
      if_neg (by linarith), mul_zero]
  · intro _ _; rfl

private theorem tent_mix {u v c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (total : c+d=1)
    (side : (2*u ≤ 1 ∧ 2*v ≤ 1) ∨ (1 ≤ 2*u ∧ 1 ≤ 2*v)) :
    ThetaTransfer.tent (c*u+d*v) ≤ c*ThetaTransfer.tent u + d*ThetaTransfer.tent v := by
  let hinge (k z : ℝ) := max (k*z-1) 0
  have affine (k : ℝ) : k*(c*u+d*v)-1 = c*(k*u-1)+d*(k*v-1) := by
    linarith only [total]
  have chord (k : ℝ) : hinge k (c*u+d*v) ≤ c*hinge k u+d*hinge k v := by
    unfold hinge
    rw [affine]
    apply max_le
    · gcongr <;> exact le_max_left _ _
    · positivity
  have middle : hinge 2 (c*u+d*v) = c*hinge 2 u+d*hinge 2 v := by
    unfold hinge
    rw [affine]
    rcases side with ⟨a,b⟩ | ⟨a,b⟩
    · rw [max_eq_right (sub_nonpos.mpr a), max_eq_right (sub_nonpos.mpr b),
        max_eq_right (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr a))
          (mul_nonpos_of_nonneg_of_nonpos hd (sub_nonpos.mpr b)))]
      ring
    · rw [max_eq_left (sub_nonneg.mpr a), max_eq_left (sub_nonneg.mpr b),
        max_eq_left (add_nonneg (mul_nonneg hc (sub_nonneg.mpr a))
          (mul_nonneg hd (sub_nonneg.mpr b)))]
  have four := chord 4
  have one := chord 1
  simp only [hinge, one_mul] at four one middle
  unfold ThetaTransfer.tent
  linarith only [four, one, middle]

/-- In the interval between two successive doubled primes, the tent surplus is convex.
The negative coefficient in its three ramps changes slope only at a doubled prime. -/
theorem excess_convex_between_centres {a b : ℝ}
    (noCentre : ∀ p : ℕ, p.Prime → 2*(p:ℝ) ≤ a ∨ b ≤ 2*(p:ℝ)) :
    ConvexOn ℝ (Icc a b) excess := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy c d hc hd total
  simp only [smul_eq_mul]
  have mix : c*x+d*y ∈ Icc a b := (convex_Icc a b : Convex ℝ _ ) hx hy hc hd total
  have atoms (p : ℕ) (prim : p.Prime) :
      Real.log p * ThetaTransfer.tent ((c*x+d*y)/4/p) ≤
        c*(Real.log p*ThetaTransfer.tent (x/4/p)) +
        d*(Real.log p*ThetaTransfer.tent (y/4/p)) := by
    have pp : (0:ℝ) < p := by exact_mod_cast prim.pos
    have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast prim.one_le)
    have side (z : ℝ) : 2*(z/4/p) = z/(2*p) := by ring
    have h := tent_mix (u := x/4/p) (v := y/4/p) hc hd total (by
      simp only [side]
      rcases noCentre p prim with left | right
      · right
        exact ⟨(le_div_iff₀ (by positivity)).mpr (by linarith [hx.1]),
          (le_div_iff₀ (by positivity)).mpr (by linarith [hy.1])⟩
      · left
        exact ⟨(div_le_iff₀ (by positivity)).mpr (by linarith [hx.2]),
          (div_le_iff₀ (by positivity)).mpr (by linarith [hy.2])⟩)
    rw [show (c*x+d*y)/4/p = c*(x/4/p)+d*(y/4/p) by ring]
    linarith only [mul_le_mul_of_nonneg_left h hlog]
  have hp : ThetaTransfer.primeSum ((c*x+d*y)/4) ≤
      c*ThetaTransfer.primeSum (x/4)+d*ThetaTransfer.primeSum (y/4) := by
    rw [extend_sum mix.2, extend_sum hx.2, extend_sum hy.2]
    unfold primeSumTo
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun p hp => atoms p (Finset.mem_filter.mp hp).2)
  unfold excess
  apply max_le
  · positivity
  · linarith only [hp, mul_le_mul_of_nonneg_left
      (le_max_right 0 (ThetaTransfer.primeSum (x/4)-x/2*Real.log 2)) hc,
      mul_le_mul_of_nonneg_left
      (le_max_right 0 (ThetaTransfer.primeSum (y/4)-y/2*Real.log 2)) hd]

theorem excess_continuousOn (a b : ℝ) : ContinuousOn excess (Icc a b) := by
  let f (x : ℝ) := max 0 (primeSumTo ⌊b⌋₊ x - x/2*Real.log 2)
  have cf : Continuous f := by unfold f primeSumTo ThetaTransfer.tent; fun_prop
  exact cf.continuousOn.congr (fun x hx => by
    unfold excess f; rw [extend_sum hx.2])

end PrimeCentreMean
