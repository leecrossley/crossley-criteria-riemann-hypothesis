import Mathlib
import ZetaShared.Perron
import ZetaCount.Final
import ZetaExplicit.LogDeriv
import ZetaExplicit.Sides

/-! Changing the truncation height of the sum over zeros by at most one. -/

open Complex Set Filter Topology

noncomputable section
namespace ZetaExplicit

open ZetaShared

lemma zerosBelow_mono {T T' : ℝ} (h : T ≤ T') : zerosBelow T ⊆ zerosBelow T' :=
  fun _ hρ => ⟨hρ.1, hρ.2.1, hρ.2.2.1.trans_le h, hρ.2.2.2⟩

lemma diff_subset_near {T T' : ℝ} (hT' : T' ≤ T + 1) :
    zerosBelow T' \ zerosBelow T ⊆ zerosNear T ∪ zerosNear (-T) := by
  rintro ρ ⟨⟨h0, h1, h2, hz⟩, hn⟩
  have hge : T ≤ |ρ.im| := by
    by_contra h
    exact hn ⟨h0, h1, not_le.mp h, hz⟩
  rcases le_or_gt 0 ρ.im with him | him
  · left
    rw [abs_of_nonneg him] at hge h2
    exact ⟨h0, h1, abs_le.mpr ⟨by linarith, by linarith⟩, hz⟩
  · right
    rw [abs_of_neg him] at hge h2
    exact ⟨h0, h1, abs_le.mpr ⟨by linarith, by linarith⟩, hz⟩

lemma norm_term_le {u T : ℝ} (hu : 1 ≤ u) (hT : 0 < T) {ρ : ℂ} (h1 : ρ.re < 1)
    (hge : T ≤ |ρ.im|) :
    ‖(mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (mult ρ : ℝ) * (u / T) := by
  have hu0 : 0 < u := by linarith
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_cpow_eq_rpow_re_of_pos hu0]
  have h2 : u ^ ρ.re ≤ u := by
    calc u ^ ρ.re ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu h1.le
      _ = u := Real.rpow_one u
  have h3 : T ≤ ‖ρ‖ := hge.trans (Complex.abs_im_le_norm ρ)
  exact mul_le_mul_of_nonneg_left (div_le_div₀ hu0.le h2 hT h3) (Nat.cast_nonneg _)

theorem height_change (hN : ZeroCountStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 →
      ‖∑ᶠ ρ ∈ zerosBelow T', (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) -
        ∑ᶠ ρ ∈ zerosBelow T, (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (u * T) ^ 2 / T) := by
  classical
  obtain ⟨C, hC, hcount⟩ := hN
  refine ⟨2 * C, by positivity, fun u T T' hT hTu hTT' hT'1 => ?_⟩
  have hu : 1 ≤ u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hL1, hLle, -, -, -⟩ := log_facts hT hTu
  set f : ℂ → ℂ := fun ρ => (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) with hf
  set D : Set ℂ := zerosBelow T' \ zerosBelow T with hD
  have hDfin : D.Finite := (zerosBelow_finite T').subset sdiff_subset
  have hsplit : ∑ᶠ ρ ∈ zerosBelow T', f ρ = ∑ᶠ ρ ∈ zerosBelow T, f ρ + ∑ᶠ ρ ∈ D, f ρ := by
    rw [← finsum_mem_union disjoint_sdiff_right (zerosBelow_finite T) hDfin,
      union_sdiff_cancel (zerosBelow_mono hTT')]
  rw [hsplit, add_sub_cancel_left]
  have hDsub := diff_subset_near (T := T) (T' := T') hT'1
  have hnear : (zerosNear T ∪ zerosNear (-T)).Finite := (hcount T).1.union (hcount (-T)).1
  have hmultD : ∑ᶠ ρ ∈ D, (mult ρ : ℝ) ≤ 2 * C * Real.log (T + 2) := by
    have h1 : ∑ᶠ ρ ∈ D, (mult ρ : ℝ) ≤ ∑ᶠ ρ ∈ zerosNear T ∪ zerosNear (-T), (mult ρ : ℝ) :=
      ZetaCount.finsum_mem_le_of_subset_of_nonneg hDsub hnear fun _ => Nat.cast_nonneg _
    have h2 := finsum_mem_union_inter (f := fun ρ : ℂ => (mult ρ : ℝ)) (hcount T).1 (hcount (-T)).1
    have h3 : 0 ≤ ∑ᶠ ρ ∈ zerosNear T ∩ zerosNear (-T), (mult ρ : ℝ) :=
      finsum_nonneg fun ρ => finsum_nonneg fun _ => Nat.cast_nonneg _
    have h4 := (hcount T).2
    have h5 := (hcount (-T)).2
    rw [abs_neg] at h5
    rw [abs_of_pos hT0] at h4 h5
    linarith
  calc ‖∑ᶠ ρ ∈ D, f ρ‖ = ‖∑ ρ ∈ hDfin.toFinset, f ρ‖ := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hDfin]
    _ ≤ ∑ ρ ∈ hDfin.toFinset, ‖f ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hDfin.toFinset, (mult ρ : ℝ) * (u / T) := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        rw [Set.Finite.mem_toFinset] at hρ
        obtain ⟨⟨h0, h1, h2, hz⟩, hn⟩ := hρ
        have hge : T ≤ |ρ.im| := by
          by_contra h
          exact hn ⟨h0, h1, not_le.mp h, hz⟩
        exact norm_term_le hu hT0 h1 hge
    _ = (∑ᶠ ρ ∈ D, (mult ρ : ℝ)) * (u / T) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hDfin, Finset.sum_mul]
    _ ≤ (2 * C * Real.log (T + 2)) * (u / T) :=
        mul_le_mul_of_nonneg_right hmultD (by positivity)
    _ ≤ (2 * C * Real.log (u * T) ^ 2) * (u / T) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : Real.log (T + 2) ≤ Real.log (u * T) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * C * (u * Real.log (u * T) ^ 2 / T) := by ring

end ZetaExplicit

#print axioms ZetaExplicit.height_change
