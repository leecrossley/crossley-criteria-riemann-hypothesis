import Mathlib
import ZetaShared.Statements
import ZetaCount.RightHalf

/-! The zero count in unit windows: the left half of the window at height `t` is reflected by
`ρ ↦ 1 - ρ` into the right half of the window at height `-t`. -/

open Complex Set Filter Topology Metric
open ZetaShared

noncomputable section
namespace ZetaCount

/-- Zeros in the left half of the window at height `t`. -/
def leftZeros (t : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0}

lemma zerosNear_eq (t : ℝ) : zerosNear t = leftZeros t ∪ rightZeros t := by
  ext ρ
  simp only [zerosNear, leftZeros, rightZeros, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    rcases lt_or_ge ρ.re (1 / 2) with h | h
    · exact Or.inl ⟨h0, h, h2, h3⟩
    · exact Or.inr ⟨h, h1, h2, h3⟩
  · rintro (⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩)
    · exact ⟨h0, by linarith, h2, h3⟩
    · exact ⟨by linarith, h1, h2, h3⟩

lemma disjoint_left_right (t : ℝ) : Disjoint (leftZeros t) (rightZeros t) := by
  rw [Set.disjoint_left]
  intro ρ hl hr
  have h1 := hl.2.1
  have h2 := hr.1
  linarith

lemma zerosNear_finite (t : ℝ) : (zerosNear t).Finite := by
  refine ((isCompact_closedBall ((t : ℂ) * I) 2).inter_riemannZetaZeros_finite).subset
    fun ρ hρ => ⟨?_, hρ.2.2.2⟩
  obtain ⟨h0, h1, h2, -⟩ := hρ
  rw [mem_closedBall, dist_eq_norm]
  have h := Complex.norm_le_abs_re_add_abs_im (ρ - (t : ℂ) * I)
  have e1 : (ρ - (t : ℂ) * I).re = ρ.re := by simp
  have e2 : (ρ - (t : ℂ) * I).im = ρ.im - t := by simp
  rw [e1, e2, abs_of_pos h0] at h
  linarith

lemma leftZeros_finite (t : ℝ) : (leftZeros t).Finite :=
  (zerosNear_finite t).subset (by rw [zerosNear_eq]; exact subset_union_left)

/-- The functional equation carries zeros in the strip to zeros. -/
lemma zeta_one_sub_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 := by
  have hn : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]

lemma image_left_subset_right (t : ℝ) :
    (fun ρ : ℂ => 1 - ρ) '' leftZeros t ⊆ rightZeros (-t) := by
  rintro _ ⟨ρ, ⟨h0, h1, h2, h3⟩, rfl⟩
  refine ⟨?_, ?_, ?_, zeta_one_sub_eq_zero h0 (by linarith) h3⟩
  · simp; linarith
  · simp; linarith
  · have e : (1 - ρ).im - -t = -(ρ.im - t) := by simp; ring
    rw [e, abs_neg]; exact h2

lemma finsum_mem_le_of_subset_of_nonneg {α : Type*} {f : α → ℝ} {A B : Set α} (hAB : A ⊆ B)
    (hB : B.Finite) (hf : ∀ x, 0 ≤ f x) : ∑ᶠ x ∈ A, f x ≤ ∑ᶠ x ∈ B, f x := by
  have hnn : 0 ≤ ∑ᶠ x ∈ B \ A, f x := finsum_nonneg fun x => finsum_nonneg fun _ => hf x
  calc ∑ᶠ x ∈ A, f x ≤ ∑ᶠ x ∈ A, f x + ∑ᶠ x ∈ B \ A, f x := by linarith
    _ = ∑ᶠ x ∈ A ∪ B \ A, f x :=
      (finsum_mem_union disjoint_sdiff_right (hB.subset hAB) (hB.subset sdiff_subset)).symm
    _ = ∑ᶠ x ∈ B, f x := by rw [union_sdiff_cancel hAB]

/-- The left half of the window at `t` is dominated by the right half of the window at `-t`. -/
lemma leftCount_le (t : ℝ) :
    ∑ᶠ ρ ∈ leftZeros t, (mult ρ : ℝ) ≤ ∑ᶠ ρ ∈ rightZeros (-t), (mult ρ : ℝ) := by
  have hinj : (leftZeros t).InjOn (fun ρ : ℂ => 1 - ρ) := fun a _ b _ h => by
    simpa using h
  calc ∑ᶠ ρ ∈ leftZeros t, (mult ρ : ℝ)
      = ∑ᶠ ρ ∈ leftZeros t, (mult (1 - ρ) : ℝ) :=
        finsum_mem_congr rfl fun ρ hρ => by rw [mult_one_sub hρ.1 (by linarith [hρ.2.1])]
    _ = ∑ᶠ w ∈ (fun ρ : ℂ => 1 - ρ) '' leftZeros t, (mult w : ℝ) :=
        (finsum_mem_image (f := fun w => (mult w : ℝ)) hinj).symm
    _ ≤ ∑ᶠ ρ ∈ rightZeros (-t), (mult ρ : ℝ) :=
        finsum_mem_le_of_subset_of_nonneg (image_left_subset_right t) (rightZeros_finite (-t))
          fun x => Nat.cast_nonneg _

/-- The Riemann zeta function has `O(log (|t| + 2))` nontrivial zeros, with multiplicity, in each
unit window of the critical strip. -/
theorem zeroCountStatement : ZetaShared.ZeroCountStatement := by
  refine ⟨2 * rightConst, by have := rightConst_pos; positivity, fun t => ⟨zerosNear_finite t, ?_⟩⟩
  rw [zerosNear_eq, finsum_mem_union (disjoint_left_right t) (leftZeros_finite t)
    (rightZeros_finite t)]
  have h1 := (leftCount_le t).trans (rightCount_le (-t))
  have h2 := rightCount_le t
  rw [abs_neg] at h1
  linarith

end ZetaCount

#print axioms ZetaCount.zeroCountStatement
