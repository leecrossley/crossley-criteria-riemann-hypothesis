import Mathlib
import ZetaShared.Perron
import ZetaCount.Order
import ZetaExplicit.Rect
import ZetaExplicit.Factor
import ZetaExplicit.LogDeriv

/-! The residue computation: the boundary integral of the Perron integrand over the rectangle
`[-1/2, x₂] × [-T', T']`. -/

open Complex Set Filter Topology ComplexConjugate

noncomputable section
namespace ZetaExplicit

open ZetaShared

/-- The constant `-ζ'(0)/ζ(0)`, written through `Z s = (s - 1) ζ(s)`. -/
def zeroConst : ℂ := -(deriv riemannZeta₁ 0 / riemannZeta₁ 0) - 1

/-- No zeros of `ζ` on the closed rectangle other than those counted by `zerosBelow T'`. -/
lemma zeta_ne_zero_of_mem_rect {x₂ T' : ℝ}
    (hleft : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 0 → riemannZeta s ≠ 0)
    (hheight : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 2 → riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0)
    {s : ℂ} (hs : s ∈ rectClosed (-1 / 2) x₂ (-T') T') (hsS : s ∉ zerosBelow T') :
    riemannZeta s ≠ 0 := by
  obtain ⟨h1, -, h3, h4⟩ := hs
  intro hz
  have hre1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hre0 : 0 < s.re := by
    by_contra h
    exact hleft s h1 (not_lt.mp h) hz
  have him : |s.im| < T' := by
    rcases lt_or_eq_of_le (abs_le.mpr ⟨h3, h4⟩) with h | h
    · exact h
    · exfalso
      rcases abs_eq_abs.mp (h.trans (abs_of_nonneg ((abs_nonneg _).trans h.le)).symm) with h' | h'
      · apply hheight s.re h1 (by linarith)
        rw [← h']; simpa using hz
      · apply zeta_conj_ne_zero (hheight s.re h1 (by linarith))
        have : conj ((s.re : ℂ) + (T' : ℂ) * I) = s := by
          apply Complex.ext <;> simp [h']
        rw [this]; exact hz
  exact hsS ⟨hre0, hre1, him, hz⟩

theorem residue_formula {u : ℝ} (hu : 0 < u) {x₂ T' : ℝ} (hx₂ : 1 < x₂) (hT' : 0 < T')
    (hleft : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 0 → riemannZeta s ≠ 0)
    (hheight : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 2 → riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0) :
    rectInt (perronIntegrand u) (-1 / 2) x₂ (-T') T' =
      2 * Real.pi * I * ((u : ℂ) - ∑ᶠ ρ ∈ zerosBelow T', (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)
        + zeroConst) := by
  classical
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  set S : Finset ℂ := (zerosBelow_finite T').toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ ρ ∈ zerosBelow T' := fun ρ => by rw [hS, Set.Finite.mem_toFinset]
  obtain ⟨g, hg, hfac, hgS⟩ := exists_factor differentiable_riemannZeta₁ zeta₁_order_ne_top S
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt riemannZeta₁ ρ with hm
  -- basic facts about points of `S`
  have hS0 : ∀ ρ ∈ S, ρ ≠ 0 := fun ρ hρ h => by
    have := ((hmemS ρ).mp hρ).1; rw [h] at this; simp at this
  have hS1 : ∀ ρ ∈ S, ρ ≠ 1 := fun ρ hρ h => by
    have := ((hmemS ρ).mp hρ).2.1; rw [h] at this; simp at this
  have h0S : (0 : ℂ) ∉ S := fun h => hS0 0 h rfl
  have h1S : (1 : ℂ) ∉ S := fun h => hS1 1 h rfl
  have hmult : ∀ ρ ∈ S, (m ρ : ℂ) = (mult ρ : ℂ) := fun ρ hρ => by
    rw [hm, ZetaCount.mult_eq_orderNat_zeta₁ (hS1 ρ hρ)]
  -- the open set where the cofactor does not vanish
  set U : Set ℂ := {s | g s ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hg.continuous continuous_const
  have hζrect : ∀ s ∈ rectClosed (-1 / 2) x₂ (-T') T', s ∉ S → riemannZeta s ≠ 0 :=
    fun s hs hsS => zeta_ne_zero_of_mem_rect hleft hheight hs (fun h => hsS ((hmemS s).mpr h))
  have hsub : rectClosed (-1 / 2) x₂ (-T') T' ⊆ U := by
    intro s hs
    by_cases hsS : s ∈ S
    · exact hgS s hsS
    · have hZ : riemannZeta₁ s ≠ 0 := fun h =>
        hζrect s hs hsS (IndependentLandau.zeta₁_eq_zero_iff.mp h)
      intro h0
      apply hZ
      rw [hfac s, show g s = 0 from h0, mul_zero]
  -- the holomorphic pieces
  set K : ℂ → ℂ := fun s => deriv g s / g s with hK
  have hKd : DifferentiableOn ℂ K U := fun s hs =>
    (((hg.analyticAt s).deriv.differentiableAt).div (hg s) hs).differentiableWithinAt
  set E : ℂ → ℂ := fun s => (u : ℂ) ^ s with hE
  have hEd : Differentiable ℂ E := fun s => (differentiableAt_id.const_cpow (Or.inl hu0))
  set c₀ : ℂ := ∑ ρ ∈ S, (m ρ : ℂ) / ρ with hc₀
  set H₀ : ℂ → ℂ := fun s => E s * (c₀ - K s - 1) with hH₀
  have hH₀d : DifferentiableOn ℂ H₀ U :=
    hEd.differentiableOn.mul ((differentiableOn_const _).sub hKd |>.sub (differentiableOn_const _))
  set H : ℂ → ℂ → ℂ := fun a => if a = 0 then H₀ else if a = 1 then E
    else fun s => -((m a : ℂ) / a) * E s with hH
  set P : Finset ℂ := insert 0 (insert 1 S) with hP
  have h0P : (0 : ℂ) ∉ insert 1 S := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact zero_ne_one h
    · exact h0S h
  have hsum : ∀ f : ℂ → ℂ, ∑ a ∈ P, f a = f 0 + (f 1 + ∑ ρ ∈ S, f ρ) := fun f => by
    rw [hP, Finset.sum_insert h0P, Finset.sum_insert h1S]
  have hH0 : H 0 = H₀ := by simp [hH]
  have hH1 : H 1 = E := by simp [hH]
  have hHρ : ∀ ρ ∈ S, H ρ = fun s => -((m ρ : ℂ) / ρ) * E s := fun ρ hρ => by
    simp [hH, hS0 ρ hρ, hS1 ρ hρ]
  have hxpos : (-1 / 2 : ℝ) ≤ x₂ := by linarith
  have hypos : -T' ≤ T' := by linarith
  have hres := rectInt_eq_sum_residues (x₁ := -1 / 2) (x₂ := x₂) (y₁ := -T') (y₂ := T') hxpos hypos
    hUo hsub P H ?_ ?_ (F := perronIntegrand u) ?_
  · rw [hres, hsum (fun a => H a a), hH0, hH1]
    have hsumS : ∑ ρ ∈ S, H ρ ρ = -∑ ρ ∈ S, (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [hHρ ρ hρ, hmult ρ hρ]
      simp only [hE]; ring
    have hfin : ∑ᶠ ρ ∈ zerosBelow T', (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) =
        ∑ ρ ∈ S, (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) :=
      finsum_mem_eq_finite_toFinset_sum _ (zerosBelow_finite T')
    have h0U : g 0 ≠ 0 := hsub ⟨by simp; norm_num, by simp; linarith, by simp; linarith,
      by simp; linarith⟩
    have hK0 : deriv riemannZeta₁ 0 / riemannZeta₁ 0 = -c₀ + K 0 := by
      rw [logDeriv_of_factor hg hfac h0S h0U, hc₀, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [zero_sub, div_neg]
    have hE0 : E 0 = 1 := by simp [hE]
    have hE1 : E 1 = (u : ℂ) := by simp [hE]
    rw [hsumS, hfin, hH₀, zeroConst, hK0, hE1]
    simp only [hE0]
    ring
  · -- differentiability of the numerators
    intro a ha
    rw [hP, Finset.mem_insert, Finset.mem_insert] at ha
    rcases ha with rfl | rfl | ha
    · rw [hH0]; exact hH₀d
    · rw [hH1]; exact hEd.differentiableOn
    · rw [hHρ a ha]; exact (hEd.differentiableOn.const_mul _)
  · -- poles are strictly inside
    intro a ha
    rw [hP, Finset.mem_insert, Finset.mem_insert] at ha
    rcases ha with rfl | rfl | ha
    · refine ⟨by simp; norm_num, by simp; linarith, by simp; linarith, by simp; linarith⟩
    · refine ⟨by simp; norm_num, by simp; linarith, by simp; linarith, by simp; linarith⟩
    · obtain ⟨h0, h1, h2, -⟩ := (hmemS a).mp ha
      rw [abs_lt] at h2
      exact ⟨by linarith, by linarith, h2.1, h2.2⟩
  · -- the partial fraction identity on the boundary
    intro s hs
    have hsc : s ∈ rectClosed (-1 / 2) x₂ (-T') T' := rectBdry_subset_closed hs
    have hsS : s ∉ S := by
      intro h
      obtain ⟨h0, h1, h2, -⟩ := (hmemS s).mp h
      rw [abs_lt] at h2
      obtain ⟨-, -, -, -, h' | h' | h' | h'⟩ := hs <;> linarith
    have hs0 : s ≠ 0 := by
      rintro rfl
      obtain ⟨-, -, -, -, h' | h' | h' | h'⟩ := hs <;> simp at h' <;> linarith
    have hs1 : s ≠ 1 := by
      rintro rfl
      obtain ⟨-, -, -, -, h' | h' | h' | h'⟩ := hs <;> simp at h' <;> linarith
    have hζ : riemannZeta s ≠ 0 := hζrect s hsc hsS
    have hgs : g s ≠ 0 := hsub hsc
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hlog : deriv riemannZeta s / riemannZeta s =
        ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) + K s - 1 / (s - 1) := by
      rw [logDeriv_zeta_eq hs1 hζ, logDeriv_of_factor hg hfac hsS hgs]
    have hA : ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) = s * ∑ ρ ∈ S, (m ρ : ℂ) / ρ / (s - ρ) - c₀ := by
      rw [hc₀, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have h1 : ρ ≠ 0 := hS0 ρ hρ
      have h2 : s - ρ ≠ 0 := sub_ne_zero.mpr (by rintro rfl; exact hsS hρ)
      field_simp
      ring
    have hB : ∑ ρ ∈ S, H ρ s / (s - ρ) = -E s * ∑ ρ ∈ S, (m ρ : ℂ) / ρ / (s - ρ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [hHρ ρ hρ]; ring
    rw [hsum (fun a => H a s / (s - a)), hH0, hH1, hB]
    unfold perronIntegrand
    rw [hlog, hA, hH₀]
    simp only [hE, sub_zero]
    field_simp
    ring

end ZetaExplicit

#print axioms ZetaExplicit.residue_formula
