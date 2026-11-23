import Mathlib

/-! Factoring finitely many zeros out of an entire function, and the resulting partial-fraction
form of the logarithmic derivative. Mathlib only. -/

open Complex Set Filter Topology

noncomputable section
namespace ZetaExplicit

/-- Zeros in a finite set can be divided out of an entire function that vanishes identically
nowhere: `Z s = ∏ (s - ρ)^{ord_ρ} · g s` with `g` entire and non-zero on the set. -/
theorem exists_factor {Z : ℂ → ℂ} (hZ : Differentiable ℂ Z)
    (hnt : ∀ z, analyticOrderAt Z z ≠ ⊤) (S : Finset ℂ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ s, Z s = (∏ ρ ∈ S, (s - ρ) ^ analyticOrderNatAt Z ρ) * g s) ∧ ∀ ρ ∈ S, g ρ ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨Z, hZ, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨g₀, hg₀, hfac, hne⟩ := ih
    set n := analyticOrderNatAt Z a with hn
    set P : ℂ → ℂ := fun s => ∏ ρ ∈ S, (s - ρ) ^ analyticOrderNatAt Z ρ with hP
    have hPa : P a ≠ 0 := by
      rw [hP]
      refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr ?_)
      rintro rfl; exact ha hρ
    have hPan : AnalyticAt ℂ P a := by
      have : Differentiable ℂ P := by rw [hP]; fun_prop
      exact this.analyticAt a
    have hg₀an : AnalyticAt ℂ g₀ a := hg₀.analyticAt a
    have hZeq : Z = P * g₀ := funext fun s => hfac s
    have hord : analyticOrderAt g₀ a = (n : ℕ∞) := by
      have h1 : analyticOrderAt Z a = analyticOrderAt P a + analyticOrderAt g₀ a := by
        rw [hZeq]; exact analyticOrderAt_mul hPan hg₀an
      rw [hPan.analyticOrderAt_eq_zero.mpr hPa, zero_add] at h1
      rw [← h1, hn, Nat.cast_analyticOrderNatAt (hnt a)]
    obtain ⟨h, hhan, hha, hev⟩ := (hg₀an.analyticOrderAt_eq_natCast).mp hord
    simp only [smul_eq_mul] at hev
    refine ⟨Function.update (fun s => g₀ s / (s - a) ^ n) a (h a), ?_, ?_, ?_⟩
    · intro s
      rcases eq_or_ne s a with rfl | hs
      · refine hhan.differentiableAt.congr_of_eventuallyEq ?_
        filter_upwards [hev] with z hz
        rcases eq_or_ne z s with rfl | hzs
        · simp
        · have : z - s ≠ 0 := sub_ne_zero.mpr hzs
          rw [Function.update_of_ne hzs, hz]
          field_simp
      · have hd : DifferentiableAt ℂ (fun s => g₀ s / (s - a) ^ n) s :=
          (hg₀ s).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hs))
        refine hd.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
        exact Function.update_of_ne hz _ _
    · intro s
      rw [Finset.prod_insert ha]
      rcases eq_or_ne s a with rfl | hs
      · rw [Function.update_self, hfac s, hev.self_of_nhds]
        ring
      · have : s - a ≠ 0 := sub_ne_zero.mpr hs
        rw [Function.update_of_ne hs, hfac s]
        field_simp
        rfl
    · intro ρ hρ
      rcases Finset.mem_insert.mp hρ with rfl | hρS
      · rwa [Function.update_self]
      · have hρa : ρ ≠ a := by rintro rfl; exact ha hρS
        rw [Function.update_of_ne hρa]
        exact div_ne_zero (hne ρ hρS) (pow_ne_zero _ (sub_ne_zero.mpr hρa))

/-- Partial fractions for the logarithmic derivative of a factored function. -/
theorem logDeriv_of_factor {Z g : ℂ → ℂ} {S : Finset ℂ} {m : ℂ → ℕ} (hg : Differentiable ℂ g)
    (hfac : ∀ s, Z s = (∏ ρ ∈ S, (s - ρ) ^ m ρ) * g s) {s : ℂ} (hs : s ∉ S) (hgs : g s ≠ 0) :
    deriv Z s / Z s = ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) + deriv g s / g s := by
  have hZeq : Z = fun s => (∏ ρ ∈ S, (s - ρ) ^ m ρ) * g s := funext hfac
  have hne : ∀ ρ ∈ S, (s - ρ) ^ m ρ ≠ 0 := fun ρ hρ =>
    pow_ne_zero _ (sub_ne_zero.mpr (by rintro rfl; exact hs hρ))
  have hd : ∀ ρ ∈ S, DifferentiableAt ℂ (fun s : ℂ => (s - ρ) ^ m ρ) s := fun ρ _ => by fun_prop
  have h1 : logDeriv Z s = logDeriv (fun s => ∏ ρ ∈ S, (s - ρ) ^ m ρ) s + logDeriv g s := by
    rw [hZeq]
    exact logDeriv_mul s (Finset.prod_ne_zero_iff.mpr hne) hgs (by fun_prop) (hg s)
  rw [logDeriv_prod hne hd] at h1
  rw [← logDeriv_apply, ← logDeriv_apply, h1]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
  simp [div_eq_mul_inv]

end ZetaExplicit

#print axioms ZetaExplicit.exists_factor
#print axioms ZetaExplicit.logDeriv_of_factor
