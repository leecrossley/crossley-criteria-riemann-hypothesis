import Mathlib
import ZetaShared.Statements
import IndependentLandau.Analytic

/-! Multiplicities: the order of `ζ` at `ρ ≠ 1` equals the order of `riemannZeta₁`, and in the
open critical strip the order of `ζ` is invariant under `ρ ↦ 1 - ρ`. -/

open Complex Set Filter Topology

noncomputable section
namespace ZetaCount

lemma analyticAt_zeta {ρ : ℂ} (h : ρ ≠ 1) : AnalyticAt ℂ riemannZeta ρ :=
  analyticOn_riemannZeta ρ h

/-- Away from `1`, `ζ` and `(s - 1) ζ(s)` vanish to the same order. -/
lemma order_zeta_eq_order_zeta₁ {ρ : ℂ} (h : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ = analyticOrderAt riemannZeta₁ ρ := by
  have hev : riemannZeta₁ =ᶠ[𝓝 ρ] (fun s : ℂ => s - 1) * riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h] with s hs
    exact IndependentLandau.zeta₁_eq hs
  have ha : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := by fun_prop
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul ha (analyticAt_zeta h),
    ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr h), zero_add]

lemma mult_eq_orderNat_zeta₁ {ρ : ℂ} (h : ρ ≠ 1) :
    ZetaShared.mult ρ = analyticOrderNatAt riemannZeta₁ ρ := by
  unfold ZetaShared.mult analyticOrderNatAt
  rw [order_zeta_eq_order_zeta₁ h]

lemma analyticAt_completedZeta {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta ρ := by
  have hopen : IsOpen ({0}ᶜ ∩ {1}ᶜ : Set ℂ) :=
    isOpen_compl_singleton.inter isOpen_compl_singleton
  have hd : DifferentiableOn ℂ completedRiemannZeta ({0}ᶜ ∩ {1}ᶜ) := fun s hs =>
    (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds ⟨h0, h1⟩)

/-- In `re s > 0`, away from `1`, `ζ` and the completed zeta function vanish to the same order. -/
lemma order_zeta_eq_order_completed {ρ : ℂ} (hre : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ = analyticOrderAt completedRiemannZeta ρ := by
  have h0 : ρ ≠ 0 := by rintro rfl; simp at hre
  have hev : riemannZeta =ᶠ[𝓝 ρ] completedRiemannZeta * (fun s => (Gammaℝ s)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
    rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]; rfl
  have hG : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul (analyticAt_completedZeta h0 h1) hG,
    hG.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre)), add_zero]

lemma order_completed_one_sub (ρ : ℂ) :
    analyticOrderAt completedRiemannZeta (1 - ρ) = analyticOrderAt completedRiemannZeta ρ := by
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hd : deriv (fun s : ℂ => 1 - s) ρ ≠ 0 := by
    rw [deriv_const_sub, deriv_id'']; norm_num
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta) hg hd
  have e : completedRiemannZeta ∘ (fun s : ℂ => 1 - s) = completedRiemannZeta := by
    funext s; exact completedRiemannZeta_one_sub s
  rw [e] at h
  exact h.symm

/-- The functional equation preserves multiplicities in the open critical strip. -/
theorem mult_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ZetaShared.mult (1 - ρ) = ZetaShared.mult ρ := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  have hre' : 0 < (1 - ρ).re := by simp; linarith
  have hρ1' : (1 - ρ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold ZetaShared.mult analyticOrderNatAt
  rw [order_zeta_eq_order_completed hre' hρ1', order_zeta_eq_order_completed h0 hρ1,
    order_completed_one_sub]

end ZetaCount
