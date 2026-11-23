import Mathlib
import IndependentLandau.Ramp

/-! The continued transform `zetaPhi`: definition, holomorphy off the zeros, isolation of the
zeros and the simple poles at the zeros.

We use Mathlib's entire function `riemannZeta₁ s = (s - 1) ζ(s)` (value `1` and derivative `γ`
at `s = 1`). With `N s = γ - ζ₁'(s)/ζ₁(s)`, which vanishes at `1`,

  `Φ s = (N s / (s - 1)) / s + (1 + γ) / s`,

where `N s / (s - 1)` is taken as the divided difference `dslope N 1 s`, which removes the
singularity at `s = 1`. -/

open Complex Set Filter Topology

noncomputable section

namespace IndependentLandau

local notation "γ" => (Real.eulerMascheroniConstant : ℂ)

/-- `γ - ζ₁'/ζ₁`, which vanishes at `1`. -/
def zetaN (s : ℂ) : ℂ := γ - deriv riemannZeta₁ s / riemannZeta₁ s

/-- The continuation of the Laplace transform of the centred ramp. -/
def zetaPhi (s : ℂ) : ℂ := dslope zetaN 1 s / s + (1 + γ) / s

lemma zetaN_one : zetaN 1 = 0 := by simp [zetaN]

lemma zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

lemma zeta₁_eq_zero_iff {s : ℂ} : riemannZeta₁ s = 0 ↔ riemannZeta s = 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [riemannZeta_one_ne_zero]
  · rw [zeta₁_eq hs, mul_eq_zero, or_iff_right (sub_ne_zero.mpr hs)]

lemma mem_zetaZeros {ρ : ℂ} : ρ ∈ zetaZeros ↔ 0 < ρ.re ∧ riemannZeta₁ ρ = 0 := by
  rw [zeta₁_eq_zero_iff]; rfl

lemma analyticAt_zeta₁ (s : ℂ) : AnalyticAt ℂ riemannZeta₁ s :=
  differentiable_riemannZeta₁.analyticAt s

lemma zeta₁_not_eventually_zero (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, riemannZeta₁ w = 0 := by
  intro h
  have han : AnalyticOnNhd ℂ riemannZeta₁ univ := fun x _ => analyticAt_zeta₁ x
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h
    (mem_univ 1)
  simp at this

/-- The zeros do not accumulate anywhere. -/
lemma zetaZeros_iso (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ∉ zetaZeros := by
  rcases (analyticAt_zeta₁ z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h (zeta₁_not_eventually_zero z)
  · filter_upwards [h] with w hw hmem
    exact hw (mem_zetaZeros.mp hmem).2

lemma analyticAt_zetaN {s : ℂ} (h : riemannZeta₁ s ≠ 0) : AnalyticAt ℂ zetaN s :=
  analyticAt_const.sub ((analyticAt_zeta₁ s).deriv.div (analyticAt_zeta₁ s) h)

lemma analyticAt_dslope_zetaN {s : ℂ} (h : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ (dslope zetaN 1) s := by
  have hV : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} :=
    isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  have h1 : (1 : ℂ) ∈ {s : ℂ | riemannZeta₁ s ≠ 0} := by simp
  have hd : DifferentiableOn ℂ zetaN {s : ℂ | riemannZeta₁ s ≠ 0} := fun x hx =>
    (analyticAt_zetaN hx).differentiableAt.differentiableWithinAt
  exact ((Complex.differentiableOn_dslope (hV.mem_nhds h1)).mpr hd).analyticAt (hV.mem_nhds h)

lemma analyticAt_zetaPhi {s : ℂ} (h : riemannZeta₁ s ≠ 0) (hs0 : s ≠ 0) :
    AnalyticAt ℂ zetaPhi s :=
  ((analyticAt_dslope_zetaN h).div analyticAt_id hs0).add
    (analyticAt_const.div analyticAt_id hs0)

lemma differentiableOn_zetaPhi :
    DifferentiableOn ℂ zetaPhi ({s : ℂ | 0 < s.re} \ zetaZeros) := by
  rintro s ⟨hs, hz⟩
  have hs' : 0 < s.re := hs
  have h1 : riemannZeta₁ s ≠ 0 := fun h => hz (mem_zetaZeros.mpr ⟨hs', h⟩)
  have h0 : s ≠ 0 := by rintro rfl; simp at hs'
  exact (analyticAt_zetaPhi h1 h0).differentiableAt.differentiableWithinAt

/-- The explicit formula for `zetaPhi` away from `0`, `1` and the zeros. -/
lemma zetaPhi_eq {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hζ : riemannZeta s ≠ 0) :
    zetaPhi s = -deriv riemannZeta s / riemannZeta s / (s * (s - 1)) - 1 / (s - 1) ^ 2
      + (1 + γ) / (s - 1) := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hZ : riemannZeta₁ s ≠ 0 := fun h0 => hζ (zeta₁_eq_zero_iff.mp h0)
  rw [zetaPhi, dslope_of_ne _ hs1, slope_def_field, zetaN_one, zetaN,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1, riemannZeta_eq_inv_sub_mul hs1]
  generalize deriv riemannZeta₁ s = D
  generalize riemannZeta₁ s = Z at hZ ⊢
  field_simp
  ring

/-- A quotient `A s / (s - ρ)` with `A` analytic at `ρ` is a principal part plus an analytic
function. -/
lemma exists_pole_decomp {A : ℂ → ℂ} {ρ : ℂ} (hA : AnalyticAt ℂ A ρ) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ s, s ≠ ρ → A s / (s - ρ) = A ρ / (s - ρ) + h s := by
  refine ⟨dslope A ρ, ?_, ?_⟩
  · have hV : IsOpen {x | AnalyticAt ℂ A x} := isOpen_analyticAt ℂ A
    have hd : DifferentiableOn ℂ A {x | AnalyticAt ℂ A x} := fun x hx =>
      (show AnalyticAt ℂ A x from hx).differentiableAt.differentiableWithinAt
    exact ((Complex.differentiableOn_dslope (hV.mem_nhds hA)).mpr hd).analyticAt
      (hV.mem_nhds hA)
  · intro s hs
    rw [dslope_of_ne _ hs, slope_def_field]
    have : s - ρ ≠ 0 := sub_ne_zero.mpr hs
    field_simp
    ring

/-- Near a zero of order `m`, the logarithmic derivative of `ζ₁` is `m / (s - ρ)` plus the
logarithmic derivative of a nonvanishing analytic function. -/
lemma logDeriv_zeta₁_near_zero {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0) :
    ∃ (m : ℕ) (k : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ k ρ ∧ k ρ ≠ 0 ∧
      ∀ᶠ s in 𝓝[≠] ρ,
        deriv riemannZeta₁ s / riemannZeta₁ s = m / (s - ρ) + deriv k s / k s := by
  obtain ⟨m, k, hk, hkρ, hev⟩ :=
    (analyticAt_zeta₁ ρ).exists_eventuallyEq_pow_smul_nonzero_iff.mpr
      (zeta₁_not_eventually_zero ρ)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · have := hev.self_of_nhds
      simp [hρ] at this
      exact absurd this.symm hkρ
    · exact h
  refine ⟨m, k, hm, hk, hkρ, ?_⟩
  have hev' : riemannZeta₁ =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ m * k z := by
    filter_upwards [hev] with z hz
    simpa [smul_eq_mul] using hz
  have hderiv : deriv riemannZeta₁ =ᶠ[𝓝 ρ] deriv (fun z => (z - ρ) ^ m * k z) := hev'.deriv
  have hkan : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ k s := hk.eventually_analyticAt
  have hkne : ∀ᶠ s in 𝓝 ρ, k s ≠ 0 := hk.continuousAt.eventually_ne hkρ
  filter_upwards [hev'.filter_mono nhdsWithin_le_nhds, hderiv.filter_mono nhdsWithin_le_nhds,
    hkan.filter_mono nhdsWithin_le_nhds, hkne.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with s h1 h2 h3 h4 h5
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr h5
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hd : HasDerivAt (fun z => (z - ρ) ^ (m' + 1) * k z)
      (((m' + 1 : ℕ) : ℂ) * (s - ρ) ^ m' * k s + (s - ρ) ^ (m' + 1) * deriv k s) s := by
    have hp : HasDerivAt (fun z : ℂ => (z - ρ) ^ (m' + 1))
        (((m' + 1 : ℕ) : ℂ) * (s - ρ) ^ m') s := by
      simpa using ((hasDerivAt_id s).sub_const ρ).fun_pow (m' + 1)
    exact hp.mul h3.differentiableAt.hasDerivAt
  rw [h2, hd.deriv, h1]
  field_simp
  push_cast
  ring

/-- `zetaPhi` has a simple pole at each zero, with positive real residue at a real zero. -/
lemma zetaPhi_pole {ρ : ℂ} (hρ : ρ ∈ zetaZeros) :
    ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
      ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, zetaPhi s = c / (s - ρ) + h s := by
  obtain ⟨hre, hζ⟩ := hρ
  have hZ : riemannZeta₁ ρ = 0 := zeta₁_eq_zero_iff.mpr hζ
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at hre
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hZ
  obtain ⟨m, k, hm, hk, hkρ, hev⟩ := logDeriv_zeta₁_near_zero hZ
  let A : ℂ → ℂ := fun s =>
    ((γ * (s - ρ) - m - (s - ρ) * (deriv k s / k s)) / (s - 1)) / s + (1 + γ) * (s - ρ) / s
  have hA : AnalyticAt ℂ A ρ := by
    have hid : AnalyticAt ℂ (fun s : ℂ => s) ρ := analyticAt_id
    have hsub : AnalyticAt ℂ (fun s : ℂ => s - ρ) ρ := hid.sub analyticAt_const
    have hs1 : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := hid.sub analyticAt_const
    have hq : AnalyticAt ℂ (fun s => deriv k s / k s) ρ := hk.deriv.div hk hkρ
    exact (((((analyticAt_const.mul hsub).sub analyticAt_const).sub (hsub.mul hq)).div hs1
      (sub_ne_zero.mpr hρ1)).div hid hρ0).add ((analyticAt_const.mul hsub).div hid hρ0)
  have hAρ : A ρ = -(m : ℂ) / (ρ * (ρ - 1)) := by
    have h1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
    simp only [A, sub_self, mul_zero, zero_mul, zero_div, add_zero, zero_sub, sub_zero]
    field_simp
  obtain ⟨h, hh, hdecomp⟩ := exists_pole_decomp hA
  refine ⟨A ρ, ?_, ?_, h, hh, ?_⟩
  · rw [hAρ]
    exact div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne'))
      (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1))
  · intro him
    have hρr : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hlt : ρ.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
    have hc : A ρ = ((-(m : ℝ) / (ρ.re * (ρ.re - 1)) : ℝ) : ℂ) := by
      rw [hAρ]
      conv_lhs => rw [hρr]
      push_cast
      rfl
    rw [hc]
    refine ⟨?_, Complex.ofReal_im _⟩
    rw [Complex.ofReal_re]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg hre (by linarith))
  · have hne1 : ∀ᶠ s in 𝓝 ρ, s ≠ 1 := isOpen_ne.mem_nhds hρ1
    have hne0 : ∀ᶠ s in 𝓝 ρ, s ≠ 0 := isOpen_ne.mem_nhds hρ0
    filter_upwards [hev, eventually_mem_nhdsWithin, hne1.filter_mono nhdsWithin_le_nhds,
      hne0.filter_mono nhdsWithin_le_nhds] with s h1 h2 h3 h4
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr h2
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h3
    rw [← hdecomp s h2]
    rw [zetaPhi, dslope_of_ne _ h3, slope_def_field, zetaN_one, sub_zero, zetaN, h1]
    simp only [A]
    generalize deriv k s / k s = q
    field_simp
    ring

end IndependentLandau
